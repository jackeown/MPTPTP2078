%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:49:05 EST 2020

% Result     : Theorem 1.58s
% Output     : Refutation 1.58s
% Verified   : 
% Statistics : Number of formulae       :   91 ( 235 expanded)
%              Number of leaves         :   17 (  71 expanded)
%              Depth                    :   19
%              Number of atoms          :  292 (1023 expanded)
%              Number of equality atoms :   46 (  91 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f668,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f589,f591,f667])).

fof(f667,plain,(
    ~ spl8_12 ),
    inference(avatar_contradiction_clause,[],[f666])).

fof(f666,plain,
    ( $false
    | ~ spl8_12 ),
    inference(subsumption_resolution,[],[f665,f40])).

fof(f40,plain,(
    ~ r1_tarski(k8_relat_1(sK0,sK2),k8_relat_1(sK1,sK3)) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,
    ( ~ r1_tarski(k8_relat_1(sK0,sK2),k8_relat_1(sK1,sK3))
    & r1_tarski(sK0,sK1)
    & r1_tarski(sK2,sK3)
    & v1_relat_1(sK3)
    & v1_relat_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f13,f24,f23])).

fof(f23,plain,
    ( ? [X0,X1,X2] :
        ( ? [X3] :
            ( ~ r1_tarski(k8_relat_1(X0,X2),k8_relat_1(X1,X3))
            & r1_tarski(X0,X1)
            & r1_tarski(X2,X3)
            & v1_relat_1(X3) )
        & v1_relat_1(X2) )
   => ( ? [X3] :
          ( ~ r1_tarski(k8_relat_1(sK0,sK2),k8_relat_1(sK1,X3))
          & r1_tarski(sK0,sK1)
          & r1_tarski(sK2,X3)
          & v1_relat_1(X3) )
      & v1_relat_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,
    ( ? [X3] :
        ( ~ r1_tarski(k8_relat_1(sK0,sK2),k8_relat_1(sK1,X3))
        & r1_tarski(sK0,sK1)
        & r1_tarski(sK2,X3)
        & v1_relat_1(X3) )
   => ( ~ r1_tarski(k8_relat_1(sK0,sK2),k8_relat_1(sK1,sK3))
      & r1_tarski(sK0,sK1)
      & r1_tarski(sK2,sK3)
      & v1_relat_1(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f13,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( ~ r1_tarski(k8_relat_1(X0,X2),k8_relat_1(X1,X3))
          & r1_tarski(X0,X1)
          & r1_tarski(X2,X3)
          & v1_relat_1(X3) )
      & v1_relat_1(X2) ) ),
    inference(flattening,[],[f12])).

% (19117)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
fof(f12,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( ~ r1_tarski(k8_relat_1(X0,X2),k8_relat_1(X1,X3))
          & r1_tarski(X0,X1)
          & r1_tarski(X2,X3)
          & v1_relat_1(X3) )
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( v1_relat_1(X2)
       => ! [X3] :
            ( v1_relat_1(X3)
           => ( ( r1_tarski(X0,X1)
                & r1_tarski(X2,X3) )
             => r1_tarski(k8_relat_1(X0,X2),k8_relat_1(X1,X3)) ) ) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f10,conjecture,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ! [X3] :
          ( v1_relat_1(X3)
         => ( ( r1_tarski(X0,X1)
              & r1_tarski(X2,X3) )
           => r1_tarski(k8_relat_1(X0,X2),k8_relat_1(X1,X3)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t133_relat_1)).

fof(f665,plain,
    ( r1_tarski(k8_relat_1(sK0,sK2),k8_relat_1(sK1,sK3))
    | ~ spl8_12 ),
    inference(superposition,[],[f607,f127])).

fof(f127,plain,(
    k8_relat_1(sK0,sK2) = k8_relat_1(sK1,k8_relat_1(sK0,sK2)) ),
    inference(resolution,[],[f75,f36])).

fof(f36,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f25])).

fof(f75,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k8_relat_1(sK0,X0) = k8_relat_1(sK1,k8_relat_1(sK0,X0)) ) ),
    inference(resolution,[],[f39,f49])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k8_relat_1(X0,X2) = k8_relat_1(X1,k8_relat_1(X0,X2))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( k8_relat_1(X0,X2) = k8_relat_1(X1,k8_relat_1(X0,X2))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( k8_relat_1(X0,X2) = k8_relat_1(X1,k8_relat_1(X0,X2))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r1_tarski(X0,X1)
       => k8_relat_1(X0,X2) = k8_relat_1(X1,k8_relat_1(X0,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t129_relat_1)).

fof(f39,plain,(
    r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f25])).

fof(f607,plain,
    ( ! [X3] : r1_tarski(k8_relat_1(X3,k8_relat_1(sK0,sK2)),k8_relat_1(X3,sK3))
    | ~ spl8_12 ),
    inference(resolution,[],[f299,f167])).

fof(f167,plain,(
    ! [X4,X5] :
      ( ~ v1_relat_1(k8_relat_1(X5,sK2))
      | r1_tarski(k8_relat_1(X4,k8_relat_1(X5,sK2)),k8_relat_1(X4,sK3)) ) ),
    inference(subsumption_resolution,[],[f166,f37])).

fof(f37,plain,(
    v1_relat_1(sK3) ),
    inference(cnf_transformation,[],[f25])).

% (19114)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
fof(f166,plain,(
    ! [X4,X5] :
      ( r1_tarski(k8_relat_1(X4,k8_relat_1(X5,sK2)),k8_relat_1(X4,sK3))
      | ~ v1_relat_1(sK3)
      | ~ v1_relat_1(k8_relat_1(X5,sK2)) ) ),
    inference(resolution,[],[f162,f46])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X1,X2)
      | r1_tarski(k8_relat_1(X0,X1),k8_relat_1(X0,X2))
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r1_tarski(k8_relat_1(X0,X1),k8_relat_1(X0,X2))
          | ~ r1_tarski(X1,X2)
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r1_tarski(k8_relat_1(X0,X1),k8_relat_1(X0,X2))
          | ~ r1_tarski(X1,X2)
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => ( r1_tarski(X1,X2)
           => r1_tarski(k8_relat_1(X0,X1),k8_relat_1(X0,X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t132_relat_1)).

fof(f162,plain,(
    ! [X2] : r1_tarski(k8_relat_1(X2,sK2),sK3) ),
    inference(resolution,[],[f149,f68])).

fof(f68,plain,(
    ! [X0] : r1_tarski(k8_relat_1(X0,sK3),sK3) ),
    inference(resolution,[],[f37,f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | r1_tarski(k8_relat_1(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( r1_tarski(k8_relat_1(X0,X1),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k8_relat_1(X0,X1),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t117_relat_1)).

fof(f149,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k8_relat_1(X0,sK3),X1)
      | r1_tarski(k8_relat_1(X0,sK2),X1) ) ),
    inference(superposition,[],[f50,f115])).

fof(f115,plain,(
    ! [X3] : k8_relat_1(X3,sK3) = k2_xboole_0(k8_relat_1(X3,sK2),k8_relat_1(X3,sK3)) ),
    inference(resolution,[],[f74,f47])).

fof(f47,plain,(
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

fof(f74,plain,(
    ! [X1] : r1_tarski(k8_relat_1(X1,sK2),k8_relat_1(X1,sK3)) ),
    inference(subsumption_resolution,[],[f73,f36])).

fof(f73,plain,(
    ! [X1] :
      ( r1_tarski(k8_relat_1(X1,sK2),k8_relat_1(X1,sK3))
      | ~ v1_relat_1(sK2) ) ),
    inference(subsumption_resolution,[],[f72,f37])).

fof(f72,plain,(
    ! [X1] :
      ( r1_tarski(k8_relat_1(X1,sK2),k8_relat_1(X1,sK3))
      | ~ v1_relat_1(sK3)
      | ~ v1_relat_1(sK2) ) ),
    inference(resolution,[],[f38,f46])).

fof(f38,plain,(
    r1_tarski(sK2,sK3) ),
    inference(cnf_transformation,[],[f25])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(k2_xboole_0(X0,X1),X2)
      | r1_tarski(X0,X2) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(k2_xboole_0(X0,X1),X2) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X1),X2)
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_xboole_1)).

fof(f299,plain,
    ( v1_relat_1(k8_relat_1(sK0,sK2))
    | ~ spl8_12 ),
    inference(avatar_component_clause,[],[f298])).

fof(f298,plain,
    ( spl8_12
  <=> v1_relat_1(k8_relat_1(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_12])])).

fof(f591,plain,
    ( spl8_4
    | spl8_12 ),
    inference(avatar_contradiction_clause,[],[f590])).

fof(f590,plain,
    ( $false
    | spl8_4
    | spl8_12 ),
    inference(subsumption_resolution,[],[f224,f319])).

fof(f319,plain,
    ( r2_hidden(sK4(k8_relat_1(sK0,sK2)),k8_relat_1(sK0,sK2))
    | spl8_12 ),
    inference(resolution,[],[f300,f42])).

fof(f42,plain,(
    ! [X0] :
      ( v1_relat_1(X0)
      | r2_hidden(sK4(X0),X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ( v1_relat_1(X0)
        | ( ! [X2,X3] : k4_tarski(X2,X3) != sK4(X0)
          & r2_hidden(sK4(X0),X0) ) )
      & ( ! [X4] :
            ( k4_tarski(sK5(X4),sK6(X4)) = X4
            | ~ r2_hidden(X4,X0) )
        | ~ v1_relat_1(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6])],[f27,f29,f28])).

fof(f28,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ! [X2,X3] : k4_tarski(X2,X3) != X1
          & r2_hidden(X1,X0) )
     => ( ! [X3,X2] : k4_tarski(X2,X3) != sK4(X0)
        & r2_hidden(sK4(X0),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,(
    ! [X4] :
      ( ? [X5,X6] : k4_tarski(X5,X6) = X4
     => k4_tarski(sK5(X4),sK6(X4)) = X4 ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,(
    ! [X0] :
      ( ( v1_relat_1(X0)
        | ? [X1] :
            ( ! [X2,X3] : k4_tarski(X2,X3) != X1
            & r2_hidden(X1,X0) ) )
      & ( ! [X4] :
            ( ? [X5,X6] : k4_tarski(X5,X6) = X4
            | ~ r2_hidden(X4,X0) )
        | ~ v1_relat_1(X0) ) ) ),
    inference(rectify,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ( v1_relat_1(X0)
        | ? [X1] :
            ( ! [X2,X3] : k4_tarski(X2,X3) != X1
            & r2_hidden(X1,X0) ) )
      & ( ! [X1] :
            ( ? [X2,X3] : k4_tarski(X2,X3) = X1
            | ~ r2_hidden(X1,X0) )
        | ~ v1_relat_1(X0) ) ) ),
    inference(nnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( v1_relat_1(X0)
    <=> ! [X1] :
          ( ? [X2,X3] : k4_tarski(X2,X3) = X1
          | ~ r2_hidden(X1,X0) ) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
    <=> ! [X1] :
          ~ ( ! [X2,X3] : k4_tarski(X2,X3) != X1
            & r2_hidden(X1,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_relat_1)).

fof(f300,plain,
    ( ~ v1_relat_1(k8_relat_1(sK0,sK2))
    | spl8_12 ),
    inference(avatar_component_clause,[],[f298])).

fof(f224,plain,
    ( ~ r2_hidden(sK4(k8_relat_1(sK0,sK2)),k8_relat_1(sK0,sK2))
    | spl8_4 ),
    inference(avatar_component_clause,[],[f223])).

fof(f223,plain,
    ( spl8_4
  <=> r2_hidden(sK4(k8_relat_1(sK0,sK2)),k8_relat_1(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_4])])).

fof(f589,plain,
    ( ~ spl8_4
    | spl8_12 ),
    inference(avatar_contradiction_clause,[],[f588])).

fof(f588,plain,
    ( $false
    | ~ spl8_4
    | spl8_12 ),
    inference(subsumption_resolution,[],[f587,f300])).

fof(f587,plain,
    ( v1_relat_1(k8_relat_1(sK0,sK2))
    | ~ spl8_4 ),
    inference(equality_resolution,[],[f586])).

fof(f586,plain,
    ( ! [X0] :
        ( sK4(X0) != sK4(k8_relat_1(sK0,sK2))
        | v1_relat_1(X0) )
    | ~ spl8_4 ),
    inference(superposition,[],[f43,f324])).

fof(f324,plain,
    ( sK4(k8_relat_1(sK0,sK2)) = k4_tarski(sK5(sK4(k8_relat_1(sK0,sK2))),sK6(sK4(k8_relat_1(sK0,sK2))))
    | ~ spl8_4 ),
    inference(subsumption_resolution,[],[f320,f37])).

fof(f320,plain,
    ( sK4(k8_relat_1(sK0,sK2)) = k4_tarski(sK5(sK4(k8_relat_1(sK0,sK2))),sK6(sK4(k8_relat_1(sK0,sK2))))
    | ~ v1_relat_1(sK3)
    | ~ spl8_4 ),
    inference(resolution,[],[f294,f41])).

fof(f41,plain,(
    ! [X4,X0] :
      ( ~ r2_hidden(X4,X0)
      | k4_tarski(sK5(X4),sK6(X4)) = X4
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f294,plain,
    ( r2_hidden(sK4(k8_relat_1(sK0,sK2)),sK3)
    | ~ spl8_4 ),
    inference(resolution,[],[f225,f176])).

fof(f176,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,k8_relat_1(X1,sK2))
      | r2_hidden(X0,sK3) ) ),
    inference(resolution,[],[f159,f147])).

fof(f147,plain,(
    ! [X2,X3] :
      ( ~ r2_hidden(X3,k8_relat_1(X2,sK3))
      | r2_hidden(X3,sK3) ) ),
    inference(superposition,[],[f65,f101])).

fof(f101,plain,(
    ! [X2] : k8_relat_1(X2,sK3) = k1_setfam_1(k2_tarski(k8_relat_1(X2,sK3),sK3)) ),
    inference(resolution,[],[f68,f57])).

fof(f57,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k1_setfam_1(k2_tarski(X0,X1)) = X0 ) ),
    inference(definition_unfolding,[],[f48,f44])).

fof(f44,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).

fof(f48,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f65,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,k1_setfam_1(k2_tarski(X0,X1)))
      | r2_hidden(X4,X1) ) ),
    inference(equality_resolution,[],[f62])).

fof(f62,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k1_setfam_1(k2_tarski(X0,X1)) != X2 ) ),
    inference(definition_unfolding,[],[f52,f44])).

fof(f52,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ( ( ~ r2_hidden(sK7(X0,X1,X2),X1)
            | ~ r2_hidden(sK7(X0,X1,X2),X0)
            | ~ r2_hidden(sK7(X0,X1,X2),X2) )
          & ( ( r2_hidden(sK7(X0,X1,X2),X1)
              & r2_hidden(sK7(X0,X1,X2),X0) )
            | r2_hidden(sK7(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f33,f34])).

fof(f34,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ~ r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X3,X2) )
          & ( ( r2_hidden(X3,X1)
              & r2_hidden(X3,X0) )
            | r2_hidden(X3,X2) ) )
     => ( ( ~ r2_hidden(sK7(X0,X1,X2),X1)
          | ~ r2_hidden(sK7(X0,X1,X2),X0)
          | ~ r2_hidden(sK7(X0,X1,X2),X2) )
        & ( ( r2_hidden(sK7(X0,X1,X2),X1)
            & r2_hidden(sK7(X0,X1,X2),X0) )
          | r2_hidden(sK7(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_xboole_0)).

fof(f159,plain,(
    ! [X2,X3] :
      ( r2_hidden(X3,k8_relat_1(X2,sK3))
      | ~ r2_hidden(X3,k8_relat_1(X2,sK2)) ) ),
    inference(superposition,[],[f65,f114])).

fof(f114,plain,(
    ! [X2] : k8_relat_1(X2,sK2) = k1_setfam_1(k2_tarski(k8_relat_1(X2,sK2),k8_relat_1(X2,sK3))) ),
    inference(resolution,[],[f74,f57])).

fof(f225,plain,
    ( r2_hidden(sK4(k8_relat_1(sK0,sK2)),k8_relat_1(sK0,sK2))
    | ~ spl8_4 ),
    inference(avatar_component_clause,[],[f223])).

fof(f43,plain,(
    ! [X2,X0,X3] :
      ( k4_tarski(X2,X3) != sK4(X0)
      | v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f30])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.14  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n007.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 18:55:36 EST 2020
% 0.15/0.35  % CPUTime    : 
% 1.34/0.55  % (19109)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 1.34/0.55  % (19105)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 1.34/0.55  % (19118)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 1.34/0.56  % (19101)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 1.34/0.56  % (19121)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 1.58/0.57  % (19127)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 1.58/0.57  % (19113)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.58/0.57  % (19118)Refutation not found, incomplete strategy% (19118)------------------------------
% 1.58/0.57  % (19118)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.58/0.57  % (19118)Termination reason: Refutation not found, incomplete strategy
% 1.58/0.57  
% 1.58/0.57  % (19118)Memory used [KB]: 10618
% 1.58/0.57  % (19118)Time elapsed: 0.140 s
% 1.58/0.57  % (19118)------------------------------
% 1.58/0.57  % (19118)------------------------------
% 1.58/0.58  % (19106)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 1.58/0.58  % (19103)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 1.58/0.58  % (19104)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 1.58/0.58  % (19107)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 1.58/0.59  % (19115)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 1.58/0.59  % (19102)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 1.58/0.60  % (19116)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 1.58/0.60  % (19128)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 1.58/0.60  % (19126)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 1.58/0.60  % (19110)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 1.58/0.60  % (19129)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 1.58/0.60  % (19123)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 1.58/0.60  % (19123)Refutation not found, incomplete strategy% (19123)------------------------------
% 1.58/0.60  % (19123)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.58/0.60  % (19123)Termination reason: Refutation not found, incomplete strategy
% 1.58/0.60  
% 1.58/0.60  % (19123)Memory used [KB]: 10746
% 1.58/0.60  % (19123)Time elapsed: 0.174 s
% 1.58/0.60  % (19123)------------------------------
% 1.58/0.60  % (19123)------------------------------
% 1.58/0.61  % (19108)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 1.58/0.61  % (19110)Refutation not found, incomplete strategy% (19110)------------------------------
% 1.58/0.61  % (19110)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.58/0.61  % (19110)Termination reason: Refutation not found, incomplete strategy
% 1.58/0.61  
% 1.58/0.61  % (19110)Memory used [KB]: 10874
% 1.58/0.61  % (19110)Time elapsed: 0.179 s
% 1.58/0.61  % (19110)------------------------------
% 1.58/0.61  % (19110)------------------------------
% 1.58/0.61  % (19109)Refutation found. Thanks to Tanya!
% 1.58/0.61  % SZS status Theorem for theBenchmark
% 1.58/0.61  % (19125)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 1.58/0.61  % (19124)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 1.58/0.61  % (19111)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 1.58/0.61  % (19122)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 1.58/0.61  % (19112)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 1.58/0.62  % (19119)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 1.58/0.62  % (19120)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 1.58/0.62  % SZS output start Proof for theBenchmark
% 1.58/0.62  fof(f668,plain,(
% 1.58/0.62    $false),
% 1.58/0.62    inference(avatar_sat_refutation,[],[f589,f591,f667])).
% 1.58/0.62  fof(f667,plain,(
% 1.58/0.62    ~spl8_12),
% 1.58/0.62    inference(avatar_contradiction_clause,[],[f666])).
% 1.58/0.62  fof(f666,plain,(
% 1.58/0.62    $false | ~spl8_12),
% 1.58/0.62    inference(subsumption_resolution,[],[f665,f40])).
% 1.58/0.62  fof(f40,plain,(
% 1.58/0.62    ~r1_tarski(k8_relat_1(sK0,sK2),k8_relat_1(sK1,sK3))),
% 1.58/0.62    inference(cnf_transformation,[],[f25])).
% 1.58/0.62  fof(f25,plain,(
% 1.58/0.62    (~r1_tarski(k8_relat_1(sK0,sK2),k8_relat_1(sK1,sK3)) & r1_tarski(sK0,sK1) & r1_tarski(sK2,sK3) & v1_relat_1(sK3)) & v1_relat_1(sK2)),
% 1.58/0.62    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f13,f24,f23])).
% 1.58/0.62  fof(f23,plain,(
% 1.58/0.62    ? [X0,X1,X2] : (? [X3] : (~r1_tarski(k8_relat_1(X0,X2),k8_relat_1(X1,X3)) & r1_tarski(X0,X1) & r1_tarski(X2,X3) & v1_relat_1(X3)) & v1_relat_1(X2)) => (? [X3] : (~r1_tarski(k8_relat_1(sK0,sK2),k8_relat_1(sK1,X3)) & r1_tarski(sK0,sK1) & r1_tarski(sK2,X3) & v1_relat_1(X3)) & v1_relat_1(sK2))),
% 1.58/0.62    introduced(choice_axiom,[])).
% 1.58/0.62  fof(f24,plain,(
% 1.58/0.62    ? [X3] : (~r1_tarski(k8_relat_1(sK0,sK2),k8_relat_1(sK1,X3)) & r1_tarski(sK0,sK1) & r1_tarski(sK2,X3) & v1_relat_1(X3)) => (~r1_tarski(k8_relat_1(sK0,sK2),k8_relat_1(sK1,sK3)) & r1_tarski(sK0,sK1) & r1_tarski(sK2,sK3) & v1_relat_1(sK3))),
% 1.58/0.62    introduced(choice_axiom,[])).
% 1.58/0.62  fof(f13,plain,(
% 1.58/0.62    ? [X0,X1,X2] : (? [X3] : (~r1_tarski(k8_relat_1(X0,X2),k8_relat_1(X1,X3)) & r1_tarski(X0,X1) & r1_tarski(X2,X3) & v1_relat_1(X3)) & v1_relat_1(X2))),
% 1.58/0.62    inference(flattening,[],[f12])).
% 1.58/0.62  % (19117)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 1.58/0.62  fof(f12,plain,(
% 1.58/0.62    ? [X0,X1,X2] : (? [X3] : ((~r1_tarski(k8_relat_1(X0,X2),k8_relat_1(X1,X3)) & (r1_tarski(X0,X1) & r1_tarski(X2,X3))) & v1_relat_1(X3)) & v1_relat_1(X2))),
% 1.58/0.62    inference(ennf_transformation,[],[f11])).
% 1.58/0.62  fof(f11,negated_conjecture,(
% 1.58/0.62    ~! [X0,X1,X2] : (v1_relat_1(X2) => ! [X3] : (v1_relat_1(X3) => ((r1_tarski(X0,X1) & r1_tarski(X2,X3)) => r1_tarski(k8_relat_1(X0,X2),k8_relat_1(X1,X3)))))),
% 1.58/0.62    inference(negated_conjecture,[],[f10])).
% 1.58/0.62  fof(f10,conjecture,(
% 1.58/0.62    ! [X0,X1,X2] : (v1_relat_1(X2) => ! [X3] : (v1_relat_1(X3) => ((r1_tarski(X0,X1) & r1_tarski(X2,X3)) => r1_tarski(k8_relat_1(X0,X2),k8_relat_1(X1,X3)))))),
% 1.58/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t133_relat_1)).
% 1.58/0.62  fof(f665,plain,(
% 1.58/0.62    r1_tarski(k8_relat_1(sK0,sK2),k8_relat_1(sK1,sK3)) | ~spl8_12),
% 1.58/0.62    inference(superposition,[],[f607,f127])).
% 1.58/0.62  fof(f127,plain,(
% 1.58/0.62    k8_relat_1(sK0,sK2) = k8_relat_1(sK1,k8_relat_1(sK0,sK2))),
% 1.58/0.62    inference(resolution,[],[f75,f36])).
% 1.58/0.62  fof(f36,plain,(
% 1.58/0.62    v1_relat_1(sK2)),
% 1.58/0.62    inference(cnf_transformation,[],[f25])).
% 1.58/0.62  fof(f75,plain,(
% 1.58/0.62    ( ! [X0] : (~v1_relat_1(X0) | k8_relat_1(sK0,X0) = k8_relat_1(sK1,k8_relat_1(sK0,X0))) )),
% 1.58/0.62    inference(resolution,[],[f39,f49])).
% 1.58/0.62  fof(f49,plain,(
% 1.58/0.62    ( ! [X2,X0,X1] : (~r1_tarski(X0,X1) | k8_relat_1(X0,X2) = k8_relat_1(X1,k8_relat_1(X0,X2)) | ~v1_relat_1(X2)) )),
% 1.58/0.62    inference(cnf_transformation,[],[f21])).
% 1.58/0.62  fof(f21,plain,(
% 1.58/0.62    ! [X0,X1,X2] : (k8_relat_1(X0,X2) = k8_relat_1(X1,k8_relat_1(X0,X2)) | ~r1_tarski(X0,X1) | ~v1_relat_1(X2))),
% 1.58/0.62    inference(flattening,[],[f20])).
% 1.58/0.62  fof(f20,plain,(
% 1.58/0.62    ! [X0,X1,X2] : ((k8_relat_1(X0,X2) = k8_relat_1(X1,k8_relat_1(X0,X2)) | ~r1_tarski(X0,X1)) | ~v1_relat_1(X2))),
% 1.58/0.62    inference(ennf_transformation,[],[f8])).
% 1.58/0.62  fof(f8,axiom,(
% 1.58/0.62    ! [X0,X1,X2] : (v1_relat_1(X2) => (r1_tarski(X0,X1) => k8_relat_1(X0,X2) = k8_relat_1(X1,k8_relat_1(X0,X2))))),
% 1.58/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t129_relat_1)).
% 1.58/0.62  fof(f39,plain,(
% 1.58/0.62    r1_tarski(sK0,sK1)),
% 1.58/0.62    inference(cnf_transformation,[],[f25])).
% 1.58/0.62  fof(f607,plain,(
% 1.58/0.62    ( ! [X3] : (r1_tarski(k8_relat_1(X3,k8_relat_1(sK0,sK2)),k8_relat_1(X3,sK3))) ) | ~spl8_12),
% 1.58/0.62    inference(resolution,[],[f299,f167])).
% 1.58/0.62  fof(f167,plain,(
% 1.58/0.62    ( ! [X4,X5] : (~v1_relat_1(k8_relat_1(X5,sK2)) | r1_tarski(k8_relat_1(X4,k8_relat_1(X5,sK2)),k8_relat_1(X4,sK3))) )),
% 1.58/0.62    inference(subsumption_resolution,[],[f166,f37])).
% 1.58/0.62  fof(f37,plain,(
% 1.58/0.62    v1_relat_1(sK3)),
% 1.58/0.62    inference(cnf_transformation,[],[f25])).
% 1.58/0.62  % (19114)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 1.58/0.62  fof(f166,plain,(
% 1.58/0.62    ( ! [X4,X5] : (r1_tarski(k8_relat_1(X4,k8_relat_1(X5,sK2)),k8_relat_1(X4,sK3)) | ~v1_relat_1(sK3) | ~v1_relat_1(k8_relat_1(X5,sK2))) )),
% 1.58/0.62    inference(resolution,[],[f162,f46])).
% 1.58/0.62  fof(f46,plain,(
% 1.58/0.62    ( ! [X2,X0,X1] : (~r1_tarski(X1,X2) | r1_tarski(k8_relat_1(X0,X1),k8_relat_1(X0,X2)) | ~v1_relat_1(X2) | ~v1_relat_1(X1)) )),
% 1.58/0.62    inference(cnf_transformation,[],[f17])).
% 1.58/0.62  fof(f17,plain,(
% 1.58/0.62    ! [X0,X1] : (! [X2] : (r1_tarski(k8_relat_1(X0,X1),k8_relat_1(X0,X2)) | ~r1_tarski(X1,X2) | ~v1_relat_1(X2)) | ~v1_relat_1(X1))),
% 1.58/0.62    inference(flattening,[],[f16])).
% 1.58/0.62  fof(f16,plain,(
% 1.58/0.62    ! [X0,X1] : (! [X2] : ((r1_tarski(k8_relat_1(X0,X1),k8_relat_1(X0,X2)) | ~r1_tarski(X1,X2)) | ~v1_relat_1(X2)) | ~v1_relat_1(X1))),
% 1.58/0.62    inference(ennf_transformation,[],[f9])).
% 1.58/0.62  fof(f9,axiom,(
% 1.58/0.62    ! [X0,X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => (r1_tarski(X1,X2) => r1_tarski(k8_relat_1(X0,X1),k8_relat_1(X0,X2)))))),
% 1.58/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t132_relat_1)).
% 1.58/0.62  fof(f162,plain,(
% 1.58/0.62    ( ! [X2] : (r1_tarski(k8_relat_1(X2,sK2),sK3)) )),
% 1.58/0.62    inference(resolution,[],[f149,f68])).
% 1.58/0.62  fof(f68,plain,(
% 1.58/0.62    ( ! [X0] : (r1_tarski(k8_relat_1(X0,sK3),sK3)) )),
% 1.58/0.62    inference(resolution,[],[f37,f45])).
% 1.58/0.62  fof(f45,plain,(
% 1.58/0.62    ( ! [X0,X1] : (~v1_relat_1(X1) | r1_tarski(k8_relat_1(X0,X1),X1)) )),
% 1.58/0.62    inference(cnf_transformation,[],[f15])).
% 1.58/0.62  fof(f15,plain,(
% 1.58/0.62    ! [X0,X1] : (r1_tarski(k8_relat_1(X0,X1),X1) | ~v1_relat_1(X1))),
% 1.58/0.62    inference(ennf_transformation,[],[f7])).
% 1.58/0.62  fof(f7,axiom,(
% 1.58/0.62    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k8_relat_1(X0,X1),X1))),
% 1.58/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t117_relat_1)).
% 1.58/0.62  fof(f149,plain,(
% 1.58/0.62    ( ! [X0,X1] : (~r1_tarski(k8_relat_1(X0,sK3),X1) | r1_tarski(k8_relat_1(X0,sK2),X1)) )),
% 1.58/0.62    inference(superposition,[],[f50,f115])).
% 1.58/0.62  fof(f115,plain,(
% 1.58/0.62    ( ! [X3] : (k8_relat_1(X3,sK3) = k2_xboole_0(k8_relat_1(X3,sK2),k8_relat_1(X3,sK3))) )),
% 1.58/0.62    inference(resolution,[],[f74,f47])).
% 1.58/0.62  fof(f47,plain,(
% 1.58/0.62    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k2_xboole_0(X0,X1) = X1) )),
% 1.58/0.62    inference(cnf_transformation,[],[f18])).
% 1.58/0.62  fof(f18,plain,(
% 1.58/0.62    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 1.58/0.62    inference(ennf_transformation,[],[f3])).
% 1.58/0.62  fof(f3,axiom,(
% 1.58/0.62    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 1.58/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).
% 1.58/0.62  fof(f74,plain,(
% 1.58/0.62    ( ! [X1] : (r1_tarski(k8_relat_1(X1,sK2),k8_relat_1(X1,sK3))) )),
% 1.58/0.62    inference(subsumption_resolution,[],[f73,f36])).
% 1.58/0.62  fof(f73,plain,(
% 1.58/0.62    ( ! [X1] : (r1_tarski(k8_relat_1(X1,sK2),k8_relat_1(X1,sK3)) | ~v1_relat_1(sK2)) )),
% 1.58/0.62    inference(subsumption_resolution,[],[f72,f37])).
% 1.58/0.62  fof(f72,plain,(
% 1.58/0.62    ( ! [X1] : (r1_tarski(k8_relat_1(X1,sK2),k8_relat_1(X1,sK3)) | ~v1_relat_1(sK3) | ~v1_relat_1(sK2)) )),
% 1.58/0.62    inference(resolution,[],[f38,f46])).
% 1.58/0.62  fof(f38,plain,(
% 1.58/0.62    r1_tarski(sK2,sK3)),
% 1.58/0.62    inference(cnf_transformation,[],[f25])).
% 1.58/0.62  fof(f50,plain,(
% 1.58/0.62    ( ! [X2,X0,X1] : (~r1_tarski(k2_xboole_0(X0,X1),X2) | r1_tarski(X0,X2)) )),
% 1.58/0.62    inference(cnf_transformation,[],[f22])).
% 1.58/0.62  fof(f22,plain,(
% 1.58/0.62    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(k2_xboole_0(X0,X1),X2))),
% 1.58/0.62    inference(ennf_transformation,[],[f2])).
% 1.58/0.62  fof(f2,axiom,(
% 1.58/0.62    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X1),X2) => r1_tarski(X0,X2))),
% 1.58/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_xboole_1)).
% 1.58/0.62  fof(f299,plain,(
% 1.58/0.62    v1_relat_1(k8_relat_1(sK0,sK2)) | ~spl8_12),
% 1.58/0.62    inference(avatar_component_clause,[],[f298])).
% 1.58/0.62  fof(f298,plain,(
% 1.58/0.62    spl8_12 <=> v1_relat_1(k8_relat_1(sK0,sK2))),
% 1.58/0.62    introduced(avatar_definition,[new_symbols(naming,[spl8_12])])).
% 1.58/0.62  fof(f591,plain,(
% 1.58/0.62    spl8_4 | spl8_12),
% 1.58/0.62    inference(avatar_contradiction_clause,[],[f590])).
% 1.58/0.62  fof(f590,plain,(
% 1.58/0.62    $false | (spl8_4 | spl8_12)),
% 1.58/0.62    inference(subsumption_resolution,[],[f224,f319])).
% 1.58/0.62  fof(f319,plain,(
% 1.58/0.62    r2_hidden(sK4(k8_relat_1(sK0,sK2)),k8_relat_1(sK0,sK2)) | spl8_12),
% 1.58/0.62    inference(resolution,[],[f300,f42])).
% 1.58/0.62  fof(f42,plain,(
% 1.58/0.62    ( ! [X0] : (v1_relat_1(X0) | r2_hidden(sK4(X0),X0)) )),
% 1.58/0.62    inference(cnf_transformation,[],[f30])).
% 1.58/0.62  fof(f30,plain,(
% 1.58/0.62    ! [X0] : ((v1_relat_1(X0) | (! [X2,X3] : k4_tarski(X2,X3) != sK4(X0) & r2_hidden(sK4(X0),X0))) & (! [X4] : (k4_tarski(sK5(X4),sK6(X4)) = X4 | ~r2_hidden(X4,X0)) | ~v1_relat_1(X0)))),
% 1.58/0.62    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6])],[f27,f29,f28])).
% 1.58/0.62  fof(f28,plain,(
% 1.58/0.62    ! [X0] : (? [X1] : (! [X2,X3] : k4_tarski(X2,X3) != X1 & r2_hidden(X1,X0)) => (! [X3,X2] : k4_tarski(X2,X3) != sK4(X0) & r2_hidden(sK4(X0),X0)))),
% 1.58/0.62    introduced(choice_axiom,[])).
% 1.58/0.62  fof(f29,plain,(
% 1.58/0.62    ! [X4] : (? [X5,X6] : k4_tarski(X5,X6) = X4 => k4_tarski(sK5(X4),sK6(X4)) = X4)),
% 1.58/0.62    introduced(choice_axiom,[])).
% 1.58/0.62  fof(f27,plain,(
% 1.58/0.62    ! [X0] : ((v1_relat_1(X0) | ? [X1] : (! [X2,X3] : k4_tarski(X2,X3) != X1 & r2_hidden(X1,X0))) & (! [X4] : (? [X5,X6] : k4_tarski(X5,X6) = X4 | ~r2_hidden(X4,X0)) | ~v1_relat_1(X0)))),
% 1.58/0.62    inference(rectify,[],[f26])).
% 1.58/0.62  fof(f26,plain,(
% 1.58/0.62    ! [X0] : ((v1_relat_1(X0) | ? [X1] : (! [X2,X3] : k4_tarski(X2,X3) != X1 & r2_hidden(X1,X0))) & (! [X1] : (? [X2,X3] : k4_tarski(X2,X3) = X1 | ~r2_hidden(X1,X0)) | ~v1_relat_1(X0)))),
% 1.58/0.62    inference(nnf_transformation,[],[f14])).
% 1.58/0.62  fof(f14,plain,(
% 1.58/0.62    ! [X0] : (v1_relat_1(X0) <=> ! [X1] : (? [X2,X3] : k4_tarski(X2,X3) = X1 | ~r2_hidden(X1,X0)))),
% 1.58/0.62    inference(ennf_transformation,[],[f6])).
% 1.58/0.62  fof(f6,axiom,(
% 1.58/0.62    ! [X0] : (v1_relat_1(X0) <=> ! [X1] : ~(! [X2,X3] : k4_tarski(X2,X3) != X1 & r2_hidden(X1,X0)))),
% 1.58/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_relat_1)).
% 1.58/0.62  fof(f300,plain,(
% 1.58/0.62    ~v1_relat_1(k8_relat_1(sK0,sK2)) | spl8_12),
% 1.58/0.62    inference(avatar_component_clause,[],[f298])).
% 1.58/0.62  fof(f224,plain,(
% 1.58/0.62    ~r2_hidden(sK4(k8_relat_1(sK0,sK2)),k8_relat_1(sK0,sK2)) | spl8_4),
% 1.58/0.62    inference(avatar_component_clause,[],[f223])).
% 1.58/0.62  fof(f223,plain,(
% 1.58/0.62    spl8_4 <=> r2_hidden(sK4(k8_relat_1(sK0,sK2)),k8_relat_1(sK0,sK2))),
% 1.58/0.62    introduced(avatar_definition,[new_symbols(naming,[spl8_4])])).
% 1.58/0.62  fof(f589,plain,(
% 1.58/0.62    ~spl8_4 | spl8_12),
% 1.58/0.62    inference(avatar_contradiction_clause,[],[f588])).
% 1.58/0.62  fof(f588,plain,(
% 1.58/0.62    $false | (~spl8_4 | spl8_12)),
% 1.58/0.62    inference(subsumption_resolution,[],[f587,f300])).
% 1.58/0.62  fof(f587,plain,(
% 1.58/0.62    v1_relat_1(k8_relat_1(sK0,sK2)) | ~spl8_4),
% 1.58/0.62    inference(equality_resolution,[],[f586])).
% 1.58/0.62  fof(f586,plain,(
% 1.58/0.62    ( ! [X0] : (sK4(X0) != sK4(k8_relat_1(sK0,sK2)) | v1_relat_1(X0)) ) | ~spl8_4),
% 1.58/0.62    inference(superposition,[],[f43,f324])).
% 1.58/0.62  fof(f324,plain,(
% 1.58/0.62    sK4(k8_relat_1(sK0,sK2)) = k4_tarski(sK5(sK4(k8_relat_1(sK0,sK2))),sK6(sK4(k8_relat_1(sK0,sK2)))) | ~spl8_4),
% 1.58/0.62    inference(subsumption_resolution,[],[f320,f37])).
% 1.58/0.62  fof(f320,plain,(
% 1.58/0.62    sK4(k8_relat_1(sK0,sK2)) = k4_tarski(sK5(sK4(k8_relat_1(sK0,sK2))),sK6(sK4(k8_relat_1(sK0,sK2)))) | ~v1_relat_1(sK3) | ~spl8_4),
% 1.58/0.62    inference(resolution,[],[f294,f41])).
% 1.58/0.62  fof(f41,plain,(
% 1.58/0.62    ( ! [X4,X0] : (~r2_hidden(X4,X0) | k4_tarski(sK5(X4),sK6(X4)) = X4 | ~v1_relat_1(X0)) )),
% 1.58/0.62    inference(cnf_transformation,[],[f30])).
% 1.58/0.62  fof(f294,plain,(
% 1.58/0.62    r2_hidden(sK4(k8_relat_1(sK0,sK2)),sK3) | ~spl8_4),
% 1.58/0.62    inference(resolution,[],[f225,f176])).
% 1.58/0.62  fof(f176,plain,(
% 1.58/0.62    ( ! [X0,X1] : (~r2_hidden(X0,k8_relat_1(X1,sK2)) | r2_hidden(X0,sK3)) )),
% 1.58/0.62    inference(resolution,[],[f159,f147])).
% 1.58/0.62  fof(f147,plain,(
% 1.58/0.62    ( ! [X2,X3] : (~r2_hidden(X3,k8_relat_1(X2,sK3)) | r2_hidden(X3,sK3)) )),
% 1.58/0.62    inference(superposition,[],[f65,f101])).
% 1.58/0.62  fof(f101,plain,(
% 1.58/0.62    ( ! [X2] : (k8_relat_1(X2,sK3) = k1_setfam_1(k2_tarski(k8_relat_1(X2,sK3),sK3))) )),
% 1.58/0.62    inference(resolution,[],[f68,f57])).
% 1.58/0.62  fof(f57,plain,(
% 1.58/0.62    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k1_setfam_1(k2_tarski(X0,X1)) = X0) )),
% 1.58/0.62    inference(definition_unfolding,[],[f48,f44])).
% 1.58/0.62  fof(f44,plain,(
% 1.58/0.62    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 1.58/0.62    inference(cnf_transformation,[],[f5])).
% 1.58/0.62  fof(f5,axiom,(
% 1.58/0.62    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 1.58/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).
% 1.58/0.62  fof(f48,plain,(
% 1.58/0.62    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 1.58/0.62    inference(cnf_transformation,[],[f19])).
% 1.58/0.63  fof(f19,plain,(
% 1.58/0.63    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 1.58/0.63    inference(ennf_transformation,[],[f4])).
% 1.58/0.63  fof(f4,axiom,(
% 1.58/0.63    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 1.58/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).
% 1.58/0.63  fof(f65,plain,(
% 1.58/0.63    ( ! [X4,X0,X1] : (~r2_hidden(X4,k1_setfam_1(k2_tarski(X0,X1))) | r2_hidden(X4,X1)) )),
% 1.58/0.63    inference(equality_resolution,[],[f62])).
% 1.58/0.63  fof(f62,plain,(
% 1.58/0.63    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X1) | ~r2_hidden(X4,X2) | k1_setfam_1(k2_tarski(X0,X1)) != X2) )),
% 1.58/0.63    inference(definition_unfolding,[],[f52,f44])).
% 1.58/0.63  fof(f52,plain,(
% 1.58/0.63    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X1) | ~r2_hidden(X4,X2) | k3_xboole_0(X0,X1) != X2) )),
% 1.58/0.63    inference(cnf_transformation,[],[f35])).
% 1.58/0.63  fof(f35,plain,(
% 1.58/0.63    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ((~r2_hidden(sK7(X0,X1,X2),X1) | ~r2_hidden(sK7(X0,X1,X2),X0) | ~r2_hidden(sK7(X0,X1,X2),X2)) & ((r2_hidden(sK7(X0,X1,X2),X1) & r2_hidden(sK7(X0,X1,X2),X0)) | r2_hidden(sK7(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k3_xboole_0(X0,X1) != X2))),
% 1.58/0.63    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f33,f34])).
% 1.58/0.63  fof(f34,plain,(
% 1.58/0.63    ! [X2,X1,X0] : (? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2))) => ((~r2_hidden(sK7(X0,X1,X2),X1) | ~r2_hidden(sK7(X0,X1,X2),X0) | ~r2_hidden(sK7(X0,X1,X2),X2)) & ((r2_hidden(sK7(X0,X1,X2),X1) & r2_hidden(sK7(X0,X1,X2),X0)) | r2_hidden(sK7(X0,X1,X2),X2))))),
% 1.58/0.63    introduced(choice_axiom,[])).
% 1.58/0.63  fof(f33,plain,(
% 1.58/0.63    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k3_xboole_0(X0,X1) != X2))),
% 1.58/0.63    inference(rectify,[],[f32])).
% 1.58/0.63  fof(f32,plain,(
% 1.58/0.63    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | ~r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k3_xboole_0(X0,X1) != X2))),
% 1.58/0.63    inference(flattening,[],[f31])).
% 1.58/0.63  fof(f31,plain,(
% 1.58/0.63    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k3_xboole_0(X0,X1) != X2))),
% 1.58/0.63    inference(nnf_transformation,[],[f1])).
% 1.58/0.63  fof(f1,axiom,(
% 1.58/0.63    ! [X0,X1,X2] : (k3_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 1.58/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_xboole_0)).
% 1.58/0.63  fof(f159,plain,(
% 1.58/0.63    ( ! [X2,X3] : (r2_hidden(X3,k8_relat_1(X2,sK3)) | ~r2_hidden(X3,k8_relat_1(X2,sK2))) )),
% 1.58/0.63    inference(superposition,[],[f65,f114])).
% 1.58/0.63  fof(f114,plain,(
% 1.58/0.63    ( ! [X2] : (k8_relat_1(X2,sK2) = k1_setfam_1(k2_tarski(k8_relat_1(X2,sK2),k8_relat_1(X2,sK3)))) )),
% 1.58/0.63    inference(resolution,[],[f74,f57])).
% 1.58/0.63  fof(f225,plain,(
% 1.58/0.63    r2_hidden(sK4(k8_relat_1(sK0,sK2)),k8_relat_1(sK0,sK2)) | ~spl8_4),
% 1.58/0.63    inference(avatar_component_clause,[],[f223])).
% 1.58/0.63  fof(f43,plain,(
% 1.58/0.63    ( ! [X2,X0,X3] : (k4_tarski(X2,X3) != sK4(X0) | v1_relat_1(X0)) )),
% 1.58/0.63    inference(cnf_transformation,[],[f30])).
% 1.58/0.63  % SZS output end Proof for theBenchmark
% 1.58/0.63  % (19109)------------------------------
% 1.58/0.63  % (19109)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.58/0.63  % (19109)Termination reason: Refutation
% 1.58/0.63  
% 1.58/0.63  % (19109)Memory used [KB]: 11385
% 1.58/0.63  % (19109)Time elapsed: 0.191 s
% 1.58/0.63  % (19109)------------------------------
% 1.58/0.63  % (19109)------------------------------
% 1.58/0.63  % (19100)Success in time 0.253 s
%------------------------------------------------------------------------------
