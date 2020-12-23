%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:54:16 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   77 ( 222 expanded)
%              Number of leaves         :   12 (  57 expanded)
%              Depth                    :   20
%              Number of atoms          :  203 ( 977 expanded)
%              Number of equality atoms :   40 (  78 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
% (32016)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% (32008)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% (31998)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% (32023)Refutation not found, incomplete strategy% (32023)------------------------------
% (32023)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (32023)Termination reason: Refutation not found, incomplete strategy

% (32023)Memory used [KB]: 10746
% (32023)Time elapsed: 0.143 s
% (32023)------------------------------
% (32023)------------------------------
% (32006)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
fof(f189,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f126,f134,f188])).

fof(f188,plain,(
    ~ spl3_6 ),
    inference(avatar_contradiction_clause,[],[f187])).

fof(f187,plain,
    ( $false
    | ~ spl3_6 ),
    inference(subsumption_resolution,[],[f186,f30])).

fof(f30,plain,(
    ~ r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,
    ( ~ r1_tarski(sK0,sK1)
    & v2_funct_1(sK2)
    & r1_tarski(sK0,k1_relat_1(sK2))
    & r1_tarski(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1))
    & v1_funct_1(sK2)
    & v1_relat_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f12,f20])).

fof(f20,plain,
    ( ? [X0,X1,X2] :
        ( ~ r1_tarski(X0,X1)
        & v2_funct_1(X2)
        & r1_tarski(X0,k1_relat_1(X2))
        & r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
        & v1_funct_1(X2)
        & v1_relat_1(X2) )
   => ( ~ r1_tarski(sK0,sK1)
      & v2_funct_1(sK2)
      & r1_tarski(sK0,k1_relat_1(sK2))
      & r1_tarski(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1))
      & v1_funct_1(sK2)
      & v1_relat_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f12,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(X0,X1)
      & v2_funct_1(X2)
      & r1_tarski(X0,k1_relat_1(X2))
      & r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(X0,X1)
      & v2_funct_1(X2)
      & r1_tarski(X0,k1_relat_1(X2))
      & r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( v1_funct_1(X2)
          & v1_relat_1(X2) )
       => ( ( v2_funct_1(X2)
            & r1_tarski(X0,k1_relat_1(X2))
            & r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) )
         => r1_tarski(X0,X1) ) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f9,conjecture,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( ( v2_funct_1(X2)
          & r1_tarski(X0,k1_relat_1(X2))
          & r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) )
       => r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t157_funct_1)).

fof(f186,plain,
    ( r1_tarski(sK0,sK1)
    | ~ spl3_6 ),
    inference(subsumption_resolution,[],[f177,f87])).

fof(f87,plain,(
    k1_xboole_0 = k5_xboole_0(sK0,sK0) ),
    inference(forward_demodulation,[],[f83,f49])).

fof(f49,plain,(
    sK0 = k3_xboole_0(sK0,k1_relat_1(sK2)) ),
    inference(resolution,[],[f34,f28])).

fof(f28,plain,(
    r1_tarski(sK0,k1_relat_1(sK2)) ),
    inference(cnf_transformation,[],[f21])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k3_xboole_0(X0,X1) = X0 ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f83,plain,(
    k1_xboole_0 = k5_xboole_0(sK0,k3_xboole_0(sK0,k1_relat_1(sK2))) ),
    inference(resolution,[],[f42,f28])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k1_xboole_0 = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ) ),
    inference(definition_unfolding,[],[f40,f32])).

fof(f32,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f40,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( k4_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | k4_xboole_0(X0,X1) != k1_xboole_0 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

fof(f177,plain,
    ( k1_xboole_0 != k5_xboole_0(sK0,sK0)
    | r1_tarski(sK0,sK1)
    | ~ spl3_6 ),
    inference(superposition,[],[f43,f164])).

fof(f164,plain,
    ( sK0 = k3_xboole_0(sK0,sK1)
    | ~ spl3_6 ),
    inference(resolution,[],[f161,f54])).

fof(f54,plain,(
    ! [X2,X1] :
      ( ~ r1_tarski(X1,k3_xboole_0(X1,X2))
      | k3_xboole_0(X1,X2) = X1 ) ),
    inference(resolution,[],[f38,f31])).

fof(f31,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).

fof(f38,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
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

fof(f161,plain,
    ( r1_tarski(sK0,k3_xboole_0(sK0,sK1))
    | ~ spl3_6 ),
    inference(forward_demodulation,[],[f160,f125])).

fof(f125,plain,
    ( sK0 = k10_relat_1(sK2,k9_relat_1(sK2,sK0))
    | ~ spl3_6 ),
    inference(avatar_component_clause,[],[f123])).

fof(f123,plain,
    ( spl3_6
  <=> sK0 = k10_relat_1(sK2,k9_relat_1(sK2,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f160,plain,(
    r1_tarski(k10_relat_1(sK2,k9_relat_1(sK2,sK0)),k3_xboole_0(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f159,f25])).

fof(f25,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f21])).

fof(f159,plain,
    ( r1_tarski(k10_relat_1(sK2,k9_relat_1(sK2,sK0)),k3_xboole_0(sK0,sK1))
    | ~ v1_relat_1(sK2) ),
    inference(subsumption_resolution,[],[f158,f26])).

fof(f26,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f21])).

fof(f158,plain,
    ( r1_tarski(k10_relat_1(sK2,k9_relat_1(sK2,sK0)),k3_xboole_0(sK0,sK1))
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2) ),
    inference(subsumption_resolution,[],[f154,f29])).

fof(f29,plain,(
    v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f21])).

fof(f154,plain,
    ( r1_tarski(k10_relat_1(sK2,k9_relat_1(sK2,sK0)),k3_xboole_0(sK0,sK1))
    | ~ v2_funct_1(sK2)
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2) ),
    inference(superposition,[],[f35,f144])).

fof(f144,plain,(
    k9_relat_1(sK2,sK0) = k9_relat_1(sK2,k3_xboole_0(sK0,sK1)) ),
    inference(superposition,[],[f129,f48])).

fof(f48,plain,(
    k9_relat_1(sK2,sK0) = k3_xboole_0(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1)) ),
    inference(resolution,[],[f34,f27])).

fof(f27,plain,(
    r1_tarski(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1)) ),
    inference(cnf_transformation,[],[f21])).

fof(f129,plain,(
    ! [X0,X1] : k9_relat_1(sK2,k3_xboole_0(X0,X1)) = k3_xboole_0(k9_relat_1(sK2,X0),k9_relat_1(sK2,X1)) ),
    inference(subsumption_resolution,[],[f128,f25])).

fof(f128,plain,(
    ! [X0,X1] :
      ( k9_relat_1(sK2,k3_xboole_0(X0,X1)) = k3_xboole_0(k9_relat_1(sK2,X0),k9_relat_1(sK2,X1))
      | ~ v1_relat_1(sK2) ) ),
    inference(subsumption_resolution,[],[f127,f26])).

fof(f127,plain,(
    ! [X0,X1] :
      ( k9_relat_1(sK2,k3_xboole_0(X0,X1)) = k3_xboole_0(k9_relat_1(sK2,X0),k9_relat_1(sK2,X1))
      | ~ v1_funct_1(sK2)
      | ~ v1_relat_1(sK2) ) ),
    inference(resolution,[],[f41,f29])).

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_funct_1(X2)
      | k9_relat_1(X2,k3_xboole_0(X0,X1)) = k3_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( k9_relat_1(X2,k3_xboole_0(X0,X1)) = k3_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
      | ~ v2_funct_1(X2)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( k9_relat_1(X2,k3_xboole_0(X0,X1)) = k3_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
      | ~ v2_funct_1(X2)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( v2_funct_1(X2)
       => k9_relat_1(X2,k3_xboole_0(X0,X1)) = k3_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t121_funct_1)).

fof(f35,plain,(
    ! [X0,X1] :
      ( r1_tarski(k10_relat_1(X1,k9_relat_1(X1,X0)),X0)
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( r1_tarski(k10_relat_1(X1,k9_relat_1(X1,X0)),X0)
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( r1_tarski(k10_relat_1(X1,k9_relat_1(X1,X0)),X0)
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( v2_funct_1(X1)
       => r1_tarski(k10_relat_1(X1,k9_relat_1(X1,X0)),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t152_funct_1)).

fof(f43,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k5_xboole_0(X0,k3_xboole_0(X0,X1))
      | r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f39,f32])).

fof(f39,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | k4_xboole_0(X0,X1) != k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f24])).

fof(f134,plain,(
    spl3_5 ),
    inference(avatar_contradiction_clause,[],[f133])).

fof(f133,plain,
    ( $false
    | spl3_5 ),
    inference(subsumption_resolution,[],[f132,f25])).

fof(f132,plain,
    ( ~ v1_relat_1(sK2)
    | spl3_5 ),
    inference(subsumption_resolution,[],[f131,f26])).

fof(f131,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | spl3_5 ),
    inference(subsumption_resolution,[],[f130,f29])).

fof(f130,plain,
    ( ~ v2_funct_1(sK2)
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | spl3_5 ),
    inference(resolution,[],[f121,f35])).

fof(f121,plain,
    ( ~ r1_tarski(k10_relat_1(sK2,k9_relat_1(sK2,sK0)),sK0)
    | spl3_5 ),
    inference(avatar_component_clause,[],[f119])).

fof(f119,plain,
    ( spl3_5
  <=> r1_tarski(k10_relat_1(sK2,k9_relat_1(sK2,sK0)),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f126,plain,
    ( ~ spl3_5
    | spl3_6 ),
    inference(avatar_split_clause,[],[f115,f123,f119])).

fof(f115,plain,
    ( sK0 = k10_relat_1(sK2,k9_relat_1(sK2,sK0))
    | ~ r1_tarski(k10_relat_1(sK2,k9_relat_1(sK2,sK0)),sK0) ),
    inference(resolution,[],[f113,f38])).

fof(f113,plain,(
    r1_tarski(sK0,k10_relat_1(sK2,k9_relat_1(sK2,sK0))) ),
    inference(subsumption_resolution,[],[f110,f87])).

fof(f110,plain,
    ( k1_xboole_0 != k5_xboole_0(sK0,sK0)
    | r1_tarski(sK0,k10_relat_1(sK2,k9_relat_1(sK2,sK0))) ),
    inference(superposition,[],[f43,f108])).

fof(f108,plain,(
    sK0 = k3_xboole_0(sK0,k10_relat_1(sK2,k9_relat_1(sK2,sK0))) ),
    inference(subsumption_resolution,[],[f107,f25])).

fof(f107,plain,
    ( ~ v1_relat_1(sK2)
    | sK0 = k3_xboole_0(sK0,k10_relat_1(sK2,k9_relat_1(sK2,sK0))) ),
    inference(resolution,[],[f100,f28])).

fof(f100,plain,(
    ! [X4,X5] :
      ( ~ r1_tarski(X4,k1_relat_1(X5))
      | ~ v1_relat_1(X5)
      | k3_xboole_0(X4,k10_relat_1(X5,k9_relat_1(X5,X4))) = X4 ) ),
    inference(resolution,[],[f33,f34])).

fof(f33,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(X0,k1_relat_1(X1))
       => r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t146_funct_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n019.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 11:18:52 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.54  % (32007)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.22/0.54  % (31995)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.22/0.55  % (32023)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 0.22/0.55  % (32000)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.22/0.56  % (31996)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.22/0.56  % (32001)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.57  % (32001)Refutation found. Thanks to Tanya!
% 0.22/0.57  % SZS status Theorem for theBenchmark
% 0.22/0.57  % SZS output start Proof for theBenchmark
% 0.22/0.57  % (32016)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 0.22/0.57  % (32008)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.22/0.57  % (31998)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.22/0.57  % (32023)Refutation not found, incomplete strategy% (32023)------------------------------
% 0.22/0.57  % (32023)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.57  % (32023)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.57  
% 0.22/0.57  % (32023)Memory used [KB]: 10746
% 0.22/0.57  % (32023)Time elapsed: 0.143 s
% 0.22/0.57  % (32023)------------------------------
% 0.22/0.57  % (32023)------------------------------
% 0.22/0.58  % (32006)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.22/0.58  fof(f189,plain,(
% 0.22/0.58    $false),
% 0.22/0.58    inference(avatar_sat_refutation,[],[f126,f134,f188])).
% 0.22/0.58  fof(f188,plain,(
% 0.22/0.58    ~spl3_6),
% 0.22/0.58    inference(avatar_contradiction_clause,[],[f187])).
% 0.22/0.58  fof(f187,plain,(
% 0.22/0.58    $false | ~spl3_6),
% 0.22/0.58    inference(subsumption_resolution,[],[f186,f30])).
% 0.22/0.58  fof(f30,plain,(
% 0.22/0.58    ~r1_tarski(sK0,sK1)),
% 0.22/0.58    inference(cnf_transformation,[],[f21])).
% 0.22/0.58  fof(f21,plain,(
% 0.22/0.58    ~r1_tarski(sK0,sK1) & v2_funct_1(sK2) & r1_tarski(sK0,k1_relat_1(sK2)) & r1_tarski(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1)) & v1_funct_1(sK2) & v1_relat_1(sK2)),
% 0.22/0.58    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f12,f20])).
% 0.22/0.58  fof(f20,plain,(
% 0.22/0.58    ? [X0,X1,X2] : (~r1_tarski(X0,X1) & v2_funct_1(X2) & r1_tarski(X0,k1_relat_1(X2)) & r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) & v1_funct_1(X2) & v1_relat_1(X2)) => (~r1_tarski(sK0,sK1) & v2_funct_1(sK2) & r1_tarski(sK0,k1_relat_1(sK2)) & r1_tarski(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1)) & v1_funct_1(sK2) & v1_relat_1(sK2))),
% 0.22/0.58    introduced(choice_axiom,[])).
% 0.22/0.58  fof(f12,plain,(
% 0.22/0.58    ? [X0,X1,X2] : (~r1_tarski(X0,X1) & v2_funct_1(X2) & r1_tarski(X0,k1_relat_1(X2)) & r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) & v1_funct_1(X2) & v1_relat_1(X2))),
% 0.22/0.58    inference(flattening,[],[f11])).
% 0.22/0.58  fof(f11,plain,(
% 0.22/0.58    ? [X0,X1,X2] : ((~r1_tarski(X0,X1) & (v2_funct_1(X2) & r1_tarski(X0,k1_relat_1(X2)) & r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1)))) & (v1_funct_1(X2) & v1_relat_1(X2)))),
% 0.22/0.58    inference(ennf_transformation,[],[f10])).
% 0.22/0.58  fof(f10,negated_conjecture,(
% 0.22/0.58    ~! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ((v2_funct_1(X2) & r1_tarski(X0,k1_relat_1(X2)) & r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1))) => r1_tarski(X0,X1)))),
% 0.22/0.58    inference(negated_conjecture,[],[f9])).
% 0.22/0.58  fof(f9,conjecture,(
% 0.22/0.58    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ((v2_funct_1(X2) & r1_tarski(X0,k1_relat_1(X2)) & r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1))) => r1_tarski(X0,X1)))),
% 0.22/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t157_funct_1)).
% 0.22/0.58  fof(f186,plain,(
% 0.22/0.58    r1_tarski(sK0,sK1) | ~spl3_6),
% 0.22/0.58    inference(subsumption_resolution,[],[f177,f87])).
% 0.22/0.58  fof(f87,plain,(
% 0.22/0.58    k1_xboole_0 = k5_xboole_0(sK0,sK0)),
% 0.22/0.58    inference(forward_demodulation,[],[f83,f49])).
% 0.22/0.58  fof(f49,plain,(
% 0.22/0.58    sK0 = k3_xboole_0(sK0,k1_relat_1(sK2))),
% 0.22/0.58    inference(resolution,[],[f34,f28])).
% 0.22/0.58  fof(f28,plain,(
% 0.22/0.58    r1_tarski(sK0,k1_relat_1(sK2))),
% 0.22/0.58    inference(cnf_transformation,[],[f21])).
% 0.22/0.58  fof(f34,plain,(
% 0.22/0.58    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0) )),
% 0.22/0.58    inference(cnf_transformation,[],[f15])).
% 0.22/0.58  fof(f15,plain,(
% 0.22/0.58    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 0.22/0.58    inference(ennf_transformation,[],[f5])).
% 0.22/0.58  fof(f5,axiom,(
% 0.22/0.58    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 0.22/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).
% 0.22/0.58  fof(f83,plain,(
% 0.22/0.58    k1_xboole_0 = k5_xboole_0(sK0,k3_xboole_0(sK0,k1_relat_1(sK2)))),
% 0.22/0.58    inference(resolution,[],[f42,f28])).
% 0.22/0.58  fof(f42,plain,(
% 0.22/0.58    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k1_xboole_0 = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 0.22/0.58    inference(definition_unfolding,[],[f40,f32])).
% 0.22/0.58  fof(f32,plain,(
% 0.22/0.58    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 0.22/0.58    inference(cnf_transformation,[],[f3])).
% 0.22/0.58  fof(f3,axiom,(
% 0.22/0.58    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 0.22/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).
% 0.22/0.58  fof(f40,plain,(
% 0.22/0.58    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) )),
% 0.22/0.58    inference(cnf_transformation,[],[f24])).
% 0.22/0.58  fof(f24,plain,(
% 0.22/0.58    ! [X0,X1] : ((k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0))),
% 0.22/0.58    inference(nnf_transformation,[],[f2])).
% 0.22/0.58  fof(f2,axiom,(
% 0.22/0.58    ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 <=> r1_tarski(X0,X1))),
% 0.22/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).
% 0.22/0.58  fof(f177,plain,(
% 0.22/0.58    k1_xboole_0 != k5_xboole_0(sK0,sK0) | r1_tarski(sK0,sK1) | ~spl3_6),
% 0.22/0.58    inference(superposition,[],[f43,f164])).
% 0.22/0.58  fof(f164,plain,(
% 0.22/0.58    sK0 = k3_xboole_0(sK0,sK1) | ~spl3_6),
% 0.22/0.58    inference(resolution,[],[f161,f54])).
% 0.22/0.58  fof(f54,plain,(
% 0.22/0.58    ( ! [X2,X1] : (~r1_tarski(X1,k3_xboole_0(X1,X2)) | k3_xboole_0(X1,X2) = X1) )),
% 0.22/0.58    inference(resolution,[],[f38,f31])).
% 0.22/0.58  fof(f31,plain,(
% 0.22/0.58    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) )),
% 0.22/0.58    inference(cnf_transformation,[],[f4])).
% 0.22/0.58  fof(f4,axiom,(
% 0.22/0.58    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0)),
% 0.22/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).
% 0.22/0.58  fof(f38,plain,(
% 0.22/0.58    ( ! [X0,X1] : (~r1_tarski(X1,X0) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 0.22/0.58    inference(cnf_transformation,[],[f23])).
% 0.22/0.58  fof(f23,plain,(
% 0.22/0.58    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.22/0.58    inference(flattening,[],[f22])).
% 0.22/0.58  fof(f22,plain,(
% 0.22/0.58    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.22/0.58    inference(nnf_transformation,[],[f1])).
% 0.22/0.58  fof(f1,axiom,(
% 0.22/0.58    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.22/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.22/0.58  fof(f161,plain,(
% 0.22/0.58    r1_tarski(sK0,k3_xboole_0(sK0,sK1)) | ~spl3_6),
% 0.22/0.58    inference(forward_demodulation,[],[f160,f125])).
% 0.22/0.58  fof(f125,plain,(
% 0.22/0.58    sK0 = k10_relat_1(sK2,k9_relat_1(sK2,sK0)) | ~spl3_6),
% 0.22/0.58    inference(avatar_component_clause,[],[f123])).
% 0.22/0.58  fof(f123,plain,(
% 0.22/0.58    spl3_6 <=> sK0 = k10_relat_1(sK2,k9_relat_1(sK2,sK0))),
% 0.22/0.58    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 0.22/0.58  fof(f160,plain,(
% 0.22/0.58    r1_tarski(k10_relat_1(sK2,k9_relat_1(sK2,sK0)),k3_xboole_0(sK0,sK1))),
% 0.22/0.58    inference(subsumption_resolution,[],[f159,f25])).
% 0.22/0.58  fof(f25,plain,(
% 0.22/0.58    v1_relat_1(sK2)),
% 0.22/0.58    inference(cnf_transformation,[],[f21])).
% 0.22/0.58  fof(f159,plain,(
% 0.22/0.58    r1_tarski(k10_relat_1(sK2,k9_relat_1(sK2,sK0)),k3_xboole_0(sK0,sK1)) | ~v1_relat_1(sK2)),
% 0.22/0.58    inference(subsumption_resolution,[],[f158,f26])).
% 0.22/0.58  fof(f26,plain,(
% 0.22/0.58    v1_funct_1(sK2)),
% 0.22/0.58    inference(cnf_transformation,[],[f21])).
% 0.22/0.58  fof(f158,plain,(
% 0.22/0.58    r1_tarski(k10_relat_1(sK2,k9_relat_1(sK2,sK0)),k3_xboole_0(sK0,sK1)) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2)),
% 0.22/0.58    inference(subsumption_resolution,[],[f154,f29])).
% 0.22/0.58  fof(f29,plain,(
% 0.22/0.58    v2_funct_1(sK2)),
% 0.22/0.58    inference(cnf_transformation,[],[f21])).
% 0.22/0.58  fof(f154,plain,(
% 0.22/0.58    r1_tarski(k10_relat_1(sK2,k9_relat_1(sK2,sK0)),k3_xboole_0(sK0,sK1)) | ~v2_funct_1(sK2) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2)),
% 0.22/0.58    inference(superposition,[],[f35,f144])).
% 0.22/0.58  fof(f144,plain,(
% 0.22/0.58    k9_relat_1(sK2,sK0) = k9_relat_1(sK2,k3_xboole_0(sK0,sK1))),
% 0.22/0.58    inference(superposition,[],[f129,f48])).
% 0.22/0.58  fof(f48,plain,(
% 0.22/0.58    k9_relat_1(sK2,sK0) = k3_xboole_0(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1))),
% 0.22/0.58    inference(resolution,[],[f34,f27])).
% 0.22/0.58  fof(f27,plain,(
% 0.22/0.58    r1_tarski(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1))),
% 0.22/0.58    inference(cnf_transformation,[],[f21])).
% 0.22/0.58  fof(f129,plain,(
% 0.22/0.58    ( ! [X0,X1] : (k9_relat_1(sK2,k3_xboole_0(X0,X1)) = k3_xboole_0(k9_relat_1(sK2,X0),k9_relat_1(sK2,X1))) )),
% 0.22/0.58    inference(subsumption_resolution,[],[f128,f25])).
% 0.22/0.58  fof(f128,plain,(
% 0.22/0.58    ( ! [X0,X1] : (k9_relat_1(sK2,k3_xboole_0(X0,X1)) = k3_xboole_0(k9_relat_1(sK2,X0),k9_relat_1(sK2,X1)) | ~v1_relat_1(sK2)) )),
% 0.22/0.58    inference(subsumption_resolution,[],[f127,f26])).
% 0.22/0.58  fof(f127,plain,(
% 0.22/0.58    ( ! [X0,X1] : (k9_relat_1(sK2,k3_xboole_0(X0,X1)) = k3_xboole_0(k9_relat_1(sK2,X0),k9_relat_1(sK2,X1)) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2)) )),
% 0.22/0.58    inference(resolution,[],[f41,f29])).
% 0.22/0.59  fof(f41,plain,(
% 0.22/0.59    ( ! [X2,X0,X1] : (~v2_funct_1(X2) | k9_relat_1(X2,k3_xboole_0(X0,X1)) = k3_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 0.22/0.59    inference(cnf_transformation,[],[f19])).
% 0.22/0.59  fof(f19,plain,(
% 0.22/0.59    ! [X0,X1,X2] : (k9_relat_1(X2,k3_xboole_0(X0,X1)) = k3_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) | ~v2_funct_1(X2) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 0.22/0.59    inference(flattening,[],[f18])).
% 0.22/0.59  fof(f18,plain,(
% 0.22/0.59    ! [X0,X1,X2] : ((k9_relat_1(X2,k3_xboole_0(X0,X1)) = k3_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) | ~v2_funct_1(X2)) | (~v1_funct_1(X2) | ~v1_relat_1(X2)))),
% 0.22/0.59    inference(ennf_transformation,[],[f6])).
% 0.22/0.59  fof(f6,axiom,(
% 0.22/0.59    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (v2_funct_1(X2) => k9_relat_1(X2,k3_xboole_0(X0,X1)) = k3_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1))))),
% 0.22/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t121_funct_1)).
% 0.22/0.59  fof(f35,plain,(
% 0.22/0.59    ( ! [X0,X1] : (r1_tarski(k10_relat_1(X1,k9_relat_1(X1,X0)),X0) | ~v2_funct_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 0.22/0.59    inference(cnf_transformation,[],[f17])).
% 0.22/0.59  fof(f17,plain,(
% 0.22/0.59    ! [X0,X1] : (r1_tarski(k10_relat_1(X1,k9_relat_1(X1,X0)),X0) | ~v2_funct_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 0.22/0.59    inference(flattening,[],[f16])).
% 0.22/0.59  fof(f16,plain,(
% 0.22/0.59    ! [X0,X1] : ((r1_tarski(k10_relat_1(X1,k9_relat_1(X1,X0)),X0) | ~v2_funct_1(X1)) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 0.22/0.59    inference(ennf_transformation,[],[f8])).
% 0.22/0.59  fof(f8,axiom,(
% 0.22/0.59    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (v2_funct_1(X1) => r1_tarski(k10_relat_1(X1,k9_relat_1(X1,X0)),X0)))),
% 0.22/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t152_funct_1)).
% 0.22/0.59  fof(f43,plain,(
% 0.22/0.59    ( ! [X0,X1] : (k1_xboole_0 != k5_xboole_0(X0,k3_xboole_0(X0,X1)) | r1_tarski(X0,X1)) )),
% 0.22/0.59    inference(definition_unfolding,[],[f39,f32])).
% 0.22/0.59  fof(f39,plain,(
% 0.22/0.59    ( ! [X0,X1] : (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0) )),
% 0.22/0.59    inference(cnf_transformation,[],[f24])).
% 0.22/0.59  fof(f134,plain,(
% 0.22/0.59    spl3_5),
% 0.22/0.59    inference(avatar_contradiction_clause,[],[f133])).
% 0.22/0.59  fof(f133,plain,(
% 0.22/0.59    $false | spl3_5),
% 0.22/0.59    inference(subsumption_resolution,[],[f132,f25])).
% 0.22/0.59  fof(f132,plain,(
% 0.22/0.59    ~v1_relat_1(sK2) | spl3_5),
% 0.22/0.59    inference(subsumption_resolution,[],[f131,f26])).
% 0.22/0.59  fof(f131,plain,(
% 0.22/0.59    ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | spl3_5),
% 0.22/0.59    inference(subsumption_resolution,[],[f130,f29])).
% 0.22/0.59  fof(f130,plain,(
% 0.22/0.59    ~v2_funct_1(sK2) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | spl3_5),
% 0.22/0.59    inference(resolution,[],[f121,f35])).
% 0.22/0.59  fof(f121,plain,(
% 0.22/0.59    ~r1_tarski(k10_relat_1(sK2,k9_relat_1(sK2,sK0)),sK0) | spl3_5),
% 0.22/0.59    inference(avatar_component_clause,[],[f119])).
% 0.22/0.59  fof(f119,plain,(
% 0.22/0.59    spl3_5 <=> r1_tarski(k10_relat_1(sK2,k9_relat_1(sK2,sK0)),sK0)),
% 0.22/0.59    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 0.22/0.59  fof(f126,plain,(
% 0.22/0.59    ~spl3_5 | spl3_6),
% 0.22/0.59    inference(avatar_split_clause,[],[f115,f123,f119])).
% 0.22/0.59  fof(f115,plain,(
% 0.22/0.59    sK0 = k10_relat_1(sK2,k9_relat_1(sK2,sK0)) | ~r1_tarski(k10_relat_1(sK2,k9_relat_1(sK2,sK0)),sK0)),
% 0.22/0.59    inference(resolution,[],[f113,f38])).
% 0.22/0.59  fof(f113,plain,(
% 0.22/0.59    r1_tarski(sK0,k10_relat_1(sK2,k9_relat_1(sK2,sK0)))),
% 0.22/0.59    inference(subsumption_resolution,[],[f110,f87])).
% 0.22/0.59  fof(f110,plain,(
% 0.22/0.59    k1_xboole_0 != k5_xboole_0(sK0,sK0) | r1_tarski(sK0,k10_relat_1(sK2,k9_relat_1(sK2,sK0)))),
% 0.22/0.59    inference(superposition,[],[f43,f108])).
% 0.22/0.59  fof(f108,plain,(
% 0.22/0.59    sK0 = k3_xboole_0(sK0,k10_relat_1(sK2,k9_relat_1(sK2,sK0)))),
% 0.22/0.59    inference(subsumption_resolution,[],[f107,f25])).
% 0.22/0.59  fof(f107,plain,(
% 0.22/0.59    ~v1_relat_1(sK2) | sK0 = k3_xboole_0(sK0,k10_relat_1(sK2,k9_relat_1(sK2,sK0)))),
% 0.22/0.59    inference(resolution,[],[f100,f28])).
% 0.22/0.59  fof(f100,plain,(
% 0.22/0.59    ( ! [X4,X5] : (~r1_tarski(X4,k1_relat_1(X5)) | ~v1_relat_1(X5) | k3_xboole_0(X4,k10_relat_1(X5,k9_relat_1(X5,X4))) = X4) )),
% 0.22/0.59    inference(resolution,[],[f33,f34])).
% 0.22/0.59  fof(f33,plain,(
% 0.22/0.59    ( ! [X0,X1] : (r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) | ~r1_tarski(X0,k1_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 0.22/0.59    inference(cnf_transformation,[],[f14])).
% 0.22/0.59  fof(f14,plain,(
% 0.22/0.59    ! [X0,X1] : (r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) | ~r1_tarski(X0,k1_relat_1(X1)) | ~v1_relat_1(X1))),
% 0.22/0.59    inference(flattening,[],[f13])).
% 0.22/0.59  fof(f13,plain,(
% 0.22/0.59    ! [X0,X1] : ((r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) | ~r1_tarski(X0,k1_relat_1(X1))) | ~v1_relat_1(X1))),
% 0.22/0.59    inference(ennf_transformation,[],[f7])).
% 0.22/0.59  fof(f7,axiom,(
% 0.22/0.59    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(X0,k1_relat_1(X1)) => r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))))),
% 0.22/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t146_funct_1)).
% 0.22/0.59  % SZS output end Proof for theBenchmark
% 0.22/0.59  % (32001)------------------------------
% 0.22/0.59  % (32001)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.59  % (32001)Termination reason: Refutation
% 0.22/0.59  
% 0.22/0.59  % (32001)Memory used [KB]: 10746
% 0.22/0.59  % (32001)Time elapsed: 0.146 s
% 0.22/0.59  % (32001)------------------------------
% 0.22/0.59  % (32001)------------------------------
% 0.22/0.59  % (32011)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 0.22/0.59  % (31994)Success in time 0.226 s
%------------------------------------------------------------------------------
