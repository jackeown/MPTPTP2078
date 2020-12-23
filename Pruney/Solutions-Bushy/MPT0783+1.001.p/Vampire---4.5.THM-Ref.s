%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0783+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n031.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:48:39 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   71 ( 250 expanded)
%              Number of leaves         :   11 (  70 expanded)
%              Depth                    :   14
%              Number of atoms          :  200 ( 904 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f115,plain,(
    $false ),
    inference(unit_resulting_resolution,[],[f34,f86,f110,f36])).

fof(f36,plain,(
    ! [X0] :
      ( ~ sP1(X0)
      | ~ sP0(X0)
      | v2_wellord1(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ( ( v2_wellord1(X0)
          | ~ sP0(X0) )
        & ( sP0(X0)
          | ~ v2_wellord1(X0) ) )
      | ~ sP1(X0) ) ),
    inference(nnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ( v2_wellord1(X0)
      <=> sP0(X0) )
      | ~ sP1(X0) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f110,plain,(
    ! [X1] : sP0(k2_wellord1(sK3,X1)) ),
    inference(global_subsumption,[],[f108])).

fof(f108,plain,(
    ! [X0] : sP0(k2_wellord1(sK3,X0)) ),
    inference(global_subsumption,[],[f77,f80,f85,f107])).

fof(f107,plain,(
    ! [X0] :
      ( sP0(k2_wellord1(sK3,X0))
      | ~ v4_relat_2(k2_wellord1(sK3,X0))
      | ~ v8_relat_2(k2_wellord1(sK3,X0))
      | ~ v1_relat_2(k2_wellord1(sK3,X0)) ) ),
    inference(subsumption_resolution,[],[f105,f69])).

fof(f69,plain,(
    ! [X0] : v6_relat_2(k2_wellord1(sK3,X0)) ),
    inference(unit_resulting_resolution,[],[f32,f60,f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ~ v6_relat_2(X1)
      | v6_relat_2(k2_wellord1(X1,X0))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( v6_relat_2(k2_wellord1(X1,X0))
      | ~ v6_relat_2(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( v6_relat_2(k2_wellord1(X1,X0))
      | ~ v6_relat_2(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v6_relat_2(X1)
       => v6_relat_2(k2_wellord1(X1,X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t23_wellord1)).

fof(f60,plain,(
    v6_relat_2(sK3) ),
    inference(unit_resulting_resolution,[],[f52,f40])).

fof(f40,plain,(
    ! [X0] :
      ( ~ sP0(X0)
      | v6_relat_2(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( ( sP0(X0)
        | ~ v1_wellord1(X0)
        | ~ v6_relat_2(X0)
        | ~ v4_relat_2(X0)
        | ~ v8_relat_2(X0)
        | ~ v1_relat_2(X0) )
      & ( ( v1_wellord1(X0)
          & v6_relat_2(X0)
          & v4_relat_2(X0)
          & v8_relat_2(X0)
          & v1_relat_2(X0) )
        | ~ sP0(X0) ) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ( sP0(X0)
        | ~ v1_wellord1(X0)
        | ~ v6_relat_2(X0)
        | ~ v4_relat_2(X0)
        | ~ v8_relat_2(X0)
        | ~ v1_relat_2(X0) )
      & ( ( v1_wellord1(X0)
          & v6_relat_2(X0)
          & v4_relat_2(X0)
          & v8_relat_2(X0)
          & v1_relat_2(X0) )
        | ~ sP0(X0) ) ) ),
    inference(nnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( sP0(X0)
    <=> ( v1_wellord1(X0)
        & v6_relat_2(X0)
        & v4_relat_2(X0)
        & v8_relat_2(X0)
        & v1_relat_2(X0) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f52,plain,(
    sP0(sK3) ),
    inference(unit_resulting_resolution,[],[f33,f50,f35])).

fof(f35,plain,(
    ! [X0] :
      ( ~ sP1(X0)
      | ~ v2_wellord1(X0)
      | sP0(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f50,plain,(
    sP1(sK3) ),
    inference(unit_resulting_resolution,[],[f32,f43])).

fof(f43,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | sP1(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( sP1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(definition_folding,[],[f12,f25,f24])).

fof(f12,plain,(
    ! [X0] :
      ( ( v2_wellord1(X0)
      <=> ( v1_wellord1(X0)
          & v6_relat_2(X0)
          & v4_relat_2(X0)
          & v8_relat_2(X0)
          & v1_relat_2(X0) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( v2_wellord1(X0)
      <=> ( v1_wellord1(X0)
          & v6_relat_2(X0)
          & v4_relat_2(X0)
          & v8_relat_2(X0)
          & v1_relat_2(X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_wellord1)).

fof(f33,plain,(
    v2_wellord1(sK3) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,
    ( ~ v2_wellord1(k2_wellord1(sK3,sK2))
    & v2_wellord1(sK3)
    & v1_relat_1(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f11,f27])).

fof(f27,plain,
    ( ? [X0,X1] :
        ( ~ v2_wellord1(k2_wellord1(X1,X0))
        & v2_wellord1(X1)
        & v1_relat_1(X1) )
   => ( ~ v2_wellord1(k2_wellord1(sK3,sK2))
      & v2_wellord1(sK3)
      & v1_relat_1(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f11,plain,(
    ? [X0,X1] :
      ( ~ v2_wellord1(k2_wellord1(X1,X0))
      & v2_wellord1(X1)
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ? [X0,X1] :
      ( ~ v2_wellord1(k2_wellord1(X1,X0))
      & v2_wellord1(X1)
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,negated_conjecture,(
    ~ ! [X0,X1] :
        ( v1_relat_1(X1)
       => ( v2_wellord1(X1)
         => v2_wellord1(k2_wellord1(X1,X0)) ) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f8,conjecture,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v2_wellord1(X1)
       => v2_wellord1(k2_wellord1(X1,X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t32_wellord1)).

fof(f32,plain,(
    v1_relat_1(sK3) ),
    inference(cnf_transformation,[],[f28])).

fof(f105,plain,(
    ! [X0] :
      ( sP0(k2_wellord1(sK3,X0))
      | ~ v6_relat_2(k2_wellord1(sK3,X0))
      | ~ v4_relat_2(k2_wellord1(sK3,X0))
      | ~ v8_relat_2(k2_wellord1(sK3,X0))
      | ~ v1_relat_2(k2_wellord1(sK3,X0)) ) ),
    inference(resolution,[],[f72,f42])).

fof(f42,plain,(
    ! [X0] :
      ( ~ v1_wellord1(X0)
      | sP0(X0)
      | ~ v6_relat_2(X0)
      | ~ v4_relat_2(X0)
      | ~ v8_relat_2(X0)
      | ~ v1_relat_2(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f72,plain,(
    ! [X0] : v1_wellord1(k2_wellord1(sK3,X0)) ),
    inference(unit_resulting_resolution,[],[f32,f59,f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ~ v1_wellord1(X1)
      | v1_wellord1(k2_wellord1(X1,X0))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( v1_wellord1(k2_wellord1(X1,X0))
      | ~ v1_wellord1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( v1_wellord1(k2_wellord1(X1,X0))
      | ~ v1_wellord1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v1_wellord1(X1)
       => v1_wellord1(k2_wellord1(X1,X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_wellord1)).

fof(f59,plain,(
    v1_wellord1(sK3) ),
    inference(unit_resulting_resolution,[],[f52,f41])).

fof(f41,plain,(
    ! [X0] :
      ( ~ sP0(X0)
      | v1_wellord1(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f85,plain,(
    ! [X0] : v1_relat_2(k2_wellord1(sK3,X0)) ),
    inference(subsumption_resolution,[],[f84,f32])).

fof(f84,plain,(
    ! [X0] :
      ( v1_relat_2(k2_wellord1(sK3,X0))
      | ~ v1_relat_1(sK3) ) ),
    inference(resolution,[],[f63,f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_2(X1)
      | v1_relat_2(k2_wellord1(X1,X0))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( v1_relat_2(k2_wellord1(X1,X0))
      | ~ v1_relat_2(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( v1_relat_2(k2_wellord1(X1,X0))
      | ~ v1_relat_2(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v1_relat_2(X1)
       => v1_relat_2(k2_wellord1(X1,X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_wellord1)).

fof(f63,plain,(
    v1_relat_2(sK3) ),
    inference(unit_resulting_resolution,[],[f52,f37])).

fof(f37,plain,(
    ! [X0] :
      ( ~ sP0(X0)
      | v1_relat_2(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f80,plain,(
    ! [X0] : v8_relat_2(k2_wellord1(sK3,X0)) ),
    inference(subsumption_resolution,[],[f79,f32])).

fof(f79,plain,(
    ! [X0] :
      ( v8_relat_2(k2_wellord1(sK3,X0))
      | ~ v1_relat_1(sK3) ) ),
    inference(resolution,[],[f62,f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( ~ v8_relat_2(X1)
      | v8_relat_2(k2_wellord1(X1,X0))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( v8_relat_2(k2_wellord1(X1,X0))
      | ~ v8_relat_2(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( v8_relat_2(k2_wellord1(X1,X0))
      | ~ v8_relat_2(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v8_relat_2(X1)
       => v8_relat_2(k2_wellord1(X1,X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t24_wellord1)).

fof(f62,plain,(
    v8_relat_2(sK3) ),
    inference(unit_resulting_resolution,[],[f52,f38])).

fof(f38,plain,(
    ! [X0] :
      ( ~ sP0(X0)
      | v8_relat_2(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f77,plain,(
    ! [X0] : v4_relat_2(k2_wellord1(sK3,X0)) ),
    inference(subsumption_resolution,[],[f76,f32])).

fof(f76,plain,(
    ! [X0] :
      ( v4_relat_2(k2_wellord1(sK3,X0))
      | ~ v1_relat_1(sK3) ) ),
    inference(resolution,[],[f61,f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ~ v4_relat_2(X1)
      | v4_relat_2(k2_wellord1(X1,X0))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( v4_relat_2(k2_wellord1(X1,X0))
      | ~ v4_relat_2(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( v4_relat_2(k2_wellord1(X1,X0))
      | ~ v4_relat_2(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v4_relat_2(X1)
       => v4_relat_2(k2_wellord1(X1,X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_wellord1)).

fof(f61,plain,(
    v4_relat_2(sK3) ),
    inference(unit_resulting_resolution,[],[f52,f39])).

fof(f39,plain,(
    ! [X0] :
      ( ~ sP0(X0)
      | v4_relat_2(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f86,plain,(
    ! [X0] : sP1(k2_wellord1(sK3,X0)) ),
    inference(unit_resulting_resolution,[],[f56,f43])).

fof(f56,plain,(
    ! [X0] : v1_relat_1(k2_wellord1(sK3,X0)) ),
    inference(unit_resulting_resolution,[],[f32,f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | v1_relat_1(k2_wellord1(X0,X1)) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k2_wellord1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X0)
     => v1_relat_1(k2_wellord1(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_wellord1)).

fof(f34,plain,(
    ~ v2_wellord1(k2_wellord1(sK3,sK2)) ),
    inference(cnf_transformation,[],[f28])).

%------------------------------------------------------------------------------
