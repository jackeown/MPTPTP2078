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
% DateTime   : Thu Dec  3 12:52:39 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   70 ( 166 expanded)
%              Number of leaves         :   12 (  53 expanded)
%              Depth                    :   24
%              Number of atoms          :  428 (1498 expanded)
%              Number of equality atoms :  143 ( 588 expanded)
%              Maximal formula depth    :   16 (   7 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f187,plain,(
    $false ),
    inference(subsumption_resolution,[],[f186,f59])).

fof(f59,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f57])).

fof(f57,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
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

fof(f186,plain,(
    ~ r1_tarski(sK2,sK2) ),
    inference(forward_demodulation,[],[f185,f41])).

fof(f41,plain,(
    ! [X0] : k2_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

fof(f185,plain,(
    ~ r1_tarski(k2_relat_1(k6_relat_1(sK2)),sK2) ),
    inference(subsumption_resolution,[],[f184,f37])).

fof(f37,plain,(
    k6_relat_1(sK2) != sK4 ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,
    ( k6_relat_1(sK2) != sK4
    & sK3 = k5_relat_1(sK4,sK3)
    & v2_funct_1(sK3)
    & r1_tarski(k2_relat_1(sK4),sK2)
    & sK2 = k1_relat_1(sK4)
    & sK2 = k1_relat_1(sK3)
    & v1_funct_1(sK4)
    & v1_relat_1(sK4)
    & v1_funct_1(sK3)
    & v1_relat_1(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f9,f18,f17])).

fof(f17,plain,
    ( ? [X0,X1] :
        ( ? [X2] :
            ( k6_relat_1(X0) != X2
            & k5_relat_1(X2,X1) = X1
            & v2_funct_1(X1)
            & r1_tarski(k2_relat_1(X2),X0)
            & k1_relat_1(X2) = X0
            & k1_relat_1(X1) = X0
            & v1_funct_1(X2)
            & v1_relat_1(X2) )
        & v1_funct_1(X1)
        & v1_relat_1(X1) )
   => ( ? [X2] :
          ( k6_relat_1(sK2) != X2
          & sK3 = k5_relat_1(X2,sK3)
          & v2_funct_1(sK3)
          & r1_tarski(k2_relat_1(X2),sK2)
          & k1_relat_1(X2) = sK2
          & sK2 = k1_relat_1(sK3)
          & v1_funct_1(X2)
          & v1_relat_1(X2) )
      & v1_funct_1(sK3)
      & v1_relat_1(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,
    ( ? [X2] :
        ( k6_relat_1(sK2) != X2
        & sK3 = k5_relat_1(X2,sK3)
        & v2_funct_1(sK3)
        & r1_tarski(k2_relat_1(X2),sK2)
        & k1_relat_1(X2) = sK2
        & sK2 = k1_relat_1(sK3)
        & v1_funct_1(X2)
        & v1_relat_1(X2) )
   => ( k6_relat_1(sK2) != sK4
      & sK3 = k5_relat_1(sK4,sK3)
      & v2_funct_1(sK3)
      & r1_tarski(k2_relat_1(sK4),sK2)
      & sK2 = k1_relat_1(sK4)
      & sK2 = k1_relat_1(sK3)
      & v1_funct_1(sK4)
      & v1_relat_1(sK4) ) ),
    introduced(choice_axiom,[])).

fof(f9,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( k6_relat_1(X0) != X2
          & k5_relat_1(X2,X1) = X1
          & v2_funct_1(X1)
          & r1_tarski(k2_relat_1(X2),X0)
          & k1_relat_1(X2) = X0
          & k1_relat_1(X1) = X0
          & v1_funct_1(X2)
          & v1_relat_1(X2) )
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f8])).

fof(f8,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( k6_relat_1(X0) != X2
          & k5_relat_1(X2,X1) = X1
          & v2_funct_1(X1)
          & r1_tarski(k2_relat_1(X2),X0)
          & k1_relat_1(X2) = X0
          & k1_relat_1(X1) = X0
          & v1_funct_1(X2)
          & v1_relat_1(X2) )
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ( v1_funct_1(X1)
          & v1_relat_1(X1) )
       => ! [X2] :
            ( ( v1_funct_1(X2)
              & v1_relat_1(X2) )
           => ( ( k5_relat_1(X2,X1) = X1
                & v2_funct_1(X1)
                & r1_tarski(k2_relat_1(X2),X0)
                & k1_relat_1(X2) = X0
                & k1_relat_1(X1) = X0 )
             => k6_relat_1(X0) = X2 ) ) ) ),
    inference(negated_conjecture,[],[f6])).

fof(f6,conjecture,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ! [X2] :
          ( ( v1_funct_1(X2)
            & v1_relat_1(X2) )
         => ( ( k5_relat_1(X2,X1) = X1
              & v2_funct_1(X1)
              & r1_tarski(k2_relat_1(X2),X0)
              & k1_relat_1(X2) = X0
              & k1_relat_1(X1) = X0 )
           => k6_relat_1(X0) = X2 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_funct_1)).

fof(f184,plain,
    ( ~ r1_tarski(k2_relat_1(k6_relat_1(sK2)),sK2)
    | k6_relat_1(sK2) = sK4 ),
    inference(subsumption_resolution,[],[f183,f38])).

fof(f38,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_funct_1(k6_relat_1(X0))
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc3_funct_1)).

fof(f183,plain,
    ( ~ r1_tarski(k2_relat_1(k6_relat_1(sK2)),sK2)
    | ~ v1_relat_1(k6_relat_1(sK2))
    | k6_relat_1(sK2) = sK4 ),
    inference(subsumption_resolution,[],[f182,f39])).

fof(f39,plain,(
    ! [X0] : v1_funct_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f4])).

fof(f182,plain,
    ( ~ r1_tarski(k2_relat_1(k6_relat_1(sK2)),sK2)
    | ~ v1_funct_1(k6_relat_1(sK2))
    | ~ v1_relat_1(k6_relat_1(sK2))
    | k6_relat_1(sK2) = sK4 ),
    inference(subsumption_resolution,[],[f181,f40])).

fof(f40,plain,(
    ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f2])).

fof(f181,plain,
    ( sK2 != k1_relat_1(k6_relat_1(sK2))
    | ~ r1_tarski(k2_relat_1(k6_relat_1(sK2)),sK2)
    | ~ v1_funct_1(k6_relat_1(sK2))
    | ~ v1_relat_1(k6_relat_1(sK2))
    | k6_relat_1(sK2) = sK4 ),
    inference(trivial_inequality_removal,[],[f180])).

fof(f180,plain,
    ( sK3 != sK3
    | sK2 != k1_relat_1(k6_relat_1(sK2))
    | ~ r1_tarski(k2_relat_1(k6_relat_1(sK2)),sK2)
    | ~ v1_funct_1(k6_relat_1(sK2))
    | ~ v1_relat_1(k6_relat_1(sK2))
    | k6_relat_1(sK2) = sK4 ),
    inference(superposition,[],[f164,f85])).

fof(f85,plain,(
    sK3 = k5_relat_1(k6_relat_1(sK2),sK3) ),
    inference(resolution,[],[f82,f59])).

fof(f82,plain,(
    ! [X0] :
      ( ~ r1_tarski(sK2,X0)
      | sK3 = k5_relat_1(k6_relat_1(X0),sK3) ) ),
    inference(subsumption_resolution,[],[f79,f28])).

fof(f28,plain,(
    v1_relat_1(sK3) ),
    inference(cnf_transformation,[],[f19])).

fof(f79,plain,(
    ! [X0] :
      ( ~ r1_tarski(sK2,X0)
      | sK3 = k5_relat_1(k6_relat_1(X0),sK3)
      | ~ v1_relat_1(sK3) ) ),
    inference(superposition,[],[f55,f32])).

fof(f32,plain,(
    sK2 = k1_relat_1(sK3) ),
    inference(cnf_transformation,[],[f19])).

fof(f55,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k1_relat_1(X1),X0)
      | k5_relat_1(k6_relat_1(X0),X1) = X1
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( k5_relat_1(k6_relat_1(X0),X1) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( k5_relat_1(k6_relat_1(X0),X1) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(k1_relat_1(X1),X0)
       => k5_relat_1(k6_relat_1(X0),X1) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t77_relat_1)).

fof(f164,plain,(
    ! [X0] :
      ( sK3 != k5_relat_1(X0,sK3)
      | k1_relat_1(X0) != sK2
      | ~ r1_tarski(k2_relat_1(X0),sK2)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | sK4 = X0 ) ),
    inference(forward_demodulation,[],[f163,f33])).

fof(f33,plain,(
    sK2 = k1_relat_1(sK4) ),
    inference(cnf_transformation,[],[f19])).

fof(f163,plain,(
    ! [X0] :
      ( sK3 != k5_relat_1(X0,sK3)
      | ~ r1_tarski(k2_relat_1(X0),sK2)
      | k1_relat_1(X0) != k1_relat_1(sK4)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | sK4 = X0 ) ),
    inference(subsumption_resolution,[],[f162,f34])).

fof(f34,plain,(
    r1_tarski(k2_relat_1(sK4),sK2) ),
    inference(cnf_transformation,[],[f19])).

fof(f162,plain,(
    ! [X0] :
      ( sK3 != k5_relat_1(X0,sK3)
      | ~ r1_tarski(k2_relat_1(X0),sK2)
      | k1_relat_1(X0) != k1_relat_1(sK4)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | sK4 = X0
      | ~ r1_tarski(k2_relat_1(sK4),sK2) ) ),
    inference(subsumption_resolution,[],[f161,f30])).

fof(f30,plain,(
    v1_relat_1(sK4) ),
    inference(cnf_transformation,[],[f19])).

fof(f161,plain,(
    ! [X0] :
      ( sK3 != k5_relat_1(X0,sK3)
      | ~ r1_tarski(k2_relat_1(X0),sK2)
      | k1_relat_1(X0) != k1_relat_1(sK4)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | ~ v1_relat_1(sK4)
      | sK4 = X0
      | ~ r1_tarski(k2_relat_1(sK4),sK2) ) ),
    inference(subsumption_resolution,[],[f155,f31])).

fof(f31,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f19])).

fof(f155,plain,(
    ! [X0] :
      ( sK3 != k5_relat_1(X0,sK3)
      | ~ r1_tarski(k2_relat_1(X0),sK2)
      | k1_relat_1(X0) != k1_relat_1(sK4)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | ~ v1_funct_1(sK4)
      | ~ v1_relat_1(sK4)
      | sK4 = X0
      | ~ r1_tarski(k2_relat_1(sK4),sK2) ) ),
    inference(superposition,[],[f140,f36])).

fof(f36,plain,(
    sK3 = k5_relat_1(sK4,sK3) ),
    inference(cnf_transformation,[],[f19])).

fof(f140,plain,(
    ! [X0,X1] :
      ( k5_relat_1(X0,sK3) != k5_relat_1(X1,sK3)
      | ~ r1_tarski(k2_relat_1(X1),sK2)
      | k1_relat_1(X1) != k1_relat_1(X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | X0 = X1
      | ~ r1_tarski(k2_relat_1(X0),sK2) ) ),
    inference(forward_demodulation,[],[f139,f32])).

fof(f139,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k2_relat_1(X1),sK2)
      | k1_relat_1(X1) != k1_relat_1(X0)
      | ~ r1_tarski(k2_relat_1(X0),k1_relat_1(sK3))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | X0 = X1
      | k5_relat_1(X0,sK3) != k5_relat_1(X1,sK3) ) ),
    inference(forward_demodulation,[],[f138,f32])).

fof(f138,plain,(
    ! [X0,X1] :
      ( k1_relat_1(X1) != k1_relat_1(X0)
      | ~ r1_tarski(k2_relat_1(X1),k1_relat_1(sK3))
      | ~ r1_tarski(k2_relat_1(X0),k1_relat_1(sK3))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | X0 = X1
      | k5_relat_1(X0,sK3) != k5_relat_1(X1,sK3) ) ),
    inference(subsumption_resolution,[],[f137,f29])).

fof(f29,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f19])).

fof(f137,plain,(
    ! [X0,X1] :
      ( k1_relat_1(X1) != k1_relat_1(X0)
      | ~ r1_tarski(k2_relat_1(X1),k1_relat_1(sK3))
      | ~ r1_tarski(k2_relat_1(X0),k1_relat_1(sK3))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | X0 = X1
      | k5_relat_1(X0,sK3) != k5_relat_1(X1,sK3)
      | ~ v1_funct_1(sK3) ) ),
    inference(subsumption_resolution,[],[f136,f28])).

% (28324)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
fof(f136,plain,(
    ! [X0,X1] :
      ( k1_relat_1(X1) != k1_relat_1(X0)
      | ~ r1_tarski(k2_relat_1(X1),k1_relat_1(sK3))
      | ~ r1_tarski(k2_relat_1(X0),k1_relat_1(sK3))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | X0 = X1
      | ~ v1_relat_1(sK3)
      | k5_relat_1(X0,sK3) != k5_relat_1(X1,sK3)
      | ~ v1_funct_1(sK3) ) ),
    inference(resolution,[],[f107,f35])).

fof(f35,plain,(
    v2_funct_1(sK3) ),
    inference(cnf_transformation,[],[f19])).

fof(f107,plain,(
    ! [X6,X8,X7] :
      ( ~ v2_funct_1(X7)
      | k1_relat_1(X6) != k1_relat_1(X8)
      | ~ r1_tarski(k2_relat_1(X8),k1_relat_1(X7))
      | ~ r1_tarski(k2_relat_1(X6),k1_relat_1(X7))
      | ~ v1_funct_1(X8)
      | ~ v1_relat_1(X8)
      | ~ v1_funct_1(X6)
      | ~ v1_relat_1(X6)
      | X6 = X8
      | ~ v1_relat_1(X7)
      | k5_relat_1(X6,X7) != k5_relat_1(X8,X7)
      | ~ v1_funct_1(X7) ) ),
    inference(resolution,[],[f44,f61])).

fof(f61,plain,(
    ! [X0] :
      ( sP0(X0)
      | ~ v1_relat_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0) ) ),
    inference(resolution,[],[f54,f42])).

fof(f42,plain,(
    ! [X0] :
      ( ~ sP1(X0)
      | ~ v2_funct_1(X0)
      | sP0(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ( ( v2_funct_1(X0)
          | ~ sP0(X0) )
        & ( sP0(X0)
          | ~ v2_funct_1(X0) ) )
      | ~ sP1(X0) ) ),
    inference(nnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ( v2_funct_1(X0)
      <=> sP0(X0) )
      | ~ sP1(X0) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f54,plain,(
    ! [X0] :
      ( sP1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( sP1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(definition_folding,[],[f11,f15,f14])).

fof(f14,plain,(
    ! [X0] :
      ( sP0(X0)
    <=> ! [X1] :
          ( ! [X2] :
              ( X1 = X2
              | k5_relat_1(X1,X0) != k5_relat_1(X2,X0)
              | k1_relat_1(X1) != k1_relat_1(X2)
              | ~ r1_tarski(k2_relat_1(X2),k1_relat_1(X0))
              | ~ r1_tarski(k2_relat_1(X1),k1_relat_1(X0))
              | ~ v1_funct_1(X2)
              | ~ v1_relat_1(X2) )
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f11,plain,(
    ! [X0] :
      ( ( v2_funct_1(X0)
      <=> ! [X1] :
            ( ! [X2] :
                ( X1 = X2
                | k5_relat_1(X1,X0) != k5_relat_1(X2,X0)
                | k1_relat_1(X1) != k1_relat_1(X2)
                | ~ r1_tarski(k2_relat_1(X2),k1_relat_1(X0))
                | ~ r1_tarski(k2_relat_1(X1),k1_relat_1(X0))
                | ~ v1_funct_1(X2)
                | ~ v1_relat_1(X2) )
            | ~ v1_funct_1(X1)
            | ~ v1_relat_1(X1) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ! [X0] :
      ( ( v2_funct_1(X0)
      <=> ! [X1] :
            ( ! [X2] :
                ( X1 = X2
                | k5_relat_1(X1,X0) != k5_relat_1(X2,X0)
                | k1_relat_1(X1) != k1_relat_1(X2)
                | ~ r1_tarski(k2_relat_1(X2),k1_relat_1(X0))
                | ~ r1_tarski(k2_relat_1(X1),k1_relat_1(X0))
                | ~ v1_funct_1(X2)
                | ~ v1_relat_1(X2) )
            | ~ v1_funct_1(X1)
            | ~ v1_relat_1(X1) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
      <=> ! [X1] :
            ( ( v1_funct_1(X1)
              & v1_relat_1(X1) )
           => ! [X2] :
                ( ( v1_funct_1(X2)
                  & v1_relat_1(X2) )
               => ( ( k5_relat_1(X1,X0) = k5_relat_1(X2,X0)
                    & k1_relat_1(X1) = k1_relat_1(X2)
                    & r1_tarski(k2_relat_1(X2),k1_relat_1(X0))
                    & r1_tarski(k2_relat_1(X1),k1_relat_1(X0)) )
                 => X1 = X2 ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_funct_1)).

fof(f44,plain,(
    ! [X4,X0,X3] :
      ( ~ sP0(X0)
      | k5_relat_1(X3,X0) != k5_relat_1(X4,X0)
      | k1_relat_1(X3) != k1_relat_1(X4)
      | ~ r1_tarski(k2_relat_1(X4),k1_relat_1(X0))
      | ~ r1_tarski(k2_relat_1(X3),k1_relat_1(X0))
      | ~ v1_funct_1(X4)
      | ~ v1_relat_1(X4)
      | ~ v1_funct_1(X3)
      | ~ v1_relat_1(X3)
      | X3 = X4 ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ( sP0(X0)
        | ( sK5(X0) != sK6(X0)
          & k5_relat_1(sK5(X0),X0) = k5_relat_1(sK6(X0),X0)
          & k1_relat_1(sK5(X0)) = k1_relat_1(sK6(X0))
          & r1_tarski(k2_relat_1(sK6(X0)),k1_relat_1(X0))
          & r1_tarski(k2_relat_1(sK5(X0)),k1_relat_1(X0))
          & v1_funct_1(sK6(X0))
          & v1_relat_1(sK6(X0))
          & v1_funct_1(sK5(X0))
          & v1_relat_1(sK5(X0)) ) )
      & ( ! [X3] :
            ( ! [X4] :
                ( X3 = X4
                | k5_relat_1(X3,X0) != k5_relat_1(X4,X0)
                | k1_relat_1(X3) != k1_relat_1(X4)
                | ~ r1_tarski(k2_relat_1(X4),k1_relat_1(X0))
                | ~ r1_tarski(k2_relat_1(X3),k1_relat_1(X0))
                | ~ v1_funct_1(X4)
                | ~ v1_relat_1(X4) )
            | ~ v1_funct_1(X3)
            | ~ v1_relat_1(X3) )
        | ~ sP0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6])],[f22,f24,f23])).

fof(f23,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( X1 != X2
              & k5_relat_1(X1,X0) = k5_relat_1(X2,X0)
              & k1_relat_1(X1) = k1_relat_1(X2)
              & r1_tarski(k2_relat_1(X2),k1_relat_1(X0))
              & r1_tarski(k2_relat_1(X1),k1_relat_1(X0))
              & v1_funct_1(X2)
              & v1_relat_1(X2) )
          & v1_funct_1(X1)
          & v1_relat_1(X1) )
     => ( ? [X2] :
            ( sK5(X0) != X2
            & k5_relat_1(X2,X0) = k5_relat_1(sK5(X0),X0)
            & k1_relat_1(X2) = k1_relat_1(sK5(X0))
            & r1_tarski(k2_relat_1(X2),k1_relat_1(X0))
            & r1_tarski(k2_relat_1(sK5(X0)),k1_relat_1(X0))
            & v1_funct_1(X2)
            & v1_relat_1(X2) )
        & v1_funct_1(sK5(X0))
        & v1_relat_1(sK5(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,(
    ! [X0] :
      ( ? [X2] :
          ( sK5(X0) != X2
          & k5_relat_1(X2,X0) = k5_relat_1(sK5(X0),X0)
          & k1_relat_1(X2) = k1_relat_1(sK5(X0))
          & r1_tarski(k2_relat_1(X2),k1_relat_1(X0))
          & r1_tarski(k2_relat_1(sK5(X0)),k1_relat_1(X0))
          & v1_funct_1(X2)
          & v1_relat_1(X2) )
     => ( sK5(X0) != sK6(X0)
        & k5_relat_1(sK5(X0),X0) = k5_relat_1(sK6(X0),X0)
        & k1_relat_1(sK5(X0)) = k1_relat_1(sK6(X0))
        & r1_tarski(k2_relat_1(sK6(X0)),k1_relat_1(X0))
        & r1_tarski(k2_relat_1(sK5(X0)),k1_relat_1(X0))
        & v1_funct_1(sK6(X0))
        & v1_relat_1(sK6(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,(
    ! [X0] :
      ( ( sP0(X0)
        | ? [X1] :
            ( ? [X2] :
                ( X1 != X2
                & k5_relat_1(X1,X0) = k5_relat_1(X2,X0)
                & k1_relat_1(X1) = k1_relat_1(X2)
                & r1_tarski(k2_relat_1(X2),k1_relat_1(X0))
                & r1_tarski(k2_relat_1(X1),k1_relat_1(X0))
                & v1_funct_1(X2)
                & v1_relat_1(X2) )
            & v1_funct_1(X1)
            & v1_relat_1(X1) ) )
      & ( ! [X3] :
            ( ! [X4] :
                ( X3 = X4
                | k5_relat_1(X3,X0) != k5_relat_1(X4,X0)
                | k1_relat_1(X3) != k1_relat_1(X4)
                | ~ r1_tarski(k2_relat_1(X4),k1_relat_1(X0))
                | ~ r1_tarski(k2_relat_1(X3),k1_relat_1(X0))
                | ~ v1_funct_1(X4)
                | ~ v1_relat_1(X4) )
            | ~ v1_funct_1(X3)
            | ~ v1_relat_1(X3) )
        | ~ sP0(X0) ) ) ),
    inference(rectify,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ( sP0(X0)
        | ? [X1] :
            ( ? [X2] :
                ( X1 != X2
                & k5_relat_1(X1,X0) = k5_relat_1(X2,X0)
                & k1_relat_1(X1) = k1_relat_1(X2)
                & r1_tarski(k2_relat_1(X2),k1_relat_1(X0))
                & r1_tarski(k2_relat_1(X1),k1_relat_1(X0))
                & v1_funct_1(X2)
                & v1_relat_1(X2) )
            & v1_funct_1(X1)
            & v1_relat_1(X1) ) )
      & ( ! [X1] :
            ( ! [X2] :
                ( X1 = X2
                | k5_relat_1(X1,X0) != k5_relat_1(X2,X0)
                | k1_relat_1(X1) != k1_relat_1(X2)
                | ~ r1_tarski(k2_relat_1(X2),k1_relat_1(X0))
                | ~ r1_tarski(k2_relat_1(X1),k1_relat_1(X0))
                | ~ v1_funct_1(X2)
                | ~ v1_relat_1(X2) )
            | ~ v1_funct_1(X1)
            | ~ v1_relat_1(X1) )
        | ~ sP0(X0) ) ) ),
    inference(nnf_transformation,[],[f14])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.15/0.34  % Computer   : n021.cluster.edu
% 0.15/0.34  % Model      : x86_64 x86_64
% 0.15/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.34  % Memory     : 8042.1875MB
% 0.15/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.34  % CPULimit   : 60
% 0.15/0.34  % WCLimit    : 600
% 0.15/0.34  % DateTime   : Tue Dec  1 15:05:49 EST 2020
% 0.15/0.34  % CPUTime    : 
% 0.21/0.49  % (28317)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.21/0.50  % (28335)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 0.21/0.50  % (28322)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 0.21/0.50  % (28333)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 0.21/0.50  % (28317)Refutation found. Thanks to Tanya!
% 0.21/0.50  % SZS status Theorem for theBenchmark
% 0.21/0.50  % SZS output start Proof for theBenchmark
% 0.21/0.50  fof(f187,plain,(
% 0.21/0.50    $false),
% 0.21/0.50    inference(subsumption_resolution,[],[f186,f59])).
% 0.21/0.50  fof(f59,plain,(
% 0.21/0.50    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 0.21/0.50    inference(equality_resolution,[],[f57])).
% 0.21/0.50  fof(f57,plain,(
% 0.21/0.50    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 0.21/0.50    inference(cnf_transformation,[],[f27])).
% 0.21/0.50  fof(f27,plain,(
% 0.21/0.50    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.21/0.50    inference(flattening,[],[f26])).
% 0.21/0.50  fof(f26,plain,(
% 0.21/0.50    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.21/0.50    inference(nnf_transformation,[],[f1])).
% 0.21/0.50  fof(f1,axiom,(
% 0.21/0.50    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.21/0.50  fof(f186,plain,(
% 0.21/0.50    ~r1_tarski(sK2,sK2)),
% 0.21/0.50    inference(forward_demodulation,[],[f185,f41])).
% 0.21/0.50  fof(f41,plain,(
% 0.21/0.50    ( ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0) )),
% 0.21/0.50    inference(cnf_transformation,[],[f2])).
% 0.21/0.50  fof(f2,axiom,(
% 0.21/0.50    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).
% 0.21/0.50  fof(f185,plain,(
% 0.21/0.50    ~r1_tarski(k2_relat_1(k6_relat_1(sK2)),sK2)),
% 0.21/0.50    inference(subsumption_resolution,[],[f184,f37])).
% 0.21/0.50  fof(f37,plain,(
% 0.21/0.50    k6_relat_1(sK2) != sK4),
% 0.21/0.50    inference(cnf_transformation,[],[f19])).
% 0.21/0.50  fof(f19,plain,(
% 0.21/0.50    (k6_relat_1(sK2) != sK4 & sK3 = k5_relat_1(sK4,sK3) & v2_funct_1(sK3) & r1_tarski(k2_relat_1(sK4),sK2) & sK2 = k1_relat_1(sK4) & sK2 = k1_relat_1(sK3) & v1_funct_1(sK4) & v1_relat_1(sK4)) & v1_funct_1(sK3) & v1_relat_1(sK3)),
% 0.21/0.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f9,f18,f17])).
% 0.21/0.50  fof(f17,plain,(
% 0.21/0.50    ? [X0,X1] : (? [X2] : (k6_relat_1(X0) != X2 & k5_relat_1(X2,X1) = X1 & v2_funct_1(X1) & r1_tarski(k2_relat_1(X2),X0) & k1_relat_1(X2) = X0 & k1_relat_1(X1) = X0 & v1_funct_1(X2) & v1_relat_1(X2)) & v1_funct_1(X1) & v1_relat_1(X1)) => (? [X2] : (k6_relat_1(sK2) != X2 & sK3 = k5_relat_1(X2,sK3) & v2_funct_1(sK3) & r1_tarski(k2_relat_1(X2),sK2) & k1_relat_1(X2) = sK2 & sK2 = k1_relat_1(sK3) & v1_funct_1(X2) & v1_relat_1(X2)) & v1_funct_1(sK3) & v1_relat_1(sK3))),
% 0.21/0.50    introduced(choice_axiom,[])).
% 0.21/0.50  fof(f18,plain,(
% 0.21/0.50    ? [X2] : (k6_relat_1(sK2) != X2 & sK3 = k5_relat_1(X2,sK3) & v2_funct_1(sK3) & r1_tarski(k2_relat_1(X2),sK2) & k1_relat_1(X2) = sK2 & sK2 = k1_relat_1(sK3) & v1_funct_1(X2) & v1_relat_1(X2)) => (k6_relat_1(sK2) != sK4 & sK3 = k5_relat_1(sK4,sK3) & v2_funct_1(sK3) & r1_tarski(k2_relat_1(sK4),sK2) & sK2 = k1_relat_1(sK4) & sK2 = k1_relat_1(sK3) & v1_funct_1(sK4) & v1_relat_1(sK4))),
% 0.21/0.50    introduced(choice_axiom,[])).
% 0.21/0.50  fof(f9,plain,(
% 0.21/0.50    ? [X0,X1] : (? [X2] : (k6_relat_1(X0) != X2 & k5_relat_1(X2,X1) = X1 & v2_funct_1(X1) & r1_tarski(k2_relat_1(X2),X0) & k1_relat_1(X2) = X0 & k1_relat_1(X1) = X0 & v1_funct_1(X2) & v1_relat_1(X2)) & v1_funct_1(X1) & v1_relat_1(X1))),
% 0.21/0.50    inference(flattening,[],[f8])).
% 0.21/0.50  fof(f8,plain,(
% 0.21/0.50    ? [X0,X1] : (? [X2] : ((k6_relat_1(X0) != X2 & (k5_relat_1(X2,X1) = X1 & v2_funct_1(X1) & r1_tarski(k2_relat_1(X2),X0) & k1_relat_1(X2) = X0 & k1_relat_1(X1) = X0)) & (v1_funct_1(X2) & v1_relat_1(X2))) & (v1_funct_1(X1) & v1_relat_1(X1)))),
% 0.21/0.50    inference(ennf_transformation,[],[f7])).
% 0.21/0.50  fof(f7,negated_conjecture,(
% 0.21/0.50    ~! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ! [X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ((k5_relat_1(X2,X1) = X1 & v2_funct_1(X1) & r1_tarski(k2_relat_1(X2),X0) & k1_relat_1(X2) = X0 & k1_relat_1(X1) = X0) => k6_relat_1(X0) = X2)))),
% 0.21/0.50    inference(negated_conjecture,[],[f6])).
% 0.21/0.50  fof(f6,conjecture,(
% 0.21/0.50    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ! [X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ((k5_relat_1(X2,X1) = X1 & v2_funct_1(X1) & r1_tarski(k2_relat_1(X2),X0) & k1_relat_1(X2) = X0 & k1_relat_1(X1) = X0) => k6_relat_1(X0) = X2)))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_funct_1)).
% 0.21/0.50  fof(f184,plain,(
% 0.21/0.50    ~r1_tarski(k2_relat_1(k6_relat_1(sK2)),sK2) | k6_relat_1(sK2) = sK4),
% 0.21/0.50    inference(subsumption_resolution,[],[f183,f38])).
% 0.21/0.50  fof(f38,plain,(
% 0.21/0.50    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 0.21/0.50    inference(cnf_transformation,[],[f4])).
% 0.21/0.50  fof(f4,axiom,(
% 0.21/0.50    ! [X0] : (v1_funct_1(k6_relat_1(X0)) & v1_relat_1(k6_relat_1(X0)))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc3_funct_1)).
% 0.21/0.50  fof(f183,plain,(
% 0.21/0.50    ~r1_tarski(k2_relat_1(k6_relat_1(sK2)),sK2) | ~v1_relat_1(k6_relat_1(sK2)) | k6_relat_1(sK2) = sK4),
% 0.21/0.50    inference(subsumption_resolution,[],[f182,f39])).
% 0.21/0.50  fof(f39,plain,(
% 0.21/0.50    ( ! [X0] : (v1_funct_1(k6_relat_1(X0))) )),
% 0.21/0.50    inference(cnf_transformation,[],[f4])).
% 0.21/0.50  fof(f182,plain,(
% 0.21/0.50    ~r1_tarski(k2_relat_1(k6_relat_1(sK2)),sK2) | ~v1_funct_1(k6_relat_1(sK2)) | ~v1_relat_1(k6_relat_1(sK2)) | k6_relat_1(sK2) = sK4),
% 0.21/0.50    inference(subsumption_resolution,[],[f181,f40])).
% 0.21/0.50  fof(f40,plain,(
% 0.21/0.50    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = X0) )),
% 0.21/0.50    inference(cnf_transformation,[],[f2])).
% 0.21/0.50  fof(f181,plain,(
% 0.21/0.50    sK2 != k1_relat_1(k6_relat_1(sK2)) | ~r1_tarski(k2_relat_1(k6_relat_1(sK2)),sK2) | ~v1_funct_1(k6_relat_1(sK2)) | ~v1_relat_1(k6_relat_1(sK2)) | k6_relat_1(sK2) = sK4),
% 0.21/0.50    inference(trivial_inequality_removal,[],[f180])).
% 0.21/0.50  fof(f180,plain,(
% 0.21/0.50    sK3 != sK3 | sK2 != k1_relat_1(k6_relat_1(sK2)) | ~r1_tarski(k2_relat_1(k6_relat_1(sK2)),sK2) | ~v1_funct_1(k6_relat_1(sK2)) | ~v1_relat_1(k6_relat_1(sK2)) | k6_relat_1(sK2) = sK4),
% 0.21/0.50    inference(superposition,[],[f164,f85])).
% 0.21/0.50  fof(f85,plain,(
% 0.21/0.50    sK3 = k5_relat_1(k6_relat_1(sK2),sK3)),
% 0.21/0.50    inference(resolution,[],[f82,f59])).
% 0.21/0.50  fof(f82,plain,(
% 0.21/0.50    ( ! [X0] : (~r1_tarski(sK2,X0) | sK3 = k5_relat_1(k6_relat_1(X0),sK3)) )),
% 0.21/0.50    inference(subsumption_resolution,[],[f79,f28])).
% 0.21/0.50  fof(f28,plain,(
% 0.21/0.50    v1_relat_1(sK3)),
% 0.21/0.50    inference(cnf_transformation,[],[f19])).
% 0.21/0.50  fof(f79,plain,(
% 0.21/0.50    ( ! [X0] : (~r1_tarski(sK2,X0) | sK3 = k5_relat_1(k6_relat_1(X0),sK3) | ~v1_relat_1(sK3)) )),
% 0.21/0.50    inference(superposition,[],[f55,f32])).
% 0.21/0.50  fof(f32,plain,(
% 0.21/0.50    sK2 = k1_relat_1(sK3)),
% 0.21/0.50    inference(cnf_transformation,[],[f19])).
% 0.21/0.50  fof(f55,plain,(
% 0.21/0.50    ( ! [X0,X1] : (~r1_tarski(k1_relat_1(X1),X0) | k5_relat_1(k6_relat_1(X0),X1) = X1 | ~v1_relat_1(X1)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f13])).
% 0.21/0.50  fof(f13,plain,(
% 0.21/0.50    ! [X0,X1] : (k5_relat_1(k6_relat_1(X0),X1) = X1 | ~r1_tarski(k1_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 0.21/0.50    inference(flattening,[],[f12])).
% 0.21/0.50  fof(f12,plain,(
% 0.21/0.50    ! [X0,X1] : ((k5_relat_1(k6_relat_1(X0),X1) = X1 | ~r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.21/0.50    inference(ennf_transformation,[],[f3])).
% 0.21/0.50  fof(f3,axiom,(
% 0.21/0.50    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(k1_relat_1(X1),X0) => k5_relat_1(k6_relat_1(X0),X1) = X1))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t77_relat_1)).
% 0.21/0.50  fof(f164,plain,(
% 0.21/0.50    ( ! [X0] : (sK3 != k5_relat_1(X0,sK3) | k1_relat_1(X0) != sK2 | ~r1_tarski(k2_relat_1(X0),sK2) | ~v1_funct_1(X0) | ~v1_relat_1(X0) | sK4 = X0) )),
% 0.21/0.50    inference(forward_demodulation,[],[f163,f33])).
% 0.21/0.50  fof(f33,plain,(
% 0.21/0.50    sK2 = k1_relat_1(sK4)),
% 0.21/0.50    inference(cnf_transformation,[],[f19])).
% 0.21/0.50  fof(f163,plain,(
% 0.21/0.50    ( ! [X0] : (sK3 != k5_relat_1(X0,sK3) | ~r1_tarski(k2_relat_1(X0),sK2) | k1_relat_1(X0) != k1_relat_1(sK4) | ~v1_funct_1(X0) | ~v1_relat_1(X0) | sK4 = X0) )),
% 0.21/0.50    inference(subsumption_resolution,[],[f162,f34])).
% 0.21/0.50  fof(f34,plain,(
% 0.21/0.50    r1_tarski(k2_relat_1(sK4),sK2)),
% 0.21/0.50    inference(cnf_transformation,[],[f19])).
% 0.21/0.51  fof(f162,plain,(
% 0.21/0.51    ( ! [X0] : (sK3 != k5_relat_1(X0,sK3) | ~r1_tarski(k2_relat_1(X0),sK2) | k1_relat_1(X0) != k1_relat_1(sK4) | ~v1_funct_1(X0) | ~v1_relat_1(X0) | sK4 = X0 | ~r1_tarski(k2_relat_1(sK4),sK2)) )),
% 0.21/0.51    inference(subsumption_resolution,[],[f161,f30])).
% 0.21/0.51  fof(f30,plain,(
% 0.21/0.51    v1_relat_1(sK4)),
% 0.21/0.51    inference(cnf_transformation,[],[f19])).
% 0.21/0.51  fof(f161,plain,(
% 0.21/0.51    ( ! [X0] : (sK3 != k5_relat_1(X0,sK3) | ~r1_tarski(k2_relat_1(X0),sK2) | k1_relat_1(X0) != k1_relat_1(sK4) | ~v1_funct_1(X0) | ~v1_relat_1(X0) | ~v1_relat_1(sK4) | sK4 = X0 | ~r1_tarski(k2_relat_1(sK4),sK2)) )),
% 0.21/0.51    inference(subsumption_resolution,[],[f155,f31])).
% 0.21/0.51  fof(f31,plain,(
% 0.21/0.51    v1_funct_1(sK4)),
% 0.21/0.51    inference(cnf_transformation,[],[f19])).
% 0.21/0.51  fof(f155,plain,(
% 0.21/0.51    ( ! [X0] : (sK3 != k5_relat_1(X0,sK3) | ~r1_tarski(k2_relat_1(X0),sK2) | k1_relat_1(X0) != k1_relat_1(sK4) | ~v1_funct_1(X0) | ~v1_relat_1(X0) | ~v1_funct_1(sK4) | ~v1_relat_1(sK4) | sK4 = X0 | ~r1_tarski(k2_relat_1(sK4),sK2)) )),
% 0.21/0.51    inference(superposition,[],[f140,f36])).
% 0.21/0.51  fof(f36,plain,(
% 0.21/0.51    sK3 = k5_relat_1(sK4,sK3)),
% 0.21/0.51    inference(cnf_transformation,[],[f19])).
% 0.21/0.51  fof(f140,plain,(
% 0.21/0.51    ( ! [X0,X1] : (k5_relat_1(X0,sK3) != k5_relat_1(X1,sK3) | ~r1_tarski(k2_relat_1(X1),sK2) | k1_relat_1(X1) != k1_relat_1(X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0) | X0 = X1 | ~r1_tarski(k2_relat_1(X0),sK2)) )),
% 0.21/0.51    inference(forward_demodulation,[],[f139,f32])).
% 0.21/0.51  fof(f139,plain,(
% 0.21/0.51    ( ! [X0,X1] : (~r1_tarski(k2_relat_1(X1),sK2) | k1_relat_1(X1) != k1_relat_1(X0) | ~r1_tarski(k2_relat_1(X0),k1_relat_1(sK3)) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0) | X0 = X1 | k5_relat_1(X0,sK3) != k5_relat_1(X1,sK3)) )),
% 0.21/0.51    inference(forward_demodulation,[],[f138,f32])).
% 0.21/0.51  fof(f138,plain,(
% 0.21/0.51    ( ! [X0,X1] : (k1_relat_1(X1) != k1_relat_1(X0) | ~r1_tarski(k2_relat_1(X1),k1_relat_1(sK3)) | ~r1_tarski(k2_relat_1(X0),k1_relat_1(sK3)) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0) | X0 = X1 | k5_relat_1(X0,sK3) != k5_relat_1(X1,sK3)) )),
% 0.21/0.51    inference(subsumption_resolution,[],[f137,f29])).
% 0.21/0.51  fof(f29,plain,(
% 0.21/0.51    v1_funct_1(sK3)),
% 0.21/0.51    inference(cnf_transformation,[],[f19])).
% 0.21/0.51  fof(f137,plain,(
% 0.21/0.51    ( ! [X0,X1] : (k1_relat_1(X1) != k1_relat_1(X0) | ~r1_tarski(k2_relat_1(X1),k1_relat_1(sK3)) | ~r1_tarski(k2_relat_1(X0),k1_relat_1(sK3)) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0) | X0 = X1 | k5_relat_1(X0,sK3) != k5_relat_1(X1,sK3) | ~v1_funct_1(sK3)) )),
% 0.21/0.51    inference(subsumption_resolution,[],[f136,f28])).
% 0.21/0.51  % (28324)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 0.21/0.51  fof(f136,plain,(
% 0.21/0.51    ( ! [X0,X1] : (k1_relat_1(X1) != k1_relat_1(X0) | ~r1_tarski(k2_relat_1(X1),k1_relat_1(sK3)) | ~r1_tarski(k2_relat_1(X0),k1_relat_1(sK3)) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0) | X0 = X1 | ~v1_relat_1(sK3) | k5_relat_1(X0,sK3) != k5_relat_1(X1,sK3) | ~v1_funct_1(sK3)) )),
% 0.21/0.51    inference(resolution,[],[f107,f35])).
% 0.21/0.51  fof(f35,plain,(
% 0.21/0.51    v2_funct_1(sK3)),
% 0.21/0.51    inference(cnf_transformation,[],[f19])).
% 0.21/0.51  fof(f107,plain,(
% 0.21/0.51    ( ! [X6,X8,X7] : (~v2_funct_1(X7) | k1_relat_1(X6) != k1_relat_1(X8) | ~r1_tarski(k2_relat_1(X8),k1_relat_1(X7)) | ~r1_tarski(k2_relat_1(X6),k1_relat_1(X7)) | ~v1_funct_1(X8) | ~v1_relat_1(X8) | ~v1_funct_1(X6) | ~v1_relat_1(X6) | X6 = X8 | ~v1_relat_1(X7) | k5_relat_1(X6,X7) != k5_relat_1(X8,X7) | ~v1_funct_1(X7)) )),
% 0.21/0.51    inference(resolution,[],[f44,f61])).
% 0.21/0.51  fof(f61,plain,(
% 0.21/0.51    ( ! [X0] : (sP0(X0) | ~v1_relat_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X0)) )),
% 0.21/0.51    inference(resolution,[],[f54,f42])).
% 0.21/0.51  fof(f42,plain,(
% 0.21/0.51    ( ! [X0] : (~sP1(X0) | ~v2_funct_1(X0) | sP0(X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f20])).
% 0.21/0.51  fof(f20,plain,(
% 0.21/0.51    ! [X0] : (((v2_funct_1(X0) | ~sP0(X0)) & (sP0(X0) | ~v2_funct_1(X0))) | ~sP1(X0))),
% 0.21/0.51    inference(nnf_transformation,[],[f15])).
% 0.21/0.51  fof(f15,plain,(
% 0.21/0.51    ! [X0] : ((v2_funct_1(X0) <=> sP0(X0)) | ~sP1(X0))),
% 0.21/0.51    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 0.21/0.51  fof(f54,plain,(
% 0.21/0.51    ( ! [X0] : (sP1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f16])).
% 0.21/0.51  fof(f16,plain,(
% 0.21/0.51    ! [X0] : (sP1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.21/0.51    inference(definition_folding,[],[f11,f15,f14])).
% 0.21/0.51  fof(f14,plain,(
% 0.21/0.51    ! [X0] : (sP0(X0) <=> ! [X1] : (! [X2] : (X1 = X2 | k5_relat_1(X1,X0) != k5_relat_1(X2,X0) | k1_relat_1(X1) != k1_relat_1(X2) | ~r1_tarski(k2_relat_1(X2),k1_relat_1(X0)) | ~r1_tarski(k2_relat_1(X1),k1_relat_1(X0)) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 0.21/0.51    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 0.21/0.51  fof(f11,plain,(
% 0.21/0.51    ! [X0] : ((v2_funct_1(X0) <=> ! [X1] : (! [X2] : (X1 = X2 | k5_relat_1(X1,X0) != k5_relat_1(X2,X0) | k1_relat_1(X1) != k1_relat_1(X2) | ~r1_tarski(k2_relat_1(X2),k1_relat_1(X0)) | ~r1_tarski(k2_relat_1(X1),k1_relat_1(X0)) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.21/0.51    inference(flattening,[],[f10])).
% 0.21/0.51  fof(f10,plain,(
% 0.21/0.51    ! [X0] : ((v2_funct_1(X0) <=> ! [X1] : (! [X2] : ((X1 = X2 | (k5_relat_1(X1,X0) != k5_relat_1(X2,X0) | k1_relat_1(X1) != k1_relat_1(X2) | ~r1_tarski(k2_relat_1(X2),k1_relat_1(X0)) | ~r1_tarski(k2_relat_1(X1),k1_relat_1(X0)))) | (~v1_funct_1(X2) | ~v1_relat_1(X2))) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.21/0.51    inference(ennf_transformation,[],[f5])).
% 0.21/0.51  fof(f5,axiom,(
% 0.21/0.51    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) <=> ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ! [X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ((k5_relat_1(X1,X0) = k5_relat_1(X2,X0) & k1_relat_1(X1) = k1_relat_1(X2) & r1_tarski(k2_relat_1(X2),k1_relat_1(X0)) & r1_tarski(k2_relat_1(X1),k1_relat_1(X0))) => X1 = X2)))))),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_funct_1)).
% 0.21/0.51  fof(f44,plain,(
% 0.21/0.51    ( ! [X4,X0,X3] : (~sP0(X0) | k5_relat_1(X3,X0) != k5_relat_1(X4,X0) | k1_relat_1(X3) != k1_relat_1(X4) | ~r1_tarski(k2_relat_1(X4),k1_relat_1(X0)) | ~r1_tarski(k2_relat_1(X3),k1_relat_1(X0)) | ~v1_funct_1(X4) | ~v1_relat_1(X4) | ~v1_funct_1(X3) | ~v1_relat_1(X3) | X3 = X4) )),
% 0.21/0.51    inference(cnf_transformation,[],[f25])).
% 0.21/0.51  fof(f25,plain,(
% 0.21/0.51    ! [X0] : ((sP0(X0) | ((sK5(X0) != sK6(X0) & k5_relat_1(sK5(X0),X0) = k5_relat_1(sK6(X0),X0) & k1_relat_1(sK5(X0)) = k1_relat_1(sK6(X0)) & r1_tarski(k2_relat_1(sK6(X0)),k1_relat_1(X0)) & r1_tarski(k2_relat_1(sK5(X0)),k1_relat_1(X0)) & v1_funct_1(sK6(X0)) & v1_relat_1(sK6(X0))) & v1_funct_1(sK5(X0)) & v1_relat_1(sK5(X0)))) & (! [X3] : (! [X4] : (X3 = X4 | k5_relat_1(X3,X0) != k5_relat_1(X4,X0) | k1_relat_1(X3) != k1_relat_1(X4) | ~r1_tarski(k2_relat_1(X4),k1_relat_1(X0)) | ~r1_tarski(k2_relat_1(X3),k1_relat_1(X0)) | ~v1_funct_1(X4) | ~v1_relat_1(X4)) | ~v1_funct_1(X3) | ~v1_relat_1(X3)) | ~sP0(X0)))),
% 0.21/0.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6])],[f22,f24,f23])).
% 0.21/0.51  fof(f23,plain,(
% 0.21/0.51    ! [X0] : (? [X1] : (? [X2] : (X1 != X2 & k5_relat_1(X1,X0) = k5_relat_1(X2,X0) & k1_relat_1(X1) = k1_relat_1(X2) & r1_tarski(k2_relat_1(X2),k1_relat_1(X0)) & r1_tarski(k2_relat_1(X1),k1_relat_1(X0)) & v1_funct_1(X2) & v1_relat_1(X2)) & v1_funct_1(X1) & v1_relat_1(X1)) => (? [X2] : (sK5(X0) != X2 & k5_relat_1(X2,X0) = k5_relat_1(sK5(X0),X0) & k1_relat_1(X2) = k1_relat_1(sK5(X0)) & r1_tarski(k2_relat_1(X2),k1_relat_1(X0)) & r1_tarski(k2_relat_1(sK5(X0)),k1_relat_1(X0)) & v1_funct_1(X2) & v1_relat_1(X2)) & v1_funct_1(sK5(X0)) & v1_relat_1(sK5(X0))))),
% 0.21/0.51    introduced(choice_axiom,[])).
% 0.21/0.51  fof(f24,plain,(
% 0.21/0.51    ! [X0] : (? [X2] : (sK5(X0) != X2 & k5_relat_1(X2,X0) = k5_relat_1(sK5(X0),X0) & k1_relat_1(X2) = k1_relat_1(sK5(X0)) & r1_tarski(k2_relat_1(X2),k1_relat_1(X0)) & r1_tarski(k2_relat_1(sK5(X0)),k1_relat_1(X0)) & v1_funct_1(X2) & v1_relat_1(X2)) => (sK5(X0) != sK6(X0) & k5_relat_1(sK5(X0),X0) = k5_relat_1(sK6(X0),X0) & k1_relat_1(sK5(X0)) = k1_relat_1(sK6(X0)) & r1_tarski(k2_relat_1(sK6(X0)),k1_relat_1(X0)) & r1_tarski(k2_relat_1(sK5(X0)),k1_relat_1(X0)) & v1_funct_1(sK6(X0)) & v1_relat_1(sK6(X0))))),
% 0.21/0.51    introduced(choice_axiom,[])).
% 0.21/0.51  fof(f22,plain,(
% 0.21/0.51    ! [X0] : ((sP0(X0) | ? [X1] : (? [X2] : (X1 != X2 & k5_relat_1(X1,X0) = k5_relat_1(X2,X0) & k1_relat_1(X1) = k1_relat_1(X2) & r1_tarski(k2_relat_1(X2),k1_relat_1(X0)) & r1_tarski(k2_relat_1(X1),k1_relat_1(X0)) & v1_funct_1(X2) & v1_relat_1(X2)) & v1_funct_1(X1) & v1_relat_1(X1))) & (! [X3] : (! [X4] : (X3 = X4 | k5_relat_1(X3,X0) != k5_relat_1(X4,X0) | k1_relat_1(X3) != k1_relat_1(X4) | ~r1_tarski(k2_relat_1(X4),k1_relat_1(X0)) | ~r1_tarski(k2_relat_1(X3),k1_relat_1(X0)) | ~v1_funct_1(X4) | ~v1_relat_1(X4)) | ~v1_funct_1(X3) | ~v1_relat_1(X3)) | ~sP0(X0)))),
% 0.21/0.51    inference(rectify,[],[f21])).
% 0.21/0.51  fof(f21,plain,(
% 0.21/0.51    ! [X0] : ((sP0(X0) | ? [X1] : (? [X2] : (X1 != X2 & k5_relat_1(X1,X0) = k5_relat_1(X2,X0) & k1_relat_1(X1) = k1_relat_1(X2) & r1_tarski(k2_relat_1(X2),k1_relat_1(X0)) & r1_tarski(k2_relat_1(X1),k1_relat_1(X0)) & v1_funct_1(X2) & v1_relat_1(X2)) & v1_funct_1(X1) & v1_relat_1(X1))) & (! [X1] : (! [X2] : (X1 = X2 | k5_relat_1(X1,X0) != k5_relat_1(X2,X0) | k1_relat_1(X1) != k1_relat_1(X2) | ~r1_tarski(k2_relat_1(X2),k1_relat_1(X0)) | ~r1_tarski(k2_relat_1(X1),k1_relat_1(X0)) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~sP0(X0)))),
% 0.21/0.51    inference(nnf_transformation,[],[f14])).
% 0.21/0.51  % SZS output end Proof for theBenchmark
% 0.21/0.51  % (28317)------------------------------
% 0.21/0.51  % (28317)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (28317)Termination reason: Refutation
% 0.21/0.51  
% 0.21/0.51  % (28317)Memory used [KB]: 6396
% 0.21/0.51  % (28317)Time elapsed: 0.090 s
% 0.21/0.51  % (28317)------------------------------
% 0.21/0.51  % (28317)------------------------------
% 0.21/0.51  % (28319)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.21/0.51  % (28315)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.51  % (28311)Success in time 0.153 s
%------------------------------------------------------------------------------
