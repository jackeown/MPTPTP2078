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
% DateTime   : Thu Dec  3 12:56:07 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   73 ( 521 expanded)
%              Number of leaves         :    9 ( 193 expanded)
%              Depth                    :   12
%              Number of atoms          :  310 (3733 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    1 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f89,plain,(
    $false ),
    inference(global_subsumption,[],[f64,f84,f85,f86,f87,f88])).

fof(f88,plain,(
    v1_relat_2(sK4) ),
    inference(resolution,[],[f83,f65])).

fof(f65,plain,(
    ! [X0] :
      ( ~ sP2(X0,sK3)
      | v1_relat_2(X0) ) ),
    inference(resolution,[],[f59,f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_2(X1)
      | v1_relat_2(X0)
      | ~ sP2(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( ( v1_wellord1(X0)
          | ~ v1_wellord1(X1) )
        & ( v4_relat_2(X0)
          | ~ v4_relat_2(X1) )
        & ( v6_relat_2(X0)
          | ~ v6_relat_2(X1) )
        & ( v8_relat_2(X0)
          | ~ v8_relat_2(X1) )
        & ( v1_relat_2(X0)
          | ~ v1_relat_2(X1) ) )
      | ~ sP2(X0,X1) ) ),
    inference(rectify,[],[f22])).

fof(f22,plain,(
    ! [X1,X0] :
      ( ( ( v1_wellord1(X1)
          | ~ v1_wellord1(X0) )
        & ( v4_relat_2(X1)
          | ~ v4_relat_2(X0) )
        & ( v6_relat_2(X1)
          | ~ v6_relat_2(X0) )
        & ( v8_relat_2(X1)
          | ~ v8_relat_2(X0) )
        & ( v1_relat_2(X1)
          | ~ v1_relat_2(X0) ) )
      | ~ sP2(X1,X0) ) ),
    inference(nnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X1,X0] :
      ( ( ( v1_wellord1(X1)
          | ~ v1_wellord1(X0) )
        & ( v4_relat_2(X1)
          | ~ v4_relat_2(X0) )
        & ( v6_relat_2(X1)
          | ~ v6_relat_2(X0) )
        & ( v8_relat_2(X1)
          | ~ v8_relat_2(X0) )
        & ( v1_relat_2(X1)
          | ~ v1_relat_2(X0) ) )
      | ~ sP2(X1,X0) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).

fof(f59,plain,(
    v1_relat_2(sK3) ),
    inference(resolution,[],[f53,f33])).

fof(f33,plain,(
    ! [X0] :
      ( ~ sP0(X0)
      | v1_relat_2(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
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
    inference(flattening,[],[f20])).

fof(f20,plain,(
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
    inference(nnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0] :
      ( sP0(X0)
    <=> ( v1_wellord1(X0)
        & v6_relat_2(X0)
        & v4_relat_2(X0)
        & v8_relat_2(X0)
        & v1_relat_2(X0) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f53,plain,(
    sP0(sK3) ),
    inference(subsumption_resolution,[],[f51,f28])).

fof(f28,plain,(
    v2_wellord1(sK3) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,
    ( ~ v2_wellord1(sK4)
    & r3_wellord1(sK3,sK4,sK5)
    & v2_wellord1(sK3)
    & v1_funct_1(sK5)
    & v1_relat_1(sK5)
    & v1_relat_1(sK4)
    & v1_relat_1(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5])],[f6,f17,f16,f15])).

fof(f15,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ~ v2_wellord1(X1)
                & r3_wellord1(X0,X1,X2)
                & v2_wellord1(X0)
                & v1_funct_1(X2)
                & v1_relat_1(X2) )
            & v1_relat_1(X1) )
        & v1_relat_1(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ~ v2_wellord1(X1)
              & r3_wellord1(sK3,X1,X2)
              & v2_wellord1(sK3)
              & v1_funct_1(X2)
              & v1_relat_1(X2) )
          & v1_relat_1(X1) )
      & v1_relat_1(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ~ v2_wellord1(X1)
            & r3_wellord1(sK3,X1,X2)
            & v2_wellord1(sK3)
            & v1_funct_1(X2)
            & v1_relat_1(X2) )
        & v1_relat_1(X1) )
   => ( ? [X2] :
          ( ~ v2_wellord1(sK4)
          & r3_wellord1(sK3,sK4,X2)
          & v2_wellord1(sK3)
          & v1_funct_1(X2)
          & v1_relat_1(X2) )
      & v1_relat_1(sK4) ) ),
    introduced(choice_axiom,[])).

fof(f17,plain,
    ( ? [X2] :
        ( ~ v2_wellord1(sK4)
        & r3_wellord1(sK3,sK4,X2)
        & v2_wellord1(sK3)
        & v1_funct_1(X2)
        & v1_relat_1(X2) )
   => ( ~ v2_wellord1(sK4)
      & r3_wellord1(sK3,sK4,sK5)
      & v2_wellord1(sK3)
      & v1_funct_1(sK5)
      & v1_relat_1(sK5) ) ),
    introduced(choice_axiom,[])).

fof(f6,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ v2_wellord1(X1)
              & r3_wellord1(X0,X1,X2)
              & v2_wellord1(X0)
              & v1_funct_1(X2)
              & v1_relat_1(X2) )
          & v1_relat_1(X1) )
      & v1_relat_1(X0) ) ),
    inference(flattening,[],[f5])).

fof(f5,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ v2_wellord1(X1)
              & r3_wellord1(X0,X1,X2)
              & v2_wellord1(X0)
              & v1_funct_1(X2)
              & v1_relat_1(X2) )
          & v1_relat_1(X1) )
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,negated_conjecture,(
    ~ ! [X0] :
        ( v1_relat_1(X0)
       => ! [X1] :
            ( v1_relat_1(X1)
           => ! [X2] :
                ( ( v1_funct_1(X2)
                  & v1_relat_1(X2) )
               => ( ( r3_wellord1(X0,X1,X2)
                    & v2_wellord1(X0) )
                 => v2_wellord1(X1) ) ) ) ) ),
    inference(negated_conjecture,[],[f3])).

fof(f3,conjecture,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ! [X2] :
              ( ( v1_funct_1(X2)
                & v1_relat_1(X2) )
             => ( ( r3_wellord1(X0,X1,X2)
                  & v2_wellord1(X0) )
               => v2_wellord1(X1) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t54_wellord1)).

fof(f51,plain,
    ( ~ v2_wellord1(sK3)
    | sP0(sK3) ),
    inference(resolution,[],[f46,f31])).

fof(f31,plain,(
    ! [X0] :
      ( ~ sP1(X0)
      | ~ v2_wellord1(X0)
      | sP0(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ( ( v2_wellord1(X0)
          | ~ sP0(X0) )
        & ( sP0(X0)
          | ~ v2_wellord1(X0) ) )
      | ~ sP1(X0) ) ),
    inference(nnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0] :
      ( ( v2_wellord1(X0)
      <=> sP0(X0) )
      | ~ sP1(X0) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f46,plain,(
    sP1(sK3) ),
    inference(resolution,[],[f24,f39])).

fof(f39,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | sP1(X0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( sP1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(definition_folding,[],[f7,f11,f10])).

fof(f7,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_wellord1)).

fof(f24,plain,(
    v1_relat_1(sK3) ),
    inference(cnf_transformation,[],[f18])).

fof(f83,plain,(
    sP2(sK4,sK3) ),
    inference(subsumption_resolution,[],[f82,f24])).

fof(f82,plain,
    ( sP2(sK4,sK3)
    | ~ v1_relat_1(sK3) ),
    inference(subsumption_resolution,[],[f81,f25])).

fof(f25,plain,(
    v1_relat_1(sK4) ),
    inference(cnf_transformation,[],[f18])).

fof(f81,plain,
    ( sP2(sK4,sK3)
    | ~ v1_relat_1(sK4)
    | ~ v1_relat_1(sK3) ),
    inference(resolution,[],[f50,f29])).

fof(f29,plain,(
    r3_wellord1(sK3,sK4,sK5) ),
    inference(cnf_transformation,[],[f18])).

fof(f50,plain,(
    ! [X0,X1] :
      ( ~ r3_wellord1(X0,X1,sK5)
      | sP2(X1,X0)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(subsumption_resolution,[],[f49,f26])).

fof(f26,plain,(
    v1_relat_1(sK5) ),
    inference(cnf_transformation,[],[f18])).

fof(f49,plain,(
    ! [X0,X1] :
      ( ~ r3_wellord1(X0,X1,sK5)
      | sP2(X1,X0)
      | ~ v1_relat_1(sK5)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(resolution,[],[f27,f45])).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_1(X2)
      | ~ r3_wellord1(X0,X1,X2)
      | sP2(X1,X0)
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( sP2(X1,X0)
              | ~ r3_wellord1(X0,X1,X2)
              | ~ v1_funct_1(X2)
              | ~ v1_relat_1(X2) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(definition_folding,[],[f9,f13])).

fof(f9,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( v1_wellord1(X1)
                  | ~ v1_wellord1(X0) )
                & ( v4_relat_2(X1)
                  | ~ v4_relat_2(X0) )
                & ( v6_relat_2(X1)
                  | ~ v6_relat_2(X0) )
                & ( v8_relat_2(X1)
                  | ~ v8_relat_2(X0) )
                & ( v1_relat_2(X1)
                  | ~ v1_relat_2(X0) ) )
              | ~ r3_wellord1(X0,X1,X2)
              | ~ v1_funct_1(X2)
              | ~ v1_relat_1(X2) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f8])).

fof(f8,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( v1_wellord1(X1)
                  | ~ v1_wellord1(X0) )
                & ( v4_relat_2(X1)
                  | ~ v4_relat_2(X0) )
                & ( v6_relat_2(X1)
                  | ~ v6_relat_2(X0) )
                & ( v8_relat_2(X1)
                  | ~ v8_relat_2(X0) )
                & ( v1_relat_2(X1)
                  | ~ v1_relat_2(X0) ) )
              | ~ r3_wellord1(X0,X1,X2)
              | ~ v1_funct_1(X2)
              | ~ v1_relat_1(X2) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ! [X2] :
              ( ( v1_funct_1(X2)
                & v1_relat_1(X2) )
             => ( r3_wellord1(X0,X1,X2)
               => ( ( v1_wellord1(X0)
                   => v1_wellord1(X1) )
                  & ( v4_relat_2(X0)
                   => v4_relat_2(X1) )
                  & ( v6_relat_2(X0)
                   => v6_relat_2(X1) )
                  & ( v8_relat_2(X0)
                   => v8_relat_2(X1) )
                  & ( v1_relat_2(X0)
                   => v1_relat_2(X1) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t53_wellord1)).

fof(f27,plain,(
    v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f18])).

fof(f87,plain,(
    v8_relat_2(sK4) ),
    inference(resolution,[],[f83,f66])).

fof(f66,plain,(
    ! [X0] :
      ( ~ sP2(X0,sK3)
      | v8_relat_2(X0) ) ),
    inference(resolution,[],[f60,f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ~ v8_relat_2(X1)
      | v8_relat_2(X0)
      | ~ sP2(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f60,plain,(
    v8_relat_2(sK3) ),
    inference(resolution,[],[f53,f34])).

fof(f34,plain,(
    ! [X0] :
      ( ~ sP0(X0)
      | v8_relat_2(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f86,plain,(
    v4_relat_2(sK4) ),
    inference(resolution,[],[f83,f67])).

fof(f67,plain,(
    ! [X0] :
      ( ~ sP2(X0,sK3)
      | v4_relat_2(X0) ) ),
    inference(resolution,[],[f61,f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ~ v4_relat_2(X1)
      | v4_relat_2(X0)
      | ~ sP2(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f61,plain,(
    v4_relat_2(sK3) ),
    inference(resolution,[],[f53,f35])).

fof(f35,plain,(
    ! [X0] :
      ( ~ sP0(X0)
      | v4_relat_2(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f85,plain,(
    v6_relat_2(sK4) ),
    inference(resolution,[],[f83,f68])).

fof(f68,plain,(
    ! [X0] :
      ( ~ sP2(X0,sK3)
      | v6_relat_2(X0) ) ),
    inference(resolution,[],[f62,f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ~ v6_relat_2(X1)
      | v6_relat_2(X0)
      | ~ sP2(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f62,plain,(
    v6_relat_2(sK3) ),
    inference(resolution,[],[f53,f36])).

fof(f36,plain,(
    ! [X0] :
      ( ~ sP0(X0)
      | v6_relat_2(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f84,plain,(
    v1_wellord1(sK4) ),
    inference(resolution,[],[f83,f69])).

fof(f69,plain,(
    ! [X0] :
      ( ~ sP2(X0,sK3)
      | v1_wellord1(X0) ) ),
    inference(resolution,[],[f63,f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ~ v1_wellord1(X1)
      | v1_wellord1(X0)
      | ~ sP2(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f63,plain,(
    v1_wellord1(sK3) ),
    inference(resolution,[],[f53,f37])).

fof(f37,plain,(
    ! [X0] :
      ( ~ sP0(X0)
      | v1_wellord1(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f64,plain,
    ( ~ v1_wellord1(sK4)
    | ~ v6_relat_2(sK4)
    | ~ v4_relat_2(sK4)
    | ~ v8_relat_2(sK4)
    | ~ v1_relat_2(sK4) ),
    inference(resolution,[],[f56,f38])).

fof(f38,plain,(
    ! [X0] :
      ( sP0(X0)
      | ~ v1_wellord1(X0)
      | ~ v6_relat_2(X0)
      | ~ v4_relat_2(X0)
      | ~ v8_relat_2(X0)
      | ~ v1_relat_2(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f56,plain,(
    ~ sP0(sK4) ),
    inference(subsumption_resolution,[],[f55,f30])).

fof(f30,plain,(
    ~ v2_wellord1(sK4) ),
    inference(cnf_transformation,[],[f18])).

fof(f55,plain,
    ( ~ sP0(sK4)
    | v2_wellord1(sK4) ),
    inference(resolution,[],[f47,f32])).

fof(f32,plain,(
    ! [X0] :
      ( ~ sP1(X0)
      | ~ sP0(X0)
      | v2_wellord1(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f47,plain,(
    sP1(sK4) ),
    inference(resolution,[],[f25,f39])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 09:36:22 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.45  % (31434)lrs+1003_2:3_afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=on:fde=unused:gs=on:inw=on:nm=0:newcnf=on:nwc=1:sas=z3:stl=30:sac=on:sp=occurrence:tha=off:updr=off:uhcvi=on_2 on theBenchmark
% 0.21/0.49  % (31443)ott+11_5:1_afp=100000:afq=1.1:br=off:gs=on:nm=64:nwc=1:sos=all:urr=on:updr=off_287 on theBenchmark
% 0.21/0.49  % (31439)dis+11_40_afr=on:afp=40000:afq=1.2:amm=sco:anc=none:br=off:fsr=off:gs=on:nm=64:nwc=1:sas=z3:sos=all:sp=reverse_arity:thf=on:urr=on:updr=off_2 on theBenchmark
% 0.21/0.49  % (31435)dis+11_24_afp=40000:afq=1.1:amm=sco:anc=none:bs=on:gs=on:gsem=off:lcm=predicate:lma=on:nm=2:nwc=1:sos=on:sac=on:updr=off_91 on theBenchmark
% 0.21/0.49  % (31446)dis+1_14_awrs=converge:awrsf=256:av=off:bs=on:bsr=on:bce=on:cond=fast:gsp=input_only:gs=on:lcm=predicate:lma=on:nm=4:nwc=1.7:sp=weighted_frequency:urr=on_33 on theBenchmark
% 0.21/0.49  % (31435)Refutation found. Thanks to Tanya!
% 0.21/0.49  % SZS status Theorem for theBenchmark
% 0.21/0.49  % SZS output start Proof for theBenchmark
% 0.21/0.49  fof(f89,plain,(
% 0.21/0.49    $false),
% 0.21/0.49    inference(global_subsumption,[],[f64,f84,f85,f86,f87,f88])).
% 0.21/0.49  fof(f88,plain,(
% 0.21/0.49    v1_relat_2(sK4)),
% 0.21/0.49    inference(resolution,[],[f83,f65])).
% 0.21/0.49  fof(f65,plain,(
% 0.21/0.49    ( ! [X0] : (~sP2(X0,sK3) | v1_relat_2(X0)) )),
% 0.21/0.49    inference(resolution,[],[f59,f40])).
% 0.21/0.49  fof(f40,plain,(
% 0.21/0.49    ( ! [X0,X1] : (~v1_relat_2(X1) | v1_relat_2(X0) | ~sP2(X0,X1)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f23])).
% 0.21/0.49  fof(f23,plain,(
% 0.21/0.49    ! [X0,X1] : (((v1_wellord1(X0) | ~v1_wellord1(X1)) & (v4_relat_2(X0) | ~v4_relat_2(X1)) & (v6_relat_2(X0) | ~v6_relat_2(X1)) & (v8_relat_2(X0) | ~v8_relat_2(X1)) & (v1_relat_2(X0) | ~v1_relat_2(X1))) | ~sP2(X0,X1))),
% 0.21/0.49    inference(rectify,[],[f22])).
% 0.21/0.49  fof(f22,plain,(
% 0.21/0.49    ! [X1,X0] : (((v1_wellord1(X1) | ~v1_wellord1(X0)) & (v4_relat_2(X1) | ~v4_relat_2(X0)) & (v6_relat_2(X1) | ~v6_relat_2(X0)) & (v8_relat_2(X1) | ~v8_relat_2(X0)) & (v1_relat_2(X1) | ~v1_relat_2(X0))) | ~sP2(X1,X0))),
% 0.21/0.49    inference(nnf_transformation,[],[f13])).
% 0.21/0.49  fof(f13,plain,(
% 0.21/0.49    ! [X1,X0] : (((v1_wellord1(X1) | ~v1_wellord1(X0)) & (v4_relat_2(X1) | ~v4_relat_2(X0)) & (v6_relat_2(X1) | ~v6_relat_2(X0)) & (v8_relat_2(X1) | ~v8_relat_2(X0)) & (v1_relat_2(X1) | ~v1_relat_2(X0))) | ~sP2(X1,X0))),
% 0.21/0.49    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).
% 0.21/0.49  fof(f59,plain,(
% 0.21/0.49    v1_relat_2(sK3)),
% 0.21/0.49    inference(resolution,[],[f53,f33])).
% 0.21/0.49  fof(f33,plain,(
% 0.21/0.49    ( ! [X0] : (~sP0(X0) | v1_relat_2(X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f21])).
% 0.21/0.49  fof(f21,plain,(
% 0.21/0.49    ! [X0] : ((sP0(X0) | ~v1_wellord1(X0) | ~v6_relat_2(X0) | ~v4_relat_2(X0) | ~v8_relat_2(X0) | ~v1_relat_2(X0)) & ((v1_wellord1(X0) & v6_relat_2(X0) & v4_relat_2(X0) & v8_relat_2(X0) & v1_relat_2(X0)) | ~sP0(X0)))),
% 0.21/0.49    inference(flattening,[],[f20])).
% 0.21/0.49  fof(f20,plain,(
% 0.21/0.49    ! [X0] : ((sP0(X0) | (~v1_wellord1(X0) | ~v6_relat_2(X0) | ~v4_relat_2(X0) | ~v8_relat_2(X0) | ~v1_relat_2(X0))) & ((v1_wellord1(X0) & v6_relat_2(X0) & v4_relat_2(X0) & v8_relat_2(X0) & v1_relat_2(X0)) | ~sP0(X0)))),
% 0.21/0.49    inference(nnf_transformation,[],[f10])).
% 0.21/0.49  fof(f10,plain,(
% 0.21/0.49    ! [X0] : (sP0(X0) <=> (v1_wellord1(X0) & v6_relat_2(X0) & v4_relat_2(X0) & v8_relat_2(X0) & v1_relat_2(X0)))),
% 0.21/0.49    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 0.21/0.49  fof(f53,plain,(
% 0.21/0.49    sP0(sK3)),
% 0.21/0.49    inference(subsumption_resolution,[],[f51,f28])).
% 0.21/0.49  fof(f28,plain,(
% 0.21/0.49    v2_wellord1(sK3)),
% 0.21/0.49    inference(cnf_transformation,[],[f18])).
% 0.21/0.49  fof(f18,plain,(
% 0.21/0.49    ((~v2_wellord1(sK4) & r3_wellord1(sK3,sK4,sK5) & v2_wellord1(sK3) & v1_funct_1(sK5) & v1_relat_1(sK5)) & v1_relat_1(sK4)) & v1_relat_1(sK3)),
% 0.21/0.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5])],[f6,f17,f16,f15])).
% 0.21/0.49  fof(f15,plain,(
% 0.21/0.49    ? [X0] : (? [X1] : (? [X2] : (~v2_wellord1(X1) & r3_wellord1(X0,X1,X2) & v2_wellord1(X0) & v1_funct_1(X2) & v1_relat_1(X2)) & v1_relat_1(X1)) & v1_relat_1(X0)) => (? [X1] : (? [X2] : (~v2_wellord1(X1) & r3_wellord1(sK3,X1,X2) & v2_wellord1(sK3) & v1_funct_1(X2) & v1_relat_1(X2)) & v1_relat_1(X1)) & v1_relat_1(sK3))),
% 0.21/0.49    introduced(choice_axiom,[])).
% 0.21/0.49  fof(f16,plain,(
% 0.21/0.49    ? [X1] : (? [X2] : (~v2_wellord1(X1) & r3_wellord1(sK3,X1,X2) & v2_wellord1(sK3) & v1_funct_1(X2) & v1_relat_1(X2)) & v1_relat_1(X1)) => (? [X2] : (~v2_wellord1(sK4) & r3_wellord1(sK3,sK4,X2) & v2_wellord1(sK3) & v1_funct_1(X2) & v1_relat_1(X2)) & v1_relat_1(sK4))),
% 0.21/0.49    introduced(choice_axiom,[])).
% 0.21/0.49  fof(f17,plain,(
% 0.21/0.49    ? [X2] : (~v2_wellord1(sK4) & r3_wellord1(sK3,sK4,X2) & v2_wellord1(sK3) & v1_funct_1(X2) & v1_relat_1(X2)) => (~v2_wellord1(sK4) & r3_wellord1(sK3,sK4,sK5) & v2_wellord1(sK3) & v1_funct_1(sK5) & v1_relat_1(sK5))),
% 0.21/0.49    introduced(choice_axiom,[])).
% 0.21/0.49  fof(f6,plain,(
% 0.21/0.49    ? [X0] : (? [X1] : (? [X2] : (~v2_wellord1(X1) & r3_wellord1(X0,X1,X2) & v2_wellord1(X0) & v1_funct_1(X2) & v1_relat_1(X2)) & v1_relat_1(X1)) & v1_relat_1(X0))),
% 0.21/0.49    inference(flattening,[],[f5])).
% 0.21/0.49  fof(f5,plain,(
% 0.21/0.49    ? [X0] : (? [X1] : (? [X2] : ((~v2_wellord1(X1) & (r3_wellord1(X0,X1,X2) & v2_wellord1(X0))) & (v1_funct_1(X2) & v1_relat_1(X2))) & v1_relat_1(X1)) & v1_relat_1(X0))),
% 0.21/0.49    inference(ennf_transformation,[],[f4])).
% 0.21/0.49  fof(f4,negated_conjecture,(
% 0.21/0.49    ~! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => ! [X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ((r3_wellord1(X0,X1,X2) & v2_wellord1(X0)) => v2_wellord1(X1)))))),
% 0.21/0.49    inference(negated_conjecture,[],[f3])).
% 0.21/0.49  fof(f3,conjecture,(
% 0.21/0.49    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => ! [X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ((r3_wellord1(X0,X1,X2) & v2_wellord1(X0)) => v2_wellord1(X1)))))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t54_wellord1)).
% 0.21/0.49  fof(f51,plain,(
% 0.21/0.49    ~v2_wellord1(sK3) | sP0(sK3)),
% 0.21/0.49    inference(resolution,[],[f46,f31])).
% 0.21/0.49  fof(f31,plain,(
% 0.21/0.49    ( ! [X0] : (~sP1(X0) | ~v2_wellord1(X0) | sP0(X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f19])).
% 0.21/0.49  fof(f19,plain,(
% 0.21/0.49    ! [X0] : (((v2_wellord1(X0) | ~sP0(X0)) & (sP0(X0) | ~v2_wellord1(X0))) | ~sP1(X0))),
% 0.21/0.49    inference(nnf_transformation,[],[f11])).
% 0.21/0.49  fof(f11,plain,(
% 0.21/0.49    ! [X0] : ((v2_wellord1(X0) <=> sP0(X0)) | ~sP1(X0))),
% 0.21/0.49    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 0.21/0.49  fof(f46,plain,(
% 0.21/0.49    sP1(sK3)),
% 0.21/0.49    inference(resolution,[],[f24,f39])).
% 0.21/0.49  fof(f39,plain,(
% 0.21/0.49    ( ! [X0] : (~v1_relat_1(X0) | sP1(X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f12])).
% 0.21/0.49  fof(f12,plain,(
% 0.21/0.49    ! [X0] : (sP1(X0) | ~v1_relat_1(X0))),
% 0.21/0.49    inference(definition_folding,[],[f7,f11,f10])).
% 0.21/0.49  fof(f7,plain,(
% 0.21/0.49    ! [X0] : ((v2_wellord1(X0) <=> (v1_wellord1(X0) & v6_relat_2(X0) & v4_relat_2(X0) & v8_relat_2(X0) & v1_relat_2(X0))) | ~v1_relat_1(X0))),
% 0.21/0.49    inference(ennf_transformation,[],[f1])).
% 0.21/0.49  fof(f1,axiom,(
% 0.21/0.49    ! [X0] : (v1_relat_1(X0) => (v2_wellord1(X0) <=> (v1_wellord1(X0) & v6_relat_2(X0) & v4_relat_2(X0) & v8_relat_2(X0) & v1_relat_2(X0))))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_wellord1)).
% 0.21/0.49  fof(f24,plain,(
% 0.21/0.49    v1_relat_1(sK3)),
% 0.21/0.49    inference(cnf_transformation,[],[f18])).
% 0.21/0.49  fof(f83,plain,(
% 0.21/0.49    sP2(sK4,sK3)),
% 0.21/0.49    inference(subsumption_resolution,[],[f82,f24])).
% 0.21/0.49  fof(f82,plain,(
% 0.21/0.49    sP2(sK4,sK3) | ~v1_relat_1(sK3)),
% 0.21/0.49    inference(subsumption_resolution,[],[f81,f25])).
% 0.21/0.49  fof(f25,plain,(
% 0.21/0.49    v1_relat_1(sK4)),
% 0.21/0.49    inference(cnf_transformation,[],[f18])).
% 0.21/0.49  fof(f81,plain,(
% 0.21/0.49    sP2(sK4,sK3) | ~v1_relat_1(sK4) | ~v1_relat_1(sK3)),
% 0.21/0.49    inference(resolution,[],[f50,f29])).
% 0.21/0.49  fof(f29,plain,(
% 0.21/0.49    r3_wellord1(sK3,sK4,sK5)),
% 0.21/0.49    inference(cnf_transformation,[],[f18])).
% 0.21/0.49  fof(f50,plain,(
% 0.21/0.49    ( ! [X0,X1] : (~r3_wellord1(X0,X1,sK5) | sP2(X1,X0) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 0.21/0.49    inference(subsumption_resolution,[],[f49,f26])).
% 0.21/0.49  fof(f26,plain,(
% 0.21/0.49    v1_relat_1(sK5)),
% 0.21/0.49    inference(cnf_transformation,[],[f18])).
% 0.21/0.49  fof(f49,plain,(
% 0.21/0.49    ( ! [X0,X1] : (~r3_wellord1(X0,X1,sK5) | sP2(X1,X0) | ~v1_relat_1(sK5) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 0.21/0.49    inference(resolution,[],[f27,f45])).
% 0.21/0.49  fof(f45,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (~v1_funct_1(X2) | ~r3_wellord1(X0,X1,X2) | sP2(X1,X0) | ~v1_relat_1(X2) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f14])).
% 0.21/0.49  fof(f14,plain,(
% 0.21/0.49    ! [X0] : (! [X1] : (! [X2] : (sP2(X1,X0) | ~r3_wellord1(X0,X1,X2) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.21/0.49    inference(definition_folding,[],[f9,f13])).
% 0.21/0.49  fof(f9,plain,(
% 0.21/0.49    ! [X0] : (! [X1] : (! [X2] : (((v1_wellord1(X1) | ~v1_wellord1(X0)) & (v4_relat_2(X1) | ~v4_relat_2(X0)) & (v6_relat_2(X1) | ~v6_relat_2(X0)) & (v8_relat_2(X1) | ~v8_relat_2(X0)) & (v1_relat_2(X1) | ~v1_relat_2(X0))) | ~r3_wellord1(X0,X1,X2) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.21/0.49    inference(flattening,[],[f8])).
% 0.21/0.49  fof(f8,plain,(
% 0.21/0.49    ! [X0] : (! [X1] : (! [X2] : ((((v1_wellord1(X1) | ~v1_wellord1(X0)) & (v4_relat_2(X1) | ~v4_relat_2(X0)) & (v6_relat_2(X1) | ~v6_relat_2(X0)) & (v8_relat_2(X1) | ~v8_relat_2(X0)) & (v1_relat_2(X1) | ~v1_relat_2(X0))) | ~r3_wellord1(X0,X1,X2)) | (~v1_funct_1(X2) | ~v1_relat_1(X2))) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.21/0.49    inference(ennf_transformation,[],[f2])).
% 0.21/0.49  fof(f2,axiom,(
% 0.21/0.49    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => ! [X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (r3_wellord1(X0,X1,X2) => ((v1_wellord1(X0) => v1_wellord1(X1)) & (v4_relat_2(X0) => v4_relat_2(X1)) & (v6_relat_2(X0) => v6_relat_2(X1)) & (v8_relat_2(X0) => v8_relat_2(X1)) & (v1_relat_2(X0) => v1_relat_2(X1)))))))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t53_wellord1)).
% 0.21/0.49  fof(f27,plain,(
% 0.21/0.49    v1_funct_1(sK5)),
% 0.21/0.49    inference(cnf_transformation,[],[f18])).
% 0.21/0.49  fof(f87,plain,(
% 0.21/0.49    v8_relat_2(sK4)),
% 0.21/0.49    inference(resolution,[],[f83,f66])).
% 0.21/0.49  fof(f66,plain,(
% 0.21/0.49    ( ! [X0] : (~sP2(X0,sK3) | v8_relat_2(X0)) )),
% 0.21/0.49    inference(resolution,[],[f60,f41])).
% 0.21/0.49  fof(f41,plain,(
% 0.21/0.49    ( ! [X0,X1] : (~v8_relat_2(X1) | v8_relat_2(X0) | ~sP2(X0,X1)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f23])).
% 0.21/0.49  fof(f60,plain,(
% 0.21/0.49    v8_relat_2(sK3)),
% 0.21/0.49    inference(resolution,[],[f53,f34])).
% 0.21/0.49  fof(f34,plain,(
% 0.21/0.49    ( ! [X0] : (~sP0(X0) | v8_relat_2(X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f21])).
% 0.21/0.49  fof(f86,plain,(
% 0.21/0.49    v4_relat_2(sK4)),
% 0.21/0.49    inference(resolution,[],[f83,f67])).
% 0.21/0.49  fof(f67,plain,(
% 0.21/0.49    ( ! [X0] : (~sP2(X0,sK3) | v4_relat_2(X0)) )),
% 0.21/0.49    inference(resolution,[],[f61,f43])).
% 0.21/0.49  fof(f43,plain,(
% 0.21/0.49    ( ! [X0,X1] : (~v4_relat_2(X1) | v4_relat_2(X0) | ~sP2(X0,X1)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f23])).
% 0.21/0.49  fof(f61,plain,(
% 0.21/0.49    v4_relat_2(sK3)),
% 0.21/0.49    inference(resolution,[],[f53,f35])).
% 0.21/0.49  fof(f35,plain,(
% 0.21/0.49    ( ! [X0] : (~sP0(X0) | v4_relat_2(X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f21])).
% 0.21/0.49  fof(f85,plain,(
% 0.21/0.49    v6_relat_2(sK4)),
% 0.21/0.49    inference(resolution,[],[f83,f68])).
% 0.21/0.49  fof(f68,plain,(
% 0.21/0.49    ( ! [X0] : (~sP2(X0,sK3) | v6_relat_2(X0)) )),
% 0.21/0.49    inference(resolution,[],[f62,f42])).
% 0.21/0.49  fof(f42,plain,(
% 0.21/0.49    ( ! [X0,X1] : (~v6_relat_2(X1) | v6_relat_2(X0) | ~sP2(X0,X1)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f23])).
% 0.21/0.49  fof(f62,plain,(
% 0.21/0.49    v6_relat_2(sK3)),
% 0.21/0.49    inference(resolution,[],[f53,f36])).
% 0.21/0.49  fof(f36,plain,(
% 0.21/0.49    ( ! [X0] : (~sP0(X0) | v6_relat_2(X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f21])).
% 0.21/0.49  fof(f84,plain,(
% 0.21/0.49    v1_wellord1(sK4)),
% 0.21/0.49    inference(resolution,[],[f83,f69])).
% 0.21/0.49  fof(f69,plain,(
% 0.21/0.49    ( ! [X0] : (~sP2(X0,sK3) | v1_wellord1(X0)) )),
% 0.21/0.49    inference(resolution,[],[f63,f44])).
% 0.21/0.49  fof(f44,plain,(
% 0.21/0.49    ( ! [X0,X1] : (~v1_wellord1(X1) | v1_wellord1(X0) | ~sP2(X0,X1)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f23])).
% 0.21/0.49  fof(f63,plain,(
% 0.21/0.49    v1_wellord1(sK3)),
% 0.21/0.49    inference(resolution,[],[f53,f37])).
% 0.21/0.49  fof(f37,plain,(
% 0.21/0.49    ( ! [X0] : (~sP0(X0) | v1_wellord1(X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f21])).
% 0.21/0.49  fof(f64,plain,(
% 0.21/0.49    ~v1_wellord1(sK4) | ~v6_relat_2(sK4) | ~v4_relat_2(sK4) | ~v8_relat_2(sK4) | ~v1_relat_2(sK4)),
% 0.21/0.49    inference(resolution,[],[f56,f38])).
% 0.21/0.49  fof(f38,plain,(
% 0.21/0.49    ( ! [X0] : (sP0(X0) | ~v1_wellord1(X0) | ~v6_relat_2(X0) | ~v4_relat_2(X0) | ~v8_relat_2(X0) | ~v1_relat_2(X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f21])).
% 0.21/0.49  fof(f56,plain,(
% 0.21/0.49    ~sP0(sK4)),
% 0.21/0.49    inference(subsumption_resolution,[],[f55,f30])).
% 0.21/0.49  fof(f30,plain,(
% 0.21/0.49    ~v2_wellord1(sK4)),
% 0.21/0.49    inference(cnf_transformation,[],[f18])).
% 0.21/0.49  fof(f55,plain,(
% 0.21/0.49    ~sP0(sK4) | v2_wellord1(sK4)),
% 0.21/0.49    inference(resolution,[],[f47,f32])).
% 0.21/0.49  fof(f32,plain,(
% 0.21/0.49    ( ! [X0] : (~sP1(X0) | ~sP0(X0) | v2_wellord1(X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f19])).
% 0.21/0.49  fof(f47,plain,(
% 0.21/0.49    sP1(sK4)),
% 0.21/0.49    inference(resolution,[],[f25,f39])).
% 0.21/0.49  % SZS output end Proof for theBenchmark
% 0.21/0.49  % (31435)------------------------------
% 0.21/0.49  % (31435)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.49  % (31435)Termination reason: Refutation
% 0.21/0.49  
% 0.21/0.49  % (31435)Memory used [KB]: 9850
% 0.21/0.49  % (31435)Time elapsed: 0.086 s
% 0.21/0.49  % (31435)------------------------------
% 0.21/0.49  % (31435)------------------------------
% 0.21/0.50  % (31440)lrs+1_1_av=off:bsr=on:br=off:gs=on:gsem=on:lma=on:lwlo=on:nm=64:nwc=1:stl=30:sp=occurrence:urr=on:updr=off_152 on theBenchmark
% 0.21/0.50  % (31425)Success in time 0.137 s
%------------------------------------------------------------------------------
