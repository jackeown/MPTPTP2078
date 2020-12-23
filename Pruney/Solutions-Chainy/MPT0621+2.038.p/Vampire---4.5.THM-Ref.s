%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:52:00 EST 2020

% Result     : Theorem 1.72s
% Output     : Refutation 1.72s
% Verified   : 
% Statistics : Number of formulae       :   66 ( 114 expanded)
%              Number of leaves         :   11 (  32 expanded)
%              Depth                    :   20
%              Number of atoms          :  260 ( 566 expanded)
%              Number of equality atoms :   92 ( 211 expanded)
%              Maximal formula depth    :   12 (   6 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f231,plain,(
    $false ),
    inference(trivial_inequality_removal,[],[f230])).

fof(f230,plain,(
    k1_xboole_0 != k1_xboole_0 ),
    inference(superposition,[],[f29,f170])).

fof(f170,plain,(
    ! [X2] : k1_xboole_0 = X2 ),
    inference(subsumption_resolution,[],[f169,f29])).

fof(f169,plain,(
    ! [X2] :
      ( k1_xboole_0 = X2
      | k1_xboole_0 = sK1 ) ),
    inference(resolution,[],[f156,f72])).

fof(f72,plain,(
    ! [X0] :
      ( r2_hidden(sK3(X0,k1_xboole_0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(resolution,[],[f65,f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK3(X0,X1),X1)
      | X0 = X1
      | r2_hidden(sK3(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ( ( ~ r2_hidden(sK3(X0,X1),X1)
          | ~ r2_hidden(sK3(X0,X1),X0) )
        & ( r2_hidden(sK3(X0,X1),X1)
          | r2_hidden(sK3(X0,X1),X0) ) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f20,f21])).

fof(f21,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
          & ( r2_hidden(X2,X1)
            | r2_hidden(X2,X0) ) )
     => ( ( ~ r2_hidden(sK3(X0,X1),X1)
          | ~ r2_hidden(sK3(X0,X1),X0) )
        & ( r2_hidden(sK3(X0,X1),X1)
          | r2_hidden(sK3(X0,X1),X0) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ? [X2] :
          ( ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
          & ( r2_hidden(X2,X1)
            | r2_hidden(X2,X0) ) ) ) ),
    inference(nnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ? [X2] :
          ( r2_hidden(X2,X0)
        <~> r2_hidden(X2,X1) ) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
        <=> r2_hidden(X2,X1) )
     => X0 = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_tarski)).

fof(f65,plain,(
    ! [X0] : ~ r2_hidden(X0,k1_xboole_0) ),
    inference(subsumption_resolution,[],[f64,f53])).

fof(f53,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,k1_xboole_0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(duplicate_literal_removal,[],[f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ r2_hidden(X0,k1_xboole_0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(resolution,[],[f42,f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( sP0(k1_xboole_0,X1,X0)
      | ~ r2_hidden(X1,X0) ) ),
    inference(superposition,[],[f45,f30])).

fof(f30,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k5_xboole_0(X1,X2))
      | sP0(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k5_xboole_0(X1,X2))
        | ~ sP0(X2,X0,X1) )
      & ( sP0(X2,X0,X1)
        | ~ r2_hidden(X0,k5_xboole_0(X1,X2)) ) ) ),
    inference(nnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k5_xboole_0(X1,X2))
    <=> sP0(X2,X0,X1) ) ),
    inference(definition_folding,[],[f13,f14])).

fof(f14,plain,(
    ! [X2,X0,X1] :
      ( sP0(X2,X0,X1)
    <=> ( r2_hidden(X0,X1)
      <~> r2_hidden(X0,X2) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k5_xboole_0(X1,X2))
    <=> ( r2_hidden(X0,X1)
      <~> r2_hidden(X0,X2) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k5_xboole_0(X1,X2))
    <=> ~ ( r2_hidden(X0,X1)
        <=> r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_0)).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( ~ sP0(X0,X1,X2)
      | ~ r2_hidden(X1,X2)
      | ~ r2_hidden(X1,X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( ( sP0(X0,X1,X2)
        | ( ( r2_hidden(X1,X2)
            | ~ r2_hidden(X1,X0) )
          & ( r2_hidden(X1,X0)
            | ~ r2_hidden(X1,X2) ) ) )
      & ( ( ( ~ r2_hidden(X1,X0)
            | ~ r2_hidden(X1,X2) )
          & ( r2_hidden(X1,X0)
            | r2_hidden(X1,X2) ) )
        | ~ sP0(X0,X1,X2) ) ) ),
    inference(rectify,[],[f25])).

fof(f25,plain,(
    ! [X2,X0,X1] :
      ( ( sP0(X2,X0,X1)
        | ( ( r2_hidden(X0,X1)
            | ~ r2_hidden(X0,X2) )
          & ( r2_hidden(X0,X2)
            | ~ r2_hidden(X0,X1) ) ) )
      & ( ( ( ~ r2_hidden(X0,X2)
            | ~ r2_hidden(X0,X1) )
          & ( r2_hidden(X0,X2)
            | r2_hidden(X0,X1) ) )
        | ~ sP0(X2,X0,X1) ) ) ),
    inference(nnf_transformation,[],[f14])).

fof(f64,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | ~ r2_hidden(X0,k1_xboole_0) ) ),
    inference(duplicate_literal_removal,[],[f59])).

fof(f59,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | ~ r2_hidden(X0,k1_xboole_0)
      | r2_hidden(X0,X1) ) ),
    inference(resolution,[],[f44,f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( ~ sP0(k1_xboole_0,X1,X0)
      | r2_hidden(X1,X0) ) ),
    inference(superposition,[],[f46,f30])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,k5_xboole_0(X1,X2))
      | ~ sP0(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( sP0(X0,X1,X2)
      | r2_hidden(X1,X2)
      | ~ r2_hidden(X1,X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f156,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,sK1)
      | k1_xboole_0 = X1 ) ),
    inference(duplicate_literal_removal,[],[f128])).

fof(f128,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = X1
      | ~ r2_hidden(X0,sK1)
      | ~ r2_hidden(X0,sK1) ) ),
    inference(superposition,[],[f34,f116])).

fof(f116,plain,(
    ! [X0,X1] :
      ( k1_funct_1(sK2(sK1),X1) = X0
      | ~ r2_hidden(X1,sK1) ) ),
    inference(superposition,[],[f40,f115])).

fof(f115,plain,(
    ! [X0] : sK2(sK1) = sK4(sK1,X0) ),
    inference(equality_resolution,[],[f114])).

fof(f114,plain,(
    ! [X0,X1] :
      ( sK1 != X0
      | sK4(X0,X1) = sK2(sK1) ) ),
    inference(equality_resolution,[],[f89])).

fof(f89,plain,(
    ! [X4,X2,X3] :
      ( sK1 != X4
      | sK4(X2,X3) = sK2(X4)
      | sK1 != X2 ) ),
    inference(subsumption_resolution,[],[f88,f37])).

fof(f37,plain,(
    ! [X0,X1] : v1_relat_1(sK4(X0,X1)) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ! [X3] :
          ( k1_funct_1(sK4(X0,X1),X3) = X1
          | ~ r2_hidden(X3,X0) )
      & k1_relat_1(sK4(X0,X1)) = X0
      & v1_funct_1(sK4(X0,X1))
      & v1_relat_1(sK4(X0,X1)) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f12,f23])).

fof(f23,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ! [X3] :
              ( k1_funct_1(X2,X3) = X1
              | ~ r2_hidden(X3,X0) )
          & k1_relat_1(X2) = X0
          & v1_funct_1(X2)
          & v1_relat_1(X2) )
     => ( ! [X3] :
            ( k1_funct_1(sK4(X0,X1),X3) = X1
            | ~ r2_hidden(X3,X0) )
        & k1_relat_1(sK4(X0,X1)) = X0
        & v1_funct_1(sK4(X0,X1))
        & v1_relat_1(sK4(X0,X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f12,plain,(
    ! [X0,X1] :
    ? [X2] :
      ( ! [X3] :
          ( k1_funct_1(X2,X3) = X1
          | ~ r2_hidden(X3,X0) )
      & k1_relat_1(X2) = X0
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
    ? [X2] :
      ( ! [X3] :
          ( r2_hidden(X3,X0)
         => k1_funct_1(X2,X3) = X1 )
      & k1_relat_1(X2) = X0
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',s3_funct_1__e2_24__funct_1)).

fof(f88,plain,(
    ! [X4,X2,X3] :
      ( sK1 != X2
      | sK4(X2,X3) = sK2(X4)
      | sK1 != X4
      | ~ v1_relat_1(sK4(X2,X3)) ) ),
    inference(subsumption_resolution,[],[f85,f38])).

fof(f38,plain,(
    ! [X0,X1] : v1_funct_1(sK4(X0,X1)) ),
    inference(cnf_transformation,[],[f24])).

fof(f85,plain,(
    ! [X4,X2,X3] :
      ( sK1 != X2
      | sK4(X2,X3) = sK2(X4)
      | sK1 != X4
      | ~ v1_funct_1(sK4(X2,X3))
      | ~ v1_relat_1(sK4(X2,X3)) ) ),
    inference(superposition,[],[f76,f39])).

fof(f39,plain,(
    ! [X0,X1] : k1_relat_1(sK4(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f24])).

fof(f76,plain,(
    ! [X0,X1] :
      ( k1_relat_1(X1) != sK1
      | sK2(X0) = X1
      | sK1 != X0
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(subsumption_resolution,[],[f75,f31])).

fof(f31,plain,(
    ! [X0] : v1_relat_1(sK2(X0)) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X2] :
          ( k1_xboole_0 = k1_funct_1(sK2(X0),X2)
          | ~ r2_hidden(X2,X0) )
      & k1_relat_1(sK2(X0)) = X0
      & v1_funct_1(sK2(X0))
      & v1_relat_1(sK2(X0)) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f10,f18])).

fof(f18,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ! [X2] :
              ( k1_xboole_0 = k1_funct_1(X1,X2)
              | ~ r2_hidden(X2,X0) )
          & k1_relat_1(X1) = X0
          & v1_funct_1(X1)
          & v1_relat_1(X1) )
     => ( ! [X2] :
            ( k1_xboole_0 = k1_funct_1(sK2(X0),X2)
            | ~ r2_hidden(X2,X0) )
        & k1_relat_1(sK2(X0)) = X0
        & v1_funct_1(sK2(X0))
        & v1_relat_1(sK2(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f10,plain,(
    ! [X0] :
    ? [X1] :
      ( ! [X2] :
          ( k1_xboole_0 = k1_funct_1(X1,X2)
          | ~ r2_hidden(X2,X0) )
      & k1_relat_1(X1) = X0
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
    ? [X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
         => k1_xboole_0 = k1_funct_1(X1,X2) )
      & k1_relat_1(X1) = X0
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',s3_funct_1__e2_25__funct_1)).

fof(f75,plain,(
    ! [X0,X1] :
      ( sK1 != X0
      | sK2(X0) = X1
      | k1_relat_1(X1) != sK1
      | ~ v1_relat_1(sK2(X0))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(subsumption_resolution,[],[f73,f32])).

fof(f32,plain,(
    ! [X0] : v1_funct_1(sK2(X0)) ),
    inference(cnf_transformation,[],[f19])).

fof(f73,plain,(
    ! [X0,X1] :
      ( sK1 != X0
      | sK2(X0) = X1
      | k1_relat_1(X1) != sK1
      | ~ v1_funct_1(sK2(X0))
      | ~ v1_relat_1(sK2(X0))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(superposition,[],[f28,f33])).

fof(f33,plain,(
    ! [X0] : k1_relat_1(sK2(X0)) = X0 ),
    inference(cnf_transformation,[],[f19])).

fof(f28,plain,(
    ! [X2,X1] :
      ( k1_relat_1(X2) != sK1
      | X1 = X2
      | k1_relat_1(X1) != sK1
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,
    ( k1_xboole_0 != sK1
    & ! [X1] :
        ( ! [X2] :
            ( X1 = X2
            | k1_relat_1(X2) != sK1
            | k1_relat_1(X1) != sK1
            | ~ v1_funct_1(X2)
            | ~ v1_relat_1(X2) )
        | ~ v1_funct_1(X1)
        | ~ v1_relat_1(X1) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f9,f16])).

fof(f16,plain,
    ( ? [X0] :
        ( k1_xboole_0 != X0
        & ! [X1] :
            ( ! [X2] :
                ( X1 = X2
                | k1_relat_1(X2) != X0
                | k1_relat_1(X1) != X0
                | ~ v1_funct_1(X2)
                | ~ v1_relat_1(X2) )
            | ~ v1_funct_1(X1)
            | ~ v1_relat_1(X1) ) )
   => ( k1_xboole_0 != sK1
      & ! [X1] :
          ( ! [X2] :
              ( X1 = X2
              | k1_relat_1(X2) != sK1
              | k1_relat_1(X1) != sK1
              | ~ v1_funct_1(X2)
              | ~ v1_relat_1(X2) )
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) ) ) ),
    introduced(choice_axiom,[])).

fof(f9,plain,(
    ? [X0] :
      ( k1_xboole_0 != X0
      & ! [X1] :
          ( ! [X2] :
              ( X1 = X2
              | k1_relat_1(X2) != X0
              | k1_relat_1(X1) != X0
              | ~ v1_funct_1(X2)
              | ~ v1_relat_1(X2) )
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) ) ) ),
    inference(flattening,[],[f8])).

fof(f8,plain,(
    ? [X0] :
      ( k1_xboole_0 != X0
      & ! [X1] :
          ( ! [X2] :
              ( X1 = X2
              | k1_relat_1(X2) != X0
              | k1_relat_1(X1) != X0
              | ~ v1_funct_1(X2)
              | ~ v1_relat_1(X2) )
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) ) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,negated_conjecture,(
    ~ ! [X0] :
        ( ! [X1] :
            ( ( v1_funct_1(X1)
              & v1_relat_1(X1) )
           => ! [X2] :
                ( ( v1_funct_1(X2)
                  & v1_relat_1(X2) )
               => ( ( k1_relat_1(X2) = X0
                    & k1_relat_1(X1) = X0 )
                 => X1 = X2 ) ) )
       => k1_xboole_0 = X0 ) ),
    inference(negated_conjecture,[],[f6])).

fof(f6,conjecture,(
    ! [X0] :
      ( ! [X1] :
          ( ( v1_funct_1(X1)
            & v1_relat_1(X1) )
         => ! [X2] :
              ( ( v1_funct_1(X2)
                & v1_relat_1(X2) )
             => ( ( k1_relat_1(X2) = X0
                  & k1_relat_1(X1) = X0 )
               => X1 = X2 ) ) )
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t16_funct_1)).

fof(f40,plain,(
    ! [X0,X3,X1] :
      ( k1_funct_1(sK4(X0,X1),X3) = X1
      | ~ r2_hidden(X3,X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f34,plain,(
    ! [X2,X0] :
      ( k1_xboole_0 = k1_funct_1(sK2(X0),X2)
      | ~ r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f29,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f17])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n004.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 17:53:38 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.53  % (23707)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.21/0.54  % (23723)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.21/0.54  % (23714)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.21/0.54  % (23710)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.21/0.54  % (23710)Refutation not found, incomplete strategy% (23710)------------------------------
% 0.21/0.54  % (23710)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (23710)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (23710)Memory used [KB]: 10618
% 0.21/0.54  % (23710)Time elapsed: 0.125 s
% 0.21/0.54  % (23710)------------------------------
% 0.21/0.54  % (23710)------------------------------
% 0.21/0.55  % (23700)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.21/0.55  % (23716)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.21/0.56  % (23730)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 1.56/0.56  % (23705)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 1.56/0.57  % (23711)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 1.56/0.57  % (23701)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 1.56/0.57  % (23711)Refutation not found, incomplete strategy% (23711)------------------------------
% 1.56/0.57  % (23711)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.56/0.57  % (23711)Termination reason: Refutation not found, incomplete strategy
% 1.56/0.57  
% 1.56/0.57  % (23711)Memory used [KB]: 10618
% 1.56/0.57  % (23711)Time elapsed: 0.154 s
% 1.56/0.57  % (23711)------------------------------
% 1.56/0.57  % (23711)------------------------------
% 1.56/0.58  % (23699)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 1.56/0.58  % (23713)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 1.72/0.58  % (23704)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 1.72/0.58  % (23730)Refutation found. Thanks to Tanya!
% 1.72/0.58  % SZS status Theorem for theBenchmark
% 1.72/0.58  % SZS output start Proof for theBenchmark
% 1.72/0.58  fof(f231,plain,(
% 1.72/0.58    $false),
% 1.72/0.58    inference(trivial_inequality_removal,[],[f230])).
% 1.72/0.58  fof(f230,plain,(
% 1.72/0.58    k1_xboole_0 != k1_xboole_0),
% 1.72/0.58    inference(superposition,[],[f29,f170])).
% 1.72/0.58  fof(f170,plain,(
% 1.72/0.58    ( ! [X2] : (k1_xboole_0 = X2) )),
% 1.72/0.58    inference(subsumption_resolution,[],[f169,f29])).
% 1.72/0.58  fof(f169,plain,(
% 1.72/0.58    ( ! [X2] : (k1_xboole_0 = X2 | k1_xboole_0 = sK1) )),
% 1.72/0.58    inference(resolution,[],[f156,f72])).
% 1.72/0.58  fof(f72,plain,(
% 1.72/0.58    ( ! [X0] : (r2_hidden(sK3(X0,k1_xboole_0),X0) | k1_xboole_0 = X0) )),
% 1.72/0.58    inference(resolution,[],[f65,f35])).
% 1.72/0.58  fof(f35,plain,(
% 1.72/0.58    ( ! [X0,X1] : (r2_hidden(sK3(X0,X1),X1) | X0 = X1 | r2_hidden(sK3(X0,X1),X0)) )),
% 1.72/0.58    inference(cnf_transformation,[],[f22])).
% 1.72/0.58  fof(f22,plain,(
% 1.72/0.58    ! [X0,X1] : (X0 = X1 | ((~r2_hidden(sK3(X0,X1),X1) | ~r2_hidden(sK3(X0,X1),X0)) & (r2_hidden(sK3(X0,X1),X1) | r2_hidden(sK3(X0,X1),X0))))),
% 1.72/0.58    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f20,f21])).
% 1.72/0.58  fof(f21,plain,(
% 1.72/0.58    ! [X1,X0] : (? [X2] : ((~r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) & (r2_hidden(X2,X1) | r2_hidden(X2,X0))) => ((~r2_hidden(sK3(X0,X1),X1) | ~r2_hidden(sK3(X0,X1),X0)) & (r2_hidden(sK3(X0,X1),X1) | r2_hidden(sK3(X0,X1),X0))))),
% 1.72/0.58    introduced(choice_axiom,[])).
% 1.72/0.58  fof(f20,plain,(
% 1.72/0.58    ! [X0,X1] : (X0 = X1 | ? [X2] : ((~r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) & (r2_hidden(X2,X1) | r2_hidden(X2,X0))))),
% 1.72/0.58    inference(nnf_transformation,[],[f11])).
% 1.72/0.58  fof(f11,plain,(
% 1.72/0.58    ! [X0,X1] : (X0 = X1 | ? [X2] : (r2_hidden(X2,X0) <~> r2_hidden(X2,X1)))),
% 1.72/0.58    inference(ennf_transformation,[],[f2])).
% 1.72/0.58  fof(f2,axiom,(
% 1.72/0.58    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) <=> r2_hidden(X2,X1)) => X0 = X1)),
% 1.72/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_tarski)).
% 1.72/0.58  fof(f65,plain,(
% 1.72/0.58    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0)) )),
% 1.72/0.58    inference(subsumption_resolution,[],[f64,f53])).
% 1.72/0.58  fof(f53,plain,(
% 1.72/0.58    ( ! [X0,X1] : (~r2_hidden(X0,k1_xboole_0) | ~r2_hidden(X0,X1)) )),
% 1.72/0.58    inference(duplicate_literal_removal,[],[f52])).
% 1.72/0.58  fof(f52,plain,(
% 1.72/0.58    ( ! [X0,X1] : (~r2_hidden(X0,X1) | ~r2_hidden(X0,k1_xboole_0) | ~r2_hidden(X0,X1)) )),
% 1.72/0.58    inference(resolution,[],[f42,f47])).
% 1.72/0.58  fof(f47,plain,(
% 1.72/0.58    ( ! [X0,X1] : (sP0(k1_xboole_0,X1,X0) | ~r2_hidden(X1,X0)) )),
% 1.72/0.58    inference(superposition,[],[f45,f30])).
% 1.72/0.58  fof(f30,plain,(
% 1.72/0.58    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 1.72/0.58    inference(cnf_transformation,[],[f3])).
% 1.72/0.58  fof(f3,axiom,(
% 1.72/0.58    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 1.72/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).
% 1.72/0.58  fof(f45,plain,(
% 1.72/0.58    ( ! [X2,X0,X1] : (~r2_hidden(X0,k5_xboole_0(X1,X2)) | sP0(X2,X0,X1)) )),
% 1.72/0.58    inference(cnf_transformation,[],[f27])).
% 1.72/0.58  fof(f27,plain,(
% 1.72/0.58    ! [X0,X1,X2] : ((r2_hidden(X0,k5_xboole_0(X1,X2)) | ~sP0(X2,X0,X1)) & (sP0(X2,X0,X1) | ~r2_hidden(X0,k5_xboole_0(X1,X2))))),
% 1.72/0.58    inference(nnf_transformation,[],[f15])).
% 1.72/0.58  fof(f15,plain,(
% 1.72/0.58    ! [X0,X1,X2] : (r2_hidden(X0,k5_xboole_0(X1,X2)) <=> sP0(X2,X0,X1))),
% 1.72/0.58    inference(definition_folding,[],[f13,f14])).
% 1.72/0.58  fof(f14,plain,(
% 1.72/0.58    ! [X2,X0,X1] : (sP0(X2,X0,X1) <=> (r2_hidden(X0,X1) <~> r2_hidden(X0,X2)))),
% 1.72/0.58    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 1.72/0.58  fof(f13,plain,(
% 1.72/0.58    ! [X0,X1,X2] : (r2_hidden(X0,k5_xboole_0(X1,X2)) <=> (r2_hidden(X0,X1) <~> r2_hidden(X0,X2)))),
% 1.72/0.58    inference(ennf_transformation,[],[f1])).
% 1.72/0.58  fof(f1,axiom,(
% 1.72/0.58    ! [X0,X1,X2] : (r2_hidden(X0,k5_xboole_0(X1,X2)) <=> ~(r2_hidden(X0,X1) <=> r2_hidden(X0,X2)))),
% 1.72/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_0)).
% 1.72/0.58  fof(f42,plain,(
% 1.72/0.58    ( ! [X2,X0,X1] : (~sP0(X0,X1,X2) | ~r2_hidden(X1,X2) | ~r2_hidden(X1,X0)) )),
% 1.72/0.58    inference(cnf_transformation,[],[f26])).
% 1.72/0.59  fof(f26,plain,(
% 1.72/0.59    ! [X0,X1,X2] : ((sP0(X0,X1,X2) | ((r2_hidden(X1,X2) | ~r2_hidden(X1,X0)) & (r2_hidden(X1,X0) | ~r2_hidden(X1,X2)))) & (((~r2_hidden(X1,X0) | ~r2_hidden(X1,X2)) & (r2_hidden(X1,X0) | r2_hidden(X1,X2))) | ~sP0(X0,X1,X2)))),
% 1.72/0.59    inference(rectify,[],[f25])).
% 1.72/0.59  fof(f25,plain,(
% 1.72/0.59    ! [X2,X0,X1] : ((sP0(X2,X0,X1) | ((r2_hidden(X0,X1) | ~r2_hidden(X0,X2)) & (r2_hidden(X0,X2) | ~r2_hidden(X0,X1)))) & (((~r2_hidden(X0,X2) | ~r2_hidden(X0,X1)) & (r2_hidden(X0,X2) | r2_hidden(X0,X1))) | ~sP0(X2,X0,X1)))),
% 1.72/0.59    inference(nnf_transformation,[],[f14])).
% 1.72/0.59  fof(f64,plain,(
% 1.72/0.59    ( ! [X0,X1] : (r2_hidden(X0,X1) | ~r2_hidden(X0,k1_xboole_0)) )),
% 1.72/0.59    inference(duplicate_literal_removal,[],[f59])).
% 1.72/0.59  fof(f59,plain,(
% 1.72/0.59    ( ! [X0,X1] : (r2_hidden(X0,X1) | ~r2_hidden(X0,k1_xboole_0) | r2_hidden(X0,X1)) )),
% 1.72/0.59    inference(resolution,[],[f44,f49])).
% 1.72/0.59  fof(f49,plain,(
% 1.72/0.59    ( ! [X0,X1] : (~sP0(k1_xboole_0,X1,X0) | r2_hidden(X1,X0)) )),
% 1.72/0.59    inference(superposition,[],[f46,f30])).
% 1.72/0.59  fof(f46,plain,(
% 1.72/0.59    ( ! [X2,X0,X1] : (r2_hidden(X0,k5_xboole_0(X1,X2)) | ~sP0(X2,X0,X1)) )),
% 1.72/0.59    inference(cnf_transformation,[],[f27])).
% 1.72/0.59  fof(f44,plain,(
% 1.72/0.59    ( ! [X2,X0,X1] : (sP0(X0,X1,X2) | r2_hidden(X1,X2) | ~r2_hidden(X1,X0)) )),
% 1.72/0.59    inference(cnf_transformation,[],[f26])).
% 1.72/0.59  fof(f156,plain,(
% 1.72/0.59    ( ! [X0,X1] : (~r2_hidden(X0,sK1) | k1_xboole_0 = X1) )),
% 1.72/0.59    inference(duplicate_literal_removal,[],[f128])).
% 1.72/0.59  fof(f128,plain,(
% 1.72/0.59    ( ! [X0,X1] : (k1_xboole_0 = X1 | ~r2_hidden(X0,sK1) | ~r2_hidden(X0,sK1)) )),
% 1.72/0.59    inference(superposition,[],[f34,f116])).
% 1.72/0.59  fof(f116,plain,(
% 1.72/0.59    ( ! [X0,X1] : (k1_funct_1(sK2(sK1),X1) = X0 | ~r2_hidden(X1,sK1)) )),
% 1.72/0.59    inference(superposition,[],[f40,f115])).
% 1.72/0.59  fof(f115,plain,(
% 1.72/0.59    ( ! [X0] : (sK2(sK1) = sK4(sK1,X0)) )),
% 1.72/0.59    inference(equality_resolution,[],[f114])).
% 1.72/0.59  fof(f114,plain,(
% 1.72/0.59    ( ! [X0,X1] : (sK1 != X0 | sK4(X0,X1) = sK2(sK1)) )),
% 1.72/0.59    inference(equality_resolution,[],[f89])).
% 1.72/0.59  fof(f89,plain,(
% 1.72/0.59    ( ! [X4,X2,X3] : (sK1 != X4 | sK4(X2,X3) = sK2(X4) | sK1 != X2) )),
% 1.72/0.59    inference(subsumption_resolution,[],[f88,f37])).
% 1.72/0.59  fof(f37,plain,(
% 1.72/0.59    ( ! [X0,X1] : (v1_relat_1(sK4(X0,X1))) )),
% 1.72/0.59    inference(cnf_transformation,[],[f24])).
% 1.72/0.59  fof(f24,plain,(
% 1.72/0.59    ! [X0,X1] : (! [X3] : (k1_funct_1(sK4(X0,X1),X3) = X1 | ~r2_hidden(X3,X0)) & k1_relat_1(sK4(X0,X1)) = X0 & v1_funct_1(sK4(X0,X1)) & v1_relat_1(sK4(X0,X1)))),
% 1.72/0.59    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f12,f23])).
% 1.72/0.59  fof(f23,plain,(
% 1.72/0.59    ! [X1,X0] : (? [X2] : (! [X3] : (k1_funct_1(X2,X3) = X1 | ~r2_hidden(X3,X0)) & k1_relat_1(X2) = X0 & v1_funct_1(X2) & v1_relat_1(X2)) => (! [X3] : (k1_funct_1(sK4(X0,X1),X3) = X1 | ~r2_hidden(X3,X0)) & k1_relat_1(sK4(X0,X1)) = X0 & v1_funct_1(sK4(X0,X1)) & v1_relat_1(sK4(X0,X1))))),
% 1.72/0.59    introduced(choice_axiom,[])).
% 1.72/0.59  fof(f12,plain,(
% 1.72/0.59    ! [X0,X1] : ? [X2] : (! [X3] : (k1_funct_1(X2,X3) = X1 | ~r2_hidden(X3,X0)) & k1_relat_1(X2) = X0 & v1_funct_1(X2) & v1_relat_1(X2))),
% 1.72/0.59    inference(ennf_transformation,[],[f4])).
% 1.72/0.59  fof(f4,axiom,(
% 1.72/0.59    ! [X0,X1] : ? [X2] : (! [X3] : (r2_hidden(X3,X0) => k1_funct_1(X2,X3) = X1) & k1_relat_1(X2) = X0 & v1_funct_1(X2) & v1_relat_1(X2))),
% 1.72/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',s3_funct_1__e2_24__funct_1)).
% 1.72/0.59  fof(f88,plain,(
% 1.72/0.59    ( ! [X4,X2,X3] : (sK1 != X2 | sK4(X2,X3) = sK2(X4) | sK1 != X4 | ~v1_relat_1(sK4(X2,X3))) )),
% 1.72/0.59    inference(subsumption_resolution,[],[f85,f38])).
% 1.72/0.59  fof(f38,plain,(
% 1.72/0.59    ( ! [X0,X1] : (v1_funct_1(sK4(X0,X1))) )),
% 1.72/0.59    inference(cnf_transformation,[],[f24])).
% 1.72/0.59  fof(f85,plain,(
% 1.72/0.59    ( ! [X4,X2,X3] : (sK1 != X2 | sK4(X2,X3) = sK2(X4) | sK1 != X4 | ~v1_funct_1(sK4(X2,X3)) | ~v1_relat_1(sK4(X2,X3))) )),
% 1.72/0.59    inference(superposition,[],[f76,f39])).
% 1.72/0.59  fof(f39,plain,(
% 1.72/0.59    ( ! [X0,X1] : (k1_relat_1(sK4(X0,X1)) = X0) )),
% 1.72/0.59    inference(cnf_transformation,[],[f24])).
% 1.72/0.59  fof(f76,plain,(
% 1.72/0.59    ( ! [X0,X1] : (k1_relat_1(X1) != sK1 | sK2(X0) = X1 | sK1 != X0 | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 1.72/0.59    inference(subsumption_resolution,[],[f75,f31])).
% 1.72/0.59  fof(f31,plain,(
% 1.72/0.59    ( ! [X0] : (v1_relat_1(sK2(X0))) )),
% 1.72/0.59    inference(cnf_transformation,[],[f19])).
% 1.72/0.59  fof(f19,plain,(
% 1.72/0.59    ! [X0] : (! [X2] : (k1_xboole_0 = k1_funct_1(sK2(X0),X2) | ~r2_hidden(X2,X0)) & k1_relat_1(sK2(X0)) = X0 & v1_funct_1(sK2(X0)) & v1_relat_1(sK2(X0)))),
% 1.72/0.59    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f10,f18])).
% 1.72/0.59  fof(f18,plain,(
% 1.72/0.59    ! [X0] : (? [X1] : (! [X2] : (k1_xboole_0 = k1_funct_1(X1,X2) | ~r2_hidden(X2,X0)) & k1_relat_1(X1) = X0 & v1_funct_1(X1) & v1_relat_1(X1)) => (! [X2] : (k1_xboole_0 = k1_funct_1(sK2(X0),X2) | ~r2_hidden(X2,X0)) & k1_relat_1(sK2(X0)) = X0 & v1_funct_1(sK2(X0)) & v1_relat_1(sK2(X0))))),
% 1.72/0.59    introduced(choice_axiom,[])).
% 1.72/0.59  fof(f10,plain,(
% 1.72/0.59    ! [X0] : ? [X1] : (! [X2] : (k1_xboole_0 = k1_funct_1(X1,X2) | ~r2_hidden(X2,X0)) & k1_relat_1(X1) = X0 & v1_funct_1(X1) & v1_relat_1(X1))),
% 1.72/0.59    inference(ennf_transformation,[],[f5])).
% 1.72/0.59  fof(f5,axiom,(
% 1.72/0.59    ! [X0] : ? [X1] : (! [X2] : (r2_hidden(X2,X0) => k1_xboole_0 = k1_funct_1(X1,X2)) & k1_relat_1(X1) = X0 & v1_funct_1(X1) & v1_relat_1(X1))),
% 1.72/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',s3_funct_1__e2_25__funct_1)).
% 1.72/0.59  fof(f75,plain,(
% 1.72/0.59    ( ! [X0,X1] : (sK1 != X0 | sK2(X0) = X1 | k1_relat_1(X1) != sK1 | ~v1_relat_1(sK2(X0)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 1.72/0.59    inference(subsumption_resolution,[],[f73,f32])).
% 1.72/0.59  fof(f32,plain,(
% 1.72/0.59    ( ! [X0] : (v1_funct_1(sK2(X0))) )),
% 1.72/0.59    inference(cnf_transformation,[],[f19])).
% 1.72/0.59  fof(f73,plain,(
% 1.72/0.59    ( ! [X0,X1] : (sK1 != X0 | sK2(X0) = X1 | k1_relat_1(X1) != sK1 | ~v1_funct_1(sK2(X0)) | ~v1_relat_1(sK2(X0)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 1.72/0.59    inference(superposition,[],[f28,f33])).
% 1.72/0.59  fof(f33,plain,(
% 1.72/0.59    ( ! [X0] : (k1_relat_1(sK2(X0)) = X0) )),
% 1.72/0.59    inference(cnf_transformation,[],[f19])).
% 1.72/0.59  fof(f28,plain,(
% 1.72/0.59    ( ! [X2,X1] : (k1_relat_1(X2) != sK1 | X1 = X2 | k1_relat_1(X1) != sK1 | ~v1_funct_1(X2) | ~v1_relat_1(X2) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 1.72/0.59    inference(cnf_transformation,[],[f17])).
% 1.72/0.59  fof(f17,plain,(
% 1.72/0.59    k1_xboole_0 != sK1 & ! [X1] : (! [X2] : (X1 = X2 | k1_relat_1(X2) != sK1 | k1_relat_1(X1) != sK1 | ~v1_funct_1(X2) | ~v1_relat_1(X2)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 1.72/0.59    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f9,f16])).
% 1.72/0.59  fof(f16,plain,(
% 1.72/0.59    ? [X0] : (k1_xboole_0 != X0 & ! [X1] : (! [X2] : (X1 = X2 | k1_relat_1(X2) != X0 | k1_relat_1(X1) != X0 | ~v1_funct_1(X2) | ~v1_relat_1(X2)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))) => (k1_xboole_0 != sK1 & ! [X1] : (! [X2] : (X1 = X2 | k1_relat_1(X2) != sK1 | k1_relat_1(X1) != sK1 | ~v1_funct_1(X2) | ~v1_relat_1(X2)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 1.72/0.59    introduced(choice_axiom,[])).
% 1.72/0.59  fof(f9,plain,(
% 1.72/0.59    ? [X0] : (k1_xboole_0 != X0 & ! [X1] : (! [X2] : (X1 = X2 | k1_relat_1(X2) != X0 | k1_relat_1(X1) != X0 | ~v1_funct_1(X2) | ~v1_relat_1(X2)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 1.72/0.59    inference(flattening,[],[f8])).
% 1.72/0.59  fof(f8,plain,(
% 1.72/0.59    ? [X0] : (k1_xboole_0 != X0 & ! [X1] : (! [X2] : ((X1 = X2 | (k1_relat_1(X2) != X0 | k1_relat_1(X1) != X0)) | (~v1_funct_1(X2) | ~v1_relat_1(X2))) | (~v1_funct_1(X1) | ~v1_relat_1(X1))))),
% 1.72/0.59    inference(ennf_transformation,[],[f7])).
% 1.72/0.59  fof(f7,negated_conjecture,(
% 1.72/0.59    ~! [X0] : (! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ! [X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ((k1_relat_1(X2) = X0 & k1_relat_1(X1) = X0) => X1 = X2))) => k1_xboole_0 = X0)),
% 1.72/0.59    inference(negated_conjecture,[],[f6])).
% 1.72/0.59  fof(f6,conjecture,(
% 1.72/0.59    ! [X0] : (! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ! [X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ((k1_relat_1(X2) = X0 & k1_relat_1(X1) = X0) => X1 = X2))) => k1_xboole_0 = X0)),
% 1.72/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t16_funct_1)).
% 1.72/0.59  fof(f40,plain,(
% 1.72/0.59    ( ! [X0,X3,X1] : (k1_funct_1(sK4(X0,X1),X3) = X1 | ~r2_hidden(X3,X0)) )),
% 1.72/0.59    inference(cnf_transformation,[],[f24])).
% 1.72/0.59  fof(f34,plain,(
% 1.72/0.59    ( ! [X2,X0] : (k1_xboole_0 = k1_funct_1(sK2(X0),X2) | ~r2_hidden(X2,X0)) )),
% 1.72/0.59    inference(cnf_transformation,[],[f19])).
% 1.72/0.59  fof(f29,plain,(
% 1.72/0.59    k1_xboole_0 != sK1),
% 1.72/0.59    inference(cnf_transformation,[],[f17])).
% 1.72/0.59  % SZS output end Proof for theBenchmark
% 1.72/0.59  % (23730)------------------------------
% 1.72/0.59  % (23730)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.72/0.59  % (23730)Termination reason: Refutation
% 1.72/0.59  
% 1.72/0.59  % (23730)Memory used [KB]: 1791
% 1.72/0.59  % (23730)Time elapsed: 0.141 s
% 1.72/0.59  % (23730)------------------------------
% 1.72/0.59  % (23730)------------------------------
% 1.72/0.59  % (23693)Success in time 0.225 s
%------------------------------------------------------------------------------
