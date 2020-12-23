%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:52:50 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   67 ( 175 expanded)
%              Number of leaves         :   12 (  48 expanded)
%              Depth                    :   12
%              Number of atoms          :  213 ( 753 expanded)
%              Number of equality atoms :   59 ( 267 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f131,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f45,f61,f66,f70,f97,f120])).

fof(f120,plain,
    ( spl1_2
    | ~ spl1_5 ),
    inference(avatar_contradiction_clause,[],[f119])).

fof(f119,plain,
    ( $false
    | spl1_2
    | ~ spl1_5 ),
    inference(subsumption_resolution,[],[f118,f44])).

fof(f44,plain,
    ( k1_relat_1(sK0) != k2_relat_1(k5_relat_1(sK0,k2_funct_1(sK0)))
    | spl1_2 ),
    inference(avatar_component_clause,[],[f42])).

fof(f42,plain,
    ( spl1_2
  <=> k1_relat_1(sK0) = k2_relat_1(k5_relat_1(sK0,k2_funct_1(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_2])])).

fof(f118,plain,
    ( k1_relat_1(sK0) = k2_relat_1(k5_relat_1(sK0,k2_funct_1(sK0)))
    | ~ spl1_5 ),
    inference(subsumption_resolution,[],[f113,f22])).

fof(f22,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,
    ( ( k1_relat_1(sK0) != k2_relat_1(k5_relat_1(sK0,k2_funct_1(sK0)))
      | k1_relat_1(sK0) != k1_relat_1(k5_relat_1(sK0,k2_funct_1(sK0))) )
    & v2_funct_1(sK0)
    & v1_funct_1(sK0)
    & v1_relat_1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f9,f18])).

fof(f18,plain,
    ( ? [X0] :
        ( ( k1_relat_1(X0) != k2_relat_1(k5_relat_1(X0,k2_funct_1(X0)))
          | k1_relat_1(X0) != k1_relat_1(k5_relat_1(X0,k2_funct_1(X0))) )
        & v2_funct_1(X0)
        & v1_funct_1(X0)
        & v1_relat_1(X0) )
   => ( ( k1_relat_1(sK0) != k2_relat_1(k5_relat_1(sK0,k2_funct_1(sK0)))
        | k1_relat_1(sK0) != k1_relat_1(k5_relat_1(sK0,k2_funct_1(sK0))) )
      & v2_funct_1(sK0)
      & v1_funct_1(sK0)
      & v1_relat_1(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f9,plain,(
    ? [X0] :
      ( ( k1_relat_1(X0) != k2_relat_1(k5_relat_1(X0,k2_funct_1(X0)))
        | k1_relat_1(X0) != k1_relat_1(k5_relat_1(X0,k2_funct_1(X0))) )
      & v2_funct_1(X0)
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(flattening,[],[f8])).

fof(f8,plain,(
    ? [X0] :
      ( ( k1_relat_1(X0) != k2_relat_1(k5_relat_1(X0,k2_funct_1(X0)))
        | k1_relat_1(X0) != k1_relat_1(k5_relat_1(X0,k2_funct_1(X0))) )
      & v2_funct_1(X0)
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,negated_conjecture,(
    ~ ! [X0] :
        ( ( v1_funct_1(X0)
          & v1_relat_1(X0) )
       => ( v2_funct_1(X0)
         => ( k1_relat_1(X0) = k2_relat_1(k5_relat_1(X0,k2_funct_1(X0)))
            & k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,k2_funct_1(X0))) ) ) ) ),
    inference(negated_conjecture,[],[f6])).

fof(f6,conjecture,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k1_relat_1(X0) = k2_relat_1(k5_relat_1(X0,k2_funct_1(X0)))
          & k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,k2_funct_1(X0))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t58_funct_1)).

fof(f113,plain,
    ( ~ v1_relat_1(sK0)
    | k1_relat_1(sK0) = k2_relat_1(k5_relat_1(sK0,k2_funct_1(sK0)))
    | ~ spl1_5 ),
    inference(resolution,[],[f65,f35])).

fof(f35,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f65,plain,
    ( ! [X1] :
        ( ~ r1_tarski(k2_relat_1(sK0),k2_relat_1(X1))
        | ~ v1_relat_1(X1)
        | k1_relat_1(sK0) = k2_relat_1(k5_relat_1(X1,k2_funct_1(sK0))) )
    | ~ spl1_5 ),
    inference(avatar_component_clause,[],[f64])).

fof(f64,plain,
    ( spl1_5
  <=> ! [X1] :
        ( k1_relat_1(sK0) = k2_relat_1(k5_relat_1(X1,k2_funct_1(sK0)))
        | ~ v1_relat_1(X1)
        | ~ r1_tarski(k2_relat_1(sK0),k2_relat_1(X1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_5])])).

fof(f97,plain,
    ( spl1_1
    | ~ spl1_4 ),
    inference(avatar_split_clause,[],[f79,f59,f38])).

fof(f38,plain,
    ( spl1_1
  <=> k1_relat_1(sK0) = k1_relat_1(k5_relat_1(sK0,k2_funct_1(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_1])])).

fof(f59,plain,
    ( spl1_4
  <=> ! [X0] :
        ( ~ r1_tarski(k2_relat_1(X0),k2_relat_1(sK0))
        | ~ v1_relat_1(X0)
        | k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,k2_funct_1(sK0))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_4])])).

fof(f79,plain,
    ( k1_relat_1(sK0) = k1_relat_1(k5_relat_1(sK0,k2_funct_1(sK0)))
    | ~ spl1_4 ),
    inference(subsumption_resolution,[],[f76,f22])).

fof(f76,plain,
    ( ~ v1_relat_1(sK0)
    | k1_relat_1(sK0) = k1_relat_1(k5_relat_1(sK0,k2_funct_1(sK0)))
    | ~ spl1_4 ),
    inference(resolution,[],[f60,f36])).

fof(f36,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f21])).

fof(f60,plain,
    ( ! [X0] :
        ( ~ r1_tarski(k2_relat_1(X0),k2_relat_1(sK0))
        | ~ v1_relat_1(X0)
        | k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,k2_funct_1(sK0))) )
    | ~ spl1_4 ),
    inference(avatar_component_clause,[],[f59])).

fof(f70,plain,(
    spl1_3 ),
    inference(avatar_contradiction_clause,[],[f69])).

fof(f69,plain,
    ( $false
    | spl1_3 ),
    inference(subsumption_resolution,[],[f68,f22])).

fof(f68,plain,
    ( ~ v1_relat_1(sK0)
    | spl1_3 ),
    inference(subsumption_resolution,[],[f67,f23])).

fof(f23,plain,(
    v1_funct_1(sK0) ),
    inference(cnf_transformation,[],[f19])).

fof(f67,plain,
    ( ~ v1_funct_1(sK0)
    | ~ v1_relat_1(sK0)
    | spl1_3 ),
    inference(resolution,[],[f57,f30])).

fof(f30,plain,(
    ! [X0] :
      ( v1_relat_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_funct_1)).

fof(f57,plain,
    ( ~ v1_relat_1(k2_funct_1(sK0))
    | spl1_3 ),
    inference(avatar_component_clause,[],[f55])).

fof(f55,plain,
    ( spl1_3
  <=> v1_relat_1(k2_funct_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_3])])).

fof(f66,plain,
    ( ~ spl1_3
    | spl1_5 ),
    inference(avatar_split_clause,[],[f62,f64,f55])).

fof(f62,plain,(
    ! [X1] :
      ( k1_relat_1(sK0) = k2_relat_1(k5_relat_1(X1,k2_funct_1(sK0)))
      | ~ r1_tarski(k2_relat_1(sK0),k2_relat_1(X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(k2_funct_1(sK0)) ) ),
    inference(forward_demodulation,[],[f53,f51])).

fof(f51,plain,(
    k1_relat_1(sK0) = k2_relat_1(k2_funct_1(sK0)) ),
    inference(subsumption_resolution,[],[f50,f22])).

fof(f50,plain,
    ( k1_relat_1(sK0) = k2_relat_1(k2_funct_1(sK0))
    | ~ v1_relat_1(sK0) ),
    inference(subsumption_resolution,[],[f47,f23])).

fof(f47,plain,
    ( k1_relat_1(sK0) = k2_relat_1(k2_funct_1(sK0))
    | ~ v1_funct_1(sK0)
    | ~ v1_relat_1(sK0) ),
    inference(resolution,[],[f24,f29])).

fof(f29,plain,(
    ! [X0] :
      ( ~ v2_funct_1(X0)
      | k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
          & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_funct_1)).

fof(f24,plain,(
    v2_funct_1(sK0) ),
    inference(cnf_transformation,[],[f19])).

fof(f53,plain,(
    ! [X1] :
      ( ~ r1_tarski(k2_relat_1(sK0),k2_relat_1(X1))
      | k2_relat_1(k2_funct_1(sK0)) = k2_relat_1(k5_relat_1(X1,k2_funct_1(sK0)))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(k2_funct_1(sK0)) ) ),
    inference(superposition,[],[f26,f49])).

fof(f49,plain,(
    k2_relat_1(sK0) = k1_relat_1(k2_funct_1(sK0)) ),
    inference(subsumption_resolution,[],[f48,f22])).

fof(f48,plain,
    ( k2_relat_1(sK0) = k1_relat_1(k2_funct_1(sK0))
    | ~ v1_relat_1(sK0) ),
    inference(subsumption_resolution,[],[f46,f23])).

fof(f46,plain,
    ( k2_relat_1(sK0) = k1_relat_1(k2_funct_1(sK0))
    | ~ v1_funct_1(sK0)
    | ~ v1_relat_1(sK0) ),
    inference(resolution,[],[f24,f28])).

fof(f28,plain,(
    ! [X0] :
      ( ~ v2_funct_1(X0)
      | k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k1_relat_1(X0),k2_relat_1(X1))
      | k2_relat_1(X0) = k2_relat_1(k5_relat_1(X1,X0))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_relat_1(X0) = k2_relat_1(k5_relat_1(X1,X0))
          | ~ r1_tarski(k1_relat_1(X0),k2_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_relat_1(X0) = k2_relat_1(k5_relat_1(X1,X0))
          | ~ r1_tarski(k1_relat_1(X0),k2_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ( r1_tarski(k1_relat_1(X0),k2_relat_1(X1))
           => k2_relat_1(X0) = k2_relat_1(k5_relat_1(X1,X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_relat_1)).

fof(f61,plain,
    ( ~ spl1_3
    | spl1_4 ),
    inference(avatar_split_clause,[],[f52,f59,f55])).

fof(f52,plain,(
    ! [X0] :
      ( ~ r1_tarski(k2_relat_1(X0),k2_relat_1(sK0))
      | k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,k2_funct_1(sK0)))
      | ~ v1_relat_1(k2_funct_1(sK0))
      | ~ v1_relat_1(X0) ) ),
    inference(superposition,[],[f27,f49])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k2_relat_1(X0),k1_relat_1(X1))
      | k1_relat_1(k5_relat_1(X0,X1)) = k1_relat_1(X0)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_relat_1(k5_relat_1(X0,X1)) = k1_relat_1(X0)
          | ~ r1_tarski(k2_relat_1(X0),k1_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_relat_1(k5_relat_1(X0,X1)) = k1_relat_1(X0)
          | ~ r1_tarski(k2_relat_1(X0),k1_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ( r1_tarski(k2_relat_1(X0),k1_relat_1(X1))
           => k1_relat_1(k5_relat_1(X0,X1)) = k1_relat_1(X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_relat_1)).

fof(f45,plain,
    ( ~ spl1_1
    | ~ spl1_2 ),
    inference(avatar_split_clause,[],[f25,f42,f38])).

fof(f25,plain,
    ( k1_relat_1(sK0) != k2_relat_1(k5_relat_1(sK0,k2_funct_1(sK0)))
    | k1_relat_1(sK0) != k1_relat_1(k5_relat_1(sK0,k2_funct_1(sK0))) ),
    inference(cnf_transformation,[],[f19])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 17:02:53 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.48  % (26496)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 0.21/0.48  % (26496)Refutation found. Thanks to Tanya!
% 0.21/0.48  % SZS status Theorem for theBenchmark
% 0.21/0.49  % (26505)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.21/0.49  % SZS output start Proof for theBenchmark
% 0.21/0.49  fof(f131,plain,(
% 0.21/0.49    $false),
% 0.21/0.49    inference(avatar_sat_refutation,[],[f45,f61,f66,f70,f97,f120])).
% 0.21/0.49  fof(f120,plain,(
% 0.21/0.49    spl1_2 | ~spl1_5),
% 0.21/0.49    inference(avatar_contradiction_clause,[],[f119])).
% 0.21/0.49  fof(f119,plain,(
% 0.21/0.49    $false | (spl1_2 | ~spl1_5)),
% 0.21/0.49    inference(subsumption_resolution,[],[f118,f44])).
% 0.21/0.49  fof(f44,plain,(
% 0.21/0.49    k1_relat_1(sK0) != k2_relat_1(k5_relat_1(sK0,k2_funct_1(sK0))) | spl1_2),
% 0.21/0.49    inference(avatar_component_clause,[],[f42])).
% 0.21/0.49  fof(f42,plain,(
% 0.21/0.49    spl1_2 <=> k1_relat_1(sK0) = k2_relat_1(k5_relat_1(sK0,k2_funct_1(sK0)))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl1_2])])).
% 0.21/0.49  fof(f118,plain,(
% 0.21/0.49    k1_relat_1(sK0) = k2_relat_1(k5_relat_1(sK0,k2_funct_1(sK0))) | ~spl1_5),
% 0.21/0.49    inference(subsumption_resolution,[],[f113,f22])).
% 0.21/0.49  fof(f22,plain,(
% 0.21/0.49    v1_relat_1(sK0)),
% 0.21/0.49    inference(cnf_transformation,[],[f19])).
% 0.21/0.49  fof(f19,plain,(
% 0.21/0.49    (k1_relat_1(sK0) != k2_relat_1(k5_relat_1(sK0,k2_funct_1(sK0))) | k1_relat_1(sK0) != k1_relat_1(k5_relat_1(sK0,k2_funct_1(sK0)))) & v2_funct_1(sK0) & v1_funct_1(sK0) & v1_relat_1(sK0)),
% 0.21/0.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f9,f18])).
% 0.21/0.49  fof(f18,plain,(
% 0.21/0.49    ? [X0] : ((k1_relat_1(X0) != k2_relat_1(k5_relat_1(X0,k2_funct_1(X0))) | k1_relat_1(X0) != k1_relat_1(k5_relat_1(X0,k2_funct_1(X0)))) & v2_funct_1(X0) & v1_funct_1(X0) & v1_relat_1(X0)) => ((k1_relat_1(sK0) != k2_relat_1(k5_relat_1(sK0,k2_funct_1(sK0))) | k1_relat_1(sK0) != k1_relat_1(k5_relat_1(sK0,k2_funct_1(sK0)))) & v2_funct_1(sK0) & v1_funct_1(sK0) & v1_relat_1(sK0))),
% 0.21/0.49    introduced(choice_axiom,[])).
% 0.21/0.49  fof(f9,plain,(
% 0.21/0.49    ? [X0] : ((k1_relat_1(X0) != k2_relat_1(k5_relat_1(X0,k2_funct_1(X0))) | k1_relat_1(X0) != k1_relat_1(k5_relat_1(X0,k2_funct_1(X0)))) & v2_funct_1(X0) & v1_funct_1(X0) & v1_relat_1(X0))),
% 0.21/0.49    inference(flattening,[],[f8])).
% 0.21/0.49  fof(f8,plain,(
% 0.21/0.49    ? [X0] : (((k1_relat_1(X0) != k2_relat_1(k5_relat_1(X0,k2_funct_1(X0))) | k1_relat_1(X0) != k1_relat_1(k5_relat_1(X0,k2_funct_1(X0)))) & v2_funct_1(X0)) & (v1_funct_1(X0) & v1_relat_1(X0)))),
% 0.21/0.49    inference(ennf_transformation,[],[f7])).
% 0.21/0.49  fof(f7,negated_conjecture,(
% 0.21/0.49    ~! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k1_relat_1(X0) = k2_relat_1(k5_relat_1(X0,k2_funct_1(X0))) & k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,k2_funct_1(X0))))))),
% 0.21/0.49    inference(negated_conjecture,[],[f6])).
% 0.21/0.49  fof(f6,conjecture,(
% 0.21/0.49    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k1_relat_1(X0) = k2_relat_1(k5_relat_1(X0,k2_funct_1(X0))) & k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,k2_funct_1(X0))))))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t58_funct_1)).
% 0.21/0.49  fof(f113,plain,(
% 0.21/0.49    ~v1_relat_1(sK0) | k1_relat_1(sK0) = k2_relat_1(k5_relat_1(sK0,k2_funct_1(sK0))) | ~spl1_5),
% 0.21/0.49    inference(resolution,[],[f65,f35])).
% 0.21/0.49  fof(f35,plain,(
% 0.21/0.49    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 0.21/0.49    inference(equality_resolution,[],[f33])).
% 0.21/0.49  fof(f33,plain,(
% 0.21/0.49    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 0.21/0.49    inference(cnf_transformation,[],[f21])).
% 0.21/0.49  fof(f21,plain,(
% 0.21/0.49    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.21/0.49    inference(flattening,[],[f20])).
% 0.21/0.49  fof(f20,plain,(
% 0.21/0.49    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.21/0.49    inference(nnf_transformation,[],[f1])).
% 0.21/0.49  fof(f1,axiom,(
% 0.21/0.49    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.21/0.49  fof(f65,plain,(
% 0.21/0.49    ( ! [X1] : (~r1_tarski(k2_relat_1(sK0),k2_relat_1(X1)) | ~v1_relat_1(X1) | k1_relat_1(sK0) = k2_relat_1(k5_relat_1(X1,k2_funct_1(sK0)))) ) | ~spl1_5),
% 0.21/0.49    inference(avatar_component_clause,[],[f64])).
% 0.21/0.49  fof(f64,plain,(
% 0.21/0.49    spl1_5 <=> ! [X1] : (k1_relat_1(sK0) = k2_relat_1(k5_relat_1(X1,k2_funct_1(sK0))) | ~v1_relat_1(X1) | ~r1_tarski(k2_relat_1(sK0),k2_relat_1(X1)))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl1_5])])).
% 0.21/0.49  fof(f97,plain,(
% 0.21/0.49    spl1_1 | ~spl1_4),
% 0.21/0.49    inference(avatar_split_clause,[],[f79,f59,f38])).
% 0.21/0.49  fof(f38,plain,(
% 0.21/0.49    spl1_1 <=> k1_relat_1(sK0) = k1_relat_1(k5_relat_1(sK0,k2_funct_1(sK0)))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl1_1])])).
% 0.21/0.49  fof(f59,plain,(
% 0.21/0.49    spl1_4 <=> ! [X0] : (~r1_tarski(k2_relat_1(X0),k2_relat_1(sK0)) | ~v1_relat_1(X0) | k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,k2_funct_1(sK0))))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl1_4])])).
% 0.21/0.49  fof(f79,plain,(
% 0.21/0.49    k1_relat_1(sK0) = k1_relat_1(k5_relat_1(sK0,k2_funct_1(sK0))) | ~spl1_4),
% 0.21/0.49    inference(subsumption_resolution,[],[f76,f22])).
% 0.21/0.49  fof(f76,plain,(
% 0.21/0.49    ~v1_relat_1(sK0) | k1_relat_1(sK0) = k1_relat_1(k5_relat_1(sK0,k2_funct_1(sK0))) | ~spl1_4),
% 0.21/0.49    inference(resolution,[],[f60,f36])).
% 0.21/0.49  fof(f36,plain,(
% 0.21/0.49    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 0.21/0.49    inference(equality_resolution,[],[f32])).
% 0.21/0.49  fof(f32,plain,(
% 0.21/0.49    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 0.21/0.49    inference(cnf_transformation,[],[f21])).
% 0.21/0.49  fof(f60,plain,(
% 0.21/0.49    ( ! [X0] : (~r1_tarski(k2_relat_1(X0),k2_relat_1(sK0)) | ~v1_relat_1(X0) | k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,k2_funct_1(sK0)))) ) | ~spl1_4),
% 0.21/0.49    inference(avatar_component_clause,[],[f59])).
% 0.21/0.49  fof(f70,plain,(
% 0.21/0.49    spl1_3),
% 0.21/0.49    inference(avatar_contradiction_clause,[],[f69])).
% 0.21/0.49  fof(f69,plain,(
% 0.21/0.49    $false | spl1_3),
% 0.21/0.49    inference(subsumption_resolution,[],[f68,f22])).
% 0.21/0.49  fof(f68,plain,(
% 0.21/0.49    ~v1_relat_1(sK0) | spl1_3),
% 0.21/0.49    inference(subsumption_resolution,[],[f67,f23])).
% 0.21/0.49  fof(f23,plain,(
% 0.21/0.49    v1_funct_1(sK0)),
% 0.21/0.49    inference(cnf_transformation,[],[f19])).
% 0.21/0.49  fof(f67,plain,(
% 0.21/0.49    ~v1_funct_1(sK0) | ~v1_relat_1(sK0) | spl1_3),
% 0.21/0.49    inference(resolution,[],[f57,f30])).
% 0.21/0.49  fof(f30,plain,(
% 0.21/0.49    ( ! [X0] : (v1_relat_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f17])).
% 0.21/0.49  fof(f17,plain,(
% 0.21/0.49    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.21/0.49    inference(flattening,[],[f16])).
% 0.21/0.49  fof(f16,plain,(
% 0.21/0.49    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.21/0.49    inference(ennf_transformation,[],[f4])).
% 0.21/0.49  fof(f4,axiom,(
% 0.21/0.49    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_funct_1)).
% 0.21/0.49  fof(f57,plain,(
% 0.21/0.49    ~v1_relat_1(k2_funct_1(sK0)) | spl1_3),
% 0.21/0.49    inference(avatar_component_clause,[],[f55])).
% 0.21/0.49  fof(f55,plain,(
% 0.21/0.49    spl1_3 <=> v1_relat_1(k2_funct_1(sK0))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl1_3])])).
% 0.21/0.49  fof(f66,plain,(
% 0.21/0.49    ~spl1_3 | spl1_5),
% 0.21/0.49    inference(avatar_split_clause,[],[f62,f64,f55])).
% 0.21/0.49  fof(f62,plain,(
% 0.21/0.49    ( ! [X1] : (k1_relat_1(sK0) = k2_relat_1(k5_relat_1(X1,k2_funct_1(sK0))) | ~r1_tarski(k2_relat_1(sK0),k2_relat_1(X1)) | ~v1_relat_1(X1) | ~v1_relat_1(k2_funct_1(sK0))) )),
% 0.21/0.49    inference(forward_demodulation,[],[f53,f51])).
% 0.21/0.49  fof(f51,plain,(
% 0.21/0.49    k1_relat_1(sK0) = k2_relat_1(k2_funct_1(sK0))),
% 0.21/0.49    inference(subsumption_resolution,[],[f50,f22])).
% 0.21/0.49  fof(f50,plain,(
% 0.21/0.49    k1_relat_1(sK0) = k2_relat_1(k2_funct_1(sK0)) | ~v1_relat_1(sK0)),
% 0.21/0.49    inference(subsumption_resolution,[],[f47,f23])).
% 0.21/0.49  fof(f47,plain,(
% 0.21/0.49    k1_relat_1(sK0) = k2_relat_1(k2_funct_1(sK0)) | ~v1_funct_1(sK0) | ~v1_relat_1(sK0)),
% 0.21/0.49    inference(resolution,[],[f24,f29])).
% 0.21/0.49  fof(f29,plain,(
% 0.21/0.49    ( ! [X0] : (~v2_funct_1(X0) | k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f15])).
% 0.21/0.49  fof(f15,plain,(
% 0.21/0.49    ! [X0] : ((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.21/0.49    inference(flattening,[],[f14])).
% 0.21/0.49  fof(f14,plain,(
% 0.21/0.49    ! [X0] : (((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.21/0.49    inference(ennf_transformation,[],[f5])).
% 0.21/0.49  fof(f5,axiom,(
% 0.21/0.49    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)))))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_funct_1)).
% 0.21/0.49  fof(f24,plain,(
% 0.21/0.49    v2_funct_1(sK0)),
% 0.21/0.49    inference(cnf_transformation,[],[f19])).
% 0.21/0.49  fof(f53,plain,(
% 0.21/0.49    ( ! [X1] : (~r1_tarski(k2_relat_1(sK0),k2_relat_1(X1)) | k2_relat_1(k2_funct_1(sK0)) = k2_relat_1(k5_relat_1(X1,k2_funct_1(sK0))) | ~v1_relat_1(X1) | ~v1_relat_1(k2_funct_1(sK0))) )),
% 0.21/0.49    inference(superposition,[],[f26,f49])).
% 0.21/0.49  fof(f49,plain,(
% 0.21/0.49    k2_relat_1(sK0) = k1_relat_1(k2_funct_1(sK0))),
% 0.21/0.49    inference(subsumption_resolution,[],[f48,f22])).
% 0.21/0.49  fof(f48,plain,(
% 0.21/0.49    k2_relat_1(sK0) = k1_relat_1(k2_funct_1(sK0)) | ~v1_relat_1(sK0)),
% 0.21/0.49    inference(subsumption_resolution,[],[f46,f23])).
% 0.21/0.49  fof(f46,plain,(
% 0.21/0.49    k2_relat_1(sK0) = k1_relat_1(k2_funct_1(sK0)) | ~v1_funct_1(sK0) | ~v1_relat_1(sK0)),
% 0.21/0.49    inference(resolution,[],[f24,f28])).
% 0.21/0.49  fof(f28,plain,(
% 0.21/0.49    ( ! [X0] : (~v2_funct_1(X0) | k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f15])).
% 0.21/0.49  fof(f26,plain,(
% 0.21/0.49    ( ! [X0,X1] : (~r1_tarski(k1_relat_1(X0),k2_relat_1(X1)) | k2_relat_1(X0) = k2_relat_1(k5_relat_1(X1,X0)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f11])).
% 0.21/0.49  fof(f11,plain,(
% 0.21/0.49    ! [X0] : (! [X1] : (k2_relat_1(X0) = k2_relat_1(k5_relat_1(X1,X0)) | ~r1_tarski(k1_relat_1(X0),k2_relat_1(X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.21/0.49    inference(flattening,[],[f10])).
% 0.21/0.49  fof(f10,plain,(
% 0.21/0.49    ! [X0] : (! [X1] : ((k2_relat_1(X0) = k2_relat_1(k5_relat_1(X1,X0)) | ~r1_tarski(k1_relat_1(X0),k2_relat_1(X1))) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.21/0.49    inference(ennf_transformation,[],[f3])).
% 0.21/0.49  fof(f3,axiom,(
% 0.21/0.49    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => (r1_tarski(k1_relat_1(X0),k2_relat_1(X1)) => k2_relat_1(X0) = k2_relat_1(k5_relat_1(X1,X0)))))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_relat_1)).
% 0.21/0.49  fof(f61,plain,(
% 0.21/0.49    ~spl1_3 | spl1_4),
% 0.21/0.49    inference(avatar_split_clause,[],[f52,f59,f55])).
% 0.21/0.49  fof(f52,plain,(
% 0.21/0.49    ( ! [X0] : (~r1_tarski(k2_relat_1(X0),k2_relat_1(sK0)) | k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,k2_funct_1(sK0))) | ~v1_relat_1(k2_funct_1(sK0)) | ~v1_relat_1(X0)) )),
% 0.21/0.49    inference(superposition,[],[f27,f49])).
% 0.21/0.49  fof(f27,plain,(
% 0.21/0.49    ( ! [X0,X1] : (~r1_tarski(k2_relat_1(X0),k1_relat_1(X1)) | k1_relat_1(k5_relat_1(X0,X1)) = k1_relat_1(X0) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f13])).
% 0.21/0.49  fof(f13,plain,(
% 0.21/0.49    ! [X0] : (! [X1] : (k1_relat_1(k5_relat_1(X0,X1)) = k1_relat_1(X0) | ~r1_tarski(k2_relat_1(X0),k1_relat_1(X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.21/0.49    inference(flattening,[],[f12])).
% 0.21/0.49  fof(f12,plain,(
% 0.21/0.49    ! [X0] : (! [X1] : ((k1_relat_1(k5_relat_1(X0,X1)) = k1_relat_1(X0) | ~r1_tarski(k2_relat_1(X0),k1_relat_1(X1))) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.21/0.49    inference(ennf_transformation,[],[f2])).
% 0.21/0.49  fof(f2,axiom,(
% 0.21/0.49    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => (r1_tarski(k2_relat_1(X0),k1_relat_1(X1)) => k1_relat_1(k5_relat_1(X0,X1)) = k1_relat_1(X0))))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_relat_1)).
% 0.21/0.49  fof(f45,plain,(
% 0.21/0.49    ~spl1_1 | ~spl1_2),
% 0.21/0.49    inference(avatar_split_clause,[],[f25,f42,f38])).
% 0.21/0.49  fof(f25,plain,(
% 0.21/0.49    k1_relat_1(sK0) != k2_relat_1(k5_relat_1(sK0,k2_funct_1(sK0))) | k1_relat_1(sK0) != k1_relat_1(k5_relat_1(sK0,k2_funct_1(sK0)))),
% 0.21/0.49    inference(cnf_transformation,[],[f19])).
% 0.21/0.49  % SZS output end Proof for theBenchmark
% 0.21/0.49  % (26496)------------------------------
% 0.21/0.49  % (26496)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.49  % (26496)Termination reason: Refutation
% 0.21/0.49  
% 0.21/0.49  % (26496)Memory used [KB]: 10618
% 0.21/0.49  % (26496)Time elapsed: 0.075 s
% 0.21/0.49  % (26496)------------------------------
% 0.21/0.49  % (26496)------------------------------
% 0.21/0.50  % (26485)Success in time 0.137 s
%------------------------------------------------------------------------------
