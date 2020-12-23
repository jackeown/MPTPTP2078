%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:55:46 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   66 ( 115 expanded)
%              Number of leaves         :   14 (  32 expanded)
%              Depth                    :   20
%              Number of atoms          :  212 ( 498 expanded)
%              Number of equality atoms :   45 (  85 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f96,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f63,f69,f91,f93,f95])).

fof(f95,plain,(
    spl2_4 ),
    inference(avatar_contradiction_clause,[],[f94])).

fof(f94,plain,
    ( $false
    | spl2_4 ),
    inference(subsumption_resolution,[],[f62,f70])).

fof(f70,plain,(
    v5_ordinal1(sK0) ),
    inference(resolution,[],[f39,f31])).

fof(f31,plain,(
    v3_ordinal1(k1_relat_1(sK0)) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,
    ( ( ~ v5_ordinal1(sK0)
      | ~ v1_funct_1(sK0)
      | ~ v5_relat_1(sK0,k2_relat_1(sK0))
      | ~ v1_relat_1(sK0) )
    & v3_ordinal1(k1_relat_1(sK0))
    & v1_funct_1(sK0)
    & v1_relat_1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f14,f21])).

fof(f21,plain,
    ( ? [X0] :
        ( ( ~ v5_ordinal1(X0)
          | ~ v1_funct_1(X0)
          | ~ v5_relat_1(X0,k2_relat_1(X0))
          | ~ v1_relat_1(X0) )
        & v3_ordinal1(k1_relat_1(X0))
        & v1_funct_1(X0)
        & v1_relat_1(X0) )
   => ( ( ~ v5_ordinal1(sK0)
        | ~ v1_funct_1(sK0)
        | ~ v5_relat_1(sK0,k2_relat_1(sK0))
        | ~ v1_relat_1(sK0) )
      & v3_ordinal1(k1_relat_1(sK0))
      & v1_funct_1(sK0)
      & v1_relat_1(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f14,plain,(
    ? [X0] :
      ( ( ~ v5_ordinal1(X0)
        | ~ v1_funct_1(X0)
        | ~ v5_relat_1(X0,k2_relat_1(X0))
        | ~ v1_relat_1(X0) )
      & v3_ordinal1(k1_relat_1(X0))
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ? [X0] :
      ( ( ~ v5_ordinal1(X0)
        | ~ v1_funct_1(X0)
        | ~ v5_relat_1(X0,k2_relat_1(X0))
        | ~ v1_relat_1(X0) )
      & v3_ordinal1(k1_relat_1(X0))
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,negated_conjecture,(
    ~ ! [X0] :
        ( ( v1_funct_1(X0)
          & v1_relat_1(X0) )
       => ( v3_ordinal1(k1_relat_1(X0))
         => ( v5_ordinal1(X0)
            & v1_funct_1(X0)
            & v5_relat_1(X0,k2_relat_1(X0))
            & v1_relat_1(X0) ) ) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f9,conjecture,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v3_ordinal1(k1_relat_1(X0))
       => ( v5_ordinal1(X0)
          & v1_funct_1(X0)
          & v5_relat_1(X0,k2_relat_1(X0))
          & v1_relat_1(X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_ordinal1)).

fof(f39,plain,(
    ! [X0] :
      ( ~ v3_ordinal1(k1_relat_1(X0))
      | v5_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( v5_ordinal1(X0)
      | ~ v3_ordinal1(k1_relat_1(X0)) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0] :
      ( v3_ordinal1(k1_relat_1(X0))
     => v5_ordinal1(X0) ) ),
    inference(unused_predicate_definition_removal,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( v5_ordinal1(X0)
    <=> v3_ordinal1(k1_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_ordinal1)).

fof(f62,plain,
    ( ~ v5_ordinal1(sK0)
    | spl2_4 ),
    inference(avatar_component_clause,[],[f61])).

fof(f61,plain,
    ( spl2_4
  <=> v5_ordinal1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).

fof(f93,plain,(
    spl2_3 ),
    inference(avatar_contradiction_clause,[],[f92])).

fof(f92,plain,
    ( $false
    | spl2_3 ),
    inference(subsumption_resolution,[],[f59,f30])).

fof(f30,plain,(
    v1_funct_1(sK0) ),
    inference(cnf_transformation,[],[f22])).

fof(f59,plain,
    ( ~ v1_funct_1(sK0)
    | spl2_3 ),
    inference(avatar_component_clause,[],[f58])).

fof(f58,plain,
    ( spl2_3
  <=> v1_funct_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).

fof(f91,plain,(
    spl2_2 ),
    inference(avatar_contradiction_clause,[],[f90])).

fof(f90,plain,
    ( $false
    | spl2_2 ),
    inference(subsumption_resolution,[],[f89,f29])).

fof(f29,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f22])).

fof(f89,plain,
    ( ~ v1_relat_1(sK0)
    | spl2_2 ),
    inference(resolution,[],[f87,f56])).

fof(f56,plain,
    ( ~ v5_relat_1(sK0,k2_relat_1(sK0))
    | spl2_2 ),
    inference(avatar_component_clause,[],[f55])).

fof(f55,plain,
    ( spl2_2
  <=> v5_relat_1(sK0,k2_relat_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f87,plain,(
    ! [X0] :
      ( v5_relat_1(X0,k2_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(resolution,[],[f80,f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k2_relat_1(X1),X0)
      | v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( ( v5_relat_1(X1,X0)
          | ~ r1_tarski(k2_relat_1(X1),X0) )
        & ( r1_tarski(k2_relat_1(X1),X0)
          | ~ v5_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).

fof(f80,plain,(
    ! [X0] : r1_tarski(X0,X0) ),
    inference(forward_demodulation,[],[f79,f67])).

fof(f67,plain,(
    ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(subsumption_resolution,[],[f66,f33])).

fof(f33,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_relat_1)).

fof(f66,plain,(
    ! [X0] :
      ( k1_relat_1(k6_relat_1(X0)) = X0
      | ~ v1_relat_1(k6_relat_1(X0)) ) ),
    inference(subsumption_resolution,[],[f50,f35])).

fof(f35,plain,(
    ! [X0] : v1_funct_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( v1_funct_1(k6_relat_1(X0))
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc3_funct_1)).

fof(f50,plain,(
    ! [X0] :
      ( k1_relat_1(k6_relat_1(X0)) = X0
      | ~ v1_funct_1(k6_relat_1(X0))
      | ~ v1_relat_1(k6_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( k1_relat_1(X1) = X0
      | k6_relat_1(X0) != X1
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( ( k6_relat_1(X0) = X1
          | ( sK1(X0,X1) != k1_funct_1(X1,sK1(X0,X1))
            & r2_hidden(sK1(X0,X1),X0) )
          | k1_relat_1(X1) != X0 )
        & ( ( ! [X3] :
                ( k1_funct_1(X1,X3) = X3
                | ~ r2_hidden(X3,X0) )
            & k1_relat_1(X1) = X0 )
          | k6_relat_1(X0) != X1 ) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f26,f27])).

fof(f27,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( k1_funct_1(X1,X2) != X2
          & r2_hidden(X2,X0) )
     => ( sK1(X0,X1) != k1_funct_1(X1,sK1(X0,X1))
        & r2_hidden(sK1(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( ( k6_relat_1(X0) = X1
          | ? [X2] :
              ( k1_funct_1(X1,X2) != X2
              & r2_hidden(X2,X0) )
          | k1_relat_1(X1) != X0 )
        & ( ( ! [X3] :
                ( k1_funct_1(X1,X3) = X3
                | ~ r2_hidden(X3,X0) )
            & k1_relat_1(X1) = X0 )
          | k6_relat_1(X0) != X1 ) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(rectify,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( ( k6_relat_1(X0) = X1
          | ? [X2] :
              ( k1_funct_1(X1,X2) != X2
              & r2_hidden(X2,X0) )
          | k1_relat_1(X1) != X0 )
        & ( ( ! [X2] :
                ( k1_funct_1(X1,X2) = X2
                | ~ r2_hidden(X2,X0) )
            & k1_relat_1(X1) = X0 )
          | k6_relat_1(X0) != X1 ) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( ( k6_relat_1(X0) = X1
          | ? [X2] :
              ( k1_funct_1(X1,X2) != X2
              & r2_hidden(X2,X0) )
          | k1_relat_1(X1) != X0 )
        & ( ( ! [X2] :
                ( k1_funct_1(X1,X2) = X2
                | ~ r2_hidden(X2,X0) )
            & k1_relat_1(X1) = X0 )
          | k6_relat_1(X0) != X1 ) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ( k6_relat_1(X0) = X1
      <=> ( ! [X2] :
              ( k1_funct_1(X1,X2) = X2
              | ~ r2_hidden(X2,X0) )
          & k1_relat_1(X1) = X0 ) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ( k6_relat_1(X0) = X1
      <=> ( ! [X2] :
              ( k1_funct_1(X1,X2) = X2
              | ~ r2_hidden(X2,X0) )
          & k1_relat_1(X1) = X0 ) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( k6_relat_1(X0) = X1
      <=> ( ! [X2] :
              ( r2_hidden(X2,X0)
             => k1_funct_1(X1,X2) = X2 )
          & k1_relat_1(X1) = X0 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t34_funct_1)).

fof(f79,plain,(
    ! [X0] : r1_tarski(k1_relat_1(k6_relat_1(X0)),X0) ),
    inference(subsumption_resolution,[],[f78,f33])).

fof(f78,plain,(
    ! [X0] :
      ( r1_tarski(k1_relat_1(k6_relat_1(X0)),X0)
      | ~ v1_relat_1(k6_relat_1(X0)) ) ),
    inference(superposition,[],[f40,f73])).

fof(f73,plain,(
    ! [X0] : k6_relat_1(X0) = k7_relat_1(k6_relat_1(X0),X0) ),
    inference(subsumption_resolution,[],[f72,f33])).

fof(f72,plain,(
    ! [X0] :
      ( k6_relat_1(X0) = k7_relat_1(k6_relat_1(X0),X0)
      | ~ v1_relat_1(k6_relat_1(X0)) ) ),
    inference(superposition,[],[f38,f67])).

fof(f38,plain,(
    ! [X0] :
      ( k7_relat_1(X0,k1_relat_1(X0)) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( k7_relat_1(X0,k1_relat_1(X0)) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k7_relat_1(X0,k1_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_relat_1)).

fof(f40,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t87_relat_1)).

fof(f69,plain,(
    spl2_1 ),
    inference(avatar_contradiction_clause,[],[f68])).

fof(f68,plain,
    ( $false
    | spl2_1 ),
    inference(subsumption_resolution,[],[f53,f29])).

fof(f53,plain,
    ( ~ v1_relat_1(sK0)
    | spl2_1 ),
    inference(avatar_component_clause,[],[f52])).

fof(f52,plain,
    ( spl2_1
  <=> v1_relat_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f63,plain,
    ( ~ spl2_1
    | ~ spl2_2
    | ~ spl2_3
    | ~ spl2_4 ),
    inference(avatar_split_clause,[],[f32,f61,f58,f55,f52])).

fof(f32,plain,
    ( ~ v5_ordinal1(sK0)
    | ~ v1_funct_1(sK0)
    | ~ v5_relat_1(sK0,k2_relat_1(sK0))
    | ~ v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f22])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n025.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 19:03:36 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.22/0.47  % (3626)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.22/0.47  % (3627)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.22/0.47  % (3629)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.22/0.48  % (3627)Refutation not found, incomplete strategy% (3627)------------------------------
% 0.22/0.48  % (3627)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.48  % (3627)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.48  
% 0.22/0.48  % (3627)Memory used [KB]: 10618
% 0.22/0.48  % (3627)Time elapsed: 0.051 s
% 0.22/0.48  % (3627)------------------------------
% 0.22/0.48  % (3627)------------------------------
% 0.22/0.48  % (3643)dis+11_3_add=off:afr=on:afp=40000:afq=2.0:amm=sco:anc=none:cond=on:nm=16:nwc=1:ss=axioms:st=5.0:sos=all:sp=reverse_arity_169 on theBenchmark
% 0.22/0.49  % (3624)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.22/0.49  % (3637)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.22/0.49  % (3640)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
% 0.22/0.49  % (3626)Refutation found. Thanks to Tanya!
% 0.22/0.49  % SZS status Theorem for theBenchmark
% 0.22/0.49  % SZS output start Proof for theBenchmark
% 0.22/0.49  fof(f96,plain,(
% 0.22/0.49    $false),
% 0.22/0.49    inference(avatar_sat_refutation,[],[f63,f69,f91,f93,f95])).
% 0.22/0.49  fof(f95,plain,(
% 0.22/0.49    spl2_4),
% 0.22/0.49    inference(avatar_contradiction_clause,[],[f94])).
% 0.22/0.49  fof(f94,plain,(
% 0.22/0.49    $false | spl2_4),
% 0.22/0.49    inference(subsumption_resolution,[],[f62,f70])).
% 0.22/0.49  fof(f70,plain,(
% 0.22/0.49    v5_ordinal1(sK0)),
% 0.22/0.49    inference(resolution,[],[f39,f31])).
% 0.22/0.49  fof(f31,plain,(
% 0.22/0.49    v3_ordinal1(k1_relat_1(sK0))),
% 0.22/0.49    inference(cnf_transformation,[],[f22])).
% 0.22/0.49  fof(f22,plain,(
% 0.22/0.49    (~v5_ordinal1(sK0) | ~v1_funct_1(sK0) | ~v5_relat_1(sK0,k2_relat_1(sK0)) | ~v1_relat_1(sK0)) & v3_ordinal1(k1_relat_1(sK0)) & v1_funct_1(sK0) & v1_relat_1(sK0)),
% 0.22/0.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f14,f21])).
% 0.22/0.49  fof(f21,plain,(
% 0.22/0.49    ? [X0] : ((~v5_ordinal1(X0) | ~v1_funct_1(X0) | ~v5_relat_1(X0,k2_relat_1(X0)) | ~v1_relat_1(X0)) & v3_ordinal1(k1_relat_1(X0)) & v1_funct_1(X0) & v1_relat_1(X0)) => ((~v5_ordinal1(sK0) | ~v1_funct_1(sK0) | ~v5_relat_1(sK0,k2_relat_1(sK0)) | ~v1_relat_1(sK0)) & v3_ordinal1(k1_relat_1(sK0)) & v1_funct_1(sK0) & v1_relat_1(sK0))),
% 0.22/0.49    introduced(choice_axiom,[])).
% 0.22/0.49  fof(f14,plain,(
% 0.22/0.49    ? [X0] : ((~v5_ordinal1(X0) | ~v1_funct_1(X0) | ~v5_relat_1(X0,k2_relat_1(X0)) | ~v1_relat_1(X0)) & v3_ordinal1(k1_relat_1(X0)) & v1_funct_1(X0) & v1_relat_1(X0))),
% 0.22/0.49    inference(flattening,[],[f13])).
% 0.22/0.49  fof(f13,plain,(
% 0.22/0.49    ? [X0] : (((~v5_ordinal1(X0) | ~v1_funct_1(X0) | ~v5_relat_1(X0,k2_relat_1(X0)) | ~v1_relat_1(X0)) & v3_ordinal1(k1_relat_1(X0))) & (v1_funct_1(X0) & v1_relat_1(X0)))),
% 0.22/0.49    inference(ennf_transformation,[],[f10])).
% 0.22/0.49  fof(f10,negated_conjecture,(
% 0.22/0.49    ~! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v3_ordinal1(k1_relat_1(X0)) => (v5_ordinal1(X0) & v1_funct_1(X0) & v5_relat_1(X0,k2_relat_1(X0)) & v1_relat_1(X0))))),
% 0.22/0.49    inference(negated_conjecture,[],[f9])).
% 0.22/0.49  fof(f9,conjecture,(
% 0.22/0.49    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v3_ordinal1(k1_relat_1(X0)) => (v5_ordinal1(X0) & v1_funct_1(X0) & v5_relat_1(X0,k2_relat_1(X0)) & v1_relat_1(X0))))),
% 0.22/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_ordinal1)).
% 0.22/0.49  fof(f39,plain,(
% 0.22/0.49    ( ! [X0] : (~v3_ordinal1(k1_relat_1(X0)) | v5_ordinal1(X0)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f16])).
% 0.22/0.49  fof(f16,plain,(
% 0.22/0.49    ! [X0] : (v5_ordinal1(X0) | ~v3_ordinal1(k1_relat_1(X0)))),
% 0.22/0.49    inference(ennf_transformation,[],[f11])).
% 0.22/0.49  fof(f11,plain,(
% 0.22/0.49    ! [X0] : (v3_ordinal1(k1_relat_1(X0)) => v5_ordinal1(X0))),
% 0.22/0.49    inference(unused_predicate_definition_removal,[],[f8])).
% 0.22/0.49  fof(f8,axiom,(
% 0.22/0.49    ! [X0] : (v5_ordinal1(X0) <=> v3_ordinal1(k1_relat_1(X0)))),
% 0.22/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_ordinal1)).
% 0.22/0.49  fof(f62,plain,(
% 0.22/0.49    ~v5_ordinal1(sK0) | spl2_4),
% 0.22/0.49    inference(avatar_component_clause,[],[f61])).
% 0.22/0.49  fof(f61,plain,(
% 0.22/0.49    spl2_4 <=> v5_ordinal1(sK0)),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).
% 0.22/0.49  fof(f93,plain,(
% 0.22/0.49    spl2_3),
% 0.22/0.49    inference(avatar_contradiction_clause,[],[f92])).
% 0.22/0.49  fof(f92,plain,(
% 0.22/0.49    $false | spl2_3),
% 0.22/0.49    inference(subsumption_resolution,[],[f59,f30])).
% 0.22/0.49  fof(f30,plain,(
% 0.22/0.49    v1_funct_1(sK0)),
% 0.22/0.49    inference(cnf_transformation,[],[f22])).
% 0.22/0.49  fof(f59,plain,(
% 0.22/0.49    ~v1_funct_1(sK0) | spl2_3),
% 0.22/0.49    inference(avatar_component_clause,[],[f58])).
% 0.22/0.49  fof(f58,plain,(
% 0.22/0.49    spl2_3 <=> v1_funct_1(sK0)),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).
% 0.22/0.49  fof(f91,plain,(
% 0.22/0.49    spl2_2),
% 0.22/0.49    inference(avatar_contradiction_clause,[],[f90])).
% 0.22/0.49  fof(f90,plain,(
% 0.22/0.49    $false | spl2_2),
% 0.22/0.49    inference(subsumption_resolution,[],[f89,f29])).
% 0.22/0.49  fof(f29,plain,(
% 0.22/0.49    v1_relat_1(sK0)),
% 0.22/0.49    inference(cnf_transformation,[],[f22])).
% 0.22/0.49  fof(f89,plain,(
% 0.22/0.49    ~v1_relat_1(sK0) | spl2_2),
% 0.22/0.49    inference(resolution,[],[f87,f56])).
% 0.22/0.49  fof(f56,plain,(
% 0.22/0.49    ~v5_relat_1(sK0,k2_relat_1(sK0)) | spl2_2),
% 0.22/0.49    inference(avatar_component_clause,[],[f55])).
% 0.22/0.49  fof(f55,plain,(
% 0.22/0.49    spl2_2 <=> v5_relat_1(sK0,k2_relat_1(sK0))),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 0.22/0.49  fof(f87,plain,(
% 0.22/0.49    ( ! [X0] : (v5_relat_1(X0,k2_relat_1(X0)) | ~v1_relat_1(X0)) )),
% 0.22/0.49    inference(resolution,[],[f80,f42])).
% 0.22/0.49  fof(f42,plain,(
% 0.22/0.49    ( ! [X0,X1] : (~r1_tarski(k2_relat_1(X1),X0) | v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f23])).
% 0.22/0.49  fof(f23,plain,(
% 0.22/0.49    ! [X0,X1] : (((v5_relat_1(X1,X0) | ~r1_tarski(k2_relat_1(X1),X0)) & (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 0.22/0.49    inference(nnf_transformation,[],[f18])).
% 0.22/0.49  fof(f18,plain,(
% 0.22/0.49    ! [X0,X1] : ((v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.22/0.49    inference(ennf_transformation,[],[f1])).
% 0.22/0.49  fof(f1,axiom,(
% 0.22/0.49    ! [X0,X1] : (v1_relat_1(X1) => (v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)))),
% 0.22/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).
% 0.22/0.49  fof(f80,plain,(
% 0.22/0.49    ( ! [X0] : (r1_tarski(X0,X0)) )),
% 0.22/0.49    inference(forward_demodulation,[],[f79,f67])).
% 0.22/0.49  fof(f67,plain,(
% 0.22/0.49    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = X0) )),
% 0.22/0.49    inference(subsumption_resolution,[],[f66,f33])).
% 0.22/0.49  fof(f33,plain,(
% 0.22/0.49    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 0.22/0.49    inference(cnf_transformation,[],[f2])).
% 0.22/0.49  fof(f2,axiom,(
% 0.22/0.49    ! [X0] : v1_relat_1(k6_relat_1(X0))),
% 0.22/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_relat_1)).
% 0.22/0.49  fof(f66,plain,(
% 0.22/0.49    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = X0 | ~v1_relat_1(k6_relat_1(X0))) )),
% 0.22/0.49    inference(subsumption_resolution,[],[f50,f35])).
% 0.22/0.49  fof(f35,plain,(
% 0.22/0.49    ( ! [X0] : (v1_funct_1(k6_relat_1(X0))) )),
% 0.22/0.49    inference(cnf_transformation,[],[f6])).
% 0.22/0.49  fof(f6,axiom,(
% 0.22/0.49    ! [X0] : (v1_funct_1(k6_relat_1(X0)) & v1_relat_1(k6_relat_1(X0)))),
% 0.22/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc3_funct_1)).
% 0.22/0.49  fof(f50,plain,(
% 0.22/0.49    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = X0 | ~v1_funct_1(k6_relat_1(X0)) | ~v1_relat_1(k6_relat_1(X0))) )),
% 0.22/0.49    inference(equality_resolution,[],[f43])).
% 0.22/0.49  fof(f43,plain,(
% 0.22/0.49    ( ! [X0,X1] : (k1_relat_1(X1) = X0 | k6_relat_1(X0) != X1 | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f28])).
% 0.22/0.49  fof(f28,plain,(
% 0.22/0.49    ! [X0,X1] : (((k6_relat_1(X0) = X1 | (sK1(X0,X1) != k1_funct_1(X1,sK1(X0,X1)) & r2_hidden(sK1(X0,X1),X0)) | k1_relat_1(X1) != X0) & ((! [X3] : (k1_funct_1(X1,X3) = X3 | ~r2_hidden(X3,X0)) & k1_relat_1(X1) = X0) | k6_relat_1(X0) != X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 0.22/0.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f26,f27])).
% 0.22/0.49  fof(f27,plain,(
% 0.22/0.49    ! [X1,X0] : (? [X2] : (k1_funct_1(X1,X2) != X2 & r2_hidden(X2,X0)) => (sK1(X0,X1) != k1_funct_1(X1,sK1(X0,X1)) & r2_hidden(sK1(X0,X1),X0)))),
% 0.22/0.49    introduced(choice_axiom,[])).
% 0.22/0.49  fof(f26,plain,(
% 0.22/0.49    ! [X0,X1] : (((k6_relat_1(X0) = X1 | ? [X2] : (k1_funct_1(X1,X2) != X2 & r2_hidden(X2,X0)) | k1_relat_1(X1) != X0) & ((! [X3] : (k1_funct_1(X1,X3) = X3 | ~r2_hidden(X3,X0)) & k1_relat_1(X1) = X0) | k6_relat_1(X0) != X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 0.22/0.49    inference(rectify,[],[f25])).
% 0.22/0.49  fof(f25,plain,(
% 0.22/0.49    ! [X0,X1] : (((k6_relat_1(X0) = X1 | ? [X2] : (k1_funct_1(X1,X2) != X2 & r2_hidden(X2,X0)) | k1_relat_1(X1) != X0) & ((! [X2] : (k1_funct_1(X1,X2) = X2 | ~r2_hidden(X2,X0)) & k1_relat_1(X1) = X0) | k6_relat_1(X0) != X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 0.22/0.49    inference(flattening,[],[f24])).
% 0.22/0.49  fof(f24,plain,(
% 0.22/0.49    ! [X0,X1] : (((k6_relat_1(X0) = X1 | (? [X2] : (k1_funct_1(X1,X2) != X2 & r2_hidden(X2,X0)) | k1_relat_1(X1) != X0)) & ((! [X2] : (k1_funct_1(X1,X2) = X2 | ~r2_hidden(X2,X0)) & k1_relat_1(X1) = X0) | k6_relat_1(X0) != X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 0.22/0.49    inference(nnf_transformation,[],[f20])).
% 0.22/0.49  fof(f20,plain,(
% 0.22/0.49    ! [X0,X1] : ((k6_relat_1(X0) = X1 <=> (! [X2] : (k1_funct_1(X1,X2) = X2 | ~r2_hidden(X2,X0)) & k1_relat_1(X1) = X0)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 0.22/0.49    inference(flattening,[],[f19])).
% 0.22/0.49  fof(f19,plain,(
% 0.22/0.49    ! [X0,X1] : ((k6_relat_1(X0) = X1 <=> (! [X2] : (k1_funct_1(X1,X2) = X2 | ~r2_hidden(X2,X0)) & k1_relat_1(X1) = X0)) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 0.22/0.49    inference(ennf_transformation,[],[f7])).
% 0.22/0.49  fof(f7,axiom,(
% 0.22/0.49    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (k6_relat_1(X0) = X1 <=> (! [X2] : (r2_hidden(X2,X0) => k1_funct_1(X1,X2) = X2) & k1_relat_1(X1) = X0)))),
% 0.22/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t34_funct_1)).
% 0.22/0.49  fof(f79,plain,(
% 0.22/0.49    ( ! [X0] : (r1_tarski(k1_relat_1(k6_relat_1(X0)),X0)) )),
% 0.22/0.49    inference(subsumption_resolution,[],[f78,f33])).
% 0.22/0.49  fof(f78,plain,(
% 0.22/0.49    ( ! [X0] : (r1_tarski(k1_relat_1(k6_relat_1(X0)),X0) | ~v1_relat_1(k6_relat_1(X0))) )),
% 0.22/0.49    inference(superposition,[],[f40,f73])).
% 0.22/0.49  fof(f73,plain,(
% 0.22/0.49    ( ! [X0] : (k6_relat_1(X0) = k7_relat_1(k6_relat_1(X0),X0)) )),
% 0.22/0.49    inference(subsumption_resolution,[],[f72,f33])).
% 0.22/0.49  fof(f72,plain,(
% 0.22/0.49    ( ! [X0] : (k6_relat_1(X0) = k7_relat_1(k6_relat_1(X0),X0) | ~v1_relat_1(k6_relat_1(X0))) )),
% 0.22/0.49    inference(superposition,[],[f38,f67])).
% 0.22/0.49  fof(f38,plain,(
% 0.22/0.49    ( ! [X0] : (k7_relat_1(X0,k1_relat_1(X0)) = X0 | ~v1_relat_1(X0)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f15])).
% 0.22/0.49  fof(f15,plain,(
% 0.22/0.49    ! [X0] : (k7_relat_1(X0,k1_relat_1(X0)) = X0 | ~v1_relat_1(X0))),
% 0.22/0.49    inference(ennf_transformation,[],[f4])).
% 0.22/0.49  fof(f4,axiom,(
% 0.22/0.49    ! [X0] : (v1_relat_1(X0) => k7_relat_1(X0,k1_relat_1(X0)) = X0)),
% 0.22/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_relat_1)).
% 0.22/0.49  fof(f40,plain,(
% 0.22/0.49    ( ! [X0,X1] : (r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0) | ~v1_relat_1(X1)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f17])).
% 0.22/0.49  fof(f17,plain,(
% 0.22/0.49    ! [X0,X1] : (r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0) | ~v1_relat_1(X1))),
% 0.22/0.49    inference(ennf_transformation,[],[f3])).
% 0.22/0.49  fof(f3,axiom,(
% 0.22/0.49    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0))),
% 0.22/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t87_relat_1)).
% 0.22/0.49  fof(f69,plain,(
% 0.22/0.49    spl2_1),
% 0.22/0.49    inference(avatar_contradiction_clause,[],[f68])).
% 0.22/0.49  fof(f68,plain,(
% 0.22/0.49    $false | spl2_1),
% 0.22/0.49    inference(subsumption_resolution,[],[f53,f29])).
% 0.22/0.49  fof(f53,plain,(
% 0.22/0.49    ~v1_relat_1(sK0) | spl2_1),
% 0.22/0.49    inference(avatar_component_clause,[],[f52])).
% 0.22/0.49  fof(f52,plain,(
% 0.22/0.49    spl2_1 <=> v1_relat_1(sK0)),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 0.22/0.49  fof(f63,plain,(
% 0.22/0.49    ~spl2_1 | ~spl2_2 | ~spl2_3 | ~spl2_4),
% 0.22/0.49    inference(avatar_split_clause,[],[f32,f61,f58,f55,f52])).
% 0.22/0.49  fof(f32,plain,(
% 0.22/0.49    ~v5_ordinal1(sK0) | ~v1_funct_1(sK0) | ~v5_relat_1(sK0,k2_relat_1(sK0)) | ~v1_relat_1(sK0)),
% 0.22/0.49    inference(cnf_transformation,[],[f22])).
% 0.22/0.49  % SZS output end Proof for theBenchmark
% 0.22/0.49  % (3626)------------------------------
% 0.22/0.49  % (3626)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.49  % (3626)Termination reason: Refutation
% 0.22/0.49  
% 0.22/0.49  % (3626)Memory used [KB]: 10618
% 0.22/0.49  % (3626)Time elapsed: 0.074 s
% 0.22/0.49  % (3626)------------------------------
% 0.22/0.49  % (3626)------------------------------
% 0.22/0.49  % (3630)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.22/0.50  % (3622)Success in time 0.13 s
%------------------------------------------------------------------------------
