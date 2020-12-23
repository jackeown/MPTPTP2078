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
% DateTime   : Thu Dec  3 12:53:38 EST 2020

% Result     : Theorem 0.23s
% Output     : Refutation 0.23s
% Verified   : 
% Statistics : Number of formulae       :   46 (  79 expanded)
%              Number of leaves         :    6 (  21 expanded)
%              Depth                    :   11
%              Number of atoms          :  118 ( 224 expanded)
%              Number of equality atoms :   28 (  51 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f225,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f61,f62,f187,f219])).

fof(f219,plain,
    ( ~ spl5_1
    | ~ spl5_2 ),
    inference(avatar_contradiction_clause,[],[f218])).

fof(f218,plain,
    ( $false
    | ~ spl5_1
    | ~ spl5_2 ),
    inference(subsumption_resolution,[],[f211,f55])).

fof(f55,plain,
    ( r2_hidden(sK0,k2_relat_1(sK1))
    | ~ spl5_1 ),
    inference(avatar_component_clause,[],[f54])).

fof(f54,plain,
    ( spl5_1
  <=> r2_hidden(sK0,k2_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f211,plain,
    ( ~ r2_hidden(sK0,k2_relat_1(sK1))
    | ~ spl5_2 ),
    inference(resolution,[],[f209,f109])).

fof(f109,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X1,k1_tarski(X0))
      | ~ r2_hidden(X0,X1) ) ),
    inference(resolution,[],[f34,f52])).

fof(f52,plain,(
    ! [X2] : r2_hidden(X2,k1_tarski(X2)) ),
    inference(equality_resolution,[],[f51])).

fof(f51,plain,(
    ! [X2,X1] :
      ( r2_hidden(X2,X1)
      | k1_tarski(X2) != X1 ) ),
    inference(equality_resolution,[],[f44])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( X0 != X2
      | r2_hidden(X2,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).

fof(f34,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,X1)
      | ~ r2_hidden(X2,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X3] :
              ~ ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X2] :
              ~ ( r2_hidden(X2,X1)
                & r2_hidden(X2,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_0)).

fof(f209,plain,
    ( r1_xboole_0(k2_relat_1(sK1),k1_tarski(sK0))
    | ~ spl5_2 ),
    inference(subsumption_resolution,[],[f204,f27])).

fof(f27,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ? [X0,X1] :
      ( ( r2_hidden(X0,k2_relat_1(X1))
      <~> k1_xboole_0 != k10_relat_1(X1,k1_tarski(X0)) )
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,negated_conjecture,(
    ~ ! [X0,X1] :
        ( v1_relat_1(X1)
       => ( r2_hidden(X0,k2_relat_1(X1))
        <=> k1_xboole_0 != k10_relat_1(X1,k1_tarski(X0)) ) ) ),
    inference(negated_conjecture,[],[f13])).

fof(f13,conjecture,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r2_hidden(X0,k2_relat_1(X1))
      <=> k1_xboole_0 != k10_relat_1(X1,k1_tarski(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t142_funct_1)).

fof(f204,plain,
    ( r1_xboole_0(k2_relat_1(sK1),k1_tarski(sK0))
    | ~ v1_relat_1(sK1)
    | ~ spl5_2 ),
    inference(trivial_inequality_removal,[],[f203])).

fof(f203,plain,
    ( k1_xboole_0 != k1_xboole_0
    | r1_xboole_0(k2_relat_1(sK1),k1_tarski(sK0))
    | ~ v1_relat_1(sK1)
    | ~ spl5_2 ),
    inference(superposition,[],[f39,f60])).

fof(f60,plain,
    ( k1_xboole_0 = k10_relat_1(sK1,k1_tarski(sK0))
    | ~ spl5_2 ),
    inference(avatar_component_clause,[],[f58])).

fof(f58,plain,
    ( spl5_2
  <=> k1_xboole_0 = k10_relat_1(sK1,k1_tarski(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f39,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k10_relat_1(X1,X0)
      | r1_xboole_0(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k10_relat_1(X1,X0)
      <=> r1_xboole_0(k2_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( k1_xboole_0 = k10_relat_1(X1,X0)
      <=> r1_xboole_0(k2_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t173_relat_1)).

fof(f187,plain,
    ( spl5_1
    | spl5_2 ),
    inference(avatar_contradiction_clause,[],[f186])).

fof(f186,plain,
    ( $false
    | spl5_1
    | spl5_2 ),
    inference(subsumption_resolution,[],[f183,f59])).

fof(f59,plain,
    ( k1_xboole_0 != k10_relat_1(sK1,k1_tarski(sK0))
    | spl5_2 ),
    inference(avatar_component_clause,[],[f58])).

fof(f183,plain,
    ( k1_xboole_0 = k10_relat_1(sK1,k1_tarski(sK0))
    | spl5_1 ),
    inference(resolution,[],[f182,f56])).

fof(f56,plain,
    ( ~ r2_hidden(sK0,k2_relat_1(sK1))
    | spl5_1 ),
    inference(avatar_component_clause,[],[f54])).

fof(f182,plain,(
    ! [X1] :
      ( r2_hidden(X1,k2_relat_1(sK1))
      | k1_xboole_0 = k10_relat_1(sK1,k1_tarski(X1)) ) ),
    inference(subsumption_resolution,[],[f181,f146])).

fof(f146,plain,(
    ! [X0] :
      ( ~ r1_xboole_0(k2_relat_1(sK1),X0)
      | k1_xboole_0 = k10_relat_1(sK1,X0) ) ),
    inference(resolution,[],[f38,f27])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | ~ r1_xboole_0(k2_relat_1(X1),X0)
      | k1_xboole_0 = k10_relat_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f181,plain,(
    ! [X1] :
      ( r2_hidden(X1,k2_relat_1(sK1))
      | r1_xboole_0(k2_relat_1(sK1),k1_tarski(X1))
      | k1_xboole_0 = k10_relat_1(sK1,k1_tarski(X1)) ) ),
    inference(superposition,[],[f35,f151])).

fof(f151,plain,(
    ! [X2] :
      ( sK3(k2_relat_1(sK1),k1_tarski(X2)) = X2
      | k1_xboole_0 = k10_relat_1(sK1,k1_tarski(X2)) ) ),
    inference(resolution,[],[f146,f89])).

fof(f89,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,k1_tarski(X1))
      | sK3(X0,k1_tarski(X1)) = X1 ) ),
    inference(resolution,[],[f36,f50])).

fof(f50,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,k1_tarski(X0))
      | X0 = X2 ) ),
    inference(equality_resolution,[],[f45])).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( X0 = X2
      | ~ r2_hidden(X2,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f5])).

fof(f36,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK3(X0,X1),X1)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f35,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK3(X0,X1),X0)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f62,plain,
    ( spl5_1
    | ~ spl5_2 ),
    inference(avatar_split_clause,[],[f25,f58,f54])).

fof(f25,plain,
    ( k1_xboole_0 != k10_relat_1(sK1,k1_tarski(sK0))
    | r2_hidden(sK0,k2_relat_1(sK1)) ),
    inference(cnf_transformation,[],[f17])).

fof(f61,plain,
    ( ~ spl5_1
    | spl5_2 ),
    inference(avatar_split_clause,[],[f26,f58,f54])).

fof(f26,plain,
    ( k1_xboole_0 = k10_relat_1(sK1,k1_tarski(sK0))
    | ~ r2_hidden(sK0,k2_relat_1(sK1)) ),
    inference(cnf_transformation,[],[f17])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n007.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.36  % CPULimit   : 60
% 0.15/0.36  % WCLimit    : 600
% 0.15/0.36  % DateTime   : Tue Dec  1 16:51:36 EST 2020
% 0.15/0.36  % CPUTime    : 
% 0.23/0.49  % (25715)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 0.23/0.49  % (25701)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 0.23/0.49  % (25707)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.23/0.50  % (25715)Refutation found. Thanks to Tanya!
% 0.23/0.50  % SZS status Theorem for theBenchmark
% 0.23/0.50  % SZS output start Proof for theBenchmark
% 0.23/0.50  fof(f225,plain,(
% 0.23/0.50    $false),
% 0.23/0.50    inference(avatar_sat_refutation,[],[f61,f62,f187,f219])).
% 0.23/0.50  fof(f219,plain,(
% 0.23/0.50    ~spl5_1 | ~spl5_2),
% 0.23/0.50    inference(avatar_contradiction_clause,[],[f218])).
% 0.23/0.50  fof(f218,plain,(
% 0.23/0.50    $false | (~spl5_1 | ~spl5_2)),
% 0.23/0.50    inference(subsumption_resolution,[],[f211,f55])).
% 0.23/0.50  fof(f55,plain,(
% 0.23/0.50    r2_hidden(sK0,k2_relat_1(sK1)) | ~spl5_1),
% 0.23/0.50    inference(avatar_component_clause,[],[f54])).
% 0.23/0.50  fof(f54,plain,(
% 0.23/0.50    spl5_1 <=> r2_hidden(sK0,k2_relat_1(sK1))),
% 0.23/0.50    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 0.23/0.50  fof(f211,plain,(
% 0.23/0.50    ~r2_hidden(sK0,k2_relat_1(sK1)) | ~spl5_2),
% 0.23/0.50    inference(resolution,[],[f209,f109])).
% 0.23/0.50  fof(f109,plain,(
% 0.23/0.50    ( ! [X0,X1] : (~r1_xboole_0(X1,k1_tarski(X0)) | ~r2_hidden(X0,X1)) )),
% 0.23/0.50    inference(resolution,[],[f34,f52])).
% 0.23/0.51  fof(f52,plain,(
% 0.23/0.51    ( ! [X2] : (r2_hidden(X2,k1_tarski(X2))) )),
% 0.23/0.51    inference(equality_resolution,[],[f51])).
% 0.23/0.51  fof(f51,plain,(
% 0.23/0.51    ( ! [X2,X1] : (r2_hidden(X2,X1) | k1_tarski(X2) != X1) )),
% 0.23/0.51    inference(equality_resolution,[],[f44])).
% 0.23/0.51  fof(f44,plain,(
% 0.23/0.51    ( ! [X2,X0,X1] : (X0 != X2 | r2_hidden(X2,X1) | k1_tarski(X0) != X1) )),
% 0.23/0.51    inference(cnf_transformation,[],[f5])).
% 0.23/0.51  fof(f5,axiom,(
% 0.23/0.51    ! [X0,X1] : (k1_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> X0 = X2))),
% 0.23/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).
% 0.23/0.51  fof(f34,plain,(
% 0.23/0.51    ( ! [X2,X0,X1] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0) | ~r1_xboole_0(X0,X1)) )),
% 0.23/0.51    inference(cnf_transformation,[],[f19])).
% 0.23/0.51  fof(f19,plain,(
% 0.23/0.51    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r1_xboole_0(X0,X1)))),
% 0.23/0.51    inference(ennf_transformation,[],[f16])).
% 0.23/0.51  fof(f16,plain,(
% 0.23/0.51    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X3] : ~(r2_hidden(X3,X1) & r2_hidden(X3,X0)) & ~r1_xboole_0(X0,X1)))),
% 0.23/0.51    inference(rectify,[],[f2])).
% 0.23/0.51  fof(f2,axiom,(
% 0.23/0.51    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X2] : ~(r2_hidden(X2,X1) & r2_hidden(X2,X0)) & ~r1_xboole_0(X0,X1)))),
% 0.23/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_0)).
% 0.23/0.51  fof(f209,plain,(
% 0.23/0.51    r1_xboole_0(k2_relat_1(sK1),k1_tarski(sK0)) | ~spl5_2),
% 0.23/0.51    inference(subsumption_resolution,[],[f204,f27])).
% 0.23/0.51  fof(f27,plain,(
% 0.23/0.51    v1_relat_1(sK1)),
% 0.23/0.51    inference(cnf_transformation,[],[f17])).
% 0.23/0.51  fof(f17,plain,(
% 0.23/0.51    ? [X0,X1] : ((r2_hidden(X0,k2_relat_1(X1)) <~> k1_xboole_0 != k10_relat_1(X1,k1_tarski(X0))) & v1_relat_1(X1))),
% 0.23/0.51    inference(ennf_transformation,[],[f14])).
% 0.23/0.51  fof(f14,negated_conjecture,(
% 0.23/0.51    ~! [X0,X1] : (v1_relat_1(X1) => (r2_hidden(X0,k2_relat_1(X1)) <=> k1_xboole_0 != k10_relat_1(X1,k1_tarski(X0))))),
% 0.23/0.51    inference(negated_conjecture,[],[f13])).
% 0.23/0.51  fof(f13,conjecture,(
% 0.23/0.51    ! [X0,X1] : (v1_relat_1(X1) => (r2_hidden(X0,k2_relat_1(X1)) <=> k1_xboole_0 != k10_relat_1(X1,k1_tarski(X0))))),
% 0.23/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t142_funct_1)).
% 0.23/0.51  fof(f204,plain,(
% 0.23/0.51    r1_xboole_0(k2_relat_1(sK1),k1_tarski(sK0)) | ~v1_relat_1(sK1) | ~spl5_2),
% 0.23/0.51    inference(trivial_inequality_removal,[],[f203])).
% 0.23/0.51  fof(f203,plain,(
% 0.23/0.51    k1_xboole_0 != k1_xboole_0 | r1_xboole_0(k2_relat_1(sK1),k1_tarski(sK0)) | ~v1_relat_1(sK1) | ~spl5_2),
% 0.23/0.51    inference(superposition,[],[f39,f60])).
% 0.23/0.51  fof(f60,plain,(
% 0.23/0.51    k1_xboole_0 = k10_relat_1(sK1,k1_tarski(sK0)) | ~spl5_2),
% 0.23/0.51    inference(avatar_component_clause,[],[f58])).
% 0.23/0.51  fof(f58,plain,(
% 0.23/0.51    spl5_2 <=> k1_xboole_0 = k10_relat_1(sK1,k1_tarski(sK0))),
% 0.23/0.51    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).
% 0.23/0.51  fof(f39,plain,(
% 0.23/0.51    ( ! [X0,X1] : (k1_xboole_0 != k10_relat_1(X1,X0) | r1_xboole_0(k2_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 0.23/0.51    inference(cnf_transformation,[],[f21])).
% 0.23/0.51  fof(f21,plain,(
% 0.23/0.51    ! [X0,X1] : ((k1_xboole_0 = k10_relat_1(X1,X0) <=> r1_xboole_0(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.23/0.51    inference(ennf_transformation,[],[f10])).
% 0.23/0.51  fof(f10,axiom,(
% 0.23/0.51    ! [X0,X1] : (v1_relat_1(X1) => (k1_xboole_0 = k10_relat_1(X1,X0) <=> r1_xboole_0(k2_relat_1(X1),X0)))),
% 0.23/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t173_relat_1)).
% 0.23/0.51  fof(f187,plain,(
% 0.23/0.51    spl5_1 | spl5_2),
% 0.23/0.51    inference(avatar_contradiction_clause,[],[f186])).
% 0.23/0.51  fof(f186,plain,(
% 0.23/0.51    $false | (spl5_1 | spl5_2)),
% 0.23/0.51    inference(subsumption_resolution,[],[f183,f59])).
% 0.23/0.51  fof(f59,plain,(
% 0.23/0.51    k1_xboole_0 != k10_relat_1(sK1,k1_tarski(sK0)) | spl5_2),
% 0.23/0.51    inference(avatar_component_clause,[],[f58])).
% 0.23/0.51  fof(f183,plain,(
% 0.23/0.51    k1_xboole_0 = k10_relat_1(sK1,k1_tarski(sK0)) | spl5_1),
% 0.23/0.51    inference(resolution,[],[f182,f56])).
% 0.23/0.51  fof(f56,plain,(
% 0.23/0.51    ~r2_hidden(sK0,k2_relat_1(sK1)) | spl5_1),
% 0.23/0.51    inference(avatar_component_clause,[],[f54])).
% 0.23/0.51  fof(f182,plain,(
% 0.23/0.51    ( ! [X1] : (r2_hidden(X1,k2_relat_1(sK1)) | k1_xboole_0 = k10_relat_1(sK1,k1_tarski(X1))) )),
% 0.23/0.51    inference(subsumption_resolution,[],[f181,f146])).
% 0.23/0.51  fof(f146,plain,(
% 0.23/0.51    ( ! [X0] : (~r1_xboole_0(k2_relat_1(sK1),X0) | k1_xboole_0 = k10_relat_1(sK1,X0)) )),
% 0.23/0.51    inference(resolution,[],[f38,f27])).
% 0.23/0.51  fof(f38,plain,(
% 0.23/0.51    ( ! [X0,X1] : (~v1_relat_1(X1) | ~r1_xboole_0(k2_relat_1(X1),X0) | k1_xboole_0 = k10_relat_1(X1,X0)) )),
% 0.23/0.51    inference(cnf_transformation,[],[f21])).
% 0.23/0.51  fof(f181,plain,(
% 0.23/0.51    ( ! [X1] : (r2_hidden(X1,k2_relat_1(sK1)) | r1_xboole_0(k2_relat_1(sK1),k1_tarski(X1)) | k1_xboole_0 = k10_relat_1(sK1,k1_tarski(X1))) )),
% 0.23/0.51    inference(superposition,[],[f35,f151])).
% 0.23/0.51  fof(f151,plain,(
% 0.23/0.51    ( ! [X2] : (sK3(k2_relat_1(sK1),k1_tarski(X2)) = X2 | k1_xboole_0 = k10_relat_1(sK1,k1_tarski(X2))) )),
% 0.23/0.51    inference(resolution,[],[f146,f89])).
% 0.23/0.51  fof(f89,plain,(
% 0.23/0.51    ( ! [X0,X1] : (r1_xboole_0(X0,k1_tarski(X1)) | sK3(X0,k1_tarski(X1)) = X1) )),
% 0.23/0.51    inference(resolution,[],[f36,f50])).
% 0.23/0.51  fof(f50,plain,(
% 0.23/0.51    ( ! [X2,X0] : (~r2_hidden(X2,k1_tarski(X0)) | X0 = X2) )),
% 0.23/0.51    inference(equality_resolution,[],[f45])).
% 0.23/0.51  fof(f45,plain,(
% 0.23/0.51    ( ! [X2,X0,X1] : (X0 = X2 | ~r2_hidden(X2,X1) | k1_tarski(X0) != X1) )),
% 0.23/0.51    inference(cnf_transformation,[],[f5])).
% 0.23/0.51  fof(f36,plain,(
% 0.23/0.51    ( ! [X0,X1] : (r2_hidden(sK3(X0,X1),X1) | r1_xboole_0(X0,X1)) )),
% 0.23/0.51    inference(cnf_transformation,[],[f19])).
% 0.23/0.51  fof(f35,plain,(
% 0.23/0.51    ( ! [X0,X1] : (r2_hidden(sK3(X0,X1),X0) | r1_xboole_0(X0,X1)) )),
% 0.23/0.51    inference(cnf_transformation,[],[f19])).
% 0.23/0.51  fof(f62,plain,(
% 0.23/0.51    spl5_1 | ~spl5_2),
% 0.23/0.51    inference(avatar_split_clause,[],[f25,f58,f54])).
% 0.23/0.51  fof(f25,plain,(
% 0.23/0.51    k1_xboole_0 != k10_relat_1(sK1,k1_tarski(sK0)) | r2_hidden(sK0,k2_relat_1(sK1))),
% 0.23/0.51    inference(cnf_transformation,[],[f17])).
% 0.23/0.51  fof(f61,plain,(
% 0.23/0.51    ~spl5_1 | spl5_2),
% 0.23/0.51    inference(avatar_split_clause,[],[f26,f58,f54])).
% 0.23/0.51  fof(f26,plain,(
% 0.23/0.51    k1_xboole_0 = k10_relat_1(sK1,k1_tarski(sK0)) | ~r2_hidden(sK0,k2_relat_1(sK1))),
% 0.23/0.51    inference(cnf_transformation,[],[f17])).
% 0.23/0.51  % SZS output end Proof for theBenchmark
% 0.23/0.51  % (25715)------------------------------
% 0.23/0.51  % (25715)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.23/0.51  % (25715)Termination reason: Refutation
% 0.23/0.51  
% 0.23/0.51  % (25715)Memory used [KB]: 10746
% 0.23/0.51  % (25715)Time elapsed: 0.063 s
% 0.23/0.51  % (25715)------------------------------
% 0.23/0.51  % (25715)------------------------------
% 0.23/0.51  % (25691)Success in time 0.141 s
%------------------------------------------------------------------------------
