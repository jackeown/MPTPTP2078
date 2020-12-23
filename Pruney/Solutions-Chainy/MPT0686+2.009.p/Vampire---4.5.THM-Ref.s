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
% DateTime   : Thu Dec  3 12:53:37 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   58 (  88 expanded)
%              Number of leaves         :   14 (  34 expanded)
%              Depth                    :    7
%              Number of atoms          :  138 ( 225 expanded)
%              Number of equality atoms :   27 (  35 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f97,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f26,f31,f36,f41,f48,f55,f61,f67,f84,f90])).

fof(f90,plain,
    ( spl3_3
    | ~ spl3_5
    | ~ spl3_8
    | ~ spl3_10 ),
    inference(avatar_contradiction_clause,[],[f89])).

fof(f89,plain,
    ( $false
    | spl3_3
    | ~ spl3_5
    | ~ spl3_8
    | ~ spl3_10 ),
    inference(subsumption_resolution,[],[f88,f35])).

fof(f35,plain,
    ( ~ r1_xboole_0(k10_relat_1(sK0,sK1),k10_relat_1(sK0,sK2))
    | spl3_3 ),
    inference(avatar_component_clause,[],[f33])).

fof(f33,plain,
    ( spl3_3
  <=> r1_xboole_0(k10_relat_1(sK0,sK1),k10_relat_1(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f88,plain,
    ( r1_xboole_0(k10_relat_1(sK0,sK1),k10_relat_1(sK0,sK2))
    | ~ spl3_5
    | ~ spl3_8
    | ~ spl3_10 ),
    inference(subsumption_resolution,[],[f85,f66])).

fof(f66,plain,
    ( k1_xboole_0 = k10_relat_1(sK0,k1_xboole_0)
    | ~ spl3_8 ),
    inference(avatar_component_clause,[],[f64])).

fof(f64,plain,
    ( spl3_8
  <=> k1_xboole_0 = k10_relat_1(sK0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).

fof(f85,plain,
    ( k1_xboole_0 != k10_relat_1(sK0,k1_xboole_0)
    | r1_xboole_0(k10_relat_1(sK0,sK1),k10_relat_1(sK0,sK2))
    | ~ spl3_5
    | ~ spl3_10 ),
    inference(superposition,[],[f83,f47])).

fof(f47,plain,
    ( k1_xboole_0 = k3_xboole_0(sK1,sK2)
    | ~ spl3_5 ),
    inference(avatar_component_clause,[],[f45])).

fof(f45,plain,
    ( spl3_5
  <=> k1_xboole_0 = k3_xboole_0(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f83,plain,
    ( ! [X0,X1] :
        ( k1_xboole_0 != k10_relat_1(sK0,k3_xboole_0(X0,X1))
        | r1_xboole_0(k10_relat_1(sK0,X0),k10_relat_1(sK0,X1)) )
    | ~ spl3_10 ),
    inference(avatar_component_clause,[],[f82])).

fof(f82,plain,
    ( spl3_10
  <=> ! [X1,X0] :
        ( k1_xboole_0 != k10_relat_1(sK0,k3_xboole_0(X0,X1))
        | r1_xboole_0(k10_relat_1(sK0,X0),k10_relat_1(sK0,X1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).

fof(f84,plain,
    ( spl3_10
    | ~ spl3_7 ),
    inference(avatar_split_clause,[],[f74,f59,f82])).

fof(f59,plain,
    ( spl3_7
  <=> ! [X1,X0] : k10_relat_1(sK0,k3_xboole_0(X0,X1)) = k3_xboole_0(k10_relat_1(sK0,X0),k10_relat_1(sK0,X1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f74,plain,
    ( ! [X0,X1] :
        ( k1_xboole_0 != k10_relat_1(sK0,k3_xboole_0(X0,X1))
        | r1_xboole_0(k10_relat_1(sK0,X0),k10_relat_1(sK0,X1)) )
    | ~ spl3_7 ),
    inference(superposition,[],[f19,f60])).

fof(f60,plain,
    ( ! [X0,X1] : k10_relat_1(sK0,k3_xboole_0(X0,X1)) = k3_xboole_0(k10_relat_1(sK0,X0),k10_relat_1(sK0,X1))
    | ~ spl3_7 ),
    inference(avatar_component_clause,[],[f59])).

fof(f19,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) != k1_xboole_0
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).

fof(f67,plain,
    ( spl3_8
    | ~ spl3_6 ),
    inference(avatar_split_clause,[],[f62,f53,f64])).

fof(f53,plain,
    ( spl3_6
  <=> ! [X0] :
        ( ~ r1_xboole_0(k2_relat_1(sK0),X0)
        | k1_xboole_0 = k10_relat_1(sK0,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f62,plain,
    ( k1_xboole_0 = k10_relat_1(sK0,k1_xboole_0)
    | ~ spl3_6 ),
    inference(resolution,[],[f54,f16])).

fof(f16,plain,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).

fof(f54,plain,
    ( ! [X0] :
        ( ~ r1_xboole_0(k2_relat_1(sK0),X0)
        | k1_xboole_0 = k10_relat_1(sK0,X0) )
    | ~ spl3_6 ),
    inference(avatar_component_clause,[],[f53])).

fof(f61,plain,
    ( spl3_7
    | ~ spl3_1
    | ~ spl3_2 ),
    inference(avatar_split_clause,[],[f57,f28,f23,f59])).

fof(f23,plain,
    ( spl3_1
  <=> v1_funct_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f28,plain,
    ( spl3_2
  <=> v1_relat_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

% (18934)lrs+1010_4_awrs=decay:awrsf=64:add=large:afp=4000:afq=1.2:amm=off:anc=none:bs=on:bsr=on:fde=none:gs=on:gsaa=from_current:gsem=on:lma=on:newcnf=on:nwc=1.7:sas=z3:stl=30:sd=10:ss=axioms:s2a=on:st=1.2:sp=frequency:updr=off:uhcvi=on_211 on theBenchmark
fof(f57,plain,
    ( ! [X0,X1] : k10_relat_1(sK0,k3_xboole_0(X0,X1)) = k3_xboole_0(k10_relat_1(sK0,X0),k10_relat_1(sK0,X1))
    | ~ spl3_1
    | ~ spl3_2 ),
    inference(subsumption_resolution,[],[f56,f30])).

fof(f30,plain,
    ( v1_relat_1(sK0)
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f28])).

fof(f56,plain,
    ( ! [X0,X1] :
        ( ~ v1_relat_1(sK0)
        | k10_relat_1(sK0,k3_xboole_0(X0,X1)) = k3_xboole_0(k10_relat_1(sK0,X0),k10_relat_1(sK0,X1)) )
    | ~ spl3_1 ),
    inference(resolution,[],[f21,f25])).

fof(f25,plain,
    ( v1_funct_1(sK0)
    | ~ spl3_1 ),
    inference(avatar_component_clause,[],[f23])).

fof(f21,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2)
      | k10_relat_1(X2,k3_xboole_0(X0,X1)) = k3_xboole_0(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1,X2] :
      ( k10_relat_1(X2,k3_xboole_0(X0,X1)) = k3_xboole_0(k10_relat_1(X2,X0),k10_relat_1(X2,X1))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ! [X0,X1,X2] :
      ( k10_relat_1(X2,k3_xboole_0(X0,X1)) = k3_xboole_0(k10_relat_1(X2,X0),k10_relat_1(X2,X1))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => k10_relat_1(X2,k3_xboole_0(X0,X1)) = k3_xboole_0(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t137_funct_1)).

fof(f55,plain,
    ( spl3_6
    | ~ spl3_2 ),
    inference(avatar_split_clause,[],[f51,f28,f53])).

fof(f51,plain,
    ( ! [X0] :
        ( ~ r1_xboole_0(k2_relat_1(sK0),X0)
        | k1_xboole_0 = k10_relat_1(sK0,X0) )
    | ~ spl3_2 ),
    inference(resolution,[],[f17,f30])).

fof(f17,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | ~ r1_xboole_0(k2_relat_1(X1),X0)
      | k1_xboole_0 = k10_relat_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k10_relat_1(X1,X0)
      <=> r1_xboole_0(k2_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( k1_xboole_0 = k10_relat_1(X1,X0)
      <=> r1_xboole_0(k2_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t173_relat_1)).

fof(f48,plain,
    ( spl3_5
    | ~ spl3_4 ),
    inference(avatar_split_clause,[],[f42,f38,f45])).

fof(f38,plain,
    ( spl3_4
  <=> r1_xboole_0(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f42,plain,
    ( k1_xboole_0 = k3_xboole_0(sK1,sK2)
    | ~ spl3_4 ),
    inference(resolution,[],[f20,f40])).

fof(f40,plain,
    ( r1_xboole_0(sK1,sK2)
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f38])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f41,plain,(
    spl3_4 ),
    inference(avatar_split_clause,[],[f12,f38])).

fof(f12,plain,(
    r1_xboole_0(sK1,sK2) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,plain,(
    ? [X0] :
      ( ? [X1,X2] :
          ( ~ r1_xboole_0(k10_relat_1(X0,X1),k10_relat_1(X0,X2))
          & r1_xboole_0(X1,X2) )
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(flattening,[],[f7])).

fof(f7,plain,(
    ? [X0] :
      ( ? [X1,X2] :
          ( ~ r1_xboole_0(k10_relat_1(X0,X1),k10_relat_1(X0,X2))
          & r1_xboole_0(X1,X2) )
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,negated_conjecture,(
    ~ ! [X0] :
        ( ( v1_funct_1(X0)
          & v1_relat_1(X0) )
       => ! [X1,X2] :
            ( r1_xboole_0(X1,X2)
           => r1_xboole_0(k10_relat_1(X0,X1),k10_relat_1(X0,X2)) ) ) ),
    inference(negated_conjecture,[],[f5])).

fof(f5,conjecture,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1,X2] :
          ( r1_xboole_0(X1,X2)
         => r1_xboole_0(k10_relat_1(X0,X1),k10_relat_1(X0,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t141_funct_1)).

fof(f36,plain,(
    ~ spl3_3 ),
    inference(avatar_split_clause,[],[f13,f33])).

fof(f13,plain,(
    ~ r1_xboole_0(k10_relat_1(sK0,sK1),k10_relat_1(sK0,sK2)) ),
    inference(cnf_transformation,[],[f8])).

fof(f31,plain,(
    spl3_2 ),
    inference(avatar_split_clause,[],[f14,f28])).

fof(f14,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f8])).

fof(f26,plain,(
    spl3_1 ),
    inference(avatar_split_clause,[],[f15,f23])).

fof(f15,plain,(
    v1_funct_1(sK0) ),
    inference(cnf_transformation,[],[f8])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n025.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 20:08:36 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.43  % (18932)lrs+11_3:2_add=large:afr=on:afp=10000:afq=1.2:amm=off:anc=none:bs=unit_only:cond=on:gs=on:gsaa=full_model:gsem=off:irw=on:lwlo=on:nm=32:nwc=1.2:sas=z3:stl=90:sac=on_214 on theBenchmark
% 0.22/0.43  % (18927)lrs+1011_5:1_acc=on:amm=off:anc=all_dependent:bd=off:ccuc=small_ones:fde=unused:gs=on:gsaa=full_model:gsem=off:lcm=predicate:lwlo=on:nm=6:newcnf=on:nwc=2.5:stl=30:sp=occurrence:updr=off_3 on theBenchmark
% 0.22/0.43  % (18927)Refutation found. Thanks to Tanya!
% 0.22/0.43  % SZS status Theorem for theBenchmark
% 0.22/0.43  % SZS output start Proof for theBenchmark
% 0.22/0.43  fof(f97,plain,(
% 0.22/0.43    $false),
% 0.22/0.43    inference(avatar_sat_refutation,[],[f26,f31,f36,f41,f48,f55,f61,f67,f84,f90])).
% 0.22/0.43  fof(f90,plain,(
% 0.22/0.43    spl3_3 | ~spl3_5 | ~spl3_8 | ~spl3_10),
% 0.22/0.43    inference(avatar_contradiction_clause,[],[f89])).
% 0.22/0.43  fof(f89,plain,(
% 0.22/0.43    $false | (spl3_3 | ~spl3_5 | ~spl3_8 | ~spl3_10)),
% 0.22/0.43    inference(subsumption_resolution,[],[f88,f35])).
% 0.22/0.43  fof(f35,plain,(
% 0.22/0.43    ~r1_xboole_0(k10_relat_1(sK0,sK1),k10_relat_1(sK0,sK2)) | spl3_3),
% 0.22/0.43    inference(avatar_component_clause,[],[f33])).
% 0.22/0.43  fof(f33,plain,(
% 0.22/0.43    spl3_3 <=> r1_xboole_0(k10_relat_1(sK0,sK1),k10_relat_1(sK0,sK2))),
% 0.22/0.43    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.22/0.43  fof(f88,plain,(
% 0.22/0.43    r1_xboole_0(k10_relat_1(sK0,sK1),k10_relat_1(sK0,sK2)) | (~spl3_5 | ~spl3_8 | ~spl3_10)),
% 0.22/0.43    inference(subsumption_resolution,[],[f85,f66])).
% 0.22/0.43  fof(f66,plain,(
% 0.22/0.43    k1_xboole_0 = k10_relat_1(sK0,k1_xboole_0) | ~spl3_8),
% 0.22/0.43    inference(avatar_component_clause,[],[f64])).
% 0.22/0.43  fof(f64,plain,(
% 0.22/0.43    spl3_8 <=> k1_xboole_0 = k10_relat_1(sK0,k1_xboole_0)),
% 0.22/0.43    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).
% 0.22/0.43  fof(f85,plain,(
% 0.22/0.43    k1_xboole_0 != k10_relat_1(sK0,k1_xboole_0) | r1_xboole_0(k10_relat_1(sK0,sK1),k10_relat_1(sK0,sK2)) | (~spl3_5 | ~spl3_10)),
% 0.22/0.43    inference(superposition,[],[f83,f47])).
% 0.22/0.43  fof(f47,plain,(
% 0.22/0.43    k1_xboole_0 = k3_xboole_0(sK1,sK2) | ~spl3_5),
% 0.22/0.43    inference(avatar_component_clause,[],[f45])).
% 0.22/0.43  fof(f45,plain,(
% 0.22/0.43    spl3_5 <=> k1_xboole_0 = k3_xboole_0(sK1,sK2)),
% 0.22/0.43    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 0.22/0.44  fof(f83,plain,(
% 0.22/0.44    ( ! [X0,X1] : (k1_xboole_0 != k10_relat_1(sK0,k3_xboole_0(X0,X1)) | r1_xboole_0(k10_relat_1(sK0,X0),k10_relat_1(sK0,X1))) ) | ~spl3_10),
% 0.22/0.44    inference(avatar_component_clause,[],[f82])).
% 0.22/0.44  fof(f82,plain,(
% 0.22/0.44    spl3_10 <=> ! [X1,X0] : (k1_xboole_0 != k10_relat_1(sK0,k3_xboole_0(X0,X1)) | r1_xboole_0(k10_relat_1(sK0,X0),k10_relat_1(sK0,X1)))),
% 0.22/0.44    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).
% 0.22/0.44  fof(f84,plain,(
% 0.22/0.44    spl3_10 | ~spl3_7),
% 0.22/0.44    inference(avatar_split_clause,[],[f74,f59,f82])).
% 0.22/0.44  fof(f59,plain,(
% 0.22/0.44    spl3_7 <=> ! [X1,X0] : k10_relat_1(sK0,k3_xboole_0(X0,X1)) = k3_xboole_0(k10_relat_1(sK0,X0),k10_relat_1(sK0,X1))),
% 0.22/0.44    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).
% 0.22/0.44  fof(f74,plain,(
% 0.22/0.44    ( ! [X0,X1] : (k1_xboole_0 != k10_relat_1(sK0,k3_xboole_0(X0,X1)) | r1_xboole_0(k10_relat_1(sK0,X0),k10_relat_1(sK0,X1))) ) | ~spl3_7),
% 0.22/0.44    inference(superposition,[],[f19,f60])).
% 0.22/0.44  fof(f60,plain,(
% 0.22/0.44    ( ! [X0,X1] : (k10_relat_1(sK0,k3_xboole_0(X0,X1)) = k3_xboole_0(k10_relat_1(sK0,X0),k10_relat_1(sK0,X1))) ) | ~spl3_7),
% 0.22/0.44    inference(avatar_component_clause,[],[f59])).
% 0.22/0.44  fof(f19,plain,(
% 0.22/0.44    ( ! [X0,X1] : (k3_xboole_0(X0,X1) != k1_xboole_0 | r1_xboole_0(X0,X1)) )),
% 0.22/0.44    inference(cnf_transformation,[],[f1])).
% 0.22/0.44  fof(f1,axiom,(
% 0.22/0.44    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 0.22/0.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).
% 0.22/0.44  fof(f67,plain,(
% 0.22/0.44    spl3_8 | ~spl3_6),
% 0.22/0.44    inference(avatar_split_clause,[],[f62,f53,f64])).
% 0.22/0.44  fof(f53,plain,(
% 0.22/0.44    spl3_6 <=> ! [X0] : (~r1_xboole_0(k2_relat_1(sK0),X0) | k1_xboole_0 = k10_relat_1(sK0,X0))),
% 0.22/0.44    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 0.22/0.44  fof(f62,plain,(
% 0.22/0.44    k1_xboole_0 = k10_relat_1(sK0,k1_xboole_0) | ~spl3_6),
% 0.22/0.44    inference(resolution,[],[f54,f16])).
% 0.22/0.44  fof(f16,plain,(
% 0.22/0.44    ( ! [X0] : (r1_xboole_0(X0,k1_xboole_0)) )),
% 0.22/0.44    inference(cnf_transformation,[],[f2])).
% 0.22/0.44  fof(f2,axiom,(
% 0.22/0.44    ! [X0] : r1_xboole_0(X0,k1_xboole_0)),
% 0.22/0.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).
% 0.22/0.44  fof(f54,plain,(
% 0.22/0.44    ( ! [X0] : (~r1_xboole_0(k2_relat_1(sK0),X0) | k1_xboole_0 = k10_relat_1(sK0,X0)) ) | ~spl3_6),
% 0.22/0.44    inference(avatar_component_clause,[],[f53])).
% 0.22/0.44  fof(f61,plain,(
% 0.22/0.44    spl3_7 | ~spl3_1 | ~spl3_2),
% 0.22/0.44    inference(avatar_split_clause,[],[f57,f28,f23,f59])).
% 0.22/0.44  fof(f23,plain,(
% 0.22/0.44    spl3_1 <=> v1_funct_1(sK0)),
% 0.22/0.44    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.22/0.44  fof(f28,plain,(
% 0.22/0.44    spl3_2 <=> v1_relat_1(sK0)),
% 0.22/0.44    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.22/0.44  % (18934)lrs+1010_4_awrs=decay:awrsf=64:add=large:afp=4000:afq=1.2:amm=off:anc=none:bs=on:bsr=on:fde=none:gs=on:gsaa=from_current:gsem=on:lma=on:newcnf=on:nwc=1.7:sas=z3:stl=30:sd=10:ss=axioms:s2a=on:st=1.2:sp=frequency:updr=off:uhcvi=on_211 on theBenchmark
% 0.22/0.44  fof(f57,plain,(
% 0.22/0.44    ( ! [X0,X1] : (k10_relat_1(sK0,k3_xboole_0(X0,X1)) = k3_xboole_0(k10_relat_1(sK0,X0),k10_relat_1(sK0,X1))) ) | (~spl3_1 | ~spl3_2)),
% 0.22/0.44    inference(subsumption_resolution,[],[f56,f30])).
% 0.22/0.44  fof(f30,plain,(
% 0.22/0.44    v1_relat_1(sK0) | ~spl3_2),
% 0.22/0.44    inference(avatar_component_clause,[],[f28])).
% 0.22/0.44  fof(f56,plain,(
% 0.22/0.44    ( ! [X0,X1] : (~v1_relat_1(sK0) | k10_relat_1(sK0,k3_xboole_0(X0,X1)) = k3_xboole_0(k10_relat_1(sK0,X0),k10_relat_1(sK0,X1))) ) | ~spl3_1),
% 0.22/0.44    inference(resolution,[],[f21,f25])).
% 0.22/0.44  fof(f25,plain,(
% 0.22/0.44    v1_funct_1(sK0) | ~spl3_1),
% 0.22/0.44    inference(avatar_component_clause,[],[f23])).
% 0.22/0.44  fof(f21,plain,(
% 0.22/0.44    ( ! [X2,X0,X1] : (~v1_funct_1(X2) | ~v1_relat_1(X2) | k10_relat_1(X2,k3_xboole_0(X0,X1)) = k3_xboole_0(k10_relat_1(X2,X0),k10_relat_1(X2,X1))) )),
% 0.22/0.44    inference(cnf_transformation,[],[f11])).
% 0.22/0.44  fof(f11,plain,(
% 0.22/0.44    ! [X0,X1,X2] : (k10_relat_1(X2,k3_xboole_0(X0,X1)) = k3_xboole_0(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 0.22/0.44    inference(flattening,[],[f10])).
% 0.22/0.44  fof(f10,plain,(
% 0.22/0.44    ! [X0,X1,X2] : (k10_relat_1(X2,k3_xboole_0(X0,X1)) = k3_xboole_0(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) | (~v1_funct_1(X2) | ~v1_relat_1(X2)))),
% 0.22/0.44    inference(ennf_transformation,[],[f4])).
% 0.22/0.44  fof(f4,axiom,(
% 0.22/0.44    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => k10_relat_1(X2,k3_xboole_0(X0,X1)) = k3_xboole_0(k10_relat_1(X2,X0),k10_relat_1(X2,X1)))),
% 0.22/0.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t137_funct_1)).
% 0.22/0.44  fof(f55,plain,(
% 0.22/0.44    spl3_6 | ~spl3_2),
% 0.22/0.44    inference(avatar_split_clause,[],[f51,f28,f53])).
% 0.22/0.44  fof(f51,plain,(
% 0.22/0.44    ( ! [X0] : (~r1_xboole_0(k2_relat_1(sK0),X0) | k1_xboole_0 = k10_relat_1(sK0,X0)) ) | ~spl3_2),
% 0.22/0.44    inference(resolution,[],[f17,f30])).
% 0.22/0.44  fof(f17,plain,(
% 0.22/0.44    ( ! [X0,X1] : (~v1_relat_1(X1) | ~r1_xboole_0(k2_relat_1(X1),X0) | k1_xboole_0 = k10_relat_1(X1,X0)) )),
% 0.22/0.44    inference(cnf_transformation,[],[f9])).
% 0.22/0.44  fof(f9,plain,(
% 0.22/0.44    ! [X0,X1] : ((k1_xboole_0 = k10_relat_1(X1,X0) <=> r1_xboole_0(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.22/0.44    inference(ennf_transformation,[],[f3])).
% 0.22/0.44  fof(f3,axiom,(
% 0.22/0.44    ! [X0,X1] : (v1_relat_1(X1) => (k1_xboole_0 = k10_relat_1(X1,X0) <=> r1_xboole_0(k2_relat_1(X1),X0)))),
% 0.22/0.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t173_relat_1)).
% 0.22/0.44  fof(f48,plain,(
% 0.22/0.44    spl3_5 | ~spl3_4),
% 0.22/0.44    inference(avatar_split_clause,[],[f42,f38,f45])).
% 0.22/0.44  fof(f38,plain,(
% 0.22/0.44    spl3_4 <=> r1_xboole_0(sK1,sK2)),
% 0.22/0.44    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.22/0.44  fof(f42,plain,(
% 0.22/0.44    k1_xboole_0 = k3_xboole_0(sK1,sK2) | ~spl3_4),
% 0.22/0.44    inference(resolution,[],[f20,f40])).
% 0.22/0.44  fof(f40,plain,(
% 0.22/0.44    r1_xboole_0(sK1,sK2) | ~spl3_4),
% 0.22/0.44    inference(avatar_component_clause,[],[f38])).
% 0.22/0.44  fof(f20,plain,(
% 0.22/0.44    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) = k1_xboole_0) )),
% 0.22/0.44    inference(cnf_transformation,[],[f1])).
% 0.22/0.44  fof(f41,plain,(
% 0.22/0.44    spl3_4),
% 0.22/0.44    inference(avatar_split_clause,[],[f12,f38])).
% 0.22/0.44  fof(f12,plain,(
% 0.22/0.44    r1_xboole_0(sK1,sK2)),
% 0.22/0.44    inference(cnf_transformation,[],[f8])).
% 0.22/0.44  fof(f8,plain,(
% 0.22/0.44    ? [X0] : (? [X1,X2] : (~r1_xboole_0(k10_relat_1(X0,X1),k10_relat_1(X0,X2)) & r1_xboole_0(X1,X2)) & v1_funct_1(X0) & v1_relat_1(X0))),
% 0.22/0.44    inference(flattening,[],[f7])).
% 0.22/0.44  fof(f7,plain,(
% 0.22/0.44    ? [X0] : (? [X1,X2] : (~r1_xboole_0(k10_relat_1(X0,X1),k10_relat_1(X0,X2)) & r1_xboole_0(X1,X2)) & (v1_funct_1(X0) & v1_relat_1(X0)))),
% 0.22/0.44    inference(ennf_transformation,[],[f6])).
% 0.22/0.44  fof(f6,negated_conjecture,(
% 0.22/0.44    ~! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1,X2] : (r1_xboole_0(X1,X2) => r1_xboole_0(k10_relat_1(X0,X1),k10_relat_1(X0,X2))))),
% 0.22/0.44    inference(negated_conjecture,[],[f5])).
% 0.22/0.44  fof(f5,conjecture,(
% 0.22/0.44    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1,X2] : (r1_xboole_0(X1,X2) => r1_xboole_0(k10_relat_1(X0,X1),k10_relat_1(X0,X2))))),
% 0.22/0.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t141_funct_1)).
% 0.22/0.44  fof(f36,plain,(
% 0.22/0.44    ~spl3_3),
% 0.22/0.44    inference(avatar_split_clause,[],[f13,f33])).
% 0.22/0.44  fof(f13,plain,(
% 0.22/0.44    ~r1_xboole_0(k10_relat_1(sK0,sK1),k10_relat_1(sK0,sK2))),
% 0.22/0.44    inference(cnf_transformation,[],[f8])).
% 0.22/0.44  fof(f31,plain,(
% 0.22/0.44    spl3_2),
% 0.22/0.44    inference(avatar_split_clause,[],[f14,f28])).
% 0.22/0.44  fof(f14,plain,(
% 0.22/0.44    v1_relat_1(sK0)),
% 0.22/0.44    inference(cnf_transformation,[],[f8])).
% 0.22/0.44  fof(f26,plain,(
% 0.22/0.44    spl3_1),
% 0.22/0.44    inference(avatar_split_clause,[],[f15,f23])).
% 0.22/0.44  fof(f15,plain,(
% 0.22/0.44    v1_funct_1(sK0)),
% 0.22/0.44    inference(cnf_transformation,[],[f8])).
% 0.22/0.44  % SZS output end Proof for theBenchmark
% 0.22/0.44  % (18927)------------------------------
% 0.22/0.44  % (18927)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.44  % (18927)Termination reason: Refutation
% 0.22/0.44  
% 0.22/0.44  % (18927)Memory used [KB]: 10618
% 0.22/0.44  % (18927)Time elapsed: 0.007 s
% 0.22/0.44  % (18927)------------------------------
% 0.22/0.44  % (18927)------------------------------
% 0.22/0.44  % (18924)Success in time 0.074 s
%------------------------------------------------------------------------------
