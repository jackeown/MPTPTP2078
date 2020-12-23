%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:53:29 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   63 ( 105 expanded)
%              Number of leaves         :   16 (  37 expanded)
%              Depth                    :    9
%              Number of atoms          :  147 ( 314 expanded)
%              Number of equality atoms :   28 (  40 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f111,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f37,f42,f47,f52,f57,f77,f87,f110])).

fof(f110,plain,
    ( ~ spl3_1
    | ~ spl3_2
    | ~ spl3_3
    | spl3_5
    | ~ spl3_7 ),
    inference(avatar_contradiction_clause,[],[f109])).

fof(f109,plain,
    ( $false
    | ~ spl3_1
    | ~ spl3_2
    | ~ spl3_3
    | spl3_5
    | ~ spl3_7 ),
    inference(subsumption_resolution,[],[f108,f56])).

fof(f56,plain,
    ( ~ r1_xboole_0(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1))
    | spl3_5 ),
    inference(avatar_component_clause,[],[f54])).

fof(f54,plain,
    ( spl3_5
  <=> r1_xboole_0(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f108,plain,
    ( r1_xboole_0(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1))
    | ~ spl3_1
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_7 ),
    inference(superposition,[],[f101,f86])).

fof(f86,plain,
    ( sK0 = k6_subset_1(sK0,sK1)
    | ~ spl3_7 ),
    inference(avatar_component_clause,[],[f84])).

fof(f84,plain,
    ( spl3_7
  <=> sK0 = k6_subset_1(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f101,plain,
    ( ! [X2,X3] : r1_xboole_0(k9_relat_1(sK2,k6_subset_1(X2,X3)),k9_relat_1(sK2,X3))
    | ~ spl3_1
    | ~ spl3_2
    | ~ spl3_3 ),
    inference(superposition,[],[f31,f71])).

fof(f71,plain,
    ( ! [X0,X1] : k9_relat_1(sK2,k6_subset_1(X0,X1)) = k6_subset_1(k9_relat_1(sK2,X0),k9_relat_1(sK2,X1))
    | ~ spl3_1
    | ~ spl3_2
    | ~ spl3_3 ),
    inference(unit_resulting_resolution,[],[f36,f41,f46,f29])).

fof(f29,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_funct_1(X2)
      | k9_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( k9_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
      | ~ v2_funct_1(X2)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ! [X0,X1,X2] :
      ( k9_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
      | ~ v2_funct_1(X2)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( v2_funct_1(X2)
       => k9_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t123_funct_1)).

fof(f46,plain,
    ( v2_funct_1(sK2)
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f44])).

fof(f44,plain,
    ( spl3_3
  <=> v2_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f41,plain,
    ( v1_funct_1(sK2)
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f39])).

fof(f39,plain,
    ( spl3_2
  <=> v1_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f36,plain,
    ( v1_relat_1(sK2)
    | ~ spl3_1 ),
    inference(avatar_component_clause,[],[f34])).

fof(f34,plain,
    ( spl3_1
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f31,plain,(
    ! [X0,X1] : r1_xboole_0(k6_subset_1(X0,X1),X1) ),
    inference(definition_unfolding,[],[f24,f25])).

fof(f25,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

fof(f24,plain,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_xboole_1)).

fof(f87,plain,
    ( spl3_7
    | ~ spl3_6 ),
    inference(avatar_split_clause,[],[f82,f74,f84])).

fof(f74,plain,
    ( spl3_6
  <=> k1_xboole_0 = k3_xboole_0(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f82,plain,
    ( sK0 = k6_subset_1(sK0,sK1)
    | ~ spl3_6 ),
    inference(forward_demodulation,[],[f79,f68])).

fof(f68,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(forward_demodulation,[],[f67,f30])).

fof(f30,plain,(
    ! [X0] : k6_subset_1(X0,k1_xboole_0) = X0 ),
    inference(definition_unfolding,[],[f23,f25])).

fof(f23,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

fof(f67,plain,(
    ! [X0] : k6_subset_1(X0,k1_xboole_0) = k5_xboole_0(X0,k1_xboole_0) ),
    inference(superposition,[],[f32,f22])).

fof(f22,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

fof(f32,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k6_subset_1(X0,X1) ),
    inference(definition_unfolding,[],[f26,f25])).

fof(f26,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f79,plain,
    ( k6_subset_1(sK0,sK1) = k5_xboole_0(sK0,k1_xboole_0)
    | ~ spl3_6 ),
    inference(superposition,[],[f32,f76])).

fof(f76,plain,
    ( k1_xboole_0 = k3_xboole_0(sK0,sK1)
    | ~ spl3_6 ),
    inference(avatar_component_clause,[],[f74])).

fof(f77,plain,
    ( spl3_6
    | ~ spl3_4 ),
    inference(avatar_split_clause,[],[f59,f49,f74])).

fof(f49,plain,
    ( spl3_4
  <=> r1_xboole_0(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f59,plain,
    ( k1_xboole_0 = k3_xboole_0(sK0,sK1)
    | ~ spl3_4 ),
    inference(unit_resulting_resolution,[],[f51,f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k3_xboole_0(X0,X1) != k1_xboole_0 )
      & ( k3_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).

fof(f51,plain,
    ( r1_xboole_0(sK0,sK1)
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f49])).

fof(f57,plain,(
    ~ spl3_5 ),
    inference(avatar_split_clause,[],[f21,f54])).

fof(f21,plain,(
    ~ r1_xboole_0(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1)) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,
    ( ~ r1_xboole_0(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1))
    & v2_funct_1(sK2)
    & r1_xboole_0(sK0,sK1)
    & v1_funct_1(sK2)
    & v1_relat_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f11,f14])).

fof(f14,plain,
    ( ? [X0,X1,X2] :
        ( ~ r1_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
        & v2_funct_1(X2)
        & r1_xboole_0(X0,X1)
        & v1_funct_1(X2)
        & v1_relat_1(X2) )
   => ( ~ r1_xboole_0(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1))
      & v2_funct_1(sK2)
      & r1_xboole_0(sK0,sK1)
      & v1_funct_1(sK2)
      & v1_relat_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f11,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
      & v2_funct_1(X2)
      & r1_xboole_0(X0,X1)
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
      & v2_funct_1(X2)
      & r1_xboole_0(X0,X1)
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( v1_funct_1(X2)
          & v1_relat_1(X2) )
       => ( ( v2_funct_1(X2)
            & r1_xboole_0(X0,X1) )
         => r1_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) ) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f8,conjecture,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( ( v2_funct_1(X2)
          & r1_xboole_0(X0,X1) )
       => r1_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t125_funct_1)).

fof(f52,plain,(
    spl3_4 ),
    inference(avatar_split_clause,[],[f19,f49])).

fof(f19,plain,(
    r1_xboole_0(sK0,sK1) ),
    inference(cnf_transformation,[],[f15])).

fof(f47,plain,(
    spl3_3 ),
    inference(avatar_split_clause,[],[f20,f44])).

fof(f20,plain,(
    v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f15])).

fof(f42,plain,(
    spl3_2 ),
    inference(avatar_split_clause,[],[f18,f39])).

fof(f18,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f15])).

fof(f37,plain,(
    spl3_1 ),
    inference(avatar_split_clause,[],[f17,f34])).

fof(f17,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f15])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 17:40:56 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.19/0.42  % (28586)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.19/0.43  % (28586)Refutation found. Thanks to Tanya!
% 0.19/0.43  % SZS status Theorem for theBenchmark
% 0.19/0.43  % SZS output start Proof for theBenchmark
% 0.19/0.43  fof(f111,plain,(
% 0.19/0.43    $false),
% 0.19/0.43    inference(avatar_sat_refutation,[],[f37,f42,f47,f52,f57,f77,f87,f110])).
% 0.19/0.43  fof(f110,plain,(
% 0.19/0.43    ~spl3_1 | ~spl3_2 | ~spl3_3 | spl3_5 | ~spl3_7),
% 0.19/0.43    inference(avatar_contradiction_clause,[],[f109])).
% 0.19/0.43  fof(f109,plain,(
% 0.19/0.43    $false | (~spl3_1 | ~spl3_2 | ~spl3_3 | spl3_5 | ~spl3_7)),
% 0.19/0.43    inference(subsumption_resolution,[],[f108,f56])).
% 0.19/0.43  fof(f56,plain,(
% 0.19/0.43    ~r1_xboole_0(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1)) | spl3_5),
% 0.19/0.43    inference(avatar_component_clause,[],[f54])).
% 0.19/0.43  fof(f54,plain,(
% 0.19/0.43    spl3_5 <=> r1_xboole_0(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1))),
% 0.19/0.43    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 0.19/0.43  fof(f108,plain,(
% 0.19/0.43    r1_xboole_0(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1)) | (~spl3_1 | ~spl3_2 | ~spl3_3 | ~spl3_7)),
% 0.19/0.43    inference(superposition,[],[f101,f86])).
% 0.19/0.43  fof(f86,plain,(
% 0.19/0.43    sK0 = k6_subset_1(sK0,sK1) | ~spl3_7),
% 0.19/0.43    inference(avatar_component_clause,[],[f84])).
% 0.19/0.43  fof(f84,plain,(
% 0.19/0.43    spl3_7 <=> sK0 = k6_subset_1(sK0,sK1)),
% 0.19/0.43    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).
% 0.19/0.43  fof(f101,plain,(
% 0.19/0.43    ( ! [X2,X3] : (r1_xboole_0(k9_relat_1(sK2,k6_subset_1(X2,X3)),k9_relat_1(sK2,X3))) ) | (~spl3_1 | ~spl3_2 | ~spl3_3)),
% 0.19/0.43    inference(superposition,[],[f31,f71])).
% 0.19/0.43  fof(f71,plain,(
% 0.19/0.43    ( ! [X0,X1] : (k9_relat_1(sK2,k6_subset_1(X0,X1)) = k6_subset_1(k9_relat_1(sK2,X0),k9_relat_1(sK2,X1))) ) | (~spl3_1 | ~spl3_2 | ~spl3_3)),
% 0.19/0.43    inference(unit_resulting_resolution,[],[f36,f41,f46,f29])).
% 0.19/0.43  fof(f29,plain,(
% 0.19/0.43    ( ! [X2,X0,X1] : (~v2_funct_1(X2) | k9_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 0.19/0.43    inference(cnf_transformation,[],[f13])).
% 0.19/0.43  fof(f13,plain,(
% 0.19/0.43    ! [X0,X1,X2] : (k9_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) | ~v2_funct_1(X2) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 0.19/0.43    inference(flattening,[],[f12])).
% 0.19/0.43  fof(f12,plain,(
% 0.19/0.43    ! [X0,X1,X2] : ((k9_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) | ~v2_funct_1(X2)) | (~v1_funct_1(X2) | ~v1_relat_1(X2)))),
% 0.19/0.43    inference(ennf_transformation,[],[f7])).
% 0.19/0.43  fof(f7,axiom,(
% 0.19/0.43    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (v2_funct_1(X2) => k9_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k9_relat_1(X2,X0),k9_relat_1(X2,X1))))),
% 0.19/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t123_funct_1)).
% 0.19/0.43  fof(f46,plain,(
% 0.19/0.43    v2_funct_1(sK2) | ~spl3_3),
% 0.19/0.43    inference(avatar_component_clause,[],[f44])).
% 0.19/0.43  fof(f44,plain,(
% 0.19/0.43    spl3_3 <=> v2_funct_1(sK2)),
% 0.19/0.43    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.19/0.43  fof(f41,plain,(
% 0.19/0.43    v1_funct_1(sK2) | ~spl3_2),
% 0.19/0.43    inference(avatar_component_clause,[],[f39])).
% 0.19/0.43  fof(f39,plain,(
% 0.19/0.43    spl3_2 <=> v1_funct_1(sK2)),
% 0.19/0.43    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.19/0.43  fof(f36,plain,(
% 0.19/0.43    v1_relat_1(sK2) | ~spl3_1),
% 0.19/0.43    inference(avatar_component_clause,[],[f34])).
% 0.19/0.43  fof(f34,plain,(
% 0.19/0.43    spl3_1 <=> v1_relat_1(sK2)),
% 0.19/0.43    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.19/0.43  fof(f31,plain,(
% 0.19/0.43    ( ! [X0,X1] : (r1_xboole_0(k6_subset_1(X0,X1),X1)) )),
% 0.19/0.43    inference(definition_unfolding,[],[f24,f25])).
% 0.19/0.43  fof(f25,plain,(
% 0.19/0.43    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k6_subset_1(X0,X1)) )),
% 0.19/0.43    inference(cnf_transformation,[],[f6])).
% 0.19/0.43  fof(f6,axiom,(
% 0.19/0.43    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1)),
% 0.19/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_subset_1)).
% 0.19/0.43  fof(f24,plain,(
% 0.19/0.43    ( ! [X0,X1] : (r1_xboole_0(k4_xboole_0(X0,X1),X1)) )),
% 0.19/0.43    inference(cnf_transformation,[],[f5])).
% 0.19/0.43  fof(f5,axiom,(
% 0.19/0.43    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1)),
% 0.19/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_xboole_1)).
% 0.19/0.43  fof(f87,plain,(
% 0.19/0.43    spl3_7 | ~spl3_6),
% 0.19/0.43    inference(avatar_split_clause,[],[f82,f74,f84])).
% 0.19/0.43  fof(f74,plain,(
% 0.19/0.43    spl3_6 <=> k1_xboole_0 = k3_xboole_0(sK0,sK1)),
% 0.19/0.43    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 0.19/0.43  fof(f82,plain,(
% 0.19/0.43    sK0 = k6_subset_1(sK0,sK1) | ~spl3_6),
% 0.19/0.43    inference(forward_demodulation,[],[f79,f68])).
% 0.19/0.43  fof(f68,plain,(
% 0.19/0.43    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.19/0.43    inference(forward_demodulation,[],[f67,f30])).
% 0.19/0.43  fof(f30,plain,(
% 0.19/0.43    ( ! [X0] : (k6_subset_1(X0,k1_xboole_0) = X0) )),
% 0.19/0.43    inference(definition_unfolding,[],[f23,f25])).
% 0.19/0.43  fof(f23,plain,(
% 0.19/0.43    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.19/0.43    inference(cnf_transformation,[],[f4])).
% 0.19/0.43  fof(f4,axiom,(
% 0.19/0.43    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 0.19/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).
% 0.19/0.43  fof(f67,plain,(
% 0.19/0.43    ( ! [X0] : (k6_subset_1(X0,k1_xboole_0) = k5_xboole_0(X0,k1_xboole_0)) )),
% 0.19/0.43    inference(superposition,[],[f32,f22])).
% 0.19/0.43  fof(f22,plain,(
% 0.19/0.43    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)) )),
% 0.19/0.43    inference(cnf_transformation,[],[f3])).
% 0.19/0.43  fof(f3,axiom,(
% 0.19/0.43    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)),
% 0.19/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).
% 0.19/0.43  fof(f32,plain,(
% 0.19/0.43    ( ! [X0,X1] : (k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k6_subset_1(X0,X1)) )),
% 0.19/0.43    inference(definition_unfolding,[],[f26,f25])).
% 0.19/0.43  fof(f26,plain,(
% 0.19/0.43    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 0.19/0.43    inference(cnf_transformation,[],[f2])).
% 0.19/0.43  fof(f2,axiom,(
% 0.19/0.43    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 0.19/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).
% 0.19/0.43  fof(f79,plain,(
% 0.19/0.43    k6_subset_1(sK0,sK1) = k5_xboole_0(sK0,k1_xboole_0) | ~spl3_6),
% 0.19/0.43    inference(superposition,[],[f32,f76])).
% 0.19/0.43  fof(f76,plain,(
% 0.19/0.43    k1_xboole_0 = k3_xboole_0(sK0,sK1) | ~spl3_6),
% 0.19/0.43    inference(avatar_component_clause,[],[f74])).
% 0.19/0.43  fof(f77,plain,(
% 0.19/0.43    spl3_6 | ~spl3_4),
% 0.19/0.43    inference(avatar_split_clause,[],[f59,f49,f74])).
% 0.19/0.43  fof(f49,plain,(
% 0.19/0.43    spl3_4 <=> r1_xboole_0(sK0,sK1)),
% 0.19/0.43    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.19/0.43  fof(f59,plain,(
% 0.19/0.43    k1_xboole_0 = k3_xboole_0(sK0,sK1) | ~spl3_4),
% 0.19/0.43    inference(unit_resulting_resolution,[],[f51,f27])).
% 0.19/0.43  fof(f27,plain,(
% 0.19/0.43    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) = k1_xboole_0) )),
% 0.19/0.43    inference(cnf_transformation,[],[f16])).
% 0.19/0.43  fof(f16,plain,(
% 0.19/0.43    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) & (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)))),
% 0.19/0.43    inference(nnf_transformation,[],[f1])).
% 0.19/0.43  fof(f1,axiom,(
% 0.19/0.43    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 0.19/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).
% 0.19/0.43  fof(f51,plain,(
% 0.19/0.43    r1_xboole_0(sK0,sK1) | ~spl3_4),
% 0.19/0.43    inference(avatar_component_clause,[],[f49])).
% 0.19/0.43  fof(f57,plain,(
% 0.19/0.43    ~spl3_5),
% 0.19/0.43    inference(avatar_split_clause,[],[f21,f54])).
% 0.19/0.43  fof(f21,plain,(
% 0.19/0.43    ~r1_xboole_0(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1))),
% 0.19/0.43    inference(cnf_transformation,[],[f15])).
% 0.19/0.43  fof(f15,plain,(
% 0.19/0.43    ~r1_xboole_0(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1)) & v2_funct_1(sK2) & r1_xboole_0(sK0,sK1) & v1_funct_1(sK2) & v1_relat_1(sK2)),
% 0.19/0.43    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f11,f14])).
% 0.19/0.43  fof(f14,plain,(
% 0.19/0.43    ? [X0,X1,X2] : (~r1_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) & v2_funct_1(X2) & r1_xboole_0(X0,X1) & v1_funct_1(X2) & v1_relat_1(X2)) => (~r1_xboole_0(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1)) & v2_funct_1(sK2) & r1_xboole_0(sK0,sK1) & v1_funct_1(sK2) & v1_relat_1(sK2))),
% 0.19/0.43    introduced(choice_axiom,[])).
% 0.19/0.43  fof(f11,plain,(
% 0.19/0.43    ? [X0,X1,X2] : (~r1_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) & v2_funct_1(X2) & r1_xboole_0(X0,X1) & v1_funct_1(X2) & v1_relat_1(X2))),
% 0.19/0.43    inference(flattening,[],[f10])).
% 0.19/0.43  fof(f10,plain,(
% 0.19/0.43    ? [X0,X1,X2] : ((~r1_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) & (v2_funct_1(X2) & r1_xboole_0(X0,X1))) & (v1_funct_1(X2) & v1_relat_1(X2)))),
% 0.19/0.43    inference(ennf_transformation,[],[f9])).
% 0.19/0.43  fof(f9,negated_conjecture,(
% 0.19/0.43    ~! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ((v2_funct_1(X2) & r1_xboole_0(X0,X1)) => r1_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1))))),
% 0.19/0.43    inference(negated_conjecture,[],[f8])).
% 0.19/0.43  fof(f8,conjecture,(
% 0.19/0.43    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ((v2_funct_1(X2) & r1_xboole_0(X0,X1)) => r1_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1))))),
% 0.19/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t125_funct_1)).
% 0.19/0.43  fof(f52,plain,(
% 0.19/0.43    spl3_4),
% 0.19/0.43    inference(avatar_split_clause,[],[f19,f49])).
% 0.19/0.43  fof(f19,plain,(
% 0.19/0.43    r1_xboole_0(sK0,sK1)),
% 0.19/0.43    inference(cnf_transformation,[],[f15])).
% 0.19/0.43  fof(f47,plain,(
% 0.19/0.43    spl3_3),
% 0.19/0.43    inference(avatar_split_clause,[],[f20,f44])).
% 0.19/0.43  fof(f20,plain,(
% 0.19/0.43    v2_funct_1(sK2)),
% 0.19/0.43    inference(cnf_transformation,[],[f15])).
% 0.19/0.43  fof(f42,plain,(
% 0.19/0.43    spl3_2),
% 0.19/0.43    inference(avatar_split_clause,[],[f18,f39])).
% 0.19/0.43  fof(f18,plain,(
% 0.19/0.43    v1_funct_1(sK2)),
% 0.19/0.43    inference(cnf_transformation,[],[f15])).
% 0.19/0.43  fof(f37,plain,(
% 0.19/0.43    spl3_1),
% 0.19/0.43    inference(avatar_split_clause,[],[f17,f34])).
% 0.19/0.43  fof(f17,plain,(
% 0.19/0.43    v1_relat_1(sK2)),
% 0.19/0.43    inference(cnf_transformation,[],[f15])).
% 0.19/0.43  % SZS output end Proof for theBenchmark
% 0.19/0.43  % (28586)------------------------------
% 0.19/0.43  % (28586)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.43  % (28586)Termination reason: Refutation
% 0.19/0.43  
% 0.19/0.43  % (28586)Memory used [KB]: 10618
% 0.19/0.43  % (28586)Time elapsed: 0.008 s
% 0.19/0.43  % (28586)------------------------------
% 0.19/0.43  % (28586)------------------------------
% 0.19/0.43  % (28570)Success in time 0.078 s
%------------------------------------------------------------------------------
