%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:56:27 EST 2020

% Result     : Theorem 1.47s
% Output     : Refutation 1.47s
% Verified   : 
% Statistics : Number of formulae       :   95 ( 152 expanded)
%              Number of leaves         :   22 (  53 expanded)
%              Depth                    :   14
%              Number of atoms          :  239 ( 382 expanded)
%              Number of equality atoms :   46 (  64 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f758,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f56,f61,f66,f75,f104,f258,f597,f626,f725])).

fof(f725,plain,
    ( ~ spl3_1
    | spl3_3
    | ~ spl3_21 ),
    inference(avatar_contradiction_clause,[],[f724])).

fof(f724,plain,
    ( $false
    | ~ spl3_1
    | spl3_3
    | ~ spl3_21 ),
    inference(subsumption_resolution,[],[f723,f67])).

fof(f67,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(resolution,[],[f45,f34])).

fof(f34,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

fof(f45,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f723,plain,
    ( ~ r1_tarski(k1_xboole_0,k2_xboole_0(sK0,sK1))
    | ~ spl3_1
    | spl3_3
    | ~ spl3_21 ),
    inference(forward_demodulation,[],[f690,f55])).

fof(f55,plain,
    ( k1_xboole_0 = k3_relat_1(k1_xboole_0)
    | ~ spl3_1 ),
    inference(avatar_component_clause,[],[f53])).

fof(f53,plain,
    ( spl3_1
  <=> k1_xboole_0 = k3_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f690,plain,
    ( ~ r1_tarski(k3_relat_1(k1_xboole_0),k2_xboole_0(sK0,sK1))
    | spl3_3
    | ~ spl3_21 ),
    inference(backward_demodulation,[],[f65,f682])).

fof(f682,plain,
    ( k1_xboole_0 = sK2
    | ~ spl3_21 ),
    inference(resolution,[],[f271,f78])).

fof(f78,plain,(
    ! [X3] :
      ( ~ r1_tarski(X3,k1_xboole_0)
      | k1_xboole_0 = X3 ) ),
    inference(resolution,[],[f44,f67])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r1_tarski(X1,X0)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
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

fof(f271,plain,
    ( r1_tarski(sK2,k1_xboole_0)
    | ~ spl3_21 ),
    inference(avatar_component_clause,[],[f270])).

fof(f270,plain,
    ( spl3_21
  <=> r1_tarski(sK2,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_21])])).

fof(f65,plain,
    ( ~ r1_tarski(k3_relat_1(sK2),k2_xboole_0(sK0,sK1))
    | spl3_3 ),
    inference(avatar_component_clause,[],[f63])).

fof(f63,plain,
    ( spl3_3
  <=> r1_tarski(k3_relat_1(sK2),k2_xboole_0(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f626,plain,
    ( spl3_21
    | spl3_3
    | ~ spl3_4
    | ~ spl3_47 ),
    inference(avatar_split_clause,[],[f611,f595,f72,f63,f270])).

fof(f72,plain,
    ( spl3_4
  <=> r1_tarski(sK2,k2_zfmisc_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f595,plain,
    ( spl3_47
  <=> ! [X7,X6] :
        ( r1_tarski(k3_relat_1(sK2),k2_xboole_0(X6,X7))
        | ~ r1_tarski(sK2,k2_zfmisc_1(X6,X7))
        | k1_xboole_0 = k2_zfmisc_1(X6,X7) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_47])])).

fof(f611,plain,
    ( r1_tarski(sK2,k1_xboole_0)
    | spl3_3
    | ~ spl3_4
    | ~ spl3_47 ),
    inference(backward_demodulation,[],[f74,f606])).

fof(f606,plain,
    ( k1_xboole_0 = k2_zfmisc_1(sK0,sK1)
    | spl3_3
    | ~ spl3_4
    | ~ spl3_47 ),
    inference(subsumption_resolution,[],[f604,f65])).

fof(f604,plain,
    ( r1_tarski(k3_relat_1(sK2),k2_xboole_0(sK0,sK1))
    | k1_xboole_0 = k2_zfmisc_1(sK0,sK1)
    | ~ spl3_4
    | ~ spl3_47 ),
    inference(resolution,[],[f596,f74])).

fof(f596,plain,
    ( ! [X6,X7] :
        ( ~ r1_tarski(sK2,k2_zfmisc_1(X6,X7))
        | r1_tarski(k3_relat_1(sK2),k2_xboole_0(X6,X7))
        | k1_xboole_0 = k2_zfmisc_1(X6,X7) )
    | ~ spl3_47 ),
    inference(avatar_component_clause,[],[f595])).

fof(f74,plain,
    ( r1_tarski(sK2,k2_zfmisc_1(sK0,sK1))
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f72])).

fof(f597,plain,
    ( spl3_47
    | ~ spl3_19 ),
    inference(avatar_split_clause,[],[f417,f256,f595])).

fof(f256,plain,
    ( spl3_19
  <=> ! [X0] :
        ( ~ r1_tarski(sK2,X0)
        | ~ v1_relat_1(X0)
        | r1_tarski(k3_relat_1(sK2),k3_relat_1(X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_19])])).

fof(f417,plain,
    ( ! [X6,X7] :
        ( r1_tarski(k3_relat_1(sK2),k2_xboole_0(X6,X7))
        | ~ r1_tarski(sK2,k2_zfmisc_1(X6,X7))
        | k1_xboole_0 = k2_zfmisc_1(X6,X7) )
    | ~ spl3_19 ),
    inference(subsumption_resolution,[],[f414,f39])).

fof(f39,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f414,plain,
    ( ! [X6,X7] :
        ( r1_tarski(k3_relat_1(sK2),k2_xboole_0(X6,X7))
        | ~ v1_relat_1(k2_zfmisc_1(X6,X7))
        | ~ r1_tarski(sK2,k2_zfmisc_1(X6,X7))
        | k1_xboole_0 = k2_zfmisc_1(X6,X7) )
    | ~ spl3_19 ),
    inference(superposition,[],[f257,f315])).

fof(f315,plain,(
    ! [X2,X1] :
      ( k3_relat_1(k2_zfmisc_1(X1,X2)) = k2_xboole_0(X1,X2)
      | k1_xboole_0 = k2_zfmisc_1(X1,X2) ) ),
    inference(duplicate_literal_removal,[],[f314])).

fof(f314,plain,(
    ! [X2,X1] :
      ( k3_relat_1(k2_zfmisc_1(X1,X2)) = k2_xboole_0(X1,X2)
      | k1_xboole_0 = k2_zfmisc_1(X1,X2)
      | k1_xboole_0 = k2_zfmisc_1(X1,X2) ) ),
    inference(superposition,[],[f180,f121])).

fof(f121,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k2_zfmisc_1(X0,X1)) = X1
      | k2_zfmisc_1(X0,X1) = k1_xboole_0 ) ),
    inference(subsumption_resolution,[],[f119,f41])).

fof(f41,plain,(
    ! [X0,X1] : r1_tarski(k2_relat_1(k2_zfmisc_1(X0,X1)),X1) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] : r1_tarski(k2_relat_1(k2_zfmisc_1(X0,X1)),X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t194_relat_1)).

fof(f119,plain,(
    ! [X0,X1] :
      ( k2_zfmisc_1(X0,X1) = k1_xboole_0
      | ~ r1_tarski(k2_relat_1(k2_zfmisc_1(X0,X1)),X1)
      | k2_relat_1(k2_zfmisc_1(X0,X1)) = X1 ) ),
    inference(resolution,[],[f107,f44])).

fof(f107,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,k2_relat_1(k2_zfmisc_1(X0,X1)))
      | k2_zfmisc_1(X0,X1) = k1_xboole_0 ) ),
    inference(subsumption_resolution,[],[f105,f39])).

fof(f105,plain,(
    ! [X0,X1] :
      ( k2_zfmisc_1(X0,X1) = k1_xboole_0
      | r1_tarski(X1,k2_relat_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_relat_1(k2_zfmisc_1(X0,X1)) ) ),
    inference(resolution,[],[f49,f35])).

fof(f35,plain,(
    ! [X0] :
      ( r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_relat_1)).

fof(f49,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3))
      | k2_zfmisc_1(X0,X1) = k1_xboole_0
      | r1_tarski(X1,X3) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r1_tarski(X1,X3)
        & r1_tarski(X0,X2) )
      | k2_zfmisc_1(X0,X1) = k1_xboole_0
      | ~ r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r1_tarski(X1,X3)
        & r1_tarski(X0,X2) )
      | k2_zfmisc_1(X0,X1) = k1_xboole_0
      | ~ r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2,X3] :
      ( r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3))
     => ( ( r1_tarski(X1,X3)
          & r1_tarski(X0,X2) )
        | k2_zfmisc_1(X0,X1) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t138_zfmisc_1)).

fof(f180,plain,(
    ! [X0,X1] :
      ( k3_relat_1(k2_zfmisc_1(X0,X1)) = k2_xboole_0(X0,k2_relat_1(k2_zfmisc_1(X0,X1)))
      | k2_zfmisc_1(X0,X1) = k1_xboole_0 ) ),
    inference(superposition,[],[f86,f113])).

fof(f113,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k2_zfmisc_1(X0,X1)) = X0
      | k2_zfmisc_1(X0,X1) = k1_xboole_0 ) ),
    inference(subsumption_resolution,[],[f111,f40])).

fof(f40,plain,(
    ! [X0,X1] : r1_tarski(k1_relat_1(k2_zfmisc_1(X0,X1)),X0) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : r1_tarski(k1_relat_1(k2_zfmisc_1(X0,X1)),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t193_relat_1)).

fof(f111,plain,(
    ! [X0,X1] :
      ( k2_zfmisc_1(X0,X1) = k1_xboole_0
      | ~ r1_tarski(k1_relat_1(k2_zfmisc_1(X0,X1)),X0)
      | k1_relat_1(k2_zfmisc_1(X0,X1)) = X0 ) ),
    inference(resolution,[],[f99,f44])).

fof(f99,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k1_relat_1(k2_zfmisc_1(X0,X1)))
      | k2_zfmisc_1(X0,X1) = k1_xboole_0 ) ),
    inference(subsumption_resolution,[],[f97,f39])).

fof(f97,plain,(
    ! [X0,X1] :
      ( k2_zfmisc_1(X0,X1) = k1_xboole_0
      | r1_tarski(X0,k1_relat_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_relat_1(k2_zfmisc_1(X0,X1)) ) ),
    inference(resolution,[],[f48,f35])).

fof(f48,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3))
      | k2_zfmisc_1(X0,X1) = k1_xboole_0
      | r1_tarski(X0,X2) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f86,plain,(
    ! [X0,X1] : k3_relat_1(k2_zfmisc_1(X0,X1)) = k2_xboole_0(k1_relat_1(k2_zfmisc_1(X0,X1)),k2_relat_1(k2_zfmisc_1(X0,X1))) ),
    inference(resolution,[],[f36,f39])).

fof(f36,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d6_relat_1)).

fof(f257,plain,
    ( ! [X0] :
        ( r1_tarski(k3_relat_1(sK2),k3_relat_1(X0))
        | ~ v1_relat_1(X0)
        | ~ r1_tarski(sK2,X0) )
    | ~ spl3_19 ),
    inference(avatar_component_clause,[],[f256])).

fof(f258,plain,
    ( spl3_19
    | ~ spl3_5 ),
    inference(avatar_split_clause,[],[f108,f101,f256])).

fof(f101,plain,
    ( spl3_5
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f108,plain,
    ( ! [X0] :
        ( ~ r1_tarski(sK2,X0)
        | ~ v1_relat_1(X0)
        | r1_tarski(k3_relat_1(sK2),k3_relat_1(X0)) )
    | ~ spl3_5 ),
    inference(resolution,[],[f103,f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X1)
      | r1_tarski(k3_relat_1(X0),k3_relat_1(X1)) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k3_relat_1(X0),k3_relat_1(X1))
          | ~ r1_tarski(X0,X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k3_relat_1(X0),k3_relat_1(X1))
          | ~ r1_tarski(X0,X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ( r1_tarski(X0,X1)
           => r1_tarski(k3_relat_1(X0),k3_relat_1(X1)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_relat_1)).

fof(f103,plain,
    ( v1_relat_1(sK2)
    | ~ spl3_5 ),
    inference(avatar_component_clause,[],[f101])).

fof(f104,plain,
    ( spl3_5
    | ~ spl3_2 ),
    inference(avatar_split_clause,[],[f95,f58,f101])).

fof(f58,plain,
    ( spl3_2
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f95,plain,
    ( v1_relat_1(sK2)
    | ~ spl3_2 ),
    inference(resolution,[],[f70,f60])).

fof(f60,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f58])).

fof(f70,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | v1_relat_1(X0) ) ),
    inference(resolution,[],[f38,f39])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

fof(f75,plain,
    ( spl3_4
    | ~ spl3_2 ),
    inference(avatar_split_clause,[],[f68,f58,f72])).

fof(f68,plain,
    ( r1_tarski(sK2,k2_zfmisc_1(sK0,sK1))
    | ~ spl3_2 ),
    inference(resolution,[],[f45,f60])).

fof(f66,plain,(
    ~ spl3_3 ),
    inference(avatar_split_clause,[],[f32,f63])).

fof(f32,plain,(
    ~ r1_tarski(k3_relat_1(sK2),k2_xboole_0(sK0,sK1)) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,
    ( ~ r1_tarski(k3_relat_1(sK2),k2_xboole_0(sK0,sK1))
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f16,f26])).

fof(f26,plain,
    ( ? [X0,X1,X2] :
        ( ~ r1_tarski(k3_relat_1(X2),k2_xboole_0(X0,X1))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
   => ( ~ r1_tarski(k3_relat_1(sK2),k2_xboole_0(sK0,sK1))
      & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(k3_relat_1(X2),k2_xboole_0(X0,X1))
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
       => r1_tarski(k3_relat_1(X2),k2_xboole_0(X0,X1)) ) ),
    inference(negated_conjecture,[],[f14])).

fof(f14,conjecture,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => r1_tarski(k3_relat_1(X2),k2_xboole_0(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t19_relset_1)).

fof(f61,plain,(
    spl3_2 ),
    inference(avatar_split_clause,[],[f31,f58])).

fof(f31,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f27])).

fof(f56,plain,(
    spl3_1 ),
    inference(avatar_split_clause,[],[f33,f53])).

fof(f33,plain,(
    k1_xboole_0 = k3_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    k1_xboole_0 = k3_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_relat_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_vampire %s %d
% 0.16/0.35  % Computer   : n023.cluster.edu
% 0.16/0.35  % Model      : x86_64 x86_64
% 0.16/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.16/0.35  % Memory     : 8042.1875MB
% 0.16/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.16/0.35  % CPULimit   : 60
% 0.16/0.35  % WCLimit    : 600
% 0.16/0.35  % DateTime   : Tue Dec  1 12:31:06 EST 2020
% 0.16/0.36  % CPUTime    : 
% 0.22/0.47  % (8752)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 0.22/0.48  % (8759)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 0.22/0.51  % (8766)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 0.22/0.51  % (8758)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.22/0.52  % (8756)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 0.22/0.52  % (8748)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.22/0.52  % (8755)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 0.22/0.52  % (8744)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 0.22/0.52  % (8746)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.22/0.52  % (8745)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 0.22/0.52  % (8745)Refutation not found, incomplete strategy% (8745)------------------------------
% 0.22/0.52  % (8745)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.52  % (8745)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.52  
% 0.22/0.52  % (8745)Memory used [KB]: 10618
% 0.22/0.52  % (8745)Time elapsed: 0.091 s
% 0.22/0.52  % (8745)------------------------------
% 0.22/0.52  % (8745)------------------------------
% 0.22/0.52  % (8754)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 1.28/0.53  % (8750)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 1.28/0.53  % (8751)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 1.28/0.53  % (8761)lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_145 on theBenchmark
% 1.28/0.53  % (8768)dis+2_128_add=large:afp=100000:afq=1.4:amm=sco:anc=none:lma=on:nm=2:newcnf=on:nwc=1:nicw=on:sas=z3:sos=theory:sac=on:updr=off_288 on theBenchmark
% 1.28/0.53  % (8769)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_364 on theBenchmark
% 1.28/0.54  % (8765)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 1.28/0.54  % (8760)lrs+4_5:4_av=off:bd=off:er=filter:lma=on:lwlo=on:nwc=1:stl=30:sp=occurrence:updr=off_230 on theBenchmark
% 1.28/0.54  % (8763)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 1.28/0.54  % (8747)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 1.28/0.55  % (8749)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 1.28/0.55  % (8749)Refutation not found, incomplete strategy% (8749)------------------------------
% 1.28/0.55  % (8749)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.28/0.55  % (8749)Termination reason: Refutation not found, incomplete strategy
% 1.28/0.55  
% 1.28/0.55  % (8749)Memory used [KB]: 6140
% 1.28/0.55  % (8749)Time elapsed: 0.127 s
% 1.28/0.55  % (8749)------------------------------
% 1.28/0.55  % (8749)------------------------------
% 1.47/0.55  % (8757)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 1.47/0.55  % (8767)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 1.47/0.56  % (8753)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
% 1.47/0.56  % (8762)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 1.47/0.57  % (8764)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 1.47/0.57  % (8746)Refutation found. Thanks to Tanya!
% 1.47/0.57  % SZS status Theorem for theBenchmark
% 1.47/0.57  % SZS output start Proof for theBenchmark
% 1.47/0.57  fof(f758,plain,(
% 1.47/0.57    $false),
% 1.47/0.57    inference(avatar_sat_refutation,[],[f56,f61,f66,f75,f104,f258,f597,f626,f725])).
% 1.47/0.57  fof(f725,plain,(
% 1.47/0.57    ~spl3_1 | spl3_3 | ~spl3_21),
% 1.47/0.57    inference(avatar_contradiction_clause,[],[f724])).
% 1.47/0.57  fof(f724,plain,(
% 1.47/0.57    $false | (~spl3_1 | spl3_3 | ~spl3_21)),
% 1.47/0.57    inference(subsumption_resolution,[],[f723,f67])).
% 1.47/0.57  fof(f67,plain,(
% 1.47/0.57    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 1.47/0.57    inference(resolution,[],[f45,f34])).
% 1.47/0.57  fof(f34,plain,(
% 1.47/0.57    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 1.47/0.57    inference(cnf_transformation,[],[f3])).
% 1.47/0.57  fof(f3,axiom,(
% 1.47/0.57    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 1.47/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).
% 1.47/0.57  fof(f45,plain,(
% 1.47/0.57    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 1.47/0.57    inference(cnf_transformation,[],[f30])).
% 1.47/0.57  fof(f30,plain,(
% 1.47/0.57    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 1.47/0.57    inference(nnf_transformation,[],[f4])).
% 1.47/0.57  fof(f4,axiom,(
% 1.47/0.57    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 1.47/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).
% 1.47/0.57  fof(f723,plain,(
% 1.47/0.57    ~r1_tarski(k1_xboole_0,k2_xboole_0(sK0,sK1)) | (~spl3_1 | spl3_3 | ~spl3_21)),
% 1.47/0.57    inference(forward_demodulation,[],[f690,f55])).
% 1.47/0.57  fof(f55,plain,(
% 1.47/0.57    k1_xboole_0 = k3_relat_1(k1_xboole_0) | ~spl3_1),
% 1.47/0.57    inference(avatar_component_clause,[],[f53])).
% 1.47/0.57  fof(f53,plain,(
% 1.47/0.57    spl3_1 <=> k1_xboole_0 = k3_relat_1(k1_xboole_0)),
% 1.47/0.57    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 1.47/0.57  fof(f690,plain,(
% 1.47/0.57    ~r1_tarski(k3_relat_1(k1_xboole_0),k2_xboole_0(sK0,sK1)) | (spl3_3 | ~spl3_21)),
% 1.47/0.57    inference(backward_demodulation,[],[f65,f682])).
% 1.47/0.57  fof(f682,plain,(
% 1.47/0.57    k1_xboole_0 = sK2 | ~spl3_21),
% 1.47/0.57    inference(resolution,[],[f271,f78])).
% 1.47/0.57  fof(f78,plain,(
% 1.47/0.57    ( ! [X3] : (~r1_tarski(X3,k1_xboole_0) | k1_xboole_0 = X3) )),
% 1.47/0.57    inference(resolution,[],[f44,f67])).
% 1.47/0.57  fof(f44,plain,(
% 1.47/0.57    ( ! [X0,X1] : (~r1_tarski(X0,X1) | ~r1_tarski(X1,X0) | X0 = X1) )),
% 1.47/0.57    inference(cnf_transformation,[],[f29])).
% 1.47/0.57  fof(f29,plain,(
% 1.47/0.57    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.47/0.57    inference(flattening,[],[f28])).
% 1.47/0.57  fof(f28,plain,(
% 1.47/0.57    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.47/0.57    inference(nnf_transformation,[],[f1])).
% 1.47/0.57  fof(f1,axiom,(
% 1.47/0.57    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.47/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 1.47/0.57  fof(f271,plain,(
% 1.47/0.57    r1_tarski(sK2,k1_xboole_0) | ~spl3_21),
% 1.47/0.57    inference(avatar_component_clause,[],[f270])).
% 1.47/0.57  fof(f270,plain,(
% 1.47/0.57    spl3_21 <=> r1_tarski(sK2,k1_xboole_0)),
% 1.47/0.57    introduced(avatar_definition,[new_symbols(naming,[spl3_21])])).
% 1.47/0.57  fof(f65,plain,(
% 1.47/0.57    ~r1_tarski(k3_relat_1(sK2),k2_xboole_0(sK0,sK1)) | spl3_3),
% 1.47/0.57    inference(avatar_component_clause,[],[f63])).
% 1.47/0.57  fof(f63,plain,(
% 1.47/0.57    spl3_3 <=> r1_tarski(k3_relat_1(sK2),k2_xboole_0(sK0,sK1))),
% 1.47/0.57    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 1.47/0.57  fof(f626,plain,(
% 1.47/0.57    spl3_21 | spl3_3 | ~spl3_4 | ~spl3_47),
% 1.47/0.57    inference(avatar_split_clause,[],[f611,f595,f72,f63,f270])).
% 1.47/0.57  fof(f72,plain,(
% 1.47/0.57    spl3_4 <=> r1_tarski(sK2,k2_zfmisc_1(sK0,sK1))),
% 1.47/0.57    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 1.47/0.57  fof(f595,plain,(
% 1.47/0.57    spl3_47 <=> ! [X7,X6] : (r1_tarski(k3_relat_1(sK2),k2_xboole_0(X6,X7)) | ~r1_tarski(sK2,k2_zfmisc_1(X6,X7)) | k1_xboole_0 = k2_zfmisc_1(X6,X7))),
% 1.47/0.57    introduced(avatar_definition,[new_symbols(naming,[spl3_47])])).
% 1.47/0.57  fof(f611,plain,(
% 1.47/0.57    r1_tarski(sK2,k1_xboole_0) | (spl3_3 | ~spl3_4 | ~spl3_47)),
% 1.47/0.57    inference(backward_demodulation,[],[f74,f606])).
% 1.47/0.57  fof(f606,plain,(
% 1.47/0.57    k1_xboole_0 = k2_zfmisc_1(sK0,sK1) | (spl3_3 | ~spl3_4 | ~spl3_47)),
% 1.47/0.57    inference(subsumption_resolution,[],[f604,f65])).
% 1.47/0.57  fof(f604,plain,(
% 1.47/0.57    r1_tarski(k3_relat_1(sK2),k2_xboole_0(sK0,sK1)) | k1_xboole_0 = k2_zfmisc_1(sK0,sK1) | (~spl3_4 | ~spl3_47)),
% 1.47/0.57    inference(resolution,[],[f596,f74])).
% 1.47/0.57  fof(f596,plain,(
% 1.47/0.57    ( ! [X6,X7] : (~r1_tarski(sK2,k2_zfmisc_1(X6,X7)) | r1_tarski(k3_relat_1(sK2),k2_xboole_0(X6,X7)) | k1_xboole_0 = k2_zfmisc_1(X6,X7)) ) | ~spl3_47),
% 1.47/0.57    inference(avatar_component_clause,[],[f595])).
% 1.47/0.57  fof(f74,plain,(
% 1.47/0.57    r1_tarski(sK2,k2_zfmisc_1(sK0,sK1)) | ~spl3_4),
% 1.47/0.57    inference(avatar_component_clause,[],[f72])).
% 1.47/0.57  fof(f597,plain,(
% 1.47/0.57    spl3_47 | ~spl3_19),
% 1.47/0.57    inference(avatar_split_clause,[],[f417,f256,f595])).
% 1.47/0.57  fof(f256,plain,(
% 1.47/0.57    spl3_19 <=> ! [X0] : (~r1_tarski(sK2,X0) | ~v1_relat_1(X0) | r1_tarski(k3_relat_1(sK2),k3_relat_1(X0)))),
% 1.47/0.57    introduced(avatar_definition,[new_symbols(naming,[spl3_19])])).
% 1.47/0.57  fof(f417,plain,(
% 1.47/0.57    ( ! [X6,X7] : (r1_tarski(k3_relat_1(sK2),k2_xboole_0(X6,X7)) | ~r1_tarski(sK2,k2_zfmisc_1(X6,X7)) | k1_xboole_0 = k2_zfmisc_1(X6,X7)) ) | ~spl3_19),
% 1.47/0.57    inference(subsumption_resolution,[],[f414,f39])).
% 1.47/0.57  fof(f39,plain,(
% 1.47/0.57    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 1.47/0.57    inference(cnf_transformation,[],[f8])).
% 1.47/0.57  fof(f8,axiom,(
% 1.47/0.57    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 1.47/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).
% 1.47/0.57  fof(f414,plain,(
% 1.47/0.57    ( ! [X6,X7] : (r1_tarski(k3_relat_1(sK2),k2_xboole_0(X6,X7)) | ~v1_relat_1(k2_zfmisc_1(X6,X7)) | ~r1_tarski(sK2,k2_zfmisc_1(X6,X7)) | k1_xboole_0 = k2_zfmisc_1(X6,X7)) ) | ~spl3_19),
% 1.47/0.57    inference(superposition,[],[f257,f315])).
% 1.47/0.57  fof(f315,plain,(
% 1.47/0.57    ( ! [X2,X1] : (k3_relat_1(k2_zfmisc_1(X1,X2)) = k2_xboole_0(X1,X2) | k1_xboole_0 = k2_zfmisc_1(X1,X2)) )),
% 1.47/0.57    inference(duplicate_literal_removal,[],[f314])).
% 1.47/0.57  fof(f314,plain,(
% 1.47/0.57    ( ! [X2,X1] : (k3_relat_1(k2_zfmisc_1(X1,X2)) = k2_xboole_0(X1,X2) | k1_xboole_0 = k2_zfmisc_1(X1,X2) | k1_xboole_0 = k2_zfmisc_1(X1,X2)) )),
% 1.47/0.57    inference(superposition,[],[f180,f121])).
% 1.47/0.57  fof(f121,plain,(
% 1.47/0.57    ( ! [X0,X1] : (k2_relat_1(k2_zfmisc_1(X0,X1)) = X1 | k2_zfmisc_1(X0,X1) = k1_xboole_0) )),
% 1.47/0.57    inference(subsumption_resolution,[],[f119,f41])).
% 1.47/0.57  fof(f41,plain,(
% 1.47/0.57    ( ! [X0,X1] : (r1_tarski(k2_relat_1(k2_zfmisc_1(X0,X1)),X1)) )),
% 1.47/0.57    inference(cnf_transformation,[],[f10])).
% 1.47/0.57  fof(f10,axiom,(
% 1.47/0.57    ! [X0,X1] : r1_tarski(k2_relat_1(k2_zfmisc_1(X0,X1)),X1)),
% 1.47/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t194_relat_1)).
% 1.47/0.57  fof(f119,plain,(
% 1.47/0.57    ( ! [X0,X1] : (k2_zfmisc_1(X0,X1) = k1_xboole_0 | ~r1_tarski(k2_relat_1(k2_zfmisc_1(X0,X1)),X1) | k2_relat_1(k2_zfmisc_1(X0,X1)) = X1) )),
% 1.47/0.57    inference(resolution,[],[f107,f44])).
% 1.47/0.57  fof(f107,plain,(
% 1.47/0.57    ( ! [X0,X1] : (r1_tarski(X1,k2_relat_1(k2_zfmisc_1(X0,X1))) | k2_zfmisc_1(X0,X1) = k1_xboole_0) )),
% 1.47/0.57    inference(subsumption_resolution,[],[f105,f39])).
% 1.47/0.57  fof(f105,plain,(
% 1.47/0.57    ( ! [X0,X1] : (k2_zfmisc_1(X0,X1) = k1_xboole_0 | r1_tarski(X1,k2_relat_1(k2_zfmisc_1(X0,X1))) | ~v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 1.47/0.57    inference(resolution,[],[f49,f35])).
% 1.47/0.57  fof(f35,plain,(
% 1.47/0.57    ( ! [X0] : (r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) | ~v1_relat_1(X0)) )),
% 1.47/0.57    inference(cnf_transformation,[],[f17])).
% 1.47/0.57  fof(f17,plain,(
% 1.47/0.57    ! [X0] : (r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) | ~v1_relat_1(X0))),
% 1.47/0.57    inference(ennf_transformation,[],[f11])).
% 1.47/0.57  fof(f11,axiom,(
% 1.47/0.57    ! [X0] : (v1_relat_1(X0) => r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))),
% 1.47/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_relat_1)).
% 1.47/0.57  fof(f49,plain,(
% 1.47/0.57    ( ! [X2,X0,X3,X1] : (~r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)) | k2_zfmisc_1(X0,X1) = k1_xboole_0 | r1_tarski(X1,X3)) )),
% 1.47/0.57    inference(cnf_transformation,[],[f25])).
% 1.47/0.57  fof(f25,plain,(
% 1.47/0.57    ! [X0,X1,X2,X3] : ((r1_tarski(X1,X3) & r1_tarski(X0,X2)) | k2_zfmisc_1(X0,X1) = k1_xboole_0 | ~r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)))),
% 1.47/0.57    inference(flattening,[],[f24])).
% 1.47/0.57  fof(f24,plain,(
% 1.47/0.57    ! [X0,X1,X2,X3] : (((r1_tarski(X1,X3) & r1_tarski(X0,X2)) | k2_zfmisc_1(X0,X1) = k1_xboole_0) | ~r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)))),
% 1.47/0.57    inference(ennf_transformation,[],[f2])).
% 1.47/0.57  fof(f2,axiom,(
% 1.47/0.57    ! [X0,X1,X2,X3] : (r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)) => ((r1_tarski(X1,X3) & r1_tarski(X0,X2)) | k2_zfmisc_1(X0,X1) = k1_xboole_0))),
% 1.47/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t138_zfmisc_1)).
% 1.47/0.57  fof(f180,plain,(
% 1.47/0.57    ( ! [X0,X1] : (k3_relat_1(k2_zfmisc_1(X0,X1)) = k2_xboole_0(X0,k2_relat_1(k2_zfmisc_1(X0,X1))) | k2_zfmisc_1(X0,X1) = k1_xboole_0) )),
% 1.47/0.57    inference(superposition,[],[f86,f113])).
% 1.47/0.57  fof(f113,plain,(
% 1.47/0.57    ( ! [X0,X1] : (k1_relat_1(k2_zfmisc_1(X0,X1)) = X0 | k2_zfmisc_1(X0,X1) = k1_xboole_0) )),
% 1.47/0.57    inference(subsumption_resolution,[],[f111,f40])).
% 1.47/0.57  fof(f40,plain,(
% 1.47/0.57    ( ! [X0,X1] : (r1_tarski(k1_relat_1(k2_zfmisc_1(X0,X1)),X0)) )),
% 1.47/0.57    inference(cnf_transformation,[],[f9])).
% 1.47/0.57  fof(f9,axiom,(
% 1.47/0.57    ! [X0,X1] : r1_tarski(k1_relat_1(k2_zfmisc_1(X0,X1)),X0)),
% 1.47/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t193_relat_1)).
% 1.47/0.57  fof(f111,plain,(
% 1.47/0.57    ( ! [X0,X1] : (k2_zfmisc_1(X0,X1) = k1_xboole_0 | ~r1_tarski(k1_relat_1(k2_zfmisc_1(X0,X1)),X0) | k1_relat_1(k2_zfmisc_1(X0,X1)) = X0) )),
% 1.47/0.57    inference(resolution,[],[f99,f44])).
% 1.47/0.57  fof(f99,plain,(
% 1.47/0.57    ( ! [X0,X1] : (r1_tarski(X0,k1_relat_1(k2_zfmisc_1(X0,X1))) | k2_zfmisc_1(X0,X1) = k1_xboole_0) )),
% 1.47/0.57    inference(subsumption_resolution,[],[f97,f39])).
% 1.47/0.57  fof(f97,plain,(
% 1.47/0.57    ( ! [X0,X1] : (k2_zfmisc_1(X0,X1) = k1_xboole_0 | r1_tarski(X0,k1_relat_1(k2_zfmisc_1(X0,X1))) | ~v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 1.47/0.57    inference(resolution,[],[f48,f35])).
% 1.47/0.57  fof(f48,plain,(
% 1.47/0.57    ( ! [X2,X0,X3,X1] : (~r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)) | k2_zfmisc_1(X0,X1) = k1_xboole_0 | r1_tarski(X0,X2)) )),
% 1.47/0.57    inference(cnf_transformation,[],[f25])).
% 1.47/0.57  fof(f86,plain,(
% 1.47/0.57    ( ! [X0,X1] : (k3_relat_1(k2_zfmisc_1(X0,X1)) = k2_xboole_0(k1_relat_1(k2_zfmisc_1(X0,X1)),k2_relat_1(k2_zfmisc_1(X0,X1)))) )),
% 1.47/0.57    inference(resolution,[],[f36,f39])).
% 1.47/0.57  fof(f36,plain,(
% 1.47/0.57    ( ! [X0] : (~v1_relat_1(X0) | k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0))) )),
% 1.47/0.57    inference(cnf_transformation,[],[f18])).
% 1.47/0.57  fof(f18,plain,(
% 1.47/0.57    ! [X0] : (k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) | ~v1_relat_1(X0))),
% 1.47/0.57    inference(ennf_transformation,[],[f7])).
% 1.47/0.57  fof(f7,axiom,(
% 1.47/0.57    ! [X0] : (v1_relat_1(X0) => k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)))),
% 1.47/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d6_relat_1)).
% 1.47/0.57  fof(f257,plain,(
% 1.47/0.57    ( ! [X0] : (r1_tarski(k3_relat_1(sK2),k3_relat_1(X0)) | ~v1_relat_1(X0) | ~r1_tarski(sK2,X0)) ) | ~spl3_19),
% 1.47/0.57    inference(avatar_component_clause,[],[f256])).
% 1.47/0.57  fof(f258,plain,(
% 1.47/0.57    spl3_19 | ~spl3_5),
% 1.47/0.57    inference(avatar_split_clause,[],[f108,f101,f256])).
% 1.47/0.57  fof(f101,plain,(
% 1.47/0.57    spl3_5 <=> v1_relat_1(sK2)),
% 1.47/0.57    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 1.47/0.57  fof(f108,plain,(
% 1.47/0.57    ( ! [X0] : (~r1_tarski(sK2,X0) | ~v1_relat_1(X0) | r1_tarski(k3_relat_1(sK2),k3_relat_1(X0))) ) | ~spl3_5),
% 1.47/0.57    inference(resolution,[],[f103,f37])).
% 1.47/0.57  fof(f37,plain,(
% 1.47/0.57    ( ! [X0,X1] : (~v1_relat_1(X0) | ~r1_tarski(X0,X1) | ~v1_relat_1(X1) | r1_tarski(k3_relat_1(X0),k3_relat_1(X1))) )),
% 1.47/0.57    inference(cnf_transformation,[],[f20])).
% 1.47/0.57  fof(f20,plain,(
% 1.47/0.57    ! [X0] : (! [X1] : (r1_tarski(k3_relat_1(X0),k3_relat_1(X1)) | ~r1_tarski(X0,X1) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 1.47/0.57    inference(flattening,[],[f19])).
% 1.47/0.57  fof(f19,plain,(
% 1.47/0.57    ! [X0] : (! [X1] : ((r1_tarski(k3_relat_1(X0),k3_relat_1(X1)) | ~r1_tarski(X0,X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 1.47/0.57    inference(ennf_transformation,[],[f12])).
% 1.47/0.57  fof(f12,axiom,(
% 1.47/0.57    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => (r1_tarski(X0,X1) => r1_tarski(k3_relat_1(X0),k3_relat_1(X1)))))),
% 1.47/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_relat_1)).
% 1.47/0.57  fof(f103,plain,(
% 1.47/0.57    v1_relat_1(sK2) | ~spl3_5),
% 1.47/0.57    inference(avatar_component_clause,[],[f101])).
% 1.47/0.57  fof(f104,plain,(
% 1.47/0.57    spl3_5 | ~spl3_2),
% 1.47/0.57    inference(avatar_split_clause,[],[f95,f58,f101])).
% 1.47/0.57  fof(f58,plain,(
% 1.47/0.57    spl3_2 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 1.47/0.57    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 1.47/0.57  fof(f95,plain,(
% 1.47/0.57    v1_relat_1(sK2) | ~spl3_2),
% 1.47/0.57    inference(resolution,[],[f70,f60])).
% 1.47/0.57  fof(f60,plain,(
% 1.47/0.57    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~spl3_2),
% 1.47/0.57    inference(avatar_component_clause,[],[f58])).
% 1.47/0.57  fof(f70,plain,(
% 1.47/0.57    ( ! [X2,X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | v1_relat_1(X0)) )),
% 1.47/0.57    inference(resolution,[],[f38,f39])).
% 1.47/0.57  fof(f38,plain,(
% 1.47/0.57    ( ! [X0,X1] : (~v1_relat_1(X0) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | v1_relat_1(X1)) )),
% 1.47/0.57    inference(cnf_transformation,[],[f21])).
% 1.47/0.57  fof(f21,plain,(
% 1.47/0.57    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 1.47/0.57    inference(ennf_transformation,[],[f6])).
% 1.47/0.57  fof(f6,axiom,(
% 1.47/0.57    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 1.47/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).
% 1.47/0.57  fof(f75,plain,(
% 1.47/0.57    spl3_4 | ~spl3_2),
% 1.47/0.57    inference(avatar_split_clause,[],[f68,f58,f72])).
% 1.47/0.57  fof(f68,plain,(
% 1.47/0.57    r1_tarski(sK2,k2_zfmisc_1(sK0,sK1)) | ~spl3_2),
% 1.47/0.57    inference(resolution,[],[f45,f60])).
% 1.47/0.57  fof(f66,plain,(
% 1.47/0.57    ~spl3_3),
% 1.47/0.57    inference(avatar_split_clause,[],[f32,f63])).
% 1.47/0.57  fof(f32,plain,(
% 1.47/0.57    ~r1_tarski(k3_relat_1(sK2),k2_xboole_0(sK0,sK1))),
% 1.47/0.57    inference(cnf_transformation,[],[f27])).
% 1.47/0.57  fof(f27,plain,(
% 1.47/0.57    ~r1_tarski(k3_relat_1(sK2),k2_xboole_0(sK0,sK1)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 1.47/0.57    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f16,f26])).
% 1.47/0.57  fof(f26,plain,(
% 1.47/0.57    ? [X0,X1,X2] : (~r1_tarski(k3_relat_1(X2),k2_xboole_0(X0,X1)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => (~r1_tarski(k3_relat_1(sK2),k2_xboole_0(sK0,sK1)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))))),
% 1.47/0.57    introduced(choice_axiom,[])).
% 1.47/0.57  fof(f16,plain,(
% 1.47/0.57    ? [X0,X1,X2] : (~r1_tarski(k3_relat_1(X2),k2_xboole_0(X0,X1)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.47/0.57    inference(ennf_transformation,[],[f15])).
% 1.47/0.57  fof(f15,negated_conjecture,(
% 1.47/0.57    ~! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => r1_tarski(k3_relat_1(X2),k2_xboole_0(X0,X1)))),
% 1.47/0.57    inference(negated_conjecture,[],[f14])).
% 1.47/0.57  fof(f14,conjecture,(
% 1.47/0.57    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => r1_tarski(k3_relat_1(X2),k2_xboole_0(X0,X1)))),
% 1.47/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t19_relset_1)).
% 1.47/0.57  fof(f61,plain,(
% 1.47/0.57    spl3_2),
% 1.47/0.57    inference(avatar_split_clause,[],[f31,f58])).
% 1.47/0.57  fof(f31,plain,(
% 1.47/0.57    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 1.47/0.57    inference(cnf_transformation,[],[f27])).
% 1.47/0.57  fof(f56,plain,(
% 1.47/0.57    spl3_1),
% 1.47/0.57    inference(avatar_split_clause,[],[f33,f53])).
% 1.47/0.57  fof(f33,plain,(
% 1.47/0.57    k1_xboole_0 = k3_relat_1(k1_xboole_0)),
% 1.47/0.57    inference(cnf_transformation,[],[f13])).
% 1.47/0.57  fof(f13,axiom,(
% 1.47/0.57    k1_xboole_0 = k3_relat_1(k1_xboole_0)),
% 1.47/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_relat_1)).
% 1.47/0.57  % SZS output end Proof for theBenchmark
% 1.47/0.57  % (8746)------------------------------
% 1.47/0.57  % (8746)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.47/0.57  % (8746)Termination reason: Refutation
% 1.47/0.57  
% 1.47/0.57  % (8746)Memory used [KB]: 6652
% 1.47/0.57  % (8746)Time elapsed: 0.134 s
% 1.47/0.57  % (8746)------------------------------
% 1.47/0.57  % (8746)------------------------------
% 1.47/0.57  % (8743)Success in time 0.2 s
%------------------------------------------------------------------------------
