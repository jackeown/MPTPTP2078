%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:54:31 EST 2020

% Result     : Theorem 0.13s
% Output     : Refutation 0.13s
% Verified   : 
% Statistics : Number of formulae       :   89 ( 132 expanded)
%              Number of leaves         :   25 (  62 expanded)
%              Depth                    :    6
%              Number of atoms          :  223 ( 327 expanded)
%              Number of equality atoms :   54 (  81 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f131,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f36,f41,f49,f50,f54,f62,f66,f70,f74,f82,f89,f94,f101,f107,f113,f119,f129])).

fof(f129,plain,
    ( spl2_1
    | ~ spl2_7
    | ~ spl2_16
    | ~ spl2_18 ),
    inference(avatar_contradiction_clause,[],[f128])).

fof(f128,plain,
    ( $false
    | spl2_1
    | ~ spl2_7
    | ~ spl2_16
    | ~ spl2_18 ),
    inference(subsumption_resolution,[],[f127,f35])).

fof(f35,plain,
    ( sK1 != k9_relat_1(k6_relat_1(sK0),sK1)
    | spl2_1 ),
    inference(avatar_component_clause,[],[f33])).

fof(f33,plain,
    ( spl2_1
  <=> sK1 = k9_relat_1(k6_relat_1(sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f127,plain,
    ( sK1 = k9_relat_1(k6_relat_1(sK0),sK1)
    | ~ spl2_7
    | ~ spl2_16
    | ~ spl2_18 ),
    inference(forward_demodulation,[],[f125,f106])).

fof(f106,plain,
    ( sK1 = k9_relat_1(k6_relat_1(sK0),k10_relat_1(k6_relat_1(sK0),sK1))
    | ~ spl2_16 ),
    inference(avatar_component_clause,[],[f104])).

fof(f104,plain,
    ( spl2_16
  <=> sK1 = k9_relat_1(k6_relat_1(sK0),k10_relat_1(k6_relat_1(sK0),sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_16])])).

fof(f125,plain,
    ( k9_relat_1(k6_relat_1(sK0),sK1) = k9_relat_1(k6_relat_1(sK0),k10_relat_1(k6_relat_1(sK0),sK1))
    | ~ spl2_7
    | ~ spl2_18 ),
    inference(superposition,[],[f118,f61])).

fof(f61,plain,
    ( ! [X0] : k3_xboole_0(X0,X0) = X0
    | ~ spl2_7 ),
    inference(avatar_component_clause,[],[f60])).

fof(f60,plain,
    ( spl2_7
  <=> ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).

fof(f118,plain,
    ( ! [X0] : k9_relat_1(k6_relat_1(k3_xboole_0(X0,sK0)),k10_relat_1(k6_relat_1(sK0),sK1)) = k9_relat_1(k6_relat_1(X0),sK1)
    | ~ spl2_18 ),
    inference(avatar_component_clause,[],[f117])).

fof(f117,plain,
    ( spl2_18
  <=> ! [X0] : k9_relat_1(k6_relat_1(k3_xboole_0(X0,sK0)),k10_relat_1(k6_relat_1(sK0),sK1)) = k9_relat_1(k6_relat_1(X0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_18])])).

fof(f119,plain,
    ( spl2_18
    | ~ spl2_16
    | ~ spl2_17 ),
    inference(avatar_split_clause,[],[f114,f111,f104,f117])).

fof(f111,plain,
    ( spl2_17
  <=> ! [X1,X0,X2] : k9_relat_1(k6_relat_1(X1),k9_relat_1(k6_relat_1(X0),X2)) = k9_relat_1(k6_relat_1(k3_xboole_0(X1,X0)),X2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_17])])).

fof(f114,plain,
    ( ! [X0] : k9_relat_1(k6_relat_1(k3_xboole_0(X0,sK0)),k10_relat_1(k6_relat_1(sK0),sK1)) = k9_relat_1(k6_relat_1(X0),sK1)
    | ~ spl2_16
    | ~ spl2_17 ),
    inference(superposition,[],[f112,f106])).

fof(f112,plain,
    ( ! [X2,X0,X1] : k9_relat_1(k6_relat_1(X1),k9_relat_1(k6_relat_1(X0),X2)) = k9_relat_1(k6_relat_1(k3_xboole_0(X1,X0)),X2)
    | ~ spl2_17 ),
    inference(avatar_component_clause,[],[f111])).

fof(f113,plain,
    ( spl2_17
    | ~ spl2_3
    | ~ spl2_8
    | ~ spl2_14 ),
    inference(avatar_split_clause,[],[f109,f92,f64,f43,f111])).

fof(f43,plain,
    ( spl2_3
  <=> ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).

fof(f64,plain,
    ( spl2_8
  <=> ! [X1,X0] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_8])])).

fof(f92,plain,
    ( spl2_14
  <=> ! [X1,X0,X2] :
        ( ~ v1_relat_1(X0)
        | k9_relat_1(k5_relat_1(k6_relat_1(X1),X0),X2) = k9_relat_1(X0,k9_relat_1(k6_relat_1(X1),X2)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_14])])).

fof(f109,plain,
    ( ! [X2,X0,X1] : k9_relat_1(k6_relat_1(X1),k9_relat_1(k6_relat_1(X0),X2)) = k9_relat_1(k6_relat_1(k3_xboole_0(X1,X0)),X2)
    | ~ spl2_3
    | ~ spl2_8
    | ~ spl2_14 ),
    inference(forward_demodulation,[],[f108,f65])).

fof(f65,plain,
    ( ! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1))
    | ~ spl2_8 ),
    inference(avatar_component_clause,[],[f64])).

fof(f108,plain,
    ( ! [X2,X0,X1] : k9_relat_1(k5_relat_1(k6_relat_1(X0),k6_relat_1(X1)),X2) = k9_relat_1(k6_relat_1(X1),k9_relat_1(k6_relat_1(X0),X2))
    | ~ spl2_3
    | ~ spl2_14 ),
    inference(resolution,[],[f93,f44])).

fof(f44,plain,
    ( ! [X0] : v1_relat_1(k6_relat_1(X0))
    | ~ spl2_3 ),
    inference(avatar_component_clause,[],[f43])).

fof(f93,plain,
    ( ! [X2,X0,X1] :
        ( ~ v1_relat_1(X0)
        | k9_relat_1(k5_relat_1(k6_relat_1(X1),X0),X2) = k9_relat_1(X0,k9_relat_1(k6_relat_1(X1),X2)) )
    | ~ spl2_14 ),
    inference(avatar_component_clause,[],[f92])).

fof(f107,plain,
    ( spl2_16
    | ~ spl2_13
    | ~ spl2_15 ),
    inference(avatar_split_clause,[],[f102,f99,f86,f104])).

fof(f86,plain,
    ( spl2_13
  <=> r1_tarski(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_13])])).

fof(f99,plain,
    ( spl2_15
  <=> ! [X1,X0] :
        ( ~ r1_tarski(X0,X1)
        | k9_relat_1(k6_relat_1(X1),k10_relat_1(k6_relat_1(X1),X0)) = X0 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_15])])).

fof(f102,plain,
    ( sK1 = k9_relat_1(k6_relat_1(sK0),k10_relat_1(k6_relat_1(sK0),sK1))
    | ~ spl2_13
    | ~ spl2_15 ),
    inference(resolution,[],[f100,f88])).

fof(f88,plain,
    ( r1_tarski(sK1,sK0)
    | ~ spl2_13 ),
    inference(avatar_component_clause,[],[f86])).

fof(f100,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(X0,X1)
        | k9_relat_1(k6_relat_1(X1),k10_relat_1(k6_relat_1(X1),X0)) = X0 )
    | ~ spl2_15 ),
    inference(avatar_component_clause,[],[f99])).

fof(f101,plain,
    ( spl2_15
    | ~ spl2_3
    | ~ spl2_4
    | ~ spl2_5
    | ~ spl2_10 ),
    inference(avatar_split_clause,[],[f97,f72,f52,f47,f43,f99])).

fof(f47,plain,
    ( spl2_4
  <=> ! [X0] : v1_funct_1(k6_relat_1(X0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).

fof(f52,plain,
    ( spl2_5
  <=> ! [X0] : k2_relat_1(k6_relat_1(X0)) = X0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).

fof(f72,plain,
    ( spl2_10
  <=> ! [X1,X0] :
        ( k9_relat_1(X1,k10_relat_1(X1,X0)) = X0
        | ~ r1_tarski(X0,k2_relat_1(X1))
        | ~ v1_funct_1(X1)
        | ~ v1_relat_1(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_10])])).

fof(f97,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(X0,X1)
        | k9_relat_1(k6_relat_1(X1),k10_relat_1(k6_relat_1(X1),X0)) = X0 )
    | ~ spl2_3
    | ~ spl2_4
    | ~ spl2_5
    | ~ spl2_10 ),
    inference(forward_demodulation,[],[f96,f53])).

fof(f53,plain,
    ( ! [X0] : k2_relat_1(k6_relat_1(X0)) = X0
    | ~ spl2_5 ),
    inference(avatar_component_clause,[],[f52])).

fof(f96,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(X0,k2_relat_1(k6_relat_1(X1)))
        | k9_relat_1(k6_relat_1(X1),k10_relat_1(k6_relat_1(X1),X0)) = X0 )
    | ~ spl2_3
    | ~ spl2_4
    | ~ spl2_10 ),
    inference(subsumption_resolution,[],[f95,f44])).

fof(f95,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(X0,k2_relat_1(k6_relat_1(X1)))
        | k9_relat_1(k6_relat_1(X1),k10_relat_1(k6_relat_1(X1),X0)) = X0
        | ~ v1_relat_1(k6_relat_1(X1)) )
    | ~ spl2_4
    | ~ spl2_10 ),
    inference(resolution,[],[f73,f48])).

fof(f48,plain,
    ( ! [X0] : v1_funct_1(k6_relat_1(X0))
    | ~ spl2_4 ),
    inference(avatar_component_clause,[],[f47])).

fof(f73,plain,
    ( ! [X0,X1] :
        ( ~ v1_funct_1(X1)
        | ~ r1_tarski(X0,k2_relat_1(X1))
        | k9_relat_1(X1,k10_relat_1(X1,X0)) = X0
        | ~ v1_relat_1(X1) )
    | ~ spl2_10 ),
    inference(avatar_component_clause,[],[f72])).

fof(f94,plain,
    ( spl2_14
    | ~ spl2_3
    | ~ spl2_9 ),
    inference(avatar_split_clause,[],[f90,f68,f43,f92])).

fof(f68,plain,
    ( spl2_9
  <=> ! [X1,X0,X2] :
        ( k9_relat_1(k5_relat_1(X1,X2),X0) = k9_relat_1(X2,k9_relat_1(X1,X0))
        | ~ v1_relat_1(X2)
        | ~ v1_relat_1(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_9])])).

fof(f90,plain,
    ( ! [X2,X0,X1] :
        ( ~ v1_relat_1(X0)
        | k9_relat_1(k5_relat_1(k6_relat_1(X1),X0),X2) = k9_relat_1(X0,k9_relat_1(k6_relat_1(X1),X2)) )
    | ~ spl2_3
    | ~ spl2_9 ),
    inference(resolution,[],[f69,f44])).

fof(f69,plain,
    ( ! [X2,X0,X1] :
        ( ~ v1_relat_1(X1)
        | ~ v1_relat_1(X2)
        | k9_relat_1(k5_relat_1(X1,X2),X0) = k9_relat_1(X2,k9_relat_1(X1,X0)) )
    | ~ spl2_9 ),
    inference(avatar_component_clause,[],[f68])).

fof(f89,plain,
    ( spl2_13
    | ~ spl2_2
    | ~ spl2_12 ),
    inference(avatar_split_clause,[],[f83,f80,f38,f86])).

fof(f38,plain,
    ( spl2_2
  <=> m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f80,plain,
    ( spl2_12
  <=> ! [X1,X0] :
        ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_12])])).

fof(f83,plain,
    ( r1_tarski(sK1,sK0)
    | ~ spl2_2
    | ~ spl2_12 ),
    inference(resolution,[],[f81,f40])).

fof(f40,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(sK0))
    | ~ spl2_2 ),
    inference(avatar_component_clause,[],[f38])).

fof(f81,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
        | r1_tarski(X0,X1) )
    | ~ spl2_12 ),
    inference(avatar_component_clause,[],[f80])).

fof(f82,plain,(
    spl2_12 ),
    inference(avatar_split_clause,[],[f30,f80])).

fof(f30,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f74,plain,(
    spl2_10 ),
    inference(avatar_split_clause,[],[f29,f72])).

fof(f29,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,k10_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k2_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,k10_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k2_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,k10_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k2_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( r1_tarski(X0,k2_relat_1(X1))
       => k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t147_funct_1)).

fof(f70,plain,(
    spl2_9 ),
    inference(avatar_split_clause,[],[f28,f68])).

fof(f28,plain,(
    ! [X2,X0,X1] :
      ( k9_relat_1(k5_relat_1(X1,X2),X0) = k9_relat_1(X2,k9_relat_1(X1,X0))
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k9_relat_1(k5_relat_1(X1,X2),X0) = k9_relat_1(X2,k9_relat_1(X1,X0))
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => k9_relat_1(k5_relat_1(X1,X2),X0) = k9_relat_1(X2,k9_relat_1(X1,X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t159_relat_1)).

fof(f66,plain,(
    spl2_8 ),
    inference(avatar_split_clause,[],[f27,f64])).

fof(f27,plain,(
    ! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_funct_1)).

fof(f62,plain,(
    spl2_7 ),
    inference(avatar_split_clause,[],[f26,f60])).

fof(f26,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

fof(f54,plain,(
    spl2_5 ),
    inference(avatar_split_clause,[],[f25,f52])).

fof(f25,plain,(
    ! [X0] : k2_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

fof(f50,plain,(
    spl2_3 ),
    inference(avatar_split_clause,[],[f22,f43])).

fof(f22,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( v1_funct_1(k6_relat_1(X0))
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc3_funct_1)).

fof(f49,plain,(
    spl2_4 ),
    inference(avatar_split_clause,[],[f23,f47])).

fof(f23,plain,(
    ! [X0] : v1_funct_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f6])).

fof(f41,plain,(
    spl2_2 ),
    inference(avatar_split_clause,[],[f19,f38])).

fof(f19,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,
    ( sK1 != k9_relat_1(k6_relat_1(sK0),sK1)
    & m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f12,f16])).

fof(f16,plain,
    ( ? [X0,X1] :
        ( k9_relat_1(k6_relat_1(X0),X1) != X1
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
   => ( sK1 != k9_relat_1(k6_relat_1(sK0),sK1)
      & m1_subset_1(sK1,k1_zfmisc_1(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f12,plain,(
    ? [X0,X1] :
      ( k9_relat_1(k6_relat_1(X0),X1) != X1
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(X0))
       => k9_relat_1(k6_relat_1(X0),X1) = X1 ) ),
    inference(negated_conjecture,[],[f9])).

fof(f9,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k9_relat_1(k6_relat_1(X0),X1) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t162_funct_1)).

fof(f36,plain,(
    ~ spl2_1 ),
    inference(avatar_split_clause,[],[f20,f33])).

fof(f20,plain,(
    sK1 != k9_relat_1(k6_relat_1(sK0),sK1) ),
    inference(cnf_transformation,[],[f17])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n017.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 09:55:31 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.42  % (21439)lrs+1011_5:1_acc=on:amm=off:anc=all_dependent:bd=off:ccuc=small_ones:fde=unused:gs=on:gsaa=full_model:gsem=off:lcm=predicate:lwlo=on:nm=6:newcnf=on:nwc=2.5:stl=30:sp=occurrence:updr=off_3 on theBenchmark
% 0.13/0.42  % (21443)ott+11_50_add=large:afr=on:afp=40000:afq=1.1:amm=sco:anc=all:bd=off:cond=fast:gs=on:gsem=on:irw=on:lma=on:nm=0:nwc=1:sp=occurrence:updr=off:uhcvi=on_102 on theBenchmark
% 0.13/0.42  % (21445)ott+4_1024_afr=on:afp=4000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:cond=fast:gsp=input_only:gs=on:gsaa=from_current:nm=16:nwc=1.1:nicw=on:sas=z3:sp=occurrence:updr=off_1389 on theBenchmark
% 0.13/0.42  % (21443)Refutation found. Thanks to Tanya!
% 0.13/0.42  % SZS status Theorem for theBenchmark
% 0.13/0.42  % SZS output start Proof for theBenchmark
% 0.13/0.42  fof(f131,plain,(
% 0.13/0.42    $false),
% 0.13/0.42    inference(avatar_sat_refutation,[],[f36,f41,f49,f50,f54,f62,f66,f70,f74,f82,f89,f94,f101,f107,f113,f119,f129])).
% 0.13/0.42  fof(f129,plain,(
% 0.13/0.42    spl2_1 | ~spl2_7 | ~spl2_16 | ~spl2_18),
% 0.13/0.42    inference(avatar_contradiction_clause,[],[f128])).
% 0.13/0.42  fof(f128,plain,(
% 0.13/0.42    $false | (spl2_1 | ~spl2_7 | ~spl2_16 | ~spl2_18)),
% 0.13/0.42    inference(subsumption_resolution,[],[f127,f35])).
% 0.13/0.42  fof(f35,plain,(
% 0.13/0.42    sK1 != k9_relat_1(k6_relat_1(sK0),sK1) | spl2_1),
% 0.13/0.42    inference(avatar_component_clause,[],[f33])).
% 0.13/0.42  fof(f33,plain,(
% 0.13/0.42    spl2_1 <=> sK1 = k9_relat_1(k6_relat_1(sK0),sK1)),
% 0.13/0.42    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 0.13/0.42  fof(f127,plain,(
% 0.13/0.42    sK1 = k9_relat_1(k6_relat_1(sK0),sK1) | (~spl2_7 | ~spl2_16 | ~spl2_18)),
% 0.13/0.42    inference(forward_demodulation,[],[f125,f106])).
% 0.13/0.42  fof(f106,plain,(
% 0.13/0.42    sK1 = k9_relat_1(k6_relat_1(sK0),k10_relat_1(k6_relat_1(sK0),sK1)) | ~spl2_16),
% 0.13/0.42    inference(avatar_component_clause,[],[f104])).
% 0.13/0.42  fof(f104,plain,(
% 0.13/0.42    spl2_16 <=> sK1 = k9_relat_1(k6_relat_1(sK0),k10_relat_1(k6_relat_1(sK0),sK1))),
% 0.13/0.42    introduced(avatar_definition,[new_symbols(naming,[spl2_16])])).
% 0.13/0.42  fof(f125,plain,(
% 0.13/0.42    k9_relat_1(k6_relat_1(sK0),sK1) = k9_relat_1(k6_relat_1(sK0),k10_relat_1(k6_relat_1(sK0),sK1)) | (~spl2_7 | ~spl2_18)),
% 0.13/0.42    inference(superposition,[],[f118,f61])).
% 0.13/0.42  fof(f61,plain,(
% 0.13/0.42    ( ! [X0] : (k3_xboole_0(X0,X0) = X0) ) | ~spl2_7),
% 0.13/0.42    inference(avatar_component_clause,[],[f60])).
% 0.13/0.42  fof(f60,plain,(
% 0.13/0.42    spl2_7 <=> ! [X0] : k3_xboole_0(X0,X0) = X0),
% 0.13/0.42    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).
% 0.13/0.42  fof(f118,plain,(
% 0.13/0.42    ( ! [X0] : (k9_relat_1(k6_relat_1(k3_xboole_0(X0,sK0)),k10_relat_1(k6_relat_1(sK0),sK1)) = k9_relat_1(k6_relat_1(X0),sK1)) ) | ~spl2_18),
% 0.13/0.42    inference(avatar_component_clause,[],[f117])).
% 0.13/0.42  fof(f117,plain,(
% 0.13/0.42    spl2_18 <=> ! [X0] : k9_relat_1(k6_relat_1(k3_xboole_0(X0,sK0)),k10_relat_1(k6_relat_1(sK0),sK1)) = k9_relat_1(k6_relat_1(X0),sK1)),
% 0.13/0.42    introduced(avatar_definition,[new_symbols(naming,[spl2_18])])).
% 0.13/0.42  fof(f119,plain,(
% 0.13/0.42    spl2_18 | ~spl2_16 | ~spl2_17),
% 0.13/0.42    inference(avatar_split_clause,[],[f114,f111,f104,f117])).
% 0.13/0.42  fof(f111,plain,(
% 0.13/0.42    spl2_17 <=> ! [X1,X0,X2] : k9_relat_1(k6_relat_1(X1),k9_relat_1(k6_relat_1(X0),X2)) = k9_relat_1(k6_relat_1(k3_xboole_0(X1,X0)),X2)),
% 0.13/0.42    introduced(avatar_definition,[new_symbols(naming,[spl2_17])])).
% 0.13/0.42  fof(f114,plain,(
% 0.13/0.42    ( ! [X0] : (k9_relat_1(k6_relat_1(k3_xboole_0(X0,sK0)),k10_relat_1(k6_relat_1(sK0),sK1)) = k9_relat_1(k6_relat_1(X0),sK1)) ) | (~spl2_16 | ~spl2_17)),
% 0.13/0.42    inference(superposition,[],[f112,f106])).
% 0.13/0.42  fof(f112,plain,(
% 0.13/0.42    ( ! [X2,X0,X1] : (k9_relat_1(k6_relat_1(X1),k9_relat_1(k6_relat_1(X0),X2)) = k9_relat_1(k6_relat_1(k3_xboole_0(X1,X0)),X2)) ) | ~spl2_17),
% 0.13/0.42    inference(avatar_component_clause,[],[f111])).
% 0.13/0.42  fof(f113,plain,(
% 0.13/0.42    spl2_17 | ~spl2_3 | ~spl2_8 | ~spl2_14),
% 0.13/0.42    inference(avatar_split_clause,[],[f109,f92,f64,f43,f111])).
% 0.13/0.42  fof(f43,plain,(
% 0.13/0.42    spl2_3 <=> ! [X0] : v1_relat_1(k6_relat_1(X0))),
% 0.13/0.42    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).
% 0.13/0.42  fof(f64,plain,(
% 0.13/0.42    spl2_8 <=> ! [X1,X0] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1))),
% 0.13/0.42    introduced(avatar_definition,[new_symbols(naming,[spl2_8])])).
% 0.13/0.42  fof(f92,plain,(
% 0.13/0.42    spl2_14 <=> ! [X1,X0,X2] : (~v1_relat_1(X0) | k9_relat_1(k5_relat_1(k6_relat_1(X1),X0),X2) = k9_relat_1(X0,k9_relat_1(k6_relat_1(X1),X2)))),
% 0.13/0.42    introduced(avatar_definition,[new_symbols(naming,[spl2_14])])).
% 0.13/0.42  fof(f109,plain,(
% 0.13/0.42    ( ! [X2,X0,X1] : (k9_relat_1(k6_relat_1(X1),k9_relat_1(k6_relat_1(X0),X2)) = k9_relat_1(k6_relat_1(k3_xboole_0(X1,X0)),X2)) ) | (~spl2_3 | ~spl2_8 | ~spl2_14)),
% 0.13/0.42    inference(forward_demodulation,[],[f108,f65])).
% 0.13/0.42  fof(f65,plain,(
% 0.13/0.42    ( ! [X0,X1] : (k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1))) ) | ~spl2_8),
% 0.13/0.42    inference(avatar_component_clause,[],[f64])).
% 0.13/0.42  fof(f108,plain,(
% 0.13/0.42    ( ! [X2,X0,X1] : (k9_relat_1(k5_relat_1(k6_relat_1(X0),k6_relat_1(X1)),X2) = k9_relat_1(k6_relat_1(X1),k9_relat_1(k6_relat_1(X0),X2))) ) | (~spl2_3 | ~spl2_14)),
% 0.13/0.42    inference(resolution,[],[f93,f44])).
% 0.13/0.42  fof(f44,plain,(
% 0.13/0.42    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) ) | ~spl2_3),
% 0.13/0.42    inference(avatar_component_clause,[],[f43])).
% 0.13/0.42  fof(f93,plain,(
% 0.13/0.42    ( ! [X2,X0,X1] : (~v1_relat_1(X0) | k9_relat_1(k5_relat_1(k6_relat_1(X1),X0),X2) = k9_relat_1(X0,k9_relat_1(k6_relat_1(X1),X2))) ) | ~spl2_14),
% 0.13/0.42    inference(avatar_component_clause,[],[f92])).
% 0.13/0.42  fof(f107,plain,(
% 0.13/0.42    spl2_16 | ~spl2_13 | ~spl2_15),
% 0.13/0.42    inference(avatar_split_clause,[],[f102,f99,f86,f104])).
% 0.13/0.42  fof(f86,plain,(
% 0.13/0.42    spl2_13 <=> r1_tarski(sK1,sK0)),
% 0.13/0.42    introduced(avatar_definition,[new_symbols(naming,[spl2_13])])).
% 0.13/0.42  fof(f99,plain,(
% 0.13/0.42    spl2_15 <=> ! [X1,X0] : (~r1_tarski(X0,X1) | k9_relat_1(k6_relat_1(X1),k10_relat_1(k6_relat_1(X1),X0)) = X0)),
% 0.13/0.42    introduced(avatar_definition,[new_symbols(naming,[spl2_15])])).
% 0.13/0.42  fof(f102,plain,(
% 0.13/0.42    sK1 = k9_relat_1(k6_relat_1(sK0),k10_relat_1(k6_relat_1(sK0),sK1)) | (~spl2_13 | ~spl2_15)),
% 0.13/0.42    inference(resolution,[],[f100,f88])).
% 0.13/0.42  fof(f88,plain,(
% 0.13/0.42    r1_tarski(sK1,sK0) | ~spl2_13),
% 0.13/0.42    inference(avatar_component_clause,[],[f86])).
% 0.13/0.42  fof(f100,plain,(
% 0.13/0.42    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k9_relat_1(k6_relat_1(X1),k10_relat_1(k6_relat_1(X1),X0)) = X0) ) | ~spl2_15),
% 0.13/0.42    inference(avatar_component_clause,[],[f99])).
% 0.13/0.42  fof(f101,plain,(
% 0.13/0.42    spl2_15 | ~spl2_3 | ~spl2_4 | ~spl2_5 | ~spl2_10),
% 0.13/0.42    inference(avatar_split_clause,[],[f97,f72,f52,f47,f43,f99])).
% 0.13/0.42  fof(f47,plain,(
% 0.13/0.42    spl2_4 <=> ! [X0] : v1_funct_1(k6_relat_1(X0))),
% 0.13/0.42    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).
% 0.13/0.42  fof(f52,plain,(
% 0.13/0.42    spl2_5 <=> ! [X0] : k2_relat_1(k6_relat_1(X0)) = X0),
% 0.13/0.42    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).
% 0.13/0.42  fof(f72,plain,(
% 0.13/0.42    spl2_10 <=> ! [X1,X0] : (k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k2_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 0.13/0.42    introduced(avatar_definition,[new_symbols(naming,[spl2_10])])).
% 0.13/0.42  fof(f97,plain,(
% 0.13/0.42    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k9_relat_1(k6_relat_1(X1),k10_relat_1(k6_relat_1(X1),X0)) = X0) ) | (~spl2_3 | ~spl2_4 | ~spl2_5 | ~spl2_10)),
% 0.13/0.42    inference(forward_demodulation,[],[f96,f53])).
% 0.13/0.42  fof(f53,plain,(
% 0.13/0.42    ( ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0) ) | ~spl2_5),
% 0.13/0.42    inference(avatar_component_clause,[],[f52])).
% 0.13/0.42  fof(f96,plain,(
% 0.13/0.42    ( ! [X0,X1] : (~r1_tarski(X0,k2_relat_1(k6_relat_1(X1))) | k9_relat_1(k6_relat_1(X1),k10_relat_1(k6_relat_1(X1),X0)) = X0) ) | (~spl2_3 | ~spl2_4 | ~spl2_10)),
% 0.13/0.42    inference(subsumption_resolution,[],[f95,f44])).
% 0.13/0.42  fof(f95,plain,(
% 0.13/0.42    ( ! [X0,X1] : (~r1_tarski(X0,k2_relat_1(k6_relat_1(X1))) | k9_relat_1(k6_relat_1(X1),k10_relat_1(k6_relat_1(X1),X0)) = X0 | ~v1_relat_1(k6_relat_1(X1))) ) | (~spl2_4 | ~spl2_10)),
% 0.13/0.42    inference(resolution,[],[f73,f48])).
% 0.13/0.42  fof(f48,plain,(
% 0.13/0.42    ( ! [X0] : (v1_funct_1(k6_relat_1(X0))) ) | ~spl2_4),
% 0.13/0.42    inference(avatar_component_clause,[],[f47])).
% 0.13/0.42  fof(f73,plain,(
% 0.13/0.42    ( ! [X0,X1] : (~v1_funct_1(X1) | ~r1_tarski(X0,k2_relat_1(X1)) | k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 | ~v1_relat_1(X1)) ) | ~spl2_10),
% 0.13/0.42    inference(avatar_component_clause,[],[f72])).
% 0.13/0.42  fof(f94,plain,(
% 0.13/0.42    spl2_14 | ~spl2_3 | ~spl2_9),
% 0.13/0.42    inference(avatar_split_clause,[],[f90,f68,f43,f92])).
% 0.13/0.42  fof(f68,plain,(
% 0.13/0.42    spl2_9 <=> ! [X1,X0,X2] : (k9_relat_1(k5_relat_1(X1,X2),X0) = k9_relat_1(X2,k9_relat_1(X1,X0)) | ~v1_relat_1(X2) | ~v1_relat_1(X1))),
% 0.13/0.42    introduced(avatar_definition,[new_symbols(naming,[spl2_9])])).
% 0.13/0.42  fof(f90,plain,(
% 0.13/0.42    ( ! [X2,X0,X1] : (~v1_relat_1(X0) | k9_relat_1(k5_relat_1(k6_relat_1(X1),X0),X2) = k9_relat_1(X0,k9_relat_1(k6_relat_1(X1),X2))) ) | (~spl2_3 | ~spl2_9)),
% 0.13/0.42    inference(resolution,[],[f69,f44])).
% 0.13/0.42  fof(f69,plain,(
% 0.13/0.42    ( ! [X2,X0,X1] : (~v1_relat_1(X1) | ~v1_relat_1(X2) | k9_relat_1(k5_relat_1(X1,X2),X0) = k9_relat_1(X2,k9_relat_1(X1,X0))) ) | ~spl2_9),
% 0.13/0.42    inference(avatar_component_clause,[],[f68])).
% 0.13/0.42  fof(f89,plain,(
% 0.13/0.42    spl2_13 | ~spl2_2 | ~spl2_12),
% 0.13/0.42    inference(avatar_split_clause,[],[f83,f80,f38,f86])).
% 0.13/0.42  fof(f38,plain,(
% 0.13/0.42    spl2_2 <=> m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 0.13/0.42    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 0.13/0.42  fof(f80,plain,(
% 0.13/0.42    spl2_12 <=> ! [X1,X0] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1)))),
% 0.13/0.42    introduced(avatar_definition,[new_symbols(naming,[spl2_12])])).
% 0.13/0.42  fof(f83,plain,(
% 0.13/0.42    r1_tarski(sK1,sK0) | (~spl2_2 | ~spl2_12)),
% 0.13/0.42    inference(resolution,[],[f81,f40])).
% 0.13/0.42  fof(f40,plain,(
% 0.13/0.42    m1_subset_1(sK1,k1_zfmisc_1(sK0)) | ~spl2_2),
% 0.13/0.42    inference(avatar_component_clause,[],[f38])).
% 0.13/0.42  fof(f81,plain,(
% 0.13/0.42    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) ) | ~spl2_12),
% 0.13/0.42    inference(avatar_component_clause,[],[f80])).
% 0.13/0.42  fof(f82,plain,(
% 0.13/0.42    spl2_12),
% 0.13/0.42    inference(avatar_split_clause,[],[f30,f80])).
% 0.13/0.42  fof(f30,plain,(
% 0.13/0.42    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 0.13/0.42    inference(cnf_transformation,[],[f18])).
% 0.13/0.42  fof(f18,plain,(
% 0.13/0.42    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 0.13/0.42    inference(nnf_transformation,[],[f2])).
% 0.13/0.42  fof(f2,axiom,(
% 0.13/0.42    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.13/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).
% 0.13/0.42  fof(f74,plain,(
% 0.13/0.42    spl2_10),
% 0.13/0.42    inference(avatar_split_clause,[],[f29,f72])).
% 0.13/0.42  fof(f29,plain,(
% 0.13/0.42    ( ! [X0,X1] : (k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k2_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 0.13/0.42    inference(cnf_transformation,[],[f15])).
% 0.13/0.42  fof(f15,plain,(
% 0.13/0.42    ! [X0,X1] : (k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k2_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 0.13/0.42    inference(flattening,[],[f14])).
% 0.13/0.42  fof(f14,plain,(
% 0.13/0.42    ! [X0,X1] : ((k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k2_relat_1(X1))) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 0.13/0.42    inference(ennf_transformation,[],[f7])).
% 0.13/0.42  fof(f7,axiom,(
% 0.13/0.42    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (r1_tarski(X0,k2_relat_1(X1)) => k9_relat_1(X1,k10_relat_1(X1,X0)) = X0))),
% 0.13/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t147_funct_1)).
% 0.13/0.42  fof(f70,plain,(
% 0.13/0.42    spl2_9),
% 0.13/0.42    inference(avatar_split_clause,[],[f28,f68])).
% 0.13/0.42  fof(f28,plain,(
% 0.13/0.42    ( ! [X2,X0,X1] : (k9_relat_1(k5_relat_1(X1,X2),X0) = k9_relat_1(X2,k9_relat_1(X1,X0)) | ~v1_relat_1(X2) | ~v1_relat_1(X1)) )),
% 0.13/0.42    inference(cnf_transformation,[],[f13])).
% 0.13/0.42  fof(f13,plain,(
% 0.13/0.42    ! [X0,X1] : (! [X2] : (k9_relat_1(k5_relat_1(X1,X2),X0) = k9_relat_1(X2,k9_relat_1(X1,X0)) | ~v1_relat_1(X2)) | ~v1_relat_1(X1))),
% 0.13/0.42    inference(ennf_transformation,[],[f4])).
% 0.13/0.42  fof(f4,axiom,(
% 0.13/0.42    ! [X0,X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => k9_relat_1(k5_relat_1(X1,X2),X0) = k9_relat_1(X2,k9_relat_1(X1,X0))))),
% 0.13/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t159_relat_1)).
% 0.13/0.42  fof(f66,plain,(
% 0.13/0.42    spl2_8),
% 0.13/0.42    inference(avatar_split_clause,[],[f27,f64])).
% 0.13/0.42  fof(f27,plain,(
% 0.13/0.42    ( ! [X0,X1] : (k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1))) )),
% 0.13/0.42    inference(cnf_transformation,[],[f8])).
% 0.13/0.42  fof(f8,axiom,(
% 0.13/0.42    ! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1))),
% 0.13/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_funct_1)).
% 0.13/0.42  fof(f62,plain,(
% 0.13/0.42    spl2_7),
% 0.13/0.42    inference(avatar_split_clause,[],[f26,f60])).
% 0.13/0.42  fof(f26,plain,(
% 0.13/0.42    ( ! [X0] : (k3_xboole_0(X0,X0) = X0) )),
% 0.13/0.42    inference(cnf_transformation,[],[f11])).
% 0.13/0.42  fof(f11,plain,(
% 0.13/0.42    ! [X0] : k3_xboole_0(X0,X0) = X0),
% 0.13/0.42    inference(rectify,[],[f1])).
% 0.13/0.42  fof(f1,axiom,(
% 0.13/0.42    ! [X0,X1] : k3_xboole_0(X0,X0) = X0),
% 0.13/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).
% 0.13/0.42  fof(f54,plain,(
% 0.13/0.42    spl2_5),
% 0.13/0.42    inference(avatar_split_clause,[],[f25,f52])).
% 0.13/0.42  fof(f25,plain,(
% 0.13/0.42    ( ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0) )),
% 0.13/0.42    inference(cnf_transformation,[],[f5])).
% 0.13/0.42  fof(f5,axiom,(
% 0.13/0.42    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 0.13/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).
% 0.13/0.42  fof(f50,plain,(
% 0.13/0.42    spl2_3),
% 0.13/0.42    inference(avatar_split_clause,[],[f22,f43])).
% 0.13/0.42  fof(f22,plain,(
% 0.13/0.42    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 0.13/0.42    inference(cnf_transformation,[],[f6])).
% 0.13/0.42  fof(f6,axiom,(
% 0.13/0.42    ! [X0] : (v1_funct_1(k6_relat_1(X0)) & v1_relat_1(k6_relat_1(X0)))),
% 0.13/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc3_funct_1)).
% 0.13/0.42  fof(f49,plain,(
% 0.13/0.42    spl2_4),
% 0.13/0.42    inference(avatar_split_clause,[],[f23,f47])).
% 0.13/0.42  fof(f23,plain,(
% 0.13/0.42    ( ! [X0] : (v1_funct_1(k6_relat_1(X0))) )),
% 0.13/0.42    inference(cnf_transformation,[],[f6])).
% 0.13/0.42  fof(f41,plain,(
% 0.13/0.42    spl2_2),
% 0.13/0.42    inference(avatar_split_clause,[],[f19,f38])).
% 0.13/0.42  fof(f19,plain,(
% 0.13/0.42    m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 0.13/0.42    inference(cnf_transformation,[],[f17])).
% 0.13/0.42  fof(f17,plain,(
% 0.13/0.42    sK1 != k9_relat_1(k6_relat_1(sK0),sK1) & m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 0.13/0.42    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f12,f16])).
% 0.13/0.42  fof(f16,plain,(
% 0.13/0.42    ? [X0,X1] : (k9_relat_1(k6_relat_1(X0),X1) != X1 & m1_subset_1(X1,k1_zfmisc_1(X0))) => (sK1 != k9_relat_1(k6_relat_1(sK0),sK1) & m1_subset_1(sK1,k1_zfmisc_1(sK0)))),
% 0.13/0.42    introduced(choice_axiom,[])).
% 0.13/0.42  fof(f12,plain,(
% 0.13/0.42    ? [X0,X1] : (k9_relat_1(k6_relat_1(X0),X1) != X1 & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.13/0.42    inference(ennf_transformation,[],[f10])).
% 0.13/0.42  fof(f10,negated_conjecture,(
% 0.13/0.42    ~! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k9_relat_1(k6_relat_1(X0),X1) = X1)),
% 0.13/0.42    inference(negated_conjecture,[],[f9])).
% 0.13/0.42  fof(f9,conjecture,(
% 0.13/0.42    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k9_relat_1(k6_relat_1(X0),X1) = X1)),
% 0.13/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t162_funct_1)).
% 0.13/0.42  fof(f36,plain,(
% 0.13/0.42    ~spl2_1),
% 0.13/0.42    inference(avatar_split_clause,[],[f20,f33])).
% 0.13/0.42  fof(f20,plain,(
% 0.13/0.42    sK1 != k9_relat_1(k6_relat_1(sK0),sK1)),
% 0.13/0.42    inference(cnf_transformation,[],[f17])).
% 0.13/0.42  % SZS output end Proof for theBenchmark
% 0.13/0.43  % (21443)------------------------------
% 0.13/0.43  % (21443)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.13/0.43  % (21443)Termination reason: Refutation
% 0.13/0.43  
% 0.13/0.43  % (21443)Memory used [KB]: 10618
% 0.13/0.43  % (21443)Time elapsed: 0.008 s
% 0.13/0.43  % (21443)------------------------------
% 0.13/0.43  % (21443)------------------------------
% 0.22/0.43  % (21435)Success in time 0.067 s
%------------------------------------------------------------------------------
