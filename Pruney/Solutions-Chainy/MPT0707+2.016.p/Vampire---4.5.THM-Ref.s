%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:54:28 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   91 ( 143 expanded)
%              Number of leaves         :   25 (  68 expanded)
%              Depth                    :    6
%              Number of atoms          :  228 ( 348 expanded)
%              Number of equality atoms :   59 (  99 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f136,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f32,f37,f41,f45,f49,f53,f57,f61,f65,f73,f80,f87,f94,f117,f123,f130,f135])).

fof(f135,plain,
    ( spl2_1
    | ~ spl2_17
    | ~ spl2_19 ),
    inference(avatar_contradiction_clause,[],[f134])).

fof(f134,plain,
    ( $false
    | spl2_1
    | ~ spl2_17
    | ~ spl2_19 ),
    inference(subsumption_resolution,[],[f132,f114])).

fof(f114,plain,
    ( sK1 = k3_xboole_0(sK0,sK1)
    | ~ spl2_17 ),
    inference(avatar_component_clause,[],[f112])).

fof(f112,plain,
    ( spl2_17
  <=> sK1 = k3_xboole_0(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_17])])).

fof(f132,plain,
    ( sK1 != k3_xboole_0(sK0,sK1)
    | spl2_1
    | ~ spl2_19 ),
    inference(superposition,[],[f31,f129])).

fof(f129,plain,
    ( ! [X0,X1] : k3_xboole_0(X1,X0) = k9_relat_1(k6_relat_1(X1),X0)
    | ~ spl2_19 ),
    inference(avatar_component_clause,[],[f128])).

fof(f128,plain,
    ( spl2_19
  <=> ! [X1,X0] : k3_xboole_0(X1,X0) = k9_relat_1(k6_relat_1(X1),X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_19])])).

fof(f31,plain,
    ( sK1 != k9_relat_1(k6_relat_1(sK0),sK1)
    | spl2_1 ),
    inference(avatar_component_clause,[],[f29])).

fof(f29,plain,
    ( spl2_1
  <=> sK1 = k9_relat_1(k6_relat_1(sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f130,plain,
    ( spl2_19
    | ~ spl2_3
    | ~ spl2_4
    | ~ spl2_8
    | ~ spl2_18 ),
    inference(avatar_split_clause,[],[f126,f121,f59,f43,f39,f128])).

fof(f39,plain,
    ( spl2_3
  <=> ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).

fof(f43,plain,
    ( spl2_4
  <=> ! [X0] : k2_relat_1(k6_relat_1(X0)) = X0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).

fof(f59,plain,
    ( spl2_8
  <=> ! [X1,X0] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_8])])).

fof(f121,plain,
    ( spl2_18
  <=> ! [X1,X0] :
        ( k2_relat_1(k5_relat_1(k6_relat_1(X1),X0)) = k9_relat_1(X0,X1)
        | ~ v1_relat_1(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_18])])).

fof(f126,plain,
    ( ! [X0,X1] : k3_xboole_0(X1,X0) = k9_relat_1(k6_relat_1(X1),X0)
    | ~ spl2_3
    | ~ spl2_4
    | ~ spl2_8
    | ~ spl2_18 ),
    inference(forward_demodulation,[],[f125,f44])).

fof(f44,plain,
    ( ! [X0] : k2_relat_1(k6_relat_1(X0)) = X0
    | ~ spl2_4 ),
    inference(avatar_component_clause,[],[f43])).

fof(f125,plain,
    ( ! [X0,X1] : k9_relat_1(k6_relat_1(X1),X0) = k2_relat_1(k6_relat_1(k3_xboole_0(X1,X0)))
    | ~ spl2_3
    | ~ spl2_8
    | ~ spl2_18 ),
    inference(forward_demodulation,[],[f124,f60])).

fof(f60,plain,
    ( ! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1))
    | ~ spl2_8 ),
    inference(avatar_component_clause,[],[f59])).

fof(f124,plain,
    ( ! [X0,X1] : k2_relat_1(k5_relat_1(k6_relat_1(X0),k6_relat_1(X1))) = k9_relat_1(k6_relat_1(X1),X0)
    | ~ spl2_3
    | ~ spl2_18 ),
    inference(resolution,[],[f122,f40])).

fof(f40,plain,
    ( ! [X0] : v1_relat_1(k6_relat_1(X0))
    | ~ spl2_3 ),
    inference(avatar_component_clause,[],[f39])).

fof(f122,plain,
    ( ! [X0,X1] :
        ( ~ v1_relat_1(X0)
        | k2_relat_1(k5_relat_1(k6_relat_1(X1),X0)) = k9_relat_1(X0,X1) )
    | ~ spl2_18 ),
    inference(avatar_component_clause,[],[f121])).

fof(f123,plain,
    ( spl2_18
    | ~ spl2_3
    | ~ spl2_4
    | ~ spl2_6 ),
    inference(avatar_split_clause,[],[f119,f51,f43,f39,f121])).

fof(f51,plain,
    ( spl2_6
  <=> ! [X1,X0] :
        ( k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0))
        | ~ v1_relat_1(X1)
        | ~ v1_relat_1(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).

fof(f119,plain,
    ( ! [X0,X1] :
        ( k2_relat_1(k5_relat_1(k6_relat_1(X1),X0)) = k9_relat_1(X0,X1)
        | ~ v1_relat_1(X0) )
    | ~ spl2_3
    | ~ spl2_4
    | ~ spl2_6 ),
    inference(forward_demodulation,[],[f118,f44])).

fof(f118,plain,
    ( ! [X0,X1] :
        ( ~ v1_relat_1(X0)
        | k2_relat_1(k5_relat_1(k6_relat_1(X1),X0)) = k9_relat_1(X0,k2_relat_1(k6_relat_1(X1))) )
    | ~ spl2_3
    | ~ spl2_6 ),
    inference(resolution,[],[f52,f40])).

fof(f52,plain,
    ( ! [X0,X1] :
        ( ~ v1_relat_1(X0)
        | ~ v1_relat_1(X1)
        | k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0)) )
    | ~ spl2_6 ),
    inference(avatar_component_clause,[],[f51])).

fof(f117,plain,
    ( spl2_17
    | ~ spl2_4
    | ~ spl2_14 ),
    inference(avatar_split_clause,[],[f116,f91,f43,f112])).

fof(f91,plain,
    ( spl2_14
  <=> k6_relat_1(sK1) = k6_relat_1(k3_xboole_0(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_14])])).

fof(f116,plain,
    ( sK1 = k3_xboole_0(sK0,sK1)
    | ~ spl2_4
    | ~ spl2_14 ),
    inference(forward_demodulation,[],[f98,f44])).

fof(f98,plain,
    ( k3_xboole_0(sK0,sK1) = k2_relat_1(k6_relat_1(sK1))
    | ~ spl2_4
    | ~ spl2_14 ),
    inference(superposition,[],[f44,f93])).

fof(f93,plain,
    ( k6_relat_1(sK1) = k6_relat_1(k3_xboole_0(sK0,sK1))
    | ~ spl2_14 ),
    inference(avatar_component_clause,[],[f91])).

fof(f94,plain,
    ( spl2_14
    | ~ spl2_7
    | ~ spl2_12
    | ~ spl2_13 ),
    inference(avatar_split_clause,[],[f89,f85,f77,f55,f91])).

fof(f55,plain,
    ( spl2_7
  <=> ! [X1,X0] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).

fof(f77,plain,
    ( spl2_12
  <=> r1_tarski(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_12])])).

fof(f85,plain,
    ( spl2_13
  <=> ! [X1,X0] :
        ( k6_relat_1(X0) = k6_relat_1(k3_xboole_0(X0,X1))
        | ~ r1_tarski(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_13])])).

fof(f89,plain,
    ( k6_relat_1(sK1) = k6_relat_1(k3_xboole_0(sK0,sK1))
    | ~ spl2_7
    | ~ spl2_12
    | ~ spl2_13 ),
    inference(forward_demodulation,[],[f88,f56])).

fof(f56,plain,
    ( ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)
    | ~ spl2_7 ),
    inference(avatar_component_clause,[],[f55])).

fof(f88,plain,
    ( k6_relat_1(sK1) = k6_relat_1(k3_xboole_0(sK1,sK0))
    | ~ spl2_12
    | ~ spl2_13 ),
    inference(resolution,[],[f86,f79])).

fof(f79,plain,
    ( r1_tarski(sK1,sK0)
    | ~ spl2_12 ),
    inference(avatar_component_clause,[],[f77])).

fof(f86,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(X0,X1)
        | k6_relat_1(X0) = k6_relat_1(k3_xboole_0(X0,X1)) )
    | ~ spl2_13 ),
    inference(avatar_component_clause,[],[f85])).

fof(f87,plain,
    ( spl2_13
    | ~ spl2_3
    | ~ spl2_5
    | ~ spl2_8
    | ~ spl2_9 ),
    inference(avatar_split_clause,[],[f83,f63,f59,f47,f39,f85])).

fof(f47,plain,
    ( spl2_5
  <=> ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).

fof(f63,plain,
    ( spl2_9
  <=> ! [X1,X0] :
        ( k5_relat_1(k6_relat_1(X0),X1) = X1
        | ~ r1_tarski(k1_relat_1(X1),X0)
        | ~ v1_relat_1(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_9])])).

fof(f83,plain,
    ( ! [X0,X1] :
        ( k6_relat_1(X0) = k6_relat_1(k3_xboole_0(X0,X1))
        | ~ r1_tarski(X0,X1) )
    | ~ spl2_3
    | ~ spl2_5
    | ~ spl2_8
    | ~ spl2_9 ),
    inference(forward_demodulation,[],[f82,f60])).

fof(f82,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(X0,X1)
        | k6_relat_1(X0) = k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) )
    | ~ spl2_3
    | ~ spl2_5
    | ~ spl2_9 ),
    inference(forward_demodulation,[],[f81,f48])).

fof(f48,plain,
    ( ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0
    | ~ spl2_5 ),
    inference(avatar_component_clause,[],[f47])).

fof(f81,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(k1_relat_1(k6_relat_1(X0)),X1)
        | k6_relat_1(X0) = k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) )
    | ~ spl2_3
    | ~ spl2_9 ),
    inference(resolution,[],[f64,f40])).

fof(f64,plain,
    ( ! [X0,X1] :
        ( ~ v1_relat_1(X1)
        | ~ r1_tarski(k1_relat_1(X1),X0)
        | k5_relat_1(k6_relat_1(X0),X1) = X1 )
    | ~ spl2_9 ),
    inference(avatar_component_clause,[],[f63])).

fof(f80,plain,
    ( spl2_12
    | ~ spl2_2
    | ~ spl2_11 ),
    inference(avatar_split_clause,[],[f74,f71,f34,f77])).

fof(f34,plain,
    ( spl2_2
  <=> m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f71,plain,
    ( spl2_11
  <=> ! [X1,X0] :
        ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_11])])).

fof(f74,plain,
    ( r1_tarski(sK1,sK0)
    | ~ spl2_2
    | ~ spl2_11 ),
    inference(resolution,[],[f72,f36])).

fof(f36,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(sK0))
    | ~ spl2_2 ),
    inference(avatar_component_clause,[],[f34])).

fof(f72,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
        | r1_tarski(X0,X1) )
    | ~ spl2_11 ),
    inference(avatar_component_clause,[],[f71])).

fof(f73,plain,(
    spl2_11 ),
    inference(avatar_split_clause,[],[f26,f71])).

fof(f26,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
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

fof(f65,plain,(
    spl2_9 ),
    inference(avatar_split_clause,[],[f25,f63])).

fof(f25,plain,(
    ! [X0,X1] :
      ( k5_relat_1(k6_relat_1(X0),X1) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
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
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(k1_relat_1(X1),X0)
       => k5_relat_1(k6_relat_1(X0),X1) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t77_relat_1)).

fof(f61,plain,(
    spl2_8 ),
    inference(avatar_split_clause,[],[f24,f59])).

fof(f24,plain,(
    ! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_funct_1)).

fof(f57,plain,(
    spl2_7 ),
    inference(avatar_split_clause,[],[f23,f55])).

fof(f23,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f53,plain,(
    spl2_6 ),
    inference(avatar_split_clause,[],[f22,f51])).

fof(f22,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t160_relat_1)).

fof(f49,plain,(
    spl2_5 ),
    inference(avatar_split_clause,[],[f20,f47])).

fof(f20,plain,(
    ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

fof(f45,plain,(
    spl2_4 ),
    inference(avatar_split_clause,[],[f21,f43])).

fof(f21,plain,(
    ! [X0] : k2_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f5])).

fof(f41,plain,(
    spl2_3 ),
    inference(avatar_split_clause,[],[f19,f39])).

fof(f19,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_relat_1)).

fof(f37,plain,(
    spl2_2 ),
    inference(avatar_split_clause,[],[f17,f34])).

fof(f17,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,
    ( sK1 != k9_relat_1(k6_relat_1(sK0),sK1)
    & m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f10,f14])).

fof(f14,plain,
    ( ? [X0,X1] :
        ( k9_relat_1(k6_relat_1(X0),X1) != X1
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
   => ( sK1 != k9_relat_1(k6_relat_1(sK0),sK1)
      & m1_subset_1(sK1,k1_zfmisc_1(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f10,plain,(
    ? [X0,X1] :
      ( k9_relat_1(k6_relat_1(X0),X1) != X1
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(X0))
       => k9_relat_1(k6_relat_1(X0),X1) = X1 ) ),
    inference(negated_conjecture,[],[f8])).

% (3446)lrs-11_8_afr=on:afp=100000:afq=2.0:anc=none:bd=off:cond=on:gs=on:lma=on:nm=2:newcnf=on:nwc=3:stl=30:sac=on:sp=occurrence_6 on theBenchmark
fof(f8,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k9_relat_1(k6_relat_1(X0),X1) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t162_funct_1)).

fof(f32,plain,(
    ~ spl2_1 ),
    inference(avatar_split_clause,[],[f18,f29])).

fof(f18,plain,(
    sK1 != k9_relat_1(k6_relat_1(sK0),sK1) ),
    inference(cnf_transformation,[],[f15])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 16:08:37 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.20/0.43  % (3451)ott+11_50_add=large:afr=on:afp=40000:afq=1.1:amm=sco:anc=all:bd=off:cond=fast:gs=on:gsem=on:irw=on:lma=on:nm=0:nwc=1:sp=occurrence:updr=off:uhcvi=on_102 on theBenchmark
% 0.20/0.43  % (3451)Refutation found. Thanks to Tanya!
% 0.20/0.43  % SZS status Theorem for theBenchmark
% 0.20/0.43  % SZS output start Proof for theBenchmark
% 0.20/0.43  fof(f136,plain,(
% 0.20/0.43    $false),
% 0.20/0.43    inference(avatar_sat_refutation,[],[f32,f37,f41,f45,f49,f53,f57,f61,f65,f73,f80,f87,f94,f117,f123,f130,f135])).
% 0.20/0.43  fof(f135,plain,(
% 0.20/0.43    spl2_1 | ~spl2_17 | ~spl2_19),
% 0.20/0.43    inference(avatar_contradiction_clause,[],[f134])).
% 0.20/0.43  fof(f134,plain,(
% 0.20/0.43    $false | (spl2_1 | ~spl2_17 | ~spl2_19)),
% 0.20/0.43    inference(subsumption_resolution,[],[f132,f114])).
% 0.20/0.43  fof(f114,plain,(
% 0.20/0.43    sK1 = k3_xboole_0(sK0,sK1) | ~spl2_17),
% 0.20/0.43    inference(avatar_component_clause,[],[f112])).
% 0.20/0.43  fof(f112,plain,(
% 0.20/0.43    spl2_17 <=> sK1 = k3_xboole_0(sK0,sK1)),
% 0.20/0.43    introduced(avatar_definition,[new_symbols(naming,[spl2_17])])).
% 0.20/0.43  fof(f132,plain,(
% 0.20/0.43    sK1 != k3_xboole_0(sK0,sK1) | (spl2_1 | ~spl2_19)),
% 0.20/0.43    inference(superposition,[],[f31,f129])).
% 0.20/0.43  fof(f129,plain,(
% 0.20/0.43    ( ! [X0,X1] : (k3_xboole_0(X1,X0) = k9_relat_1(k6_relat_1(X1),X0)) ) | ~spl2_19),
% 0.20/0.43    inference(avatar_component_clause,[],[f128])).
% 0.20/0.43  fof(f128,plain,(
% 0.20/0.43    spl2_19 <=> ! [X1,X0] : k3_xboole_0(X1,X0) = k9_relat_1(k6_relat_1(X1),X0)),
% 0.20/0.43    introduced(avatar_definition,[new_symbols(naming,[spl2_19])])).
% 0.20/0.43  fof(f31,plain,(
% 0.20/0.43    sK1 != k9_relat_1(k6_relat_1(sK0),sK1) | spl2_1),
% 0.20/0.43    inference(avatar_component_clause,[],[f29])).
% 0.20/0.43  fof(f29,plain,(
% 0.20/0.43    spl2_1 <=> sK1 = k9_relat_1(k6_relat_1(sK0),sK1)),
% 0.20/0.43    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 0.20/0.43  fof(f130,plain,(
% 0.20/0.43    spl2_19 | ~spl2_3 | ~spl2_4 | ~spl2_8 | ~spl2_18),
% 0.20/0.43    inference(avatar_split_clause,[],[f126,f121,f59,f43,f39,f128])).
% 0.20/0.43  fof(f39,plain,(
% 0.20/0.43    spl2_3 <=> ! [X0] : v1_relat_1(k6_relat_1(X0))),
% 0.20/0.43    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).
% 0.20/0.43  fof(f43,plain,(
% 0.20/0.43    spl2_4 <=> ! [X0] : k2_relat_1(k6_relat_1(X0)) = X0),
% 0.20/0.43    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).
% 0.20/0.43  fof(f59,plain,(
% 0.20/0.43    spl2_8 <=> ! [X1,X0] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1))),
% 0.20/0.43    introduced(avatar_definition,[new_symbols(naming,[spl2_8])])).
% 0.20/0.43  fof(f121,plain,(
% 0.20/0.43    spl2_18 <=> ! [X1,X0] : (k2_relat_1(k5_relat_1(k6_relat_1(X1),X0)) = k9_relat_1(X0,X1) | ~v1_relat_1(X0))),
% 0.20/0.43    introduced(avatar_definition,[new_symbols(naming,[spl2_18])])).
% 0.20/0.43  fof(f126,plain,(
% 0.20/0.43    ( ! [X0,X1] : (k3_xboole_0(X1,X0) = k9_relat_1(k6_relat_1(X1),X0)) ) | (~spl2_3 | ~spl2_4 | ~spl2_8 | ~spl2_18)),
% 0.20/0.43    inference(forward_demodulation,[],[f125,f44])).
% 0.20/0.43  fof(f44,plain,(
% 0.20/0.43    ( ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0) ) | ~spl2_4),
% 0.20/0.43    inference(avatar_component_clause,[],[f43])).
% 0.20/0.43  fof(f125,plain,(
% 0.20/0.43    ( ! [X0,X1] : (k9_relat_1(k6_relat_1(X1),X0) = k2_relat_1(k6_relat_1(k3_xboole_0(X1,X0)))) ) | (~spl2_3 | ~spl2_8 | ~spl2_18)),
% 0.20/0.43    inference(forward_demodulation,[],[f124,f60])).
% 0.20/0.43  fof(f60,plain,(
% 0.20/0.43    ( ! [X0,X1] : (k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1))) ) | ~spl2_8),
% 0.20/0.43    inference(avatar_component_clause,[],[f59])).
% 0.20/0.43  fof(f124,plain,(
% 0.20/0.43    ( ! [X0,X1] : (k2_relat_1(k5_relat_1(k6_relat_1(X0),k6_relat_1(X1))) = k9_relat_1(k6_relat_1(X1),X0)) ) | (~spl2_3 | ~spl2_18)),
% 0.20/0.43    inference(resolution,[],[f122,f40])).
% 0.20/0.43  fof(f40,plain,(
% 0.20/0.43    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) ) | ~spl2_3),
% 0.20/0.43    inference(avatar_component_clause,[],[f39])).
% 0.20/0.43  fof(f122,plain,(
% 0.20/0.43    ( ! [X0,X1] : (~v1_relat_1(X0) | k2_relat_1(k5_relat_1(k6_relat_1(X1),X0)) = k9_relat_1(X0,X1)) ) | ~spl2_18),
% 0.20/0.43    inference(avatar_component_clause,[],[f121])).
% 0.20/0.43  fof(f123,plain,(
% 0.20/0.43    spl2_18 | ~spl2_3 | ~spl2_4 | ~spl2_6),
% 0.20/0.43    inference(avatar_split_clause,[],[f119,f51,f43,f39,f121])).
% 0.20/0.43  fof(f51,plain,(
% 0.20/0.43    spl2_6 <=> ! [X1,X0] : (k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0)) | ~v1_relat_1(X1) | ~v1_relat_1(X0))),
% 0.20/0.43    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).
% 0.20/0.43  fof(f119,plain,(
% 0.20/0.43    ( ! [X0,X1] : (k2_relat_1(k5_relat_1(k6_relat_1(X1),X0)) = k9_relat_1(X0,X1) | ~v1_relat_1(X0)) ) | (~spl2_3 | ~spl2_4 | ~spl2_6)),
% 0.20/0.43    inference(forward_demodulation,[],[f118,f44])).
% 0.20/0.43  fof(f118,plain,(
% 0.20/0.43    ( ! [X0,X1] : (~v1_relat_1(X0) | k2_relat_1(k5_relat_1(k6_relat_1(X1),X0)) = k9_relat_1(X0,k2_relat_1(k6_relat_1(X1)))) ) | (~spl2_3 | ~spl2_6)),
% 0.20/0.43    inference(resolution,[],[f52,f40])).
% 0.20/0.43  fof(f52,plain,(
% 0.20/0.43    ( ! [X0,X1] : (~v1_relat_1(X0) | ~v1_relat_1(X1) | k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0))) ) | ~spl2_6),
% 0.20/0.43    inference(avatar_component_clause,[],[f51])).
% 0.20/0.43  fof(f117,plain,(
% 0.20/0.43    spl2_17 | ~spl2_4 | ~spl2_14),
% 0.20/0.43    inference(avatar_split_clause,[],[f116,f91,f43,f112])).
% 0.20/0.43  fof(f91,plain,(
% 0.20/0.43    spl2_14 <=> k6_relat_1(sK1) = k6_relat_1(k3_xboole_0(sK0,sK1))),
% 0.20/0.43    introduced(avatar_definition,[new_symbols(naming,[spl2_14])])).
% 0.20/0.43  fof(f116,plain,(
% 0.20/0.43    sK1 = k3_xboole_0(sK0,sK1) | (~spl2_4 | ~spl2_14)),
% 0.20/0.43    inference(forward_demodulation,[],[f98,f44])).
% 0.20/0.43  fof(f98,plain,(
% 0.20/0.43    k3_xboole_0(sK0,sK1) = k2_relat_1(k6_relat_1(sK1)) | (~spl2_4 | ~spl2_14)),
% 0.20/0.43    inference(superposition,[],[f44,f93])).
% 0.20/0.43  fof(f93,plain,(
% 0.20/0.43    k6_relat_1(sK1) = k6_relat_1(k3_xboole_0(sK0,sK1)) | ~spl2_14),
% 0.20/0.43    inference(avatar_component_clause,[],[f91])).
% 0.20/0.43  fof(f94,plain,(
% 0.20/0.43    spl2_14 | ~spl2_7 | ~spl2_12 | ~spl2_13),
% 0.20/0.43    inference(avatar_split_clause,[],[f89,f85,f77,f55,f91])).
% 0.20/0.43  fof(f55,plain,(
% 0.20/0.43    spl2_7 <=> ! [X1,X0] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 0.20/0.43    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).
% 0.20/0.43  fof(f77,plain,(
% 0.20/0.43    spl2_12 <=> r1_tarski(sK1,sK0)),
% 0.20/0.43    introduced(avatar_definition,[new_symbols(naming,[spl2_12])])).
% 0.20/0.43  fof(f85,plain,(
% 0.20/0.43    spl2_13 <=> ! [X1,X0] : (k6_relat_1(X0) = k6_relat_1(k3_xboole_0(X0,X1)) | ~r1_tarski(X0,X1))),
% 0.20/0.43    introduced(avatar_definition,[new_symbols(naming,[spl2_13])])).
% 0.20/0.43  fof(f89,plain,(
% 0.20/0.43    k6_relat_1(sK1) = k6_relat_1(k3_xboole_0(sK0,sK1)) | (~spl2_7 | ~spl2_12 | ~spl2_13)),
% 0.20/0.43    inference(forward_demodulation,[],[f88,f56])).
% 0.20/0.43  fof(f56,plain,(
% 0.20/0.43    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) ) | ~spl2_7),
% 0.20/0.43    inference(avatar_component_clause,[],[f55])).
% 0.20/0.43  fof(f88,plain,(
% 0.20/0.43    k6_relat_1(sK1) = k6_relat_1(k3_xboole_0(sK1,sK0)) | (~spl2_12 | ~spl2_13)),
% 0.20/0.43    inference(resolution,[],[f86,f79])).
% 0.20/0.43  fof(f79,plain,(
% 0.20/0.43    r1_tarski(sK1,sK0) | ~spl2_12),
% 0.20/0.43    inference(avatar_component_clause,[],[f77])).
% 0.20/0.43  fof(f86,plain,(
% 0.20/0.43    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k6_relat_1(X0) = k6_relat_1(k3_xboole_0(X0,X1))) ) | ~spl2_13),
% 0.20/0.43    inference(avatar_component_clause,[],[f85])).
% 0.20/0.43  fof(f87,plain,(
% 0.20/0.43    spl2_13 | ~spl2_3 | ~spl2_5 | ~spl2_8 | ~spl2_9),
% 0.20/0.43    inference(avatar_split_clause,[],[f83,f63,f59,f47,f39,f85])).
% 0.20/0.43  fof(f47,plain,(
% 0.20/0.43    spl2_5 <=> ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0),
% 0.20/0.43    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).
% 0.20/0.43  fof(f63,plain,(
% 0.20/0.43    spl2_9 <=> ! [X1,X0] : (k5_relat_1(k6_relat_1(X0),X1) = X1 | ~r1_tarski(k1_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 0.20/0.43    introduced(avatar_definition,[new_symbols(naming,[spl2_9])])).
% 0.20/0.43  fof(f83,plain,(
% 0.20/0.43    ( ! [X0,X1] : (k6_relat_1(X0) = k6_relat_1(k3_xboole_0(X0,X1)) | ~r1_tarski(X0,X1)) ) | (~spl2_3 | ~spl2_5 | ~spl2_8 | ~spl2_9)),
% 0.20/0.43    inference(forward_demodulation,[],[f82,f60])).
% 0.20/0.43  fof(f82,plain,(
% 0.20/0.43    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k6_relat_1(X0) = k5_relat_1(k6_relat_1(X1),k6_relat_1(X0))) ) | (~spl2_3 | ~spl2_5 | ~spl2_9)),
% 0.20/0.43    inference(forward_demodulation,[],[f81,f48])).
% 0.20/0.43  fof(f48,plain,(
% 0.20/0.43    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = X0) ) | ~spl2_5),
% 0.20/0.43    inference(avatar_component_clause,[],[f47])).
% 0.20/0.43  fof(f81,plain,(
% 0.20/0.43    ( ! [X0,X1] : (~r1_tarski(k1_relat_1(k6_relat_1(X0)),X1) | k6_relat_1(X0) = k5_relat_1(k6_relat_1(X1),k6_relat_1(X0))) ) | (~spl2_3 | ~spl2_9)),
% 0.20/0.43    inference(resolution,[],[f64,f40])).
% 0.20/0.43  fof(f64,plain,(
% 0.20/0.43    ( ! [X0,X1] : (~v1_relat_1(X1) | ~r1_tarski(k1_relat_1(X1),X0) | k5_relat_1(k6_relat_1(X0),X1) = X1) ) | ~spl2_9),
% 0.20/0.43    inference(avatar_component_clause,[],[f63])).
% 0.20/0.43  fof(f80,plain,(
% 0.20/0.43    spl2_12 | ~spl2_2 | ~spl2_11),
% 0.20/0.43    inference(avatar_split_clause,[],[f74,f71,f34,f77])).
% 0.20/0.43  fof(f34,plain,(
% 0.20/0.43    spl2_2 <=> m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 0.20/0.43    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 0.20/0.43  fof(f71,plain,(
% 0.20/0.43    spl2_11 <=> ! [X1,X0] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1)))),
% 0.20/0.43    introduced(avatar_definition,[new_symbols(naming,[spl2_11])])).
% 0.20/0.43  fof(f74,plain,(
% 0.20/0.43    r1_tarski(sK1,sK0) | (~spl2_2 | ~spl2_11)),
% 0.20/0.43    inference(resolution,[],[f72,f36])).
% 0.20/0.43  fof(f36,plain,(
% 0.20/0.43    m1_subset_1(sK1,k1_zfmisc_1(sK0)) | ~spl2_2),
% 0.20/0.43    inference(avatar_component_clause,[],[f34])).
% 0.20/0.43  fof(f72,plain,(
% 0.20/0.43    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) ) | ~spl2_11),
% 0.20/0.43    inference(avatar_component_clause,[],[f71])).
% 0.20/0.43  fof(f73,plain,(
% 0.20/0.43    spl2_11),
% 0.20/0.43    inference(avatar_split_clause,[],[f26,f71])).
% 0.20/0.43  fof(f26,plain,(
% 0.20/0.43    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 0.20/0.43    inference(cnf_transformation,[],[f16])).
% 0.20/0.43  fof(f16,plain,(
% 0.20/0.43    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 0.20/0.43    inference(nnf_transformation,[],[f2])).
% 0.20/0.43  fof(f2,axiom,(
% 0.20/0.43    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.20/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).
% 0.20/0.43  fof(f65,plain,(
% 0.20/0.43    spl2_9),
% 0.20/0.43    inference(avatar_split_clause,[],[f25,f63])).
% 0.20/0.43  fof(f25,plain,(
% 0.20/0.43    ( ! [X0,X1] : (k5_relat_1(k6_relat_1(X0),X1) = X1 | ~r1_tarski(k1_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 0.20/0.43    inference(cnf_transformation,[],[f13])).
% 0.20/0.43  fof(f13,plain,(
% 0.20/0.43    ! [X0,X1] : (k5_relat_1(k6_relat_1(X0),X1) = X1 | ~r1_tarski(k1_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 0.20/0.43    inference(flattening,[],[f12])).
% 0.20/0.43  fof(f12,plain,(
% 0.20/0.43    ! [X0,X1] : ((k5_relat_1(k6_relat_1(X0),X1) = X1 | ~r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.20/0.43    inference(ennf_transformation,[],[f6])).
% 0.20/0.43  fof(f6,axiom,(
% 0.20/0.43    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(k1_relat_1(X1),X0) => k5_relat_1(k6_relat_1(X0),X1) = X1))),
% 0.20/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t77_relat_1)).
% 0.20/0.43  fof(f61,plain,(
% 0.20/0.43    spl2_8),
% 0.20/0.43    inference(avatar_split_clause,[],[f24,f59])).
% 0.20/0.43  fof(f24,plain,(
% 0.20/0.43    ( ! [X0,X1] : (k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1))) )),
% 0.20/0.43    inference(cnf_transformation,[],[f7])).
% 0.20/0.43  fof(f7,axiom,(
% 0.20/0.43    ! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1))),
% 0.20/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_funct_1)).
% 0.20/0.43  fof(f57,plain,(
% 0.20/0.43    spl2_7),
% 0.20/0.43    inference(avatar_split_clause,[],[f23,f55])).
% 0.20/0.43  fof(f23,plain,(
% 0.20/0.43    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 0.20/0.43    inference(cnf_transformation,[],[f1])).
% 0.20/0.43  fof(f1,axiom,(
% 0.20/0.43    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 0.20/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 0.20/0.43  fof(f53,plain,(
% 0.20/0.43    spl2_6),
% 0.20/0.43    inference(avatar_split_clause,[],[f22,f51])).
% 0.20/0.43  fof(f22,plain,(
% 0.20/0.43    ( ! [X0,X1] : (k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 0.20/0.43    inference(cnf_transformation,[],[f11])).
% 0.20/0.43  fof(f11,plain,(
% 0.20/0.43    ! [X0] : (! [X1] : (k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.20/0.43    inference(ennf_transformation,[],[f4])).
% 0.20/0.43  fof(f4,axiom,(
% 0.20/0.43    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0))))),
% 0.20/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t160_relat_1)).
% 0.20/0.43  fof(f49,plain,(
% 0.20/0.43    spl2_5),
% 0.20/0.43    inference(avatar_split_clause,[],[f20,f47])).
% 0.20/0.43  fof(f20,plain,(
% 0.20/0.43    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = X0) )),
% 0.20/0.43    inference(cnf_transformation,[],[f5])).
% 0.20/0.43  fof(f5,axiom,(
% 0.20/0.43    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 0.20/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).
% 0.20/0.43  fof(f45,plain,(
% 0.20/0.43    spl2_4),
% 0.20/0.43    inference(avatar_split_clause,[],[f21,f43])).
% 0.20/0.43  fof(f21,plain,(
% 0.20/0.43    ( ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0) )),
% 0.20/0.43    inference(cnf_transformation,[],[f5])).
% 0.20/0.43  fof(f41,plain,(
% 0.20/0.43    spl2_3),
% 0.20/0.43    inference(avatar_split_clause,[],[f19,f39])).
% 0.20/0.43  fof(f19,plain,(
% 0.20/0.43    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 0.20/0.43    inference(cnf_transformation,[],[f3])).
% 0.20/0.43  fof(f3,axiom,(
% 0.20/0.43    ! [X0] : v1_relat_1(k6_relat_1(X0))),
% 0.20/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_relat_1)).
% 0.20/0.43  fof(f37,plain,(
% 0.20/0.43    spl2_2),
% 0.20/0.43    inference(avatar_split_clause,[],[f17,f34])).
% 0.20/0.43  fof(f17,plain,(
% 0.20/0.43    m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 0.20/0.43    inference(cnf_transformation,[],[f15])).
% 0.20/0.43  fof(f15,plain,(
% 0.20/0.43    sK1 != k9_relat_1(k6_relat_1(sK0),sK1) & m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 0.20/0.43    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f10,f14])).
% 0.20/0.43  fof(f14,plain,(
% 0.20/0.43    ? [X0,X1] : (k9_relat_1(k6_relat_1(X0),X1) != X1 & m1_subset_1(X1,k1_zfmisc_1(X0))) => (sK1 != k9_relat_1(k6_relat_1(sK0),sK1) & m1_subset_1(sK1,k1_zfmisc_1(sK0)))),
% 0.20/0.43    introduced(choice_axiom,[])).
% 0.20/0.43  fof(f10,plain,(
% 0.20/0.43    ? [X0,X1] : (k9_relat_1(k6_relat_1(X0),X1) != X1 & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.20/0.43    inference(ennf_transformation,[],[f9])).
% 0.20/0.43  fof(f9,negated_conjecture,(
% 0.20/0.43    ~! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k9_relat_1(k6_relat_1(X0),X1) = X1)),
% 0.20/0.43    inference(negated_conjecture,[],[f8])).
% 0.20/0.43  % (3446)lrs-11_8_afr=on:afp=100000:afq=2.0:anc=none:bd=off:cond=on:gs=on:lma=on:nm=2:newcnf=on:nwc=3:stl=30:sac=on:sp=occurrence_6 on theBenchmark
% 0.20/0.43  fof(f8,conjecture,(
% 0.20/0.43    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k9_relat_1(k6_relat_1(X0),X1) = X1)),
% 0.20/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t162_funct_1)).
% 0.20/0.43  fof(f32,plain,(
% 0.20/0.43    ~spl2_1),
% 0.20/0.43    inference(avatar_split_clause,[],[f18,f29])).
% 0.20/0.43  fof(f18,plain,(
% 0.20/0.43    sK1 != k9_relat_1(k6_relat_1(sK0),sK1)),
% 0.20/0.43    inference(cnf_transformation,[],[f15])).
% 0.20/0.43  % SZS output end Proof for theBenchmark
% 0.20/0.43  % (3451)------------------------------
% 0.20/0.43  % (3451)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.43  % (3451)Termination reason: Refutation
% 0.20/0.43  
% 0.20/0.43  % (3451)Memory used [KB]: 10618
% 0.20/0.43  % (3451)Time elapsed: 0.007 s
% 0.20/0.43  % (3451)------------------------------
% 0.20/0.43  % (3451)------------------------------
% 0.20/0.43  % (3445)Success in time 0.077 s
%------------------------------------------------------------------------------
