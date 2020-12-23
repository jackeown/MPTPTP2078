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
% DateTime   : Thu Dec  3 12:47:03 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   95 ( 151 expanded)
%              Number of leaves         :   28 (  71 expanded)
%              Depth                    :    6
%              Number of atoms          :  255 ( 418 expanded)
%              Number of equality atoms :    6 (   8 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f231,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f48,f53,f58,f70,f79,f83,f107,f116,f123,f129,f137,f156,f176,f190,f194,f202,f215,f230])).

fof(f230,plain,
    ( ~ spl2_2
    | ~ spl2_19
    | spl2_22
    | ~ spl2_24
    | ~ spl2_28 ),
    inference(avatar_contradiction_clause,[],[f229])).

fof(f229,plain,
    ( $false
    | ~ spl2_2
    | ~ spl2_19
    | spl2_22
    | ~ spl2_24
    | ~ spl2_28 ),
    inference(subsumption_resolution,[],[f177,f219])).

fof(f219,plain,
    ( ! [X0] : v1_relat_1(k3_xboole_0(X0,sK1))
    | ~ spl2_2
    | ~ spl2_24
    | ~ spl2_28 ),
    inference(unit_resulting_resolution,[],[f52,f175,f214])).

fof(f214,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(X0,X1)
        | ~ v1_relat_1(X1)
        | v1_relat_1(X0) )
    | ~ spl2_28 ),
    inference(avatar_component_clause,[],[f213])).

fof(f213,plain,
    ( spl2_28
  <=> ! [X1,X0] :
        ( v1_relat_1(X0)
        | ~ v1_relat_1(X1)
        | ~ r1_tarski(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_28])])).

fof(f175,plain,
    ( ! [X2,X0] : r1_tarski(k3_xboole_0(X2,X0),X0)
    | ~ spl2_24 ),
    inference(avatar_component_clause,[],[f174])).

fof(f174,plain,
    ( spl2_24
  <=> ! [X0,X2] : r1_tarski(k3_xboole_0(X2,X0),X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_24])])).

fof(f52,plain,
    ( v1_relat_1(sK1)
    | ~ spl2_2 ),
    inference(avatar_component_clause,[],[f50])).

fof(f50,plain,
    ( spl2_2
  <=> v1_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f177,plain,
    ( ~ v1_relat_1(k3_xboole_0(sK0,sK1))
    | ~ spl2_2
    | ~ spl2_19
    | spl2_22
    | ~ spl2_24 ),
    inference(unit_resulting_resolution,[],[f52,f155,f175,f136])).

fof(f136,plain,
    ( ! [X0,X1] :
        ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
        | ~ r1_tarski(X0,X1)
        | ~ v1_relat_1(X1)
        | ~ v1_relat_1(X0) )
    | ~ spl2_19 ),
    inference(avatar_component_clause,[],[f135])).

fof(f135,plain,
    ( spl2_19
  <=> ! [X1,X0] :
        ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
        | ~ r1_tarski(X0,X1)
        | ~ v1_relat_1(X1)
        | ~ v1_relat_1(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_19])])).

fof(f155,plain,
    ( ~ r1_tarski(k2_relat_1(k3_xboole_0(sK0,sK1)),k2_relat_1(sK1))
    | spl2_22 ),
    inference(avatar_component_clause,[],[f153])).

fof(f153,plain,
    ( spl2_22
  <=> r1_tarski(k2_relat_1(k3_xboole_0(sK0,sK1)),k2_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_22])])).

fof(f215,plain,
    ( spl2_28
    | ~ spl2_8
    | ~ spl2_9 ),
    inference(avatar_split_clause,[],[f108,f81,f77,f213])).

fof(f77,plain,
    ( spl2_8
  <=> ! [X1,X0] :
        ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_8])])).

fof(f81,plain,
    ( spl2_9
  <=> ! [X1,X0] :
        ( v1_relat_1(X1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
        | ~ v1_relat_1(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_9])])).

fof(f108,plain,
    ( ! [X0,X1] :
        ( v1_relat_1(X0)
        | ~ v1_relat_1(X1)
        | ~ r1_tarski(X0,X1) )
    | ~ spl2_8
    | ~ spl2_9 ),
    inference(resolution,[],[f82,f78])).

fof(f78,plain,
    ( ! [X0,X1] :
        ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
    | ~ spl2_8 ),
    inference(avatar_component_clause,[],[f77])).

fof(f82,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
        | v1_relat_1(X1)
        | ~ v1_relat_1(X0) )
    | ~ spl2_9 ),
    inference(avatar_component_clause,[],[f81])).

fof(f202,plain,
    ( ~ spl2_1
    | ~ spl2_9
    | spl2_25
    | ~ spl2_26 ),
    inference(avatar_contradiction_clause,[],[f201])).

fof(f201,plain,
    ( $false
    | ~ spl2_1
    | ~ spl2_9
    | spl2_25
    | ~ spl2_26 ),
    inference(subsumption_resolution,[],[f189,f195])).

fof(f195,plain,
    ( ! [X0] : v1_relat_1(k3_xboole_0(sK0,X0))
    | ~ spl2_1
    | ~ spl2_9
    | ~ spl2_26 ),
    inference(unit_resulting_resolution,[],[f47,f193,f82])).

fof(f193,plain,
    ( ! [X0,X1] : m1_subset_1(k3_xboole_0(X0,X1),k1_zfmisc_1(X0))
    | ~ spl2_26 ),
    inference(avatar_component_clause,[],[f192])).

fof(f192,plain,
    ( spl2_26
  <=> ! [X1,X0] : m1_subset_1(k3_xboole_0(X0,X1),k1_zfmisc_1(X0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_26])])).

fof(f47,plain,
    ( v1_relat_1(sK0)
    | ~ spl2_1 ),
    inference(avatar_component_clause,[],[f45])).

fof(f45,plain,
    ( spl2_1
  <=> v1_relat_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f189,plain,
    ( ~ v1_relat_1(k3_xboole_0(sK0,sK1))
    | spl2_25 ),
    inference(avatar_component_clause,[],[f187])).

fof(f187,plain,
    ( spl2_25
  <=> v1_relat_1(k3_xboole_0(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_25])])).

fof(f194,plain,
    ( spl2_26
    | ~ spl2_6
    | ~ spl2_8 ),
    inference(avatar_split_clause,[],[f102,f77,f68,f192])).

fof(f68,plain,
    ( spl2_6
  <=> ! [X1,X0] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).

fof(f102,plain,
    ( ! [X0,X1] : m1_subset_1(k3_xboole_0(X0,X1),k1_zfmisc_1(X0))
    | ~ spl2_6
    | ~ spl2_8 ),
    inference(unit_resulting_resolution,[],[f69,f78])).

fof(f69,plain,
    ( ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0)
    | ~ spl2_6 ),
    inference(avatar_component_clause,[],[f68])).

fof(f190,plain,
    ( ~ spl2_25
    | ~ spl2_1
    | ~ spl2_6
    | ~ spl2_19
    | spl2_21 ),
    inference(avatar_split_clause,[],[f161,f149,f135,f68,f45,f187])).

fof(f149,plain,
    ( spl2_21
  <=> r1_tarski(k2_relat_1(k3_xboole_0(sK0,sK1)),k2_relat_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_21])])).

fof(f161,plain,
    ( ~ v1_relat_1(k3_xboole_0(sK0,sK1))
    | ~ spl2_1
    | ~ spl2_6
    | ~ spl2_19
    | spl2_21 ),
    inference(unit_resulting_resolution,[],[f47,f69,f151,f136])).

fof(f151,plain,
    ( ~ r1_tarski(k2_relat_1(k3_xboole_0(sK0,sK1)),k2_relat_1(sK0))
    | spl2_21 ),
    inference(avatar_component_clause,[],[f149])).

fof(f176,plain,
    ( spl2_24
    | ~ spl2_14
    | ~ spl2_16 ),
    inference(avatar_split_clause,[],[f125,f121,f105,f174])).

fof(f105,plain,
    ( spl2_14
  <=> ! [X1,X0] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_14])])).

fof(f121,plain,
    ( spl2_16
  <=> ! [X1,X0,X2] : r1_tarski(k3_xboole_0(X0,k2_xboole_0(X1,X2)),k2_xboole_0(X1,X2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_16])])).

fof(f125,plain,
    ( ! [X2,X0] : r1_tarski(k3_xboole_0(X2,X0),X0)
    | ~ spl2_14
    | ~ spl2_16 ),
    inference(superposition,[],[f122,f106])).

fof(f106,plain,
    ( ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0
    | ~ spl2_14 ),
    inference(avatar_component_clause,[],[f105])).

fof(f122,plain,
    ( ! [X2,X0,X1] : r1_tarski(k3_xboole_0(X0,k2_xboole_0(X1,X2)),k2_xboole_0(X1,X2))
    | ~ spl2_16 ),
    inference(avatar_component_clause,[],[f121])).

fof(f156,plain,
    ( ~ spl2_21
    | ~ spl2_22
    | spl2_3
    | ~ spl2_17 ),
    inference(avatar_split_clause,[],[f142,f127,f55,f153,f149])).

fof(f55,plain,
    ( spl2_3
  <=> r1_tarski(k2_relat_1(k3_xboole_0(sK0,sK1)),k3_xboole_0(k2_relat_1(sK0),k2_relat_1(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).

fof(f127,plain,
    ( spl2_17
  <=> ! [X1,X0,X2] :
        ( r1_tarski(X0,k3_xboole_0(X1,X2))
        | ~ r1_tarski(X0,X2)
        | ~ r1_tarski(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_17])])).

fof(f142,plain,
    ( ~ r1_tarski(k2_relat_1(k3_xboole_0(sK0,sK1)),k2_relat_1(sK1))
    | ~ r1_tarski(k2_relat_1(k3_xboole_0(sK0,sK1)),k2_relat_1(sK0))
    | spl2_3
    | ~ spl2_17 ),
    inference(resolution,[],[f128,f57])).

fof(f57,plain,
    ( ~ r1_tarski(k2_relat_1(k3_xboole_0(sK0,sK1)),k3_xboole_0(k2_relat_1(sK0),k2_relat_1(sK1)))
    | spl2_3 ),
    inference(avatar_component_clause,[],[f55])).

fof(f128,plain,
    ( ! [X2,X0,X1] :
        ( r1_tarski(X0,k3_xboole_0(X1,X2))
        | ~ r1_tarski(X0,X2)
        | ~ r1_tarski(X0,X1) )
    | ~ spl2_17 ),
    inference(avatar_component_clause,[],[f127])).

fof(f137,plain,(
    spl2_19 ),
    inference(avatar_split_clause,[],[f32,f135])).

fof(f32,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
            & r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) )
          | ~ r1_tarski(X0,X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
            & r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) )
          | ~ r1_tarski(X0,X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ( r1_tarski(X0,X1)
           => ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
              & r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_relat_1)).

fof(f129,plain,(
    spl2_17 ),
    inference(avatar_split_clause,[],[f43,f127])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X0,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,k3_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t19_xboole_1)).

fof(f123,plain,
    ( spl2_16
    | ~ spl2_15 ),
    inference(avatar_split_clause,[],[f117,f114,f121])).

fof(f114,plain,
    ( spl2_15
  <=> ! [X1,X0,X2] : r1_tarski(k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)),k2_xboole_0(X1,X2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_15])])).

fof(f117,plain,
    ( ! [X2,X0,X1] : r1_tarski(k3_xboole_0(X0,k2_xboole_0(X1,X2)),k2_xboole_0(X1,X2))
    | ~ spl2_15 ),
    inference(forward_demodulation,[],[f115,f42])).

fof(f42,plain,(
    ! [X2,X0,X1] : k3_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] : k3_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t23_xboole_1)).

fof(f115,plain,
    ( ! [X2,X0,X1] : r1_tarski(k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)),k2_xboole_0(X1,X2))
    | ~ spl2_15 ),
    inference(avatar_component_clause,[],[f114])).

fof(f116,plain,(
    spl2_15 ),
    inference(avatar_split_clause,[],[f41,f114])).

fof(f41,plain,(
    ! [X2,X0,X1] : r1_tarski(k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)),k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] : r1_tarski(k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)),k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_xboole_1)).

fof(f107,plain,(
    spl2_14 ),
    inference(avatar_split_clause,[],[f38,f105])).

fof(f38,plain,(
    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t51_xboole_1)).

fof(f83,plain,(
    spl2_9 ),
    inference(avatar_split_clause,[],[f33,f81])).

fof(f33,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

fof(f79,plain,(
    spl2_8 ),
    inference(avatar_split_clause,[],[f40,f77])).

fof(f40,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f70,plain,(
    spl2_6 ),
    inference(avatar_split_clause,[],[f34,f68])).

fof(f34,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).

fof(f58,plain,(
    ~ spl2_3 ),
    inference(avatar_split_clause,[],[f28,f55])).

fof(f28,plain,(
    ~ r1_tarski(k2_relat_1(k3_xboole_0(sK0,sK1)),k3_xboole_0(k2_relat_1(sK0),k2_relat_1(sK1))) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,
    ( ~ r1_tarski(k2_relat_1(k3_xboole_0(sK0,sK1)),k3_xboole_0(k2_relat_1(sK0),k2_relat_1(sK1)))
    & v1_relat_1(sK1)
    & v1_relat_1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f16,f23,f22])).

fof(f22,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ~ r1_tarski(k2_relat_1(k3_xboole_0(X0,X1)),k3_xboole_0(k2_relat_1(X0),k2_relat_1(X1)))
            & v1_relat_1(X1) )
        & v1_relat_1(X0) )
   => ( ? [X1] :
          ( ~ r1_tarski(k2_relat_1(k3_xboole_0(sK0,X1)),k3_xboole_0(k2_relat_1(sK0),k2_relat_1(X1)))
          & v1_relat_1(X1) )
      & v1_relat_1(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,
    ( ? [X1] :
        ( ~ r1_tarski(k2_relat_1(k3_xboole_0(sK0,X1)),k3_xboole_0(k2_relat_1(sK0),k2_relat_1(X1)))
        & v1_relat_1(X1) )
   => ( ~ r1_tarski(k2_relat_1(k3_xboole_0(sK0,sK1)),k3_xboole_0(k2_relat_1(sK0),k2_relat_1(sK1)))
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ r1_tarski(k2_relat_1(k3_xboole_0(X0,X1)),k3_xboole_0(k2_relat_1(X0),k2_relat_1(X1)))
          & v1_relat_1(X1) )
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,negated_conjecture,(
    ~ ! [X0] :
        ( v1_relat_1(X0)
       => ! [X1] :
            ( v1_relat_1(X1)
           => r1_tarski(k2_relat_1(k3_xboole_0(X0,X1)),k3_xboole_0(k2_relat_1(X0),k2_relat_1(X1))) ) ) ),
    inference(negated_conjecture,[],[f14])).

fof(f14,conjecture,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => r1_tarski(k2_relat_1(k3_xboole_0(X0,X1)),k3_xboole_0(k2_relat_1(X0),k2_relat_1(X1))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t27_relat_1)).

fof(f53,plain,(
    spl2_2 ),
    inference(avatar_split_clause,[],[f27,f50])).

fof(f27,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f24])).

fof(f48,plain,(
    spl2_1 ),
    inference(avatar_split_clause,[],[f26,f45])).

fof(f26,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f24])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 12:42:11 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.42  % (4147)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.21/0.43  % (4140)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.21/0.43  % (4140)Refutation found. Thanks to Tanya!
% 0.21/0.43  % SZS status Theorem for theBenchmark
% 0.21/0.43  % SZS output start Proof for theBenchmark
% 0.21/0.43  fof(f231,plain,(
% 0.21/0.43    $false),
% 0.21/0.43    inference(avatar_sat_refutation,[],[f48,f53,f58,f70,f79,f83,f107,f116,f123,f129,f137,f156,f176,f190,f194,f202,f215,f230])).
% 0.21/0.43  fof(f230,plain,(
% 0.21/0.43    ~spl2_2 | ~spl2_19 | spl2_22 | ~spl2_24 | ~spl2_28),
% 0.21/0.43    inference(avatar_contradiction_clause,[],[f229])).
% 0.21/0.43  fof(f229,plain,(
% 0.21/0.43    $false | (~spl2_2 | ~spl2_19 | spl2_22 | ~spl2_24 | ~spl2_28)),
% 0.21/0.43    inference(subsumption_resolution,[],[f177,f219])).
% 0.21/0.43  fof(f219,plain,(
% 0.21/0.43    ( ! [X0] : (v1_relat_1(k3_xboole_0(X0,sK1))) ) | (~spl2_2 | ~spl2_24 | ~spl2_28)),
% 0.21/0.43    inference(unit_resulting_resolution,[],[f52,f175,f214])).
% 0.21/0.43  fof(f214,plain,(
% 0.21/0.43    ( ! [X0,X1] : (~r1_tarski(X0,X1) | ~v1_relat_1(X1) | v1_relat_1(X0)) ) | ~spl2_28),
% 0.21/0.43    inference(avatar_component_clause,[],[f213])).
% 0.21/0.43  fof(f213,plain,(
% 0.21/0.43    spl2_28 <=> ! [X1,X0] : (v1_relat_1(X0) | ~v1_relat_1(X1) | ~r1_tarski(X0,X1))),
% 0.21/0.43    introduced(avatar_definition,[new_symbols(naming,[spl2_28])])).
% 0.21/0.43  fof(f175,plain,(
% 0.21/0.43    ( ! [X2,X0] : (r1_tarski(k3_xboole_0(X2,X0),X0)) ) | ~spl2_24),
% 0.21/0.43    inference(avatar_component_clause,[],[f174])).
% 0.21/0.43  fof(f174,plain,(
% 0.21/0.43    spl2_24 <=> ! [X0,X2] : r1_tarski(k3_xboole_0(X2,X0),X0)),
% 0.21/0.43    introduced(avatar_definition,[new_symbols(naming,[spl2_24])])).
% 0.21/0.43  fof(f52,plain,(
% 0.21/0.43    v1_relat_1(sK1) | ~spl2_2),
% 0.21/0.43    inference(avatar_component_clause,[],[f50])).
% 0.21/0.43  fof(f50,plain,(
% 0.21/0.43    spl2_2 <=> v1_relat_1(sK1)),
% 0.21/0.43    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 0.21/0.43  fof(f177,plain,(
% 0.21/0.43    ~v1_relat_1(k3_xboole_0(sK0,sK1)) | (~spl2_2 | ~spl2_19 | spl2_22 | ~spl2_24)),
% 0.21/0.43    inference(unit_resulting_resolution,[],[f52,f155,f175,f136])).
% 0.21/0.43  fof(f136,plain,(
% 0.21/0.43    ( ! [X0,X1] : (r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) | ~r1_tarski(X0,X1) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) ) | ~spl2_19),
% 0.21/0.43    inference(avatar_component_clause,[],[f135])).
% 0.21/0.43  fof(f135,plain,(
% 0.21/0.43    spl2_19 <=> ! [X1,X0] : (r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) | ~r1_tarski(X0,X1) | ~v1_relat_1(X1) | ~v1_relat_1(X0))),
% 0.21/0.43    introduced(avatar_definition,[new_symbols(naming,[spl2_19])])).
% 0.21/0.43  fof(f155,plain,(
% 0.21/0.43    ~r1_tarski(k2_relat_1(k3_xboole_0(sK0,sK1)),k2_relat_1(sK1)) | spl2_22),
% 0.21/0.43    inference(avatar_component_clause,[],[f153])).
% 0.21/0.43  fof(f153,plain,(
% 0.21/0.43    spl2_22 <=> r1_tarski(k2_relat_1(k3_xboole_0(sK0,sK1)),k2_relat_1(sK1))),
% 0.21/0.43    introduced(avatar_definition,[new_symbols(naming,[spl2_22])])).
% 0.21/0.43  fof(f215,plain,(
% 0.21/0.43    spl2_28 | ~spl2_8 | ~spl2_9),
% 0.21/0.43    inference(avatar_split_clause,[],[f108,f81,f77,f213])).
% 0.21/0.43  fof(f77,plain,(
% 0.21/0.43    spl2_8 <=> ! [X1,X0] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1))),
% 0.21/0.43    introduced(avatar_definition,[new_symbols(naming,[spl2_8])])).
% 0.21/0.43  fof(f81,plain,(
% 0.21/0.43    spl2_9 <=> ! [X1,X0] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0))),
% 0.21/0.43    introduced(avatar_definition,[new_symbols(naming,[spl2_9])])).
% 0.21/0.43  fof(f108,plain,(
% 0.21/0.43    ( ! [X0,X1] : (v1_relat_1(X0) | ~v1_relat_1(X1) | ~r1_tarski(X0,X1)) ) | (~spl2_8 | ~spl2_9)),
% 0.21/0.43    inference(resolution,[],[f82,f78])).
% 0.21/0.43  fof(f78,plain,(
% 0.21/0.43    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) ) | ~spl2_8),
% 0.21/0.43    inference(avatar_component_clause,[],[f77])).
% 0.21/0.43  fof(f82,plain,(
% 0.21/0.43    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | v1_relat_1(X1) | ~v1_relat_1(X0)) ) | ~spl2_9),
% 0.21/0.43    inference(avatar_component_clause,[],[f81])).
% 0.21/0.43  fof(f202,plain,(
% 0.21/0.43    ~spl2_1 | ~spl2_9 | spl2_25 | ~spl2_26),
% 0.21/0.43    inference(avatar_contradiction_clause,[],[f201])).
% 0.21/0.43  fof(f201,plain,(
% 0.21/0.43    $false | (~spl2_1 | ~spl2_9 | spl2_25 | ~spl2_26)),
% 0.21/0.43    inference(subsumption_resolution,[],[f189,f195])).
% 0.21/0.43  fof(f195,plain,(
% 0.21/0.43    ( ! [X0] : (v1_relat_1(k3_xboole_0(sK0,X0))) ) | (~spl2_1 | ~spl2_9 | ~spl2_26)),
% 0.21/0.43    inference(unit_resulting_resolution,[],[f47,f193,f82])).
% 0.21/0.43  fof(f193,plain,(
% 0.21/0.43    ( ! [X0,X1] : (m1_subset_1(k3_xboole_0(X0,X1),k1_zfmisc_1(X0))) ) | ~spl2_26),
% 0.21/0.43    inference(avatar_component_clause,[],[f192])).
% 0.21/0.43  fof(f192,plain,(
% 0.21/0.43    spl2_26 <=> ! [X1,X0] : m1_subset_1(k3_xboole_0(X0,X1),k1_zfmisc_1(X0))),
% 0.21/0.43    introduced(avatar_definition,[new_symbols(naming,[spl2_26])])).
% 0.21/0.43  fof(f47,plain,(
% 0.21/0.43    v1_relat_1(sK0) | ~spl2_1),
% 0.21/0.43    inference(avatar_component_clause,[],[f45])).
% 0.21/0.43  fof(f45,plain,(
% 0.21/0.43    spl2_1 <=> v1_relat_1(sK0)),
% 0.21/0.43    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 0.21/0.43  fof(f189,plain,(
% 0.21/0.43    ~v1_relat_1(k3_xboole_0(sK0,sK1)) | spl2_25),
% 0.21/0.43    inference(avatar_component_clause,[],[f187])).
% 0.21/0.43  fof(f187,plain,(
% 0.21/0.43    spl2_25 <=> v1_relat_1(k3_xboole_0(sK0,sK1))),
% 0.21/0.43    introduced(avatar_definition,[new_symbols(naming,[spl2_25])])).
% 0.21/0.43  fof(f194,plain,(
% 0.21/0.43    spl2_26 | ~spl2_6 | ~spl2_8),
% 0.21/0.43    inference(avatar_split_clause,[],[f102,f77,f68,f192])).
% 0.21/0.43  fof(f68,plain,(
% 0.21/0.43    spl2_6 <=> ! [X1,X0] : r1_tarski(k3_xboole_0(X0,X1),X0)),
% 0.21/0.43    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).
% 0.21/0.43  fof(f102,plain,(
% 0.21/0.43    ( ! [X0,X1] : (m1_subset_1(k3_xboole_0(X0,X1),k1_zfmisc_1(X0))) ) | (~spl2_6 | ~spl2_8)),
% 0.21/0.43    inference(unit_resulting_resolution,[],[f69,f78])).
% 0.21/0.43  fof(f69,plain,(
% 0.21/0.43    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) ) | ~spl2_6),
% 0.21/0.43    inference(avatar_component_clause,[],[f68])).
% 0.21/0.43  fof(f190,plain,(
% 0.21/0.43    ~spl2_25 | ~spl2_1 | ~spl2_6 | ~spl2_19 | spl2_21),
% 0.21/0.43    inference(avatar_split_clause,[],[f161,f149,f135,f68,f45,f187])).
% 0.21/0.43  fof(f149,plain,(
% 0.21/0.43    spl2_21 <=> r1_tarski(k2_relat_1(k3_xboole_0(sK0,sK1)),k2_relat_1(sK0))),
% 0.21/0.43    introduced(avatar_definition,[new_symbols(naming,[spl2_21])])).
% 0.21/0.43  fof(f161,plain,(
% 0.21/0.43    ~v1_relat_1(k3_xboole_0(sK0,sK1)) | (~spl2_1 | ~spl2_6 | ~spl2_19 | spl2_21)),
% 0.21/0.43    inference(unit_resulting_resolution,[],[f47,f69,f151,f136])).
% 0.21/0.43  fof(f151,plain,(
% 0.21/0.43    ~r1_tarski(k2_relat_1(k3_xboole_0(sK0,sK1)),k2_relat_1(sK0)) | spl2_21),
% 0.21/0.43    inference(avatar_component_clause,[],[f149])).
% 0.21/0.43  fof(f176,plain,(
% 0.21/0.43    spl2_24 | ~spl2_14 | ~spl2_16),
% 0.21/0.43    inference(avatar_split_clause,[],[f125,f121,f105,f174])).
% 0.21/0.43  fof(f105,plain,(
% 0.21/0.43    spl2_14 <=> ! [X1,X0] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0),
% 0.21/0.43    introduced(avatar_definition,[new_symbols(naming,[spl2_14])])).
% 0.21/0.43  fof(f121,plain,(
% 0.21/0.43    spl2_16 <=> ! [X1,X0,X2] : r1_tarski(k3_xboole_0(X0,k2_xboole_0(X1,X2)),k2_xboole_0(X1,X2))),
% 0.21/0.43    introduced(avatar_definition,[new_symbols(naming,[spl2_16])])).
% 0.21/0.43  fof(f125,plain,(
% 0.21/0.43    ( ! [X2,X0] : (r1_tarski(k3_xboole_0(X2,X0),X0)) ) | (~spl2_14 | ~spl2_16)),
% 0.21/0.43    inference(superposition,[],[f122,f106])).
% 0.21/0.43  fof(f106,plain,(
% 0.21/0.43    ( ! [X0,X1] : (k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0) ) | ~spl2_14),
% 0.21/0.43    inference(avatar_component_clause,[],[f105])).
% 0.21/0.43  fof(f122,plain,(
% 0.21/0.43    ( ! [X2,X0,X1] : (r1_tarski(k3_xboole_0(X0,k2_xboole_0(X1,X2)),k2_xboole_0(X1,X2))) ) | ~spl2_16),
% 0.21/0.43    inference(avatar_component_clause,[],[f121])).
% 0.21/0.43  fof(f156,plain,(
% 0.21/0.43    ~spl2_21 | ~spl2_22 | spl2_3 | ~spl2_17),
% 0.21/0.43    inference(avatar_split_clause,[],[f142,f127,f55,f153,f149])).
% 0.21/0.43  fof(f55,plain,(
% 0.21/0.43    spl2_3 <=> r1_tarski(k2_relat_1(k3_xboole_0(sK0,sK1)),k3_xboole_0(k2_relat_1(sK0),k2_relat_1(sK1)))),
% 0.21/0.43    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).
% 0.21/0.43  fof(f127,plain,(
% 0.21/0.43    spl2_17 <=> ! [X1,X0,X2] : (r1_tarski(X0,k3_xboole_0(X1,X2)) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1))),
% 0.21/0.43    introduced(avatar_definition,[new_symbols(naming,[spl2_17])])).
% 0.21/0.43  fof(f142,plain,(
% 0.21/0.43    ~r1_tarski(k2_relat_1(k3_xboole_0(sK0,sK1)),k2_relat_1(sK1)) | ~r1_tarski(k2_relat_1(k3_xboole_0(sK0,sK1)),k2_relat_1(sK0)) | (spl2_3 | ~spl2_17)),
% 0.21/0.43    inference(resolution,[],[f128,f57])).
% 0.21/0.43  fof(f57,plain,(
% 0.21/0.43    ~r1_tarski(k2_relat_1(k3_xboole_0(sK0,sK1)),k3_xboole_0(k2_relat_1(sK0),k2_relat_1(sK1))) | spl2_3),
% 0.21/0.43    inference(avatar_component_clause,[],[f55])).
% 0.21/0.43  fof(f128,plain,(
% 0.21/0.43    ( ! [X2,X0,X1] : (r1_tarski(X0,k3_xboole_0(X1,X2)) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1)) ) | ~spl2_17),
% 0.21/0.43    inference(avatar_component_clause,[],[f127])).
% 0.21/0.43  fof(f137,plain,(
% 0.21/0.43    spl2_19),
% 0.21/0.43    inference(avatar_split_clause,[],[f32,f135])).
% 0.21/0.43  fof(f32,plain,(
% 0.21/0.43    ( ! [X0,X1] : (r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) | ~r1_tarski(X0,X1) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 0.21/0.43    inference(cnf_transformation,[],[f18])).
% 0.21/0.43  fof(f18,plain,(
% 0.21/0.43    ! [X0] : (! [X1] : ((r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) & r1_tarski(k1_relat_1(X0),k1_relat_1(X1))) | ~r1_tarski(X0,X1) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.21/0.43    inference(flattening,[],[f17])).
% 0.21/0.43  fof(f17,plain,(
% 0.21/0.43    ! [X0] : (! [X1] : (((r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) & r1_tarski(k1_relat_1(X0),k1_relat_1(X1))) | ~r1_tarski(X0,X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.21/0.43    inference(ennf_transformation,[],[f13])).
% 0.21/0.43  fof(f13,axiom,(
% 0.21/0.43    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => (r1_tarski(X0,X1) => (r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) & r1_tarski(k1_relat_1(X0),k1_relat_1(X1))))))),
% 0.21/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_relat_1)).
% 0.21/0.43  fof(f129,plain,(
% 0.21/0.43    spl2_17),
% 0.21/0.43    inference(avatar_split_clause,[],[f43,f127])).
% 0.21/0.43  fof(f43,plain,(
% 0.21/0.43    ( ! [X2,X0,X1] : (r1_tarski(X0,k3_xboole_0(X1,X2)) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1)) )),
% 0.21/0.43    inference(cnf_transformation,[],[f21])).
% 0.21/0.43  fof(f21,plain,(
% 0.21/0.43    ! [X0,X1,X2] : (r1_tarski(X0,k3_xboole_0(X1,X2)) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1))),
% 0.21/0.43    inference(flattening,[],[f20])).
% 0.21/0.43  fof(f20,plain,(
% 0.21/0.43    ! [X0,X1,X2] : (r1_tarski(X0,k3_xboole_0(X1,X2)) | (~r1_tarski(X0,X2) | ~r1_tarski(X0,X1)))),
% 0.21/0.43    inference(ennf_transformation,[],[f2])).
% 0.21/0.43  fof(f2,axiom,(
% 0.21/0.43    ! [X0,X1,X2] : ((r1_tarski(X0,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,k3_xboole_0(X1,X2)))),
% 0.21/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t19_xboole_1)).
% 0.21/0.43  fof(f123,plain,(
% 0.21/0.43    spl2_16 | ~spl2_15),
% 0.21/0.43    inference(avatar_split_clause,[],[f117,f114,f121])).
% 0.21/0.43  fof(f114,plain,(
% 0.21/0.43    spl2_15 <=> ! [X1,X0,X2] : r1_tarski(k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)),k2_xboole_0(X1,X2))),
% 0.21/0.43    introduced(avatar_definition,[new_symbols(naming,[spl2_15])])).
% 0.21/0.43  fof(f117,plain,(
% 0.21/0.43    ( ! [X2,X0,X1] : (r1_tarski(k3_xboole_0(X0,k2_xboole_0(X1,X2)),k2_xboole_0(X1,X2))) ) | ~spl2_15),
% 0.21/0.43    inference(forward_demodulation,[],[f115,f42])).
% 0.21/0.43  fof(f42,plain,(
% 0.21/0.43    ( ! [X2,X0,X1] : (k3_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2))) )),
% 0.21/0.43    inference(cnf_transformation,[],[f3])).
% 0.21/0.43  fof(f3,axiom,(
% 0.21/0.43    ! [X0,X1,X2] : k3_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2))),
% 0.21/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t23_xboole_1)).
% 0.21/0.43  fof(f115,plain,(
% 0.21/0.43    ( ! [X2,X0,X1] : (r1_tarski(k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)),k2_xboole_0(X1,X2))) ) | ~spl2_15),
% 0.21/0.43    inference(avatar_component_clause,[],[f114])).
% 0.21/0.43  fof(f116,plain,(
% 0.21/0.43    spl2_15),
% 0.21/0.43    inference(avatar_split_clause,[],[f41,f114])).
% 0.21/0.43  fof(f41,plain,(
% 0.21/0.43    ( ! [X2,X0,X1] : (r1_tarski(k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)),k2_xboole_0(X1,X2))) )),
% 0.21/0.43    inference(cnf_transformation,[],[f5])).
% 0.21/0.43  fof(f5,axiom,(
% 0.21/0.43    ! [X0,X1,X2] : r1_tarski(k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)),k2_xboole_0(X1,X2))),
% 0.21/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_xboole_1)).
% 0.21/0.43  fof(f107,plain,(
% 0.21/0.43    spl2_14),
% 0.21/0.43    inference(avatar_split_clause,[],[f38,f105])).
% 0.21/0.43  fof(f38,plain,(
% 0.21/0.43    ( ! [X0,X1] : (k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0) )),
% 0.21/0.43    inference(cnf_transformation,[],[f7])).
% 0.21/0.43  fof(f7,axiom,(
% 0.21/0.43    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0),
% 0.21/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t51_xboole_1)).
% 0.21/0.43  fof(f83,plain,(
% 0.21/0.43    spl2_9),
% 0.21/0.43    inference(avatar_split_clause,[],[f33,f81])).
% 0.21/0.43  fof(f33,plain,(
% 0.21/0.43    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 0.21/0.43    inference(cnf_transformation,[],[f19])).
% 0.21/0.43  fof(f19,plain,(
% 0.21/0.43    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 0.21/0.43    inference(ennf_transformation,[],[f12])).
% 0.21/0.43  fof(f12,axiom,(
% 0.21/0.43    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 0.21/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).
% 0.21/0.43  fof(f79,plain,(
% 0.21/0.43    spl2_8),
% 0.21/0.43    inference(avatar_split_clause,[],[f40,f77])).
% 0.21/0.43  fof(f40,plain,(
% 0.21/0.43    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 0.21/0.43    inference(cnf_transformation,[],[f25])).
% 0.21/0.43  fof(f25,plain,(
% 0.21/0.43    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 0.21/0.43    inference(nnf_transformation,[],[f11])).
% 0.21/0.43  fof(f11,axiom,(
% 0.21/0.43    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.21/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).
% 0.21/0.43  fof(f70,plain,(
% 0.21/0.43    spl2_6),
% 0.21/0.43    inference(avatar_split_clause,[],[f34,f68])).
% 0.21/0.43  fof(f34,plain,(
% 0.21/0.43    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) )),
% 0.21/0.43    inference(cnf_transformation,[],[f1])).
% 0.21/0.43  fof(f1,axiom,(
% 0.21/0.43    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0)),
% 0.21/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).
% 0.21/0.43  fof(f58,plain,(
% 0.21/0.43    ~spl2_3),
% 0.21/0.43    inference(avatar_split_clause,[],[f28,f55])).
% 0.21/0.43  fof(f28,plain,(
% 0.21/0.43    ~r1_tarski(k2_relat_1(k3_xboole_0(sK0,sK1)),k3_xboole_0(k2_relat_1(sK0),k2_relat_1(sK1)))),
% 0.21/0.43    inference(cnf_transformation,[],[f24])).
% 0.21/0.43  fof(f24,plain,(
% 0.21/0.43    (~r1_tarski(k2_relat_1(k3_xboole_0(sK0,sK1)),k3_xboole_0(k2_relat_1(sK0),k2_relat_1(sK1))) & v1_relat_1(sK1)) & v1_relat_1(sK0)),
% 0.21/0.43    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f16,f23,f22])).
% 0.21/0.43  fof(f22,plain,(
% 0.21/0.43    ? [X0] : (? [X1] : (~r1_tarski(k2_relat_1(k3_xboole_0(X0,X1)),k3_xboole_0(k2_relat_1(X0),k2_relat_1(X1))) & v1_relat_1(X1)) & v1_relat_1(X0)) => (? [X1] : (~r1_tarski(k2_relat_1(k3_xboole_0(sK0,X1)),k3_xboole_0(k2_relat_1(sK0),k2_relat_1(X1))) & v1_relat_1(X1)) & v1_relat_1(sK0))),
% 0.21/0.43    introduced(choice_axiom,[])).
% 0.21/0.43  fof(f23,plain,(
% 0.21/0.43    ? [X1] : (~r1_tarski(k2_relat_1(k3_xboole_0(sK0,X1)),k3_xboole_0(k2_relat_1(sK0),k2_relat_1(X1))) & v1_relat_1(X1)) => (~r1_tarski(k2_relat_1(k3_xboole_0(sK0,sK1)),k3_xboole_0(k2_relat_1(sK0),k2_relat_1(sK1))) & v1_relat_1(sK1))),
% 0.21/0.43    introduced(choice_axiom,[])).
% 0.21/0.43  fof(f16,plain,(
% 0.21/0.43    ? [X0] : (? [X1] : (~r1_tarski(k2_relat_1(k3_xboole_0(X0,X1)),k3_xboole_0(k2_relat_1(X0),k2_relat_1(X1))) & v1_relat_1(X1)) & v1_relat_1(X0))),
% 0.21/0.43    inference(ennf_transformation,[],[f15])).
% 0.21/0.43  fof(f15,negated_conjecture,(
% 0.21/0.43    ~! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => r1_tarski(k2_relat_1(k3_xboole_0(X0,X1)),k3_xboole_0(k2_relat_1(X0),k2_relat_1(X1)))))),
% 0.21/0.43    inference(negated_conjecture,[],[f14])).
% 0.21/0.43  fof(f14,conjecture,(
% 0.21/0.43    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => r1_tarski(k2_relat_1(k3_xboole_0(X0,X1)),k3_xboole_0(k2_relat_1(X0),k2_relat_1(X1)))))),
% 0.21/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t27_relat_1)).
% 0.21/0.43  fof(f53,plain,(
% 0.21/0.43    spl2_2),
% 0.21/0.43    inference(avatar_split_clause,[],[f27,f50])).
% 0.21/0.43  fof(f27,plain,(
% 0.21/0.43    v1_relat_1(sK1)),
% 0.21/0.43    inference(cnf_transformation,[],[f24])).
% 0.21/0.43  fof(f48,plain,(
% 0.21/0.43    spl2_1),
% 0.21/0.43    inference(avatar_split_clause,[],[f26,f45])).
% 0.21/0.43  fof(f26,plain,(
% 0.21/0.43    v1_relat_1(sK0)),
% 0.21/0.43    inference(cnf_transformation,[],[f24])).
% 0.21/0.43  % SZS output end Proof for theBenchmark
% 0.21/0.43  % (4140)------------------------------
% 0.21/0.43  % (4140)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.43  % (4140)Termination reason: Refutation
% 0.21/0.43  
% 0.21/0.43  % (4140)Memory used [KB]: 6268
% 0.21/0.43  % (4140)Time elapsed: 0.009 s
% 0.21/0.43  % (4140)------------------------------
% 0.21/0.43  % (4140)------------------------------
% 0.21/0.44  % (4134)Success in time 0.077 s
%------------------------------------------------------------------------------
