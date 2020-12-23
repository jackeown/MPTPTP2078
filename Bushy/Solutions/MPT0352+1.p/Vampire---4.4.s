%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : subset_1__t31_subset_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:38:22 EDT 2019

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  107 ( 205 expanded)
%              Number of leaves         :   27 (  81 expanded)
%              Depth                    :    8
%              Number of atoms          :  267 ( 564 expanded)
%              Number of equality atoms :   34 (  68 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f224,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f60,f67,f74,f82,f103,f104,f129,f139,f146,f162,f169,f177,f188,f198,f203,f217,f223])).

fof(f223,plain,
    ( ~ spl4_8
    | spl4_11
    | ~ spl4_18
    | ~ spl4_20 ),
    inference(avatar_contradiction_clause,[],[f222])).

fof(f222,plain,
    ( $false
    | ~ spl4_8
    | ~ spl4_11
    | ~ spl4_18
    | ~ spl4_20 ),
    inference(subsumption_resolution,[],[f221,f99])).

fof(f99,plain,
    ( ~ r1_tarski(k3_subset_1(sK0,sK2),k3_subset_1(sK0,sK1))
    | ~ spl4_11 ),
    inference(avatar_component_clause,[],[f98])).

fof(f98,plain,
    ( spl4_11
  <=> ~ r1_tarski(k3_subset_1(sK0,sK2),k3_subset_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).

fof(f221,plain,
    ( r1_tarski(k3_subset_1(sK0,sK2),k3_subset_1(sK0,sK1))
    | ~ spl4_8
    | ~ spl4_18
    | ~ spl4_20 ),
    inference(forward_demodulation,[],[f211,f168])).

fof(f168,plain,
    ( k3_subset_1(sK0,sK2) = k4_xboole_0(sK0,sK2)
    | ~ spl4_20 ),
    inference(avatar_component_clause,[],[f167])).

fof(f167,plain,
    ( spl4_20
  <=> k3_subset_1(sK0,sK2) = k4_xboole_0(sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_20])])).

fof(f211,plain,
    ( r1_tarski(k4_xboole_0(sK0,sK2),k3_subset_1(sK0,sK1))
    | ~ spl4_8
    | ~ spl4_18 ),
    inference(superposition,[],[f204,f161])).

fof(f161,plain,
    ( k3_subset_1(sK0,sK1) = k4_xboole_0(sK0,sK1)
    | ~ spl4_18 ),
    inference(avatar_component_clause,[],[f160])).

fof(f160,plain,
    ( spl4_18
  <=> k3_subset_1(sK0,sK1) = k4_xboole_0(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_18])])).

fof(f204,plain,
    ( ! [X0] : r1_tarski(k4_xboole_0(X0,sK2),k4_xboole_0(X0,sK1))
    | ~ spl4_8 ),
    inference(resolution,[],[f96,f52])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | r1_tarski(k4_xboole_0(X2,X1),k4_xboole_0(X2,X0)) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k4_xboole_0(X2,X1),k4_xboole_0(X2,X0))
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => r1_tarski(k4_xboole_0(X2,X1),k4_xboole_0(X2,X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/subset_1__t31_subset_1.p',t34_xboole_1)).

fof(f96,plain,
    ( r1_tarski(sK1,sK2)
    | ~ spl4_8 ),
    inference(avatar_component_clause,[],[f95])).

fof(f95,plain,
    ( spl4_8
  <=> r1_tarski(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).

fof(f217,plain,
    ( ~ spl4_8
    | spl4_11
    | ~ spl4_18
    | ~ spl4_20 ),
    inference(avatar_contradiction_clause,[],[f216])).

fof(f216,plain,
    ( $false
    | ~ spl4_8
    | ~ spl4_11
    | ~ spl4_18
    | ~ spl4_20 ),
    inference(subsumption_resolution,[],[f215,f99])).

fof(f215,plain,
    ( r1_tarski(k3_subset_1(sK0,sK2),k3_subset_1(sK0,sK1))
    | ~ spl4_8
    | ~ spl4_18
    | ~ spl4_20 ),
    inference(forward_demodulation,[],[f208,f161])).

fof(f208,plain,
    ( r1_tarski(k3_subset_1(sK0,sK2),k4_xboole_0(sK0,sK1))
    | ~ spl4_8
    | ~ spl4_20 ),
    inference(superposition,[],[f204,f168])).

fof(f203,plain,
    ( spl4_9
    | ~ spl4_10
    | ~ spl4_16
    | ~ spl4_24
    | ~ spl4_26 ),
    inference(avatar_contradiction_clause,[],[f202])).

fof(f202,plain,
    ( $false
    | ~ spl4_9
    | ~ spl4_10
    | ~ spl4_16
    | ~ spl4_24
    | ~ spl4_26 ),
    inference(subsumption_resolution,[],[f201,f93])).

fof(f93,plain,
    ( ~ r1_tarski(sK1,sK2)
    | ~ spl4_9 ),
    inference(avatar_component_clause,[],[f92])).

fof(f92,plain,
    ( spl4_9
  <=> ~ r1_tarski(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).

fof(f201,plain,
    ( r1_tarski(sK1,sK2)
    | ~ spl4_10
    | ~ spl4_16
    | ~ spl4_24
    | ~ spl4_26 ),
    inference(forward_demodulation,[],[f199,f191])).

fof(f191,plain,
    ( k4_xboole_0(sK0,k3_subset_1(sK0,sK2)) = sK2
    | ~ spl4_16
    | ~ spl4_24 ),
    inference(forward_demodulation,[],[f189,f145])).

fof(f145,plain,
    ( k3_subset_1(sK0,k3_subset_1(sK0,sK2)) = sK2
    | ~ spl4_16 ),
    inference(avatar_component_clause,[],[f144])).

fof(f144,plain,
    ( spl4_16
  <=> k3_subset_1(sK0,k3_subset_1(sK0,sK2)) = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_16])])).

fof(f189,plain,
    ( k3_subset_1(sK0,k3_subset_1(sK0,sK2)) = k4_xboole_0(sK0,k3_subset_1(sK0,sK2))
    | ~ spl4_24 ),
    inference(resolution,[],[f187,f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k3_subset_1(X0,X1) = k4_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,X1) = k4_xboole_0(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k3_subset_1(X0,X1) = k4_xboole_0(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/subset_1__t31_subset_1.p',d5_subset_1)).

fof(f187,plain,
    ( m1_subset_1(k3_subset_1(sK0,sK2),k1_zfmisc_1(sK0))
    | ~ spl4_24 ),
    inference(avatar_component_clause,[],[f186])).

fof(f186,plain,
    ( spl4_24
  <=> m1_subset_1(k3_subset_1(sK0,sK2),k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_24])])).

fof(f199,plain,
    ( r1_tarski(sK1,k4_xboole_0(sK0,k3_subset_1(sK0,sK2)))
    | ~ spl4_10
    | ~ spl4_26 ),
    inference(superposition,[],[f105,f197])).

fof(f197,plain,
    ( k4_xboole_0(sK0,k3_subset_1(sK0,sK1)) = sK1
    | ~ spl4_26 ),
    inference(avatar_component_clause,[],[f196])).

fof(f196,plain,
    ( spl4_26
  <=> k4_xboole_0(sK0,k3_subset_1(sK0,sK1)) = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_26])])).

fof(f105,plain,
    ( ! [X0] : r1_tarski(k4_xboole_0(X0,k3_subset_1(sK0,sK1)),k4_xboole_0(X0,k3_subset_1(sK0,sK2)))
    | ~ spl4_10 ),
    inference(resolution,[],[f52,f102])).

fof(f102,plain,
    ( r1_tarski(k3_subset_1(sK0,sK2),k3_subset_1(sK0,sK1))
    | ~ spl4_10 ),
    inference(avatar_component_clause,[],[f101])).

fof(f101,plain,
    ( spl4_10
  <=> r1_tarski(k3_subset_1(sK0,sK2),k3_subset_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).

fof(f198,plain,
    ( spl4_26
    | ~ spl4_14
    | ~ spl4_22 ),
    inference(avatar_split_clause,[],[f180,f175,f137,f196])).

fof(f137,plain,
    ( spl4_14
  <=> k3_subset_1(sK0,k3_subset_1(sK0,sK1)) = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_14])])).

fof(f175,plain,
    ( spl4_22
  <=> m1_subset_1(k3_subset_1(sK0,sK1),k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_22])])).

fof(f180,plain,
    ( k4_xboole_0(sK0,k3_subset_1(sK0,sK1)) = sK1
    | ~ spl4_14
    | ~ spl4_22 ),
    inference(forward_demodulation,[],[f178,f138])).

fof(f138,plain,
    ( k3_subset_1(sK0,k3_subset_1(sK0,sK1)) = sK1
    | ~ spl4_14 ),
    inference(avatar_component_clause,[],[f137])).

fof(f178,plain,
    ( k3_subset_1(sK0,k3_subset_1(sK0,sK1)) = k4_xboole_0(sK0,k3_subset_1(sK0,sK1))
    | ~ spl4_22 ),
    inference(resolution,[],[f176,f50])).

fof(f176,plain,
    ( m1_subset_1(k3_subset_1(sK0,sK1),k1_zfmisc_1(sK0))
    | ~ spl4_22 ),
    inference(avatar_component_clause,[],[f175])).

fof(f188,plain,
    ( spl4_24
    | ~ spl4_20 ),
    inference(avatar_split_clause,[],[f181,f167,f186])).

fof(f181,plain,
    ( m1_subset_1(k3_subset_1(sK0,sK2),k1_zfmisc_1(sK0))
    | ~ spl4_20 ),
    inference(superposition,[],[f53,f168])).

fof(f53,plain,(
    ! [X0,X1] : m1_subset_1(k4_xboole_0(X0,X1),k1_zfmisc_1(X0)) ),
    inference(forward_demodulation,[],[f46,f47])).

fof(f47,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/subset_1__t31_subset_1.p',redefinition_k6_subset_1)).

fof(f46,plain,(
    ! [X0,X1] : m1_subset_1(k6_subset_1(X0,X1),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : m1_subset_1(k6_subset_1(X0,X1),k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/subset_1__t31_subset_1.p',dt_k6_subset_1)).

fof(f177,plain,
    ( spl4_22
    | ~ spl4_18 ),
    inference(avatar_split_clause,[],[f170,f160,f175])).

fof(f170,plain,
    ( m1_subset_1(k3_subset_1(sK0,sK1),k1_zfmisc_1(sK0))
    | ~ spl4_18 ),
    inference(superposition,[],[f53,f161])).

fof(f169,plain,
    ( spl4_20
    | ~ spl4_4 ),
    inference(avatar_split_clause,[],[f151,f72,f167])).

fof(f72,plain,
    ( spl4_4
  <=> m1_subset_1(sK2,k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f151,plain,
    ( k3_subset_1(sK0,sK2) = k4_xboole_0(sK0,sK2)
    | ~ spl4_4 ),
    inference(resolution,[],[f50,f73])).

fof(f73,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(sK0))
    | ~ spl4_4 ),
    inference(avatar_component_clause,[],[f72])).

fof(f162,plain,
    ( spl4_18
    | ~ spl4_2 ),
    inference(avatar_split_clause,[],[f150,f65,f160])).

fof(f65,plain,
    ( spl4_2
  <=> m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f150,plain,
    ( k3_subset_1(sK0,sK1) = k4_xboole_0(sK0,sK1)
    | ~ spl4_2 ),
    inference(resolution,[],[f50,f66])).

fof(f66,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(sK0))
    | ~ spl4_2 ),
    inference(avatar_component_clause,[],[f65])).

fof(f146,plain,
    ( spl4_16
    | ~ spl4_4 ),
    inference(avatar_split_clause,[],[f118,f72,f144])).

fof(f118,plain,
    ( k3_subset_1(sK0,k3_subset_1(sK0,sK2)) = sK2
    | ~ spl4_4 ),
    inference(resolution,[],[f49,f73])).

fof(f49,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/subset_1__t31_subset_1.p',involutiveness_k3_subset_1)).

fof(f139,plain,
    ( spl4_14
    | ~ spl4_2 ),
    inference(avatar_split_clause,[],[f117,f65,f137])).

fof(f117,plain,
    ( k3_subset_1(sK0,k3_subset_1(sK0,sK1)) = sK1
    | ~ spl4_2 ),
    inference(resolution,[],[f49,f66])).

fof(f129,plain,
    ( spl4_12
    | ~ spl4_6
    | ~ spl4_10 ),
    inference(avatar_split_clause,[],[f112,f101,f80,f127])).

fof(f127,plain,
    ( spl4_12
  <=> r1_tarski(o_0_0_xboole_0,o_0_0_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).

fof(f80,plain,
    ( spl4_6
  <=> o_0_0_xboole_0 = k1_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).

fof(f112,plain,
    ( r1_tarski(o_0_0_xboole_0,o_0_0_xboole_0)
    | ~ spl4_6
    | ~ spl4_10 ),
    inference(forward_demodulation,[],[f111,f81])).

fof(f81,plain,
    ( o_0_0_xboole_0 = k1_xboole_0
    | ~ spl4_6 ),
    inference(avatar_component_clause,[],[f80])).

fof(f111,plain,
    ( r1_tarski(k1_xboole_0,k1_xboole_0)
    | ~ spl4_10 ),
    inference(forward_demodulation,[],[f107,f43])).

fof(f43,plain,(
    ! [X0] : k4_xboole_0(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0] : k4_xboole_0(k1_xboole_0,X0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/subset_1__t31_subset_1.p',t4_boole)).

fof(f107,plain,
    ( r1_tarski(k1_xboole_0,k4_xboole_0(k1_xboole_0,k3_subset_1(sK0,sK2)))
    | ~ spl4_10 ),
    inference(superposition,[],[f105,f43])).

fof(f104,plain,
    ( ~ spl4_9
    | ~ spl4_11 ),
    inference(avatar_split_clause,[],[f40,f98,f92])).

fof(f40,plain,
    ( ~ r1_tarski(k3_subset_1(sK0,sK2),k3_subset_1(sK0,sK1))
    | ~ r1_tarski(sK1,sK2) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,
    ( ( ~ r1_tarski(k3_subset_1(sK0,sK2),k3_subset_1(sK0,sK1))
      | ~ r1_tarski(sK1,sK2) )
    & ( r1_tarski(k3_subset_1(sK0,sK2),k3_subset_1(sK0,sK1))
      | r1_tarski(sK1,sK2) )
    & m1_subset_1(sK2,k1_zfmisc_1(sK0))
    & m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f31,f33,f32])).

fof(f32,plain,
    ( ? [X0,X1] :
        ( ? [X2] :
            ( ( ~ r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1))
              | ~ r1_tarski(X1,X2) )
            & ( r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1))
              | r1_tarski(X1,X2) )
            & m1_subset_1(X2,k1_zfmisc_1(X0)) )
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
   => ( ? [X2] :
          ( ( ~ r1_tarski(k3_subset_1(sK0,X2),k3_subset_1(sK0,sK1))
            | ~ r1_tarski(sK1,X2) )
          & ( r1_tarski(k3_subset_1(sK0,X2),k3_subset_1(sK0,sK1))
            | r1_tarski(sK1,X2) )
          & m1_subset_1(X2,k1_zfmisc_1(sK0)) )
      & m1_subset_1(sK1,k1_zfmisc_1(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ( ~ r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1))
            | ~ r1_tarski(X1,X2) )
          & ( r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1))
            | r1_tarski(X1,X2) )
          & m1_subset_1(X2,k1_zfmisc_1(X0)) )
     => ( ( ~ r1_tarski(k3_subset_1(X0,sK2),k3_subset_1(X0,X1))
          | ~ r1_tarski(X1,sK2) )
        & ( r1_tarski(k3_subset_1(X0,sK2),k3_subset_1(X0,X1))
          | r1_tarski(X1,sK2) )
        & m1_subset_1(sK2,k1_zfmisc_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ( ~ r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1))
            | ~ r1_tarski(X1,X2) )
          & ( r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1))
            | r1_tarski(X1,X2) )
          & m1_subset_1(X2,k1_zfmisc_1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ( ~ r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1))
            | ~ r1_tarski(X1,X2) )
          & ( r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1))
            | r1_tarski(X1,X2) )
          & m1_subset_1(X2,k1_zfmisc_1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(nnf_transformation,[],[f23])).

fof(f23,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ( r1_tarski(X1,X2)
          <~> r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)) )
          & m1_subset_1(X2,k1_zfmisc_1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(X0))
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(X0))
           => ( r1_tarski(X1,X2)
            <=> r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)) ) ) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X0))
         => ( r1_tarski(X1,X2)
          <=> r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/subset_1__t31_subset_1.p',t31_subset_1)).

fof(f103,plain,
    ( spl4_8
    | spl4_10 ),
    inference(avatar_split_clause,[],[f39,f101,f95])).

fof(f39,plain,
    ( r1_tarski(k3_subset_1(sK0,sK2),k3_subset_1(sK0,sK1))
    | r1_tarski(sK1,sK2) ),
    inference(cnf_transformation,[],[f34])).

fof(f82,plain,
    ( spl4_6
    | ~ spl4_0 ),
    inference(avatar_split_clause,[],[f75,f58,f80])).

fof(f58,plain,
    ( spl4_0
  <=> v1_xboole_0(o_0_0_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_0])])).

fof(f75,plain,
    ( o_0_0_xboole_0 = k1_xboole_0
    | ~ spl4_0 ),
    inference(resolution,[],[f44,f59])).

fof(f59,plain,
    ( v1_xboole_0(o_0_0_xboole_0)
    | ~ spl4_0 ),
    inference(avatar_component_clause,[],[f58])).

fof(f44,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/subset_1__t31_subset_1.p',t6_boole)).

fof(f74,plain,(
    spl4_4 ),
    inference(avatar_split_clause,[],[f38,f72])).

fof(f38,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f34])).

fof(f67,plain,(
    spl4_2 ),
    inference(avatar_split_clause,[],[f37,f65])).

fof(f37,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f34])).

fof(f60,plain,(
    spl4_0 ),
    inference(avatar_split_clause,[],[f41,f58])).

fof(f41,plain,(
    v1_xboole_0(o_0_0_xboole_0) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    v1_xboole_0(o_0_0_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/subset_1__t31_subset_1.p',dt_o_0_0_xboole_0)).
%------------------------------------------------------------------------------
