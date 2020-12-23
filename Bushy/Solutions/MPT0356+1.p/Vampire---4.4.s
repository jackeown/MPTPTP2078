%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : subset_1__t35_subset_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n028.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:38:22 EDT 2019

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  110 ( 216 expanded)
%              Number of leaves         :   31 (  91 expanded)
%              Depth                    :    9
%              Number of atoms          :  244 ( 508 expanded)
%              Number of equality atoms :   44 (  84 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f238,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f59,f66,f73,f80,f87,f94,f107,f114,f127,f134,f145,f155,f166,f174,f182,f212,f219,f234,f237])).

fof(f237,plain,
    ( ~ spl4_6
    | spl4_35 ),
    inference(avatar_contradiction_clause,[],[f236])).

fof(f236,plain,
    ( $false
    | ~ spl4_6
    | ~ spl4_35 ),
    inference(subsumption_resolution,[],[f235,f79])).

fof(f79,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(sK0))
    | ~ spl4_6 ),
    inference(avatar_component_clause,[],[f78])).

fof(f78,plain,
    ( spl4_6
  <=> m1_subset_1(sK2,k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).

fof(f235,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(sK0))
    | ~ spl4_35 ),
    inference(resolution,[],[f233,f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/subset_1__t35_subset_1.p',dt_k3_subset_1)).

fof(f233,plain,
    ( ~ m1_subset_1(k3_subset_1(sK0,sK2),k1_zfmisc_1(sK0))
    | ~ spl4_35 ),
    inference(avatar_component_clause,[],[f232])).

fof(f232,plain,
    ( spl4_35
  <=> ~ m1_subset_1(k3_subset_1(sK0,sK2),k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_35])])).

fof(f234,plain,
    ( ~ spl4_35
    | ~ spl4_4
    | ~ spl4_8
    | spl4_11
    | ~ spl4_14 ),
    inference(avatar_split_clause,[],[f227,f112,f92,f85,f71,f232])).

fof(f71,plain,
    ( spl4_4
  <=> m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f85,plain,
    ( spl4_8
  <=> r1_tarski(sK1,k3_subset_1(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).

fof(f92,plain,
    ( spl4_11
  <=> ~ r1_tarski(sK2,k3_subset_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).

fof(f112,plain,
    ( spl4_14
  <=> k3_subset_1(sK0,k3_subset_1(sK0,sK2)) = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_14])])).

fof(f227,plain,
    ( ~ m1_subset_1(k3_subset_1(sK0,sK2),k1_zfmisc_1(sK0))
    | ~ spl4_4
    | ~ spl4_8
    | ~ spl4_11
    | ~ spl4_14 ),
    inference(subsumption_resolution,[],[f226,f93])).

fof(f93,plain,
    ( ~ r1_tarski(sK2,k3_subset_1(sK0,sK1))
    | ~ spl4_11 ),
    inference(avatar_component_clause,[],[f92])).

fof(f226,plain,
    ( r1_tarski(sK2,k3_subset_1(sK0,sK1))
    | ~ m1_subset_1(k3_subset_1(sK0,sK2),k1_zfmisc_1(sK0))
    | ~ spl4_4
    | ~ spl4_8
    | ~ spl4_14 ),
    inference(forward_demodulation,[],[f225,f113])).

fof(f113,plain,
    ( k3_subset_1(sK0,k3_subset_1(sK0,sK2)) = sK2
    | ~ spl4_14 ),
    inference(avatar_component_clause,[],[f112])).

fof(f225,plain,
    ( ~ m1_subset_1(k3_subset_1(sK0,sK2),k1_zfmisc_1(sK0))
    | r1_tarski(k3_subset_1(sK0,k3_subset_1(sK0,sK2)),k3_subset_1(sK0,sK1))
    | ~ spl4_4
    | ~ spl4_8 ),
    inference(resolution,[],[f135,f72])).

fof(f72,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(sK0))
    | ~ spl4_4 ),
    inference(avatar_component_clause,[],[f71])).

fof(f135,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK1,k1_zfmisc_1(X0))
        | ~ m1_subset_1(k3_subset_1(sK0,sK2),k1_zfmisc_1(X0))
        | r1_tarski(k3_subset_1(X0,k3_subset_1(sK0,sK2)),k3_subset_1(X0,sK1)) )
    | ~ spl4_8 ),
    inference(resolution,[],[f49,f86])).

fof(f86,plain,
    ( r1_tarski(sK1,k3_subset_1(sK0,sK2))
    | ~ spl4_8 ),
    inference(avatar_component_clause,[],[f85])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X1,X2)
      | r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( ( r1_tarski(X1,X2)
              | ~ r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)) )
            & ( r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1))
              | ~ r1_tarski(X1,X2) ) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(nnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( r1_tarski(X1,X2)
          <=> r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X0))
         => ( r1_tarski(X1,X2)
          <=> r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/subset_1__t35_subset_1.p',t31_subset_1)).

fof(f219,plain,
    ( spl4_32
    | ~ spl4_6
    | ~ spl4_14 ),
    inference(avatar_split_clause,[],[f202,f112,f78,f217])).

fof(f217,plain,
    ( spl4_32
  <=> k4_xboole_0(sK0,k3_subset_1(sK0,sK2)) = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_32])])).

fof(f202,plain,
    ( k4_xboole_0(sK0,k3_subset_1(sK0,sK2)) = sK2
    | ~ spl4_6
    | ~ spl4_14 ),
    inference(forward_demodulation,[],[f197,f113])).

fof(f197,plain,
    ( k3_subset_1(sK0,k3_subset_1(sK0,sK2)) = k4_xboole_0(sK0,k3_subset_1(sK0,sK2))
    | ~ spl4_6 ),
    inference(resolution,[],[f119,f79])).

fof(f119,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k3_subset_1(X0,k3_subset_1(X0,X1)) = k4_xboole_0(X0,k3_subset_1(X0,X1)) ) ),
    inference(resolution,[],[f48,f46])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k3_subset_1(X0,X1) = k4_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,X1) = k4_xboole_0(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k3_subset_1(X0,X1) = k4_xboole_0(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/subset_1__t35_subset_1.p',d5_subset_1)).

fof(f212,plain,
    ( spl4_30
    | ~ spl4_4
    | ~ spl4_12 ),
    inference(avatar_split_clause,[],[f201,f105,f71,f210])).

fof(f210,plain,
    ( spl4_30
  <=> k4_xboole_0(sK0,k3_subset_1(sK0,sK1)) = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_30])])).

fof(f105,plain,
    ( spl4_12
  <=> k3_subset_1(sK0,k3_subset_1(sK0,sK1)) = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).

fof(f201,plain,
    ( k4_xboole_0(sK0,k3_subset_1(sK0,sK1)) = sK1
    | ~ spl4_4
    | ~ spl4_12 ),
    inference(forward_demodulation,[],[f196,f106])).

fof(f106,plain,
    ( k3_subset_1(sK0,k3_subset_1(sK0,sK1)) = sK1
    | ~ spl4_12 ),
    inference(avatar_component_clause,[],[f105])).

fof(f196,plain,
    ( k3_subset_1(sK0,k3_subset_1(sK0,sK1)) = k4_xboole_0(sK0,k3_subset_1(sK0,sK1))
    | ~ spl4_4 ),
    inference(resolution,[],[f119,f72])).

fof(f182,plain,
    ( spl4_28
    | ~ spl4_24
    | ~ spl4_26 ),
    inference(avatar_split_clause,[],[f175,f172,f164,f180])).

fof(f180,plain,
    ( spl4_28
  <=> k1_xboole_0 = sK3(k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_28])])).

fof(f164,plain,
    ( spl4_24
  <=> k3_subset_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_24])])).

fof(f172,plain,
    ( spl4_26
  <=> k3_subset_1(k1_xboole_0,k1_xboole_0) = sK3(k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_26])])).

fof(f175,plain,
    ( k1_xboole_0 = sK3(k1_zfmisc_1(k1_xboole_0))
    | ~ spl4_24
    | ~ spl4_26 ),
    inference(forward_demodulation,[],[f173,f165])).

fof(f165,plain,
    ( k3_subset_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0
    | ~ spl4_24 ),
    inference(avatar_component_clause,[],[f164])).

fof(f173,plain,
    ( k3_subset_1(k1_xboole_0,k1_xboole_0) = sK3(k1_zfmisc_1(k1_xboole_0))
    | ~ spl4_26 ),
    inference(avatar_component_clause,[],[f172])).

fof(f174,plain,
    ( spl4_26
    | ~ spl4_20 ),
    inference(avatar_split_clause,[],[f146,f143,f172])).

fof(f143,plain,
    ( spl4_20
  <=> k3_subset_1(k1_xboole_0,sK3(k1_zfmisc_1(k1_xboole_0))) = k1_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_20])])).

fof(f146,plain,
    ( k3_subset_1(k1_xboole_0,k1_xboole_0) = sK3(k1_zfmisc_1(k1_xboole_0))
    | ~ spl4_20 ),
    inference(superposition,[],[f100,f144])).

fof(f144,plain,
    ( k3_subset_1(k1_xboole_0,sK3(k1_zfmisc_1(k1_xboole_0))) = k1_xboole_0
    | ~ spl4_20 ),
    inference(avatar_component_clause,[],[f143])).

fof(f100,plain,(
    ! [X2] : k3_subset_1(X2,k3_subset_1(X2,sK3(k1_zfmisc_1(X2)))) = sK3(k1_zfmisc_1(X2)) ),
    inference(resolution,[],[f47,f45])).

fof(f45,plain,(
    ! [X0] : m1_subset_1(sK3(X0),X0) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0] : m1_subset_1(sK3(X0),X0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f12,f33])).

fof(f33,plain,(
    ! [X0] :
      ( ? [X1] : m1_subset_1(X1,X0)
     => m1_subset_1(sK3(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f12,axiom,(
    ! [X0] :
    ? [X1] : m1_subset_1(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/subset_1__t35_subset_1.p',existence_m1_subset_1)).

fof(f47,plain,(
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
    file('/export/starexec/sandbox2/benchmark/subset_1__t35_subset_1.p',involutiveness_k3_subset_1)).

fof(f166,plain,
    ( spl4_24
    | ~ spl4_22 ),
    inference(avatar_split_clause,[],[f158,f153,f164])).

fof(f153,plain,
    ( spl4_22
  <=> m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_22])])).

fof(f158,plain,
    ( k3_subset_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0
    | ~ spl4_22 ),
    inference(forward_demodulation,[],[f156,f42])).

fof(f42,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/subset_1__t35_subset_1.p',t3_boole)).

fof(f156,plain,
    ( k3_subset_1(k1_xboole_0,k1_xboole_0) = k4_xboole_0(k1_xboole_0,k1_xboole_0)
    | ~ spl4_22 ),
    inference(resolution,[],[f154,f48])).

fof(f154,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
    | ~ spl4_22 ),
    inference(avatar_component_clause,[],[f153])).

fof(f155,plain,
    ( spl4_22
    | ~ spl4_20 ),
    inference(avatar_split_clause,[],[f148,f143,f153])).

fof(f148,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
    | ~ spl4_20 ),
    inference(subsumption_resolution,[],[f147,f45])).

fof(f147,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
    | ~ m1_subset_1(sK3(k1_zfmisc_1(k1_xboole_0)),k1_zfmisc_1(k1_xboole_0))
    | ~ spl4_20 ),
    inference(superposition,[],[f46,f144])).

fof(f145,plain,(
    spl4_20 ),
    inference(avatar_split_clause,[],[f137,f143])).

fof(f137,plain,(
    k3_subset_1(k1_xboole_0,sK3(k1_zfmisc_1(k1_xboole_0))) = k1_xboole_0 ),
    inference(superposition,[],[f120,f43])).

fof(f43,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/subset_1__t35_subset_1.p',t4_boole)).

fof(f120,plain,(
    ! [X2] : k3_subset_1(X2,sK3(k1_zfmisc_1(X2))) = k4_xboole_0(X2,sK3(k1_zfmisc_1(X2))) ),
    inference(resolution,[],[f48,f45])).

fof(f134,plain,
    ( spl4_18
    | ~ spl4_6 ),
    inference(avatar_split_clause,[],[f118,f78,f132])).

fof(f132,plain,
    ( spl4_18
  <=> k3_subset_1(sK0,sK2) = k4_xboole_0(sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_18])])).

fof(f118,plain,
    ( k3_subset_1(sK0,sK2) = k4_xboole_0(sK0,sK2)
    | ~ spl4_6 ),
    inference(resolution,[],[f48,f79])).

fof(f127,plain,
    ( spl4_16
    | ~ spl4_4 ),
    inference(avatar_split_clause,[],[f117,f71,f125])).

fof(f125,plain,
    ( spl4_16
  <=> k3_subset_1(sK0,sK1) = k4_xboole_0(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_16])])).

fof(f117,plain,
    ( k3_subset_1(sK0,sK1) = k4_xboole_0(sK0,sK1)
    | ~ spl4_4 ),
    inference(resolution,[],[f48,f72])).

fof(f114,plain,
    ( spl4_14
    | ~ spl4_6 ),
    inference(avatar_split_clause,[],[f98,f78,f112])).

fof(f98,plain,
    ( k3_subset_1(sK0,k3_subset_1(sK0,sK2)) = sK2
    | ~ spl4_6 ),
    inference(resolution,[],[f47,f79])).

fof(f107,plain,
    ( spl4_12
    | ~ spl4_4 ),
    inference(avatar_split_clause,[],[f97,f71,f105])).

fof(f97,plain,
    ( k3_subset_1(sK0,k3_subset_1(sK0,sK1)) = sK1
    | ~ spl4_4 ),
    inference(resolution,[],[f47,f72])).

fof(f94,plain,(
    ~ spl4_11 ),
    inference(avatar_split_clause,[],[f39,f92])).

fof(f39,plain,(
    ~ r1_tarski(sK2,k3_subset_1(sK0,sK1)) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,
    ( ~ r1_tarski(sK2,k3_subset_1(sK0,sK1))
    & r1_tarski(sK1,k3_subset_1(sK0,sK2))
    & m1_subset_1(sK2,k1_zfmisc_1(sK0))
    & m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f23,f31,f30])).

fof(f30,plain,
    ( ? [X0,X1] :
        ( ? [X2] :
            ( ~ r1_tarski(X2,k3_subset_1(X0,X1))
            & r1_tarski(X1,k3_subset_1(X0,X2))
            & m1_subset_1(X2,k1_zfmisc_1(X0)) )
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
   => ( ? [X2] :
          ( ~ r1_tarski(X2,k3_subset_1(sK0,sK1))
          & r1_tarski(sK1,k3_subset_1(sK0,X2))
          & m1_subset_1(X2,k1_zfmisc_1(sK0)) )
      & m1_subset_1(sK1,k1_zfmisc_1(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ~ r1_tarski(X2,k3_subset_1(X0,X1))
          & r1_tarski(X1,k3_subset_1(X0,X2))
          & m1_subset_1(X2,k1_zfmisc_1(X0)) )
     => ( ~ r1_tarski(sK2,k3_subset_1(X0,X1))
        & r1_tarski(X1,k3_subset_1(X0,sK2))
        & m1_subset_1(sK2,k1_zfmisc_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ~ r1_tarski(X2,k3_subset_1(X0,X1))
          & r1_tarski(X1,k3_subset_1(X0,X2))
          & m1_subset_1(X2,k1_zfmisc_1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ~ r1_tarski(X2,k3_subset_1(X0,X1))
          & r1_tarski(X1,k3_subset_1(X0,X2))
          & m1_subset_1(X2,k1_zfmisc_1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(X0))
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(X0))
           => ( r1_tarski(X1,k3_subset_1(X0,X2))
             => r1_tarski(X2,k3_subset_1(X0,X1)) ) ) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X0))
         => ( r1_tarski(X1,k3_subset_1(X0,X2))
           => r1_tarski(X2,k3_subset_1(X0,X1)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/subset_1__t35_subset_1.p',t35_subset_1)).

fof(f87,plain,(
    spl4_8 ),
    inference(avatar_split_clause,[],[f38,f85])).

fof(f38,plain,(
    r1_tarski(sK1,k3_subset_1(sK0,sK2)) ),
    inference(cnf_transformation,[],[f32])).

fof(f80,plain,(
    spl4_6 ),
    inference(avatar_split_clause,[],[f37,f78])).

fof(f37,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f32])).

fof(f73,plain,(
    spl4_4 ),
    inference(avatar_split_clause,[],[f36,f71])).

fof(f36,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f32])).

fof(f66,plain,(
    spl4_2 ),
    inference(avatar_split_clause,[],[f41,f64])).

fof(f64,plain,
    ( spl4_2
  <=> k1_xboole_0 = o_0_0_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f41,plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/subset_1__t35_subset_1.p',d2_xboole_0)).

fof(f59,plain,(
    spl4_0 ),
    inference(avatar_split_clause,[],[f52,f57])).

fof(f57,plain,
    ( spl4_0
  <=> v1_xboole_0(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_0])])).

fof(f52,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(forward_demodulation,[],[f40,f41])).

fof(f40,plain,(
    v1_xboole_0(o_0_0_xboole_0) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    v1_xboole_0(o_0_0_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/subset_1__t35_subset_1.p',dt_o_0_0_xboole_0)).
%------------------------------------------------------------------------------
