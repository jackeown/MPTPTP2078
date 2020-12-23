%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:46:35 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  135 ( 259 expanded)
%              Number of leaves         :   35 ( 115 expanded)
%              Depth                    :    8
%              Number of atoms          :  323 ( 674 expanded)
%              Number of equality atoms :   52 ( 142 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f503,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f45,f49,f53,f57,f62,f70,f159,f163,f172,f186,f195,f221,f276,f281,f284,f291,f315,f335,f344,f345,f368,f473,f482,f500])).

fof(f500,plain,
    ( spl3_13
    | ~ spl3_47 ),
    inference(avatar_split_clause,[],[f491,f351,f137])).

fof(f137,plain,
    ( spl3_13
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).

fof(f351,plain,
    ( spl3_47
  <=> k1_xboole_0 = k2_xboole_0(sK1,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_47])])).

fof(f491,plain,
    ( k1_xboole_0 = sK1
    | ~ spl3_47 ),
    inference(superposition,[],[f71,f352])).

fof(f352,plain,
    ( k1_xboole_0 = k2_xboole_0(sK1,k1_xboole_0)
    | ~ spl3_47 ),
    inference(avatar_component_clause,[],[f351])).

fof(f71,plain,(
    ! [X1] : k2_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(superposition,[],[f65,f32])).

fof(f32,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(f65,plain,(
    ! [X0] : k2_xboole_0(k1_xboole_0,X0) = X0 ),
    inference(resolution,[],[f33,f30])).

fof(f30,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f33,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k2_xboole_0(X0,X1) = X1 ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

fof(f482,plain,
    ( ~ spl3_19
    | ~ spl3_30
    | spl3_18
    | ~ spl3_22 ),
    inference(avatar_split_clause,[],[f481,f184,f161,f231,f167])).

fof(f167,plain,
    ( spl3_19
  <=> m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_19])])).

fof(f231,plain,
    ( spl3_30
  <=> m1_subset_1(k8_setfam_1(sK0,k1_xboole_0),k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_30])])).

fof(f161,plain,
    ( spl3_18
  <=> m1_subset_1(k8_setfam_1(sK0,sK2),k1_zfmisc_1(k8_setfam_1(sK0,k1_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_18])])).

fof(f184,plain,
    ( spl3_22
  <=> k1_xboole_0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_22])])).

fof(f481,plain,
    ( ~ m1_subset_1(k8_setfam_1(sK0,k1_xboole_0),k1_zfmisc_1(sK0))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(sK0)))
    | spl3_18
    | ~ spl3_22 ),
    inference(forward_demodulation,[],[f478,f185])).

fof(f185,plain,
    ( k1_xboole_0 = sK2
    | ~ spl3_22 ),
    inference(avatar_component_clause,[],[f184])).

fof(f478,plain,
    ( ~ m1_subset_1(k8_setfam_1(sK0,sK2),k1_zfmisc_1(sK0))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(sK0)))
    | spl3_18 ),
    inference(superposition,[],[f162,f41])).

fof(f41,plain,(
    ! [X0] :
      ( k8_setfam_1(X0,k1_xboole_0) = X0
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(equality_resolution,[],[f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( k8_setfam_1(X0,X1) = X0
      | k1_xboole_0 != X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ( ( k8_setfam_1(X0,X1) = X0
          | k1_xboole_0 != X1 )
        & ( k8_setfam_1(X0,X1) = k6_setfam_1(X0,X1)
          | k1_xboole_0 = X1 ) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => ( ( k1_xboole_0 = X1
         => k8_setfam_1(X0,X1) = X0 )
        & ( k1_xboole_0 != X1
         => k8_setfam_1(X0,X1) = k6_setfam_1(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_setfam_1)).

fof(f162,plain,
    ( ~ m1_subset_1(k8_setfam_1(sK0,sK2),k1_zfmisc_1(k8_setfam_1(sK0,k1_xboole_0)))
    | spl3_18 ),
    inference(avatar_component_clause,[],[f161])).

fof(f473,plain,
    ( ~ spl3_33
    | ~ spl3_22
    | spl3_29 ),
    inference(avatar_split_clause,[],[f472,f226,f184,f259])).

fof(f259,plain,
    ( spl3_33
  <=> r1_tarski(k8_setfam_1(sK0,k1_xboole_0),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_33])])).

fof(f226,plain,
    ( spl3_29
  <=> m1_subset_1(k8_setfam_1(sK0,sK2),k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_29])])).

fof(f472,plain,
    ( ~ r1_tarski(k8_setfam_1(sK0,k1_xboole_0),sK0)
    | ~ spl3_22
    | spl3_29 ),
    inference(forward_demodulation,[],[f468,f185])).

fof(f468,plain,
    ( ~ r1_tarski(k8_setfam_1(sK0,sK2),sK0)
    | spl3_29 ),
    inference(resolution,[],[f227,f40])).

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
    inference(nnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(f227,plain,
    ( ~ m1_subset_1(k8_setfam_1(sK0,sK2),k1_zfmisc_1(sK0))
    | spl3_29 ),
    inference(avatar_component_clause,[],[f226])).

fof(f368,plain,
    ( spl3_47
    | ~ spl3_6
    | ~ spl3_22 ),
    inference(avatar_split_clause,[],[f238,f184,f68,f351])).

fof(f68,plain,
    ( spl3_6
  <=> sK2 = k2_xboole_0(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f238,plain,
    ( k1_xboole_0 = k2_xboole_0(sK1,k1_xboole_0)
    | ~ spl3_6
    | ~ spl3_22 ),
    inference(superposition,[],[f69,f185])).

fof(f69,plain,
    ( sK2 = k2_xboole_0(sK1,sK2)
    | ~ spl3_6 ),
    inference(avatar_component_clause,[],[f68])).

fof(f345,plain,
    ( k1_xboole_0 != sK2
    | m1_subset_1(k8_setfam_1(sK0,k1_xboole_0),k1_zfmisc_1(sK0))
    | ~ m1_subset_1(k8_setfam_1(sK0,sK2),k1_zfmisc_1(sK0)) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f344,plain,
    ( ~ spl3_2
    | spl3_13
    | spl3_45 ),
    inference(avatar_split_clause,[],[f341,f333,f137,f47])).

fof(f47,plain,
    ( spl3_2
  <=> r1_tarski(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f333,plain,
    ( spl3_45
  <=> r1_tarski(k1_setfam_1(sK2),k1_setfam_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_45])])).

fof(f341,plain,
    ( k1_xboole_0 = sK1
    | ~ r1_tarski(sK1,sK2)
    | spl3_45 ),
    inference(resolution,[],[f334,f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_setfam_1(X1),k1_setfam_1(X0))
      | k1_xboole_0 = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_setfam_1(X1),k1_setfam_1(X0))
      | k1_xboole_0 = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_setfam_1(X1),k1_setfam_1(X0))
      | k1_xboole_0 = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => ( r1_tarski(k1_setfam_1(X1),k1_setfam_1(X0))
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_setfam_1)).

fof(f334,plain,
    ( ~ r1_tarski(k1_setfam_1(sK2),k1_setfam_1(sK1))
    | spl3_45 ),
    inference(avatar_component_clause,[],[f333])).

fof(f335,plain,
    ( ~ spl3_45
    | spl3_1
    | ~ spl3_21
    | ~ spl3_38 ),
    inference(avatar_split_clause,[],[f331,f289,f181,f43,f333])).

fof(f43,plain,
    ( spl3_1
  <=> r1_tarski(k8_setfam_1(sK0,sK2),k8_setfam_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f181,plain,
    ( spl3_21
  <=> k8_setfam_1(sK0,sK2) = k1_setfam_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_21])])).

fof(f289,plain,
    ( spl3_38
  <=> k8_setfam_1(sK0,sK1) = k1_setfam_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_38])])).

fof(f331,plain,
    ( ~ r1_tarski(k1_setfam_1(sK2),k1_setfam_1(sK1))
    | spl3_1
    | ~ spl3_21
    | ~ spl3_38 ),
    inference(forward_demodulation,[],[f324,f182])).

fof(f182,plain,
    ( k8_setfam_1(sK0,sK2) = k1_setfam_1(sK2)
    | ~ spl3_21 ),
    inference(avatar_component_clause,[],[f181])).

fof(f324,plain,
    ( ~ r1_tarski(k8_setfam_1(sK0,sK2),k1_setfam_1(sK1))
    | spl3_1
    | ~ spl3_38 ),
    inference(superposition,[],[f44,f290])).

fof(f290,plain,
    ( k8_setfam_1(sK0,sK1) = k1_setfam_1(sK1)
    | ~ spl3_38 ),
    inference(avatar_component_clause,[],[f289])).

fof(f44,plain,
    ( ~ r1_tarski(k8_setfam_1(sK0,sK2),k8_setfam_1(sK0,sK1))
    | spl3_1 ),
    inference(avatar_component_clause,[],[f43])).

fof(f315,plain,(
    spl3_19 ),
    inference(avatar_contradiction_clause,[],[f313])).

fof(f313,plain,
    ( $false
    | spl3_19 ),
    inference(resolution,[],[f168,f31])).

fof(f31,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

fof(f168,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(sK0)))
    | spl3_19 ),
    inference(avatar_component_clause,[],[f167])).

fof(f291,plain,
    ( spl3_38
    | spl3_13
    | ~ spl3_4 ),
    inference(avatar_split_clause,[],[f175,f55,f137,f289])).

fof(f55,plain,
    ( spl3_4
  <=> m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f175,plain,
    ( k1_xboole_0 = sK1
    | k8_setfam_1(sK0,sK1) = k1_setfam_1(sK1)
    | ~ spl3_4 ),
    inference(resolution,[],[f102,f56])).

fof(f56,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0)))
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f55])).

fof(f102,plain,(
    ! [X2,X3] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X2)))
      | k1_xboole_0 = X3
      | k1_setfam_1(X3) = k8_setfam_1(X2,X3) ) ),
    inference(duplicate_literal_removal,[],[f99])).

fof(f99,plain,(
    ! [X2,X3] :
      ( k1_setfam_1(X3) = k8_setfam_1(X2,X3)
      | k1_xboole_0 = X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X2)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X2))) ) ),
    inference(superposition,[],[f37,f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( k6_setfam_1(X0,X1) = k1_setfam_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( k6_setfam_1(X0,X1) = k1_setfam_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => k6_setfam_1(X0,X1) = k1_setfam_1(X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_setfam_1)).

fof(f37,plain,(
    ! [X0,X1] :
      ( k8_setfam_1(X0,X1) = k6_setfam_1(X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f284,plain,
    ( ~ spl3_19
    | spl3_37 ),
    inference(avatar_split_clause,[],[f282,f279,f167])).

fof(f279,plain,
    ( spl3_37
  <=> m1_subset_1(sK0,k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_37])])).

fof(f282,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(sK0)))
    | spl3_37 ),
    inference(resolution,[],[f280,f94])).

fof(f94,plain,(
    ! [X0] :
      ( m1_subset_1(X0,k1_zfmisc_1(X0))
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(duplicate_literal_removal,[],[f93])).

fof(f93,plain,(
    ! [X0] :
      ( m1_subset_1(X0,k1_zfmisc_1(X0))
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(superposition,[],[f36,f41])).

fof(f36,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k8_setfam_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k8_setfam_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => m1_subset_1(k8_setfam_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k8_setfam_1)).

fof(f280,plain,
    ( ~ m1_subset_1(sK0,k1_zfmisc_1(sK0))
    | spl3_37 ),
    inference(avatar_component_clause,[],[f279])).

fof(f281,plain,
    ( ~ spl3_37
    | spl3_36 ),
    inference(avatar_split_clause,[],[f277,f274,f279])).

fof(f274,plain,
    ( spl3_36
  <=> r1_tarski(sK0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_36])])).

fof(f277,plain,
    ( ~ m1_subset_1(sK0,k1_zfmisc_1(sK0))
    | spl3_36 ),
    inference(resolution,[],[f275,f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f275,plain,
    ( ~ r1_tarski(sK0,sK0)
    | spl3_36 ),
    inference(avatar_component_clause,[],[f274])).

fof(f276,plain,
    ( ~ spl3_19
    | ~ spl3_36
    | spl3_33 ),
    inference(avatar_split_clause,[],[f272,f259,f274,f167])).

fof(f272,plain,
    ( ~ r1_tarski(sK0,sK0)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(sK0)))
    | spl3_33 ),
    inference(superposition,[],[f260,f41])).

fof(f260,plain,
    ( ~ r1_tarski(k8_setfam_1(sK0,k1_xboole_0),sK0)
    | spl3_33 ),
    inference(avatar_component_clause,[],[f259])).

fof(f221,plain,
    ( ~ spl3_3
    | spl3_24
    | ~ spl3_21 ),
    inference(avatar_split_clause,[],[f207,f181,f193,f51])).

fof(f51,plain,
    ( spl3_3
  <=> m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f193,plain,
    ( spl3_24
  <=> m1_subset_1(k1_setfam_1(sK2),k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_24])])).

fof(f207,plain,
    ( m1_subset_1(k1_setfam_1(sK2),k1_zfmisc_1(sK0))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0)))
    | ~ spl3_21 ),
    inference(superposition,[],[f36,f182])).

fof(f195,plain,
    ( ~ spl3_24
    | spl3_20
    | ~ spl3_21 ),
    inference(avatar_split_clause,[],[f191,f181,f170,f193])).

fof(f170,plain,
    ( spl3_20
  <=> r1_tarski(k8_setfam_1(sK0,sK2),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_20])])).

fof(f191,plain,
    ( ~ m1_subset_1(k1_setfam_1(sK2),k1_zfmisc_1(sK0))
    | spl3_20
    | ~ spl3_21 ),
    inference(forward_demodulation,[],[f190,f182])).

fof(f190,plain,
    ( ~ m1_subset_1(k8_setfam_1(sK0,sK2),k1_zfmisc_1(sK0))
    | spl3_20 ),
    inference(resolution,[],[f171,f39])).

fof(f171,plain,
    ( ~ r1_tarski(k8_setfam_1(sK0,sK2),sK0)
    | spl3_20 ),
    inference(avatar_component_clause,[],[f170])).

fof(f186,plain,
    ( spl3_21
    | spl3_22
    | ~ spl3_3 ),
    inference(avatar_split_clause,[],[f174,f51,f184,f181])).

fof(f174,plain,
    ( k1_xboole_0 = sK2
    | k8_setfam_1(sK0,sK2) = k1_setfam_1(sK2)
    | ~ spl3_3 ),
    inference(resolution,[],[f102,f52])).

fof(f52,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0)))
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f51])).

fof(f172,plain,
    ( ~ spl3_19
    | ~ spl3_20
    | spl3_17 ),
    inference(avatar_split_clause,[],[f165,f157,f170,f167])).

fof(f157,plain,
    ( spl3_17
  <=> r1_tarski(k8_setfam_1(sK0,sK2),k8_setfam_1(sK0,k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_17])])).

fof(f165,plain,
    ( ~ r1_tarski(k8_setfam_1(sK0,sK2),sK0)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(sK0)))
    | spl3_17 ),
    inference(superposition,[],[f158,f41])).

fof(f158,plain,
    ( ~ r1_tarski(k8_setfam_1(sK0,sK2),k8_setfam_1(sK0,k1_xboole_0))
    | spl3_17 ),
    inference(avatar_component_clause,[],[f157])).

fof(f163,plain,
    ( ~ spl3_18
    | spl3_5
    | ~ spl3_13 ),
    inference(avatar_split_clause,[],[f152,f137,f60,f161])).

fof(f60,plain,
    ( spl3_5
  <=> m1_subset_1(k8_setfam_1(sK0,sK2),k1_zfmisc_1(k8_setfam_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f152,plain,
    ( ~ m1_subset_1(k8_setfam_1(sK0,sK2),k1_zfmisc_1(k8_setfam_1(sK0,k1_xboole_0)))
    | spl3_5
    | ~ spl3_13 ),
    inference(superposition,[],[f61,f138])).

fof(f138,plain,
    ( k1_xboole_0 = sK1
    | ~ spl3_13 ),
    inference(avatar_component_clause,[],[f137])).

fof(f61,plain,
    ( ~ m1_subset_1(k8_setfam_1(sK0,sK2),k1_zfmisc_1(k8_setfam_1(sK0,sK1)))
    | spl3_5 ),
    inference(avatar_component_clause,[],[f60])).

% (20024)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% (20009)Refutation not found, incomplete strategy% (20009)------------------------------
% (20009)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (20009)Termination reason: Refutation not found, incomplete strategy

% (20009)Memory used [KB]: 6396
% (20009)Time elapsed: 0.074 s
% (20009)------------------------------
% (20009)------------------------------
% (20016)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
fof(f159,plain,
    ( ~ spl3_17
    | spl3_1
    | ~ spl3_13 ),
    inference(avatar_split_clause,[],[f149,f137,f43,f157])).

% (20014)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
fof(f149,plain,
    ( ~ r1_tarski(k8_setfam_1(sK0,sK2),k8_setfam_1(sK0,k1_xboole_0))
    | spl3_1
    | ~ spl3_13 ),
    inference(superposition,[],[f44,f138])).

fof(f70,plain,
    ( spl3_6
    | ~ spl3_2 ),
    inference(avatar_split_clause,[],[f64,f47,f68])).

fof(f64,plain,
    ( sK2 = k2_xboole_0(sK1,sK2)
    | ~ spl3_2 ),
    inference(resolution,[],[f33,f48])).

fof(f48,plain,
    ( r1_tarski(sK1,sK2)
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f47])).

fof(f62,plain,
    ( ~ spl3_5
    | spl3_1 ),
    inference(avatar_split_clause,[],[f58,f43,f60])).

fof(f58,plain,
    ( ~ m1_subset_1(k8_setfam_1(sK0,sK2),k1_zfmisc_1(k8_setfam_1(sK0,sK1)))
    | spl3_1 ),
    inference(resolution,[],[f39,f44])).

fof(f57,plain,(
    spl3_4 ),
    inference(avatar_split_clause,[],[f26,f55])).

fof(f26,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0))) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,
    ( ~ r1_tarski(k8_setfam_1(sK0,sK2),k8_setfam_1(sK0,sK1))
    & r1_tarski(sK1,sK2)
    & m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0)))
    & m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0))) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f15,f23,f22])).

fof(f22,plain,
    ( ? [X0,X1] :
        ( ? [X2] :
            ( ~ r1_tarski(k8_setfam_1(X0,X2),k8_setfam_1(X0,X1))
            & r1_tarski(X1,X2)
            & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) )
        & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) )
   => ( ? [X2] :
          ( ~ r1_tarski(k8_setfam_1(sK0,X2),k8_setfam_1(sK0,sK1))
          & r1_tarski(sK1,X2)
          & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(sK0))) )
      & m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,
    ( ? [X2] :
        ( ~ r1_tarski(k8_setfam_1(sK0,X2),k8_setfam_1(sK0,sK1))
        & r1_tarski(sK1,X2)
        & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(sK0))) )
   => ( ~ r1_tarski(k8_setfam_1(sK0,sK2),k8_setfam_1(sK0,sK1))
      & r1_tarski(sK1,sK2)
      & m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f15,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ~ r1_tarski(k8_setfam_1(X0,X2),k8_setfam_1(X0,X1))
          & r1_tarski(X1,X2)
          & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) )
      & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ~ r1_tarski(k8_setfam_1(X0,X2),k8_setfam_1(X0,X1))
          & r1_tarski(X1,X2)
          & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) )
      & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))
           => ( r1_tarski(X1,X2)
             => r1_tarski(k8_setfam_1(X0,X2),k8_setfam_1(X0,X1)) ) ) ) ),
    inference(negated_conjecture,[],[f11])).

fof(f11,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))
         => ( r1_tarski(X1,X2)
           => r1_tarski(k8_setfam_1(X0,X2),k8_setfam_1(X0,X1)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t59_setfam_1)).

fof(f53,plain,(
    spl3_3 ),
    inference(avatar_split_clause,[],[f27,f51])).

fof(f27,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0))) ),
    inference(cnf_transformation,[],[f24])).

fof(f49,plain,(
    spl3_2 ),
    inference(avatar_split_clause,[],[f28,f47])).

fof(f28,plain,(
    r1_tarski(sK1,sK2) ),
    inference(cnf_transformation,[],[f24])).

fof(f45,plain,(
    ~ spl3_1 ),
    inference(avatar_split_clause,[],[f29,f43])).

fof(f29,plain,(
    ~ r1_tarski(k8_setfam_1(sK0,sK2),k8_setfam_1(sK0,sK1)) ),
    inference(cnf_transformation,[],[f24])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.14/0.14  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n022.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 09:42:11 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.22/0.49  % (20009)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.22/0.50  % (20015)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.22/0.51  % (20015)Refutation found. Thanks to Tanya!
% 0.22/0.51  % SZS status Theorem for theBenchmark
% 0.22/0.51  % (20018)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.22/0.51  % (20017)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 0.22/0.51  % SZS output start Proof for theBenchmark
% 0.22/0.51  fof(f503,plain,(
% 0.22/0.51    $false),
% 0.22/0.51    inference(avatar_sat_refutation,[],[f45,f49,f53,f57,f62,f70,f159,f163,f172,f186,f195,f221,f276,f281,f284,f291,f315,f335,f344,f345,f368,f473,f482,f500])).
% 0.22/0.51  fof(f500,plain,(
% 0.22/0.51    spl3_13 | ~spl3_47),
% 0.22/0.51    inference(avatar_split_clause,[],[f491,f351,f137])).
% 0.22/0.51  fof(f137,plain,(
% 0.22/0.51    spl3_13 <=> k1_xboole_0 = sK1),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).
% 0.22/0.51  fof(f351,plain,(
% 0.22/0.51    spl3_47 <=> k1_xboole_0 = k2_xboole_0(sK1,k1_xboole_0)),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_47])])).
% 0.22/0.51  fof(f491,plain,(
% 0.22/0.51    k1_xboole_0 = sK1 | ~spl3_47),
% 0.22/0.51    inference(superposition,[],[f71,f352])).
% 0.22/0.51  fof(f352,plain,(
% 0.22/0.51    k1_xboole_0 = k2_xboole_0(sK1,k1_xboole_0) | ~spl3_47),
% 0.22/0.51    inference(avatar_component_clause,[],[f351])).
% 0.22/0.51  fof(f71,plain,(
% 0.22/0.51    ( ! [X1] : (k2_xboole_0(X1,k1_xboole_0) = X1) )),
% 0.22/0.51    inference(superposition,[],[f65,f32])).
% 0.22/0.51  fof(f32,plain,(
% 0.22/0.51    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f1])).
% 0.22/0.51  fof(f1,axiom,(
% 0.22/0.51    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).
% 0.22/0.51  fof(f65,plain,(
% 0.22/0.51    ( ! [X0] : (k2_xboole_0(k1_xboole_0,X0) = X0) )),
% 0.22/0.51    inference(resolution,[],[f33,f30])).
% 0.22/0.51  fof(f30,plain,(
% 0.22/0.51    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f3])).
% 0.22/0.51  fof(f3,axiom,(
% 0.22/0.51    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).
% 0.22/0.51  fof(f33,plain,(
% 0.22/0.51    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k2_xboole_0(X0,X1) = X1) )),
% 0.22/0.51    inference(cnf_transformation,[],[f16])).
% 0.22/0.51  fof(f16,plain,(
% 0.22/0.51    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 0.22/0.51    inference(ennf_transformation,[],[f2])).
% 0.22/0.51  fof(f2,axiom,(
% 0.22/0.51    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).
% 0.22/0.51  fof(f482,plain,(
% 0.22/0.51    ~spl3_19 | ~spl3_30 | spl3_18 | ~spl3_22),
% 0.22/0.51    inference(avatar_split_clause,[],[f481,f184,f161,f231,f167])).
% 0.22/0.51  fof(f167,plain,(
% 0.22/0.51    spl3_19 <=> m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(sK0)))),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_19])])).
% 0.22/0.51  fof(f231,plain,(
% 0.22/0.51    spl3_30 <=> m1_subset_1(k8_setfam_1(sK0,k1_xboole_0),k1_zfmisc_1(sK0))),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_30])])).
% 0.22/0.51  fof(f161,plain,(
% 0.22/0.51    spl3_18 <=> m1_subset_1(k8_setfam_1(sK0,sK2),k1_zfmisc_1(k8_setfam_1(sK0,k1_xboole_0)))),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_18])])).
% 0.22/0.51  fof(f184,plain,(
% 0.22/0.51    spl3_22 <=> k1_xboole_0 = sK2),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_22])])).
% 0.22/0.51  fof(f481,plain,(
% 0.22/0.51    ~m1_subset_1(k8_setfam_1(sK0,k1_xboole_0),k1_zfmisc_1(sK0)) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(sK0))) | (spl3_18 | ~spl3_22)),
% 0.22/0.51    inference(forward_demodulation,[],[f478,f185])).
% 0.22/0.51  fof(f185,plain,(
% 0.22/0.51    k1_xboole_0 = sK2 | ~spl3_22),
% 0.22/0.51    inference(avatar_component_clause,[],[f184])).
% 0.22/0.51  fof(f478,plain,(
% 0.22/0.51    ~m1_subset_1(k8_setfam_1(sK0,sK2),k1_zfmisc_1(sK0)) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(sK0))) | spl3_18),
% 0.22/0.51    inference(superposition,[],[f162,f41])).
% 0.22/0.51  fof(f41,plain,(
% 0.22/0.51    ( ! [X0] : (k8_setfam_1(X0,k1_xboole_0) = X0 | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 0.22/0.51    inference(equality_resolution,[],[f38])).
% 0.22/0.51  fof(f38,plain,(
% 0.22/0.51    ( ! [X0,X1] : (k8_setfam_1(X0,X1) = X0 | k1_xboole_0 != X1 | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 0.22/0.51    inference(cnf_transformation,[],[f21])).
% 0.22/0.51  fof(f21,plain,(
% 0.22/0.51    ! [X0,X1] : (((k8_setfam_1(X0,X1) = X0 | k1_xboole_0 != X1) & (k8_setfam_1(X0,X1) = k6_setfam_1(X0,X1) | k1_xboole_0 = X1)) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 0.22/0.51    inference(ennf_transformation,[],[f5])).
% 0.22/0.51  fof(f5,axiom,(
% 0.22/0.51    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => ((k1_xboole_0 = X1 => k8_setfam_1(X0,X1) = X0) & (k1_xboole_0 != X1 => k8_setfam_1(X0,X1) = k6_setfam_1(X0,X1))))),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_setfam_1)).
% 0.22/0.51  fof(f162,plain,(
% 0.22/0.51    ~m1_subset_1(k8_setfam_1(sK0,sK2),k1_zfmisc_1(k8_setfam_1(sK0,k1_xboole_0))) | spl3_18),
% 0.22/0.51    inference(avatar_component_clause,[],[f161])).
% 0.22/0.51  fof(f473,plain,(
% 0.22/0.51    ~spl3_33 | ~spl3_22 | spl3_29),
% 0.22/0.51    inference(avatar_split_clause,[],[f472,f226,f184,f259])).
% 0.22/0.51  fof(f259,plain,(
% 0.22/0.51    spl3_33 <=> r1_tarski(k8_setfam_1(sK0,k1_xboole_0),sK0)),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_33])])).
% 0.22/0.51  fof(f226,plain,(
% 0.22/0.51    spl3_29 <=> m1_subset_1(k8_setfam_1(sK0,sK2),k1_zfmisc_1(sK0))),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_29])])).
% 0.22/0.51  fof(f472,plain,(
% 0.22/0.51    ~r1_tarski(k8_setfam_1(sK0,k1_xboole_0),sK0) | (~spl3_22 | spl3_29)),
% 0.22/0.51    inference(forward_demodulation,[],[f468,f185])).
% 0.22/0.51  fof(f468,plain,(
% 0.22/0.51    ~r1_tarski(k8_setfam_1(sK0,sK2),sK0) | spl3_29),
% 0.22/0.51    inference(resolution,[],[f227,f40])).
% 0.22/0.51  fof(f40,plain,(
% 0.22/0.51    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f25])).
% 0.22/0.51  fof(f25,plain,(
% 0.22/0.51    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 0.22/0.51    inference(nnf_transformation,[],[f8])).
% 0.22/0.51  fof(f8,axiom,(
% 0.22/0.51    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).
% 0.22/0.51  fof(f227,plain,(
% 0.22/0.51    ~m1_subset_1(k8_setfam_1(sK0,sK2),k1_zfmisc_1(sK0)) | spl3_29),
% 0.22/0.51    inference(avatar_component_clause,[],[f226])).
% 0.22/0.51  fof(f368,plain,(
% 0.22/0.51    spl3_47 | ~spl3_6 | ~spl3_22),
% 0.22/0.51    inference(avatar_split_clause,[],[f238,f184,f68,f351])).
% 0.22/0.51  fof(f68,plain,(
% 0.22/0.51    spl3_6 <=> sK2 = k2_xboole_0(sK1,sK2)),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 0.22/0.51  fof(f238,plain,(
% 0.22/0.51    k1_xboole_0 = k2_xboole_0(sK1,k1_xboole_0) | (~spl3_6 | ~spl3_22)),
% 0.22/0.51    inference(superposition,[],[f69,f185])).
% 0.22/0.51  fof(f69,plain,(
% 0.22/0.51    sK2 = k2_xboole_0(sK1,sK2) | ~spl3_6),
% 0.22/0.51    inference(avatar_component_clause,[],[f68])).
% 0.22/0.51  fof(f345,plain,(
% 0.22/0.51    k1_xboole_0 != sK2 | m1_subset_1(k8_setfam_1(sK0,k1_xboole_0),k1_zfmisc_1(sK0)) | ~m1_subset_1(k8_setfam_1(sK0,sK2),k1_zfmisc_1(sK0))),
% 0.22/0.51    introduced(theory_tautology_sat_conflict,[])).
% 0.22/0.51  fof(f344,plain,(
% 0.22/0.51    ~spl3_2 | spl3_13 | spl3_45),
% 0.22/0.51    inference(avatar_split_clause,[],[f341,f333,f137,f47])).
% 0.22/0.51  fof(f47,plain,(
% 0.22/0.51    spl3_2 <=> r1_tarski(sK1,sK2)),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.22/0.51  fof(f333,plain,(
% 0.22/0.51    spl3_45 <=> r1_tarski(k1_setfam_1(sK2),k1_setfam_1(sK1))),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_45])])).
% 0.22/0.51  fof(f341,plain,(
% 0.22/0.51    k1_xboole_0 = sK1 | ~r1_tarski(sK1,sK2) | spl3_45),
% 0.22/0.51    inference(resolution,[],[f334,f34])).
% 0.22/0.51  fof(f34,plain,(
% 0.22/0.51    ( ! [X0,X1] : (r1_tarski(k1_setfam_1(X1),k1_setfam_1(X0)) | k1_xboole_0 = X0 | ~r1_tarski(X0,X1)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f18])).
% 0.22/0.51  fof(f18,plain,(
% 0.22/0.51    ! [X0,X1] : (r1_tarski(k1_setfam_1(X1),k1_setfam_1(X0)) | k1_xboole_0 = X0 | ~r1_tarski(X0,X1))),
% 0.22/0.51    inference(flattening,[],[f17])).
% 0.22/0.51  fof(f17,plain,(
% 0.22/0.51    ! [X0,X1] : ((r1_tarski(k1_setfam_1(X1),k1_setfam_1(X0)) | k1_xboole_0 = X0) | ~r1_tarski(X0,X1))),
% 0.22/0.51    inference(ennf_transformation,[],[f10])).
% 0.22/0.51  fof(f10,axiom,(
% 0.22/0.51    ! [X0,X1] : (r1_tarski(X0,X1) => (r1_tarski(k1_setfam_1(X1),k1_setfam_1(X0)) | k1_xboole_0 = X0))),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_setfam_1)).
% 0.22/0.51  fof(f334,plain,(
% 0.22/0.51    ~r1_tarski(k1_setfam_1(sK2),k1_setfam_1(sK1)) | spl3_45),
% 0.22/0.51    inference(avatar_component_clause,[],[f333])).
% 0.22/0.51  fof(f335,plain,(
% 0.22/0.51    ~spl3_45 | spl3_1 | ~spl3_21 | ~spl3_38),
% 0.22/0.51    inference(avatar_split_clause,[],[f331,f289,f181,f43,f333])).
% 0.22/0.51  fof(f43,plain,(
% 0.22/0.51    spl3_1 <=> r1_tarski(k8_setfam_1(sK0,sK2),k8_setfam_1(sK0,sK1))),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.22/0.51  fof(f181,plain,(
% 0.22/0.51    spl3_21 <=> k8_setfam_1(sK0,sK2) = k1_setfam_1(sK2)),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_21])])).
% 0.22/0.51  fof(f289,plain,(
% 0.22/0.51    spl3_38 <=> k8_setfam_1(sK0,sK1) = k1_setfam_1(sK1)),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_38])])).
% 0.22/0.51  fof(f331,plain,(
% 0.22/0.51    ~r1_tarski(k1_setfam_1(sK2),k1_setfam_1(sK1)) | (spl3_1 | ~spl3_21 | ~spl3_38)),
% 0.22/0.51    inference(forward_demodulation,[],[f324,f182])).
% 0.22/0.51  fof(f182,plain,(
% 0.22/0.51    k8_setfam_1(sK0,sK2) = k1_setfam_1(sK2) | ~spl3_21),
% 0.22/0.51    inference(avatar_component_clause,[],[f181])).
% 0.22/0.51  fof(f324,plain,(
% 0.22/0.51    ~r1_tarski(k8_setfam_1(sK0,sK2),k1_setfam_1(sK1)) | (spl3_1 | ~spl3_38)),
% 0.22/0.51    inference(superposition,[],[f44,f290])).
% 0.22/0.51  fof(f290,plain,(
% 0.22/0.51    k8_setfam_1(sK0,sK1) = k1_setfam_1(sK1) | ~spl3_38),
% 0.22/0.51    inference(avatar_component_clause,[],[f289])).
% 0.22/0.51  fof(f44,plain,(
% 0.22/0.51    ~r1_tarski(k8_setfam_1(sK0,sK2),k8_setfam_1(sK0,sK1)) | spl3_1),
% 0.22/0.51    inference(avatar_component_clause,[],[f43])).
% 0.22/0.51  fof(f315,plain,(
% 0.22/0.51    spl3_19),
% 0.22/0.51    inference(avatar_contradiction_clause,[],[f313])).
% 0.22/0.51  fof(f313,plain,(
% 0.22/0.51    $false | spl3_19),
% 0.22/0.51    inference(resolution,[],[f168,f31])).
% 0.22/0.51  fof(f31,plain,(
% 0.22/0.51    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 0.22/0.51    inference(cnf_transformation,[],[f4])).
% 0.22/0.51  fof(f4,axiom,(
% 0.22/0.51    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).
% 0.22/0.51  fof(f168,plain,(
% 0.22/0.51    ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(sK0))) | spl3_19),
% 0.22/0.51    inference(avatar_component_clause,[],[f167])).
% 0.22/0.51  fof(f291,plain,(
% 0.22/0.51    spl3_38 | spl3_13 | ~spl3_4),
% 0.22/0.51    inference(avatar_split_clause,[],[f175,f55,f137,f289])).
% 0.22/0.51  fof(f55,plain,(
% 0.22/0.51    spl3_4 <=> m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0)))),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.22/0.51  fof(f175,plain,(
% 0.22/0.51    k1_xboole_0 = sK1 | k8_setfam_1(sK0,sK1) = k1_setfam_1(sK1) | ~spl3_4),
% 0.22/0.51    inference(resolution,[],[f102,f56])).
% 0.22/0.51  fof(f56,plain,(
% 0.22/0.51    m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0))) | ~spl3_4),
% 0.22/0.51    inference(avatar_component_clause,[],[f55])).
% 0.22/0.51  fof(f102,plain,(
% 0.22/0.51    ( ! [X2,X3] : (~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X2))) | k1_xboole_0 = X3 | k1_setfam_1(X3) = k8_setfam_1(X2,X3)) )),
% 0.22/0.51    inference(duplicate_literal_removal,[],[f99])).
% 0.22/0.51  fof(f99,plain,(
% 0.22/0.51    ( ! [X2,X3] : (k1_setfam_1(X3) = k8_setfam_1(X2,X3) | k1_xboole_0 = X3 | ~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X2))) | ~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X2)))) )),
% 0.22/0.51    inference(superposition,[],[f37,f35])).
% 0.22/0.51  fof(f35,plain,(
% 0.22/0.51    ( ! [X0,X1] : (k6_setfam_1(X0,X1) = k1_setfam_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 0.22/0.51    inference(cnf_transformation,[],[f19])).
% 0.22/0.51  fof(f19,plain,(
% 0.22/0.51    ! [X0,X1] : (k6_setfam_1(X0,X1) = k1_setfam_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 0.22/0.51    inference(ennf_transformation,[],[f7])).
% 0.22/0.51  fof(f7,axiom,(
% 0.22/0.51    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => k6_setfam_1(X0,X1) = k1_setfam_1(X1))),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_setfam_1)).
% 0.22/0.51  fof(f37,plain,(
% 0.22/0.51    ( ! [X0,X1] : (k8_setfam_1(X0,X1) = k6_setfam_1(X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 0.22/0.51    inference(cnf_transformation,[],[f21])).
% 0.22/0.51  fof(f284,plain,(
% 0.22/0.51    ~spl3_19 | spl3_37),
% 0.22/0.51    inference(avatar_split_clause,[],[f282,f279,f167])).
% 0.22/0.51  fof(f279,plain,(
% 0.22/0.51    spl3_37 <=> m1_subset_1(sK0,k1_zfmisc_1(sK0))),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_37])])).
% 0.22/0.51  fof(f282,plain,(
% 0.22/0.51    ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(sK0))) | spl3_37),
% 0.22/0.51    inference(resolution,[],[f280,f94])).
% 0.22/0.51  fof(f94,plain,(
% 0.22/0.51    ( ! [X0] : (m1_subset_1(X0,k1_zfmisc_1(X0)) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 0.22/0.51    inference(duplicate_literal_removal,[],[f93])).
% 0.22/0.51  fof(f93,plain,(
% 0.22/0.51    ( ! [X0] : (m1_subset_1(X0,k1_zfmisc_1(X0)) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(X0))) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 0.22/0.51    inference(superposition,[],[f36,f41])).
% 0.22/0.51  fof(f36,plain,(
% 0.22/0.51    ( ! [X0,X1] : (m1_subset_1(k8_setfam_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 0.22/0.51    inference(cnf_transformation,[],[f20])).
% 0.22/0.51  fof(f20,plain,(
% 0.22/0.51    ! [X0,X1] : (m1_subset_1(k8_setfam_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 0.22/0.51    inference(ennf_transformation,[],[f6])).
% 0.22/0.51  fof(f6,axiom,(
% 0.22/0.51    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => m1_subset_1(k8_setfam_1(X0,X1),k1_zfmisc_1(X0)))),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k8_setfam_1)).
% 0.22/0.51  fof(f280,plain,(
% 0.22/0.51    ~m1_subset_1(sK0,k1_zfmisc_1(sK0)) | spl3_37),
% 0.22/0.51    inference(avatar_component_clause,[],[f279])).
% 0.22/0.51  fof(f281,plain,(
% 0.22/0.51    ~spl3_37 | spl3_36),
% 0.22/0.51    inference(avatar_split_clause,[],[f277,f274,f279])).
% 0.22/0.51  fof(f274,plain,(
% 0.22/0.51    spl3_36 <=> r1_tarski(sK0,sK0)),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_36])])).
% 0.22/0.51  fof(f277,plain,(
% 0.22/0.51    ~m1_subset_1(sK0,k1_zfmisc_1(sK0)) | spl3_36),
% 0.22/0.51    inference(resolution,[],[f275,f39])).
% 0.22/0.51  fof(f39,plain,(
% 0.22/0.51    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 0.22/0.51    inference(cnf_transformation,[],[f25])).
% 0.22/0.51  fof(f275,plain,(
% 0.22/0.51    ~r1_tarski(sK0,sK0) | spl3_36),
% 0.22/0.51    inference(avatar_component_clause,[],[f274])).
% 0.22/0.51  fof(f276,plain,(
% 0.22/0.51    ~spl3_19 | ~spl3_36 | spl3_33),
% 0.22/0.51    inference(avatar_split_clause,[],[f272,f259,f274,f167])).
% 0.22/0.51  fof(f272,plain,(
% 0.22/0.51    ~r1_tarski(sK0,sK0) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(sK0))) | spl3_33),
% 0.22/0.51    inference(superposition,[],[f260,f41])).
% 0.22/0.51  fof(f260,plain,(
% 0.22/0.51    ~r1_tarski(k8_setfam_1(sK0,k1_xboole_0),sK0) | spl3_33),
% 0.22/0.51    inference(avatar_component_clause,[],[f259])).
% 0.22/0.51  fof(f221,plain,(
% 0.22/0.51    ~spl3_3 | spl3_24 | ~spl3_21),
% 0.22/0.51    inference(avatar_split_clause,[],[f207,f181,f193,f51])).
% 0.22/0.51  fof(f51,plain,(
% 0.22/0.51    spl3_3 <=> m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0)))),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.22/0.51  fof(f193,plain,(
% 0.22/0.51    spl3_24 <=> m1_subset_1(k1_setfam_1(sK2),k1_zfmisc_1(sK0))),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_24])])).
% 0.22/0.51  fof(f207,plain,(
% 0.22/0.51    m1_subset_1(k1_setfam_1(sK2),k1_zfmisc_1(sK0)) | ~m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0))) | ~spl3_21),
% 0.22/0.51    inference(superposition,[],[f36,f182])).
% 0.22/0.51  fof(f195,plain,(
% 0.22/0.51    ~spl3_24 | spl3_20 | ~spl3_21),
% 0.22/0.51    inference(avatar_split_clause,[],[f191,f181,f170,f193])).
% 0.22/0.51  fof(f170,plain,(
% 0.22/0.51    spl3_20 <=> r1_tarski(k8_setfam_1(sK0,sK2),sK0)),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_20])])).
% 0.22/0.51  fof(f191,plain,(
% 0.22/0.51    ~m1_subset_1(k1_setfam_1(sK2),k1_zfmisc_1(sK0)) | (spl3_20 | ~spl3_21)),
% 0.22/0.51    inference(forward_demodulation,[],[f190,f182])).
% 0.22/0.51  fof(f190,plain,(
% 0.22/0.51    ~m1_subset_1(k8_setfam_1(sK0,sK2),k1_zfmisc_1(sK0)) | spl3_20),
% 0.22/0.51    inference(resolution,[],[f171,f39])).
% 0.22/0.51  fof(f171,plain,(
% 0.22/0.51    ~r1_tarski(k8_setfam_1(sK0,sK2),sK0) | spl3_20),
% 0.22/0.51    inference(avatar_component_clause,[],[f170])).
% 0.22/0.51  fof(f186,plain,(
% 0.22/0.51    spl3_21 | spl3_22 | ~spl3_3),
% 0.22/0.51    inference(avatar_split_clause,[],[f174,f51,f184,f181])).
% 0.22/0.51  fof(f174,plain,(
% 0.22/0.51    k1_xboole_0 = sK2 | k8_setfam_1(sK0,sK2) = k1_setfam_1(sK2) | ~spl3_3),
% 0.22/0.51    inference(resolution,[],[f102,f52])).
% 0.22/0.51  fof(f52,plain,(
% 0.22/0.51    m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0))) | ~spl3_3),
% 0.22/0.51    inference(avatar_component_clause,[],[f51])).
% 0.22/0.51  fof(f172,plain,(
% 0.22/0.51    ~spl3_19 | ~spl3_20 | spl3_17),
% 0.22/0.51    inference(avatar_split_clause,[],[f165,f157,f170,f167])).
% 0.22/0.51  fof(f157,plain,(
% 0.22/0.51    spl3_17 <=> r1_tarski(k8_setfam_1(sK0,sK2),k8_setfam_1(sK0,k1_xboole_0))),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_17])])).
% 0.22/0.51  fof(f165,plain,(
% 0.22/0.51    ~r1_tarski(k8_setfam_1(sK0,sK2),sK0) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(sK0))) | spl3_17),
% 0.22/0.51    inference(superposition,[],[f158,f41])).
% 0.22/0.51  fof(f158,plain,(
% 0.22/0.51    ~r1_tarski(k8_setfam_1(sK0,sK2),k8_setfam_1(sK0,k1_xboole_0)) | spl3_17),
% 0.22/0.51    inference(avatar_component_clause,[],[f157])).
% 0.22/0.51  fof(f163,plain,(
% 0.22/0.51    ~spl3_18 | spl3_5 | ~spl3_13),
% 0.22/0.51    inference(avatar_split_clause,[],[f152,f137,f60,f161])).
% 0.22/0.51  fof(f60,plain,(
% 0.22/0.51    spl3_5 <=> m1_subset_1(k8_setfam_1(sK0,sK2),k1_zfmisc_1(k8_setfam_1(sK0,sK1)))),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 0.22/0.51  fof(f152,plain,(
% 0.22/0.51    ~m1_subset_1(k8_setfam_1(sK0,sK2),k1_zfmisc_1(k8_setfam_1(sK0,k1_xboole_0))) | (spl3_5 | ~spl3_13)),
% 0.22/0.51    inference(superposition,[],[f61,f138])).
% 0.22/0.51  fof(f138,plain,(
% 0.22/0.51    k1_xboole_0 = sK1 | ~spl3_13),
% 0.22/0.51    inference(avatar_component_clause,[],[f137])).
% 0.22/0.51  fof(f61,plain,(
% 0.22/0.51    ~m1_subset_1(k8_setfam_1(sK0,sK2),k1_zfmisc_1(k8_setfam_1(sK0,sK1))) | spl3_5),
% 0.22/0.51    inference(avatar_component_clause,[],[f60])).
% 0.22/0.51  % (20024)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.22/0.52  % (20009)Refutation not found, incomplete strategy% (20009)------------------------------
% 0.22/0.52  % (20009)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.52  % (20009)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.52  
% 0.22/0.52  % (20009)Memory used [KB]: 6396
% 0.22/0.52  % (20009)Time elapsed: 0.074 s
% 0.22/0.52  % (20009)------------------------------
% 0.22/0.52  % (20009)------------------------------
% 0.22/0.52  % (20016)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.22/0.53  fof(f159,plain,(
% 0.22/0.53    ~spl3_17 | spl3_1 | ~spl3_13),
% 0.22/0.53    inference(avatar_split_clause,[],[f149,f137,f43,f157])).
% 0.22/0.53  % (20014)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.22/0.53  fof(f149,plain,(
% 0.22/0.53    ~r1_tarski(k8_setfam_1(sK0,sK2),k8_setfam_1(sK0,k1_xboole_0)) | (spl3_1 | ~spl3_13)),
% 0.22/0.53    inference(superposition,[],[f44,f138])).
% 0.22/0.53  fof(f70,plain,(
% 0.22/0.53    spl3_6 | ~spl3_2),
% 0.22/0.53    inference(avatar_split_clause,[],[f64,f47,f68])).
% 0.22/0.53  fof(f64,plain,(
% 0.22/0.53    sK2 = k2_xboole_0(sK1,sK2) | ~spl3_2),
% 0.22/0.53    inference(resolution,[],[f33,f48])).
% 0.22/0.53  fof(f48,plain,(
% 0.22/0.53    r1_tarski(sK1,sK2) | ~spl3_2),
% 0.22/0.53    inference(avatar_component_clause,[],[f47])).
% 0.22/0.53  fof(f62,plain,(
% 0.22/0.53    ~spl3_5 | spl3_1),
% 0.22/0.53    inference(avatar_split_clause,[],[f58,f43,f60])).
% 0.22/0.53  fof(f58,plain,(
% 0.22/0.53    ~m1_subset_1(k8_setfam_1(sK0,sK2),k1_zfmisc_1(k8_setfam_1(sK0,sK1))) | spl3_1),
% 0.22/0.53    inference(resolution,[],[f39,f44])).
% 0.22/0.53  fof(f57,plain,(
% 0.22/0.53    spl3_4),
% 0.22/0.53    inference(avatar_split_clause,[],[f26,f55])).
% 0.22/0.53  fof(f26,plain,(
% 0.22/0.53    m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0)))),
% 0.22/0.53    inference(cnf_transformation,[],[f24])).
% 0.22/0.53  fof(f24,plain,(
% 0.22/0.53    (~r1_tarski(k8_setfam_1(sK0,sK2),k8_setfam_1(sK0,sK1)) & r1_tarski(sK1,sK2) & m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0)))) & m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0)))),
% 0.22/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f15,f23,f22])).
% 0.22/0.53  fof(f22,plain,(
% 0.22/0.53    ? [X0,X1] : (? [X2] : (~r1_tarski(k8_setfam_1(X0,X2),k8_setfam_1(X0,X1)) & r1_tarski(X1,X2) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) => (? [X2] : (~r1_tarski(k8_setfam_1(sK0,X2),k8_setfam_1(sK0,sK1)) & r1_tarski(sK1,X2) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(sK0)))) & m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0))))),
% 0.22/0.53    introduced(choice_axiom,[])).
% 0.22/0.53  fof(f23,plain,(
% 0.22/0.53    ? [X2] : (~r1_tarski(k8_setfam_1(sK0,X2),k8_setfam_1(sK0,sK1)) & r1_tarski(sK1,X2) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(sK0)))) => (~r1_tarski(k8_setfam_1(sK0,sK2),k8_setfam_1(sK0,sK1)) & r1_tarski(sK1,sK2) & m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0))))),
% 0.22/0.53    introduced(choice_axiom,[])).
% 0.22/0.53  fof(f15,plain,(
% 0.22/0.53    ? [X0,X1] : (? [X2] : (~r1_tarski(k8_setfam_1(X0,X2),k8_setfam_1(X0,X1)) & r1_tarski(X1,X2) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 0.22/0.53    inference(flattening,[],[f14])).
% 0.22/0.53  fof(f14,plain,(
% 0.22/0.53    ? [X0,X1] : (? [X2] : ((~r1_tarski(k8_setfam_1(X0,X2),k8_setfam_1(X0,X1)) & r1_tarski(X1,X2)) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 0.22/0.53    inference(ennf_transformation,[],[f12])).
% 0.22/0.53  fof(f12,negated_conjecture,(
% 0.22/0.53    ~! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) => (r1_tarski(X1,X2) => r1_tarski(k8_setfam_1(X0,X2),k8_setfam_1(X0,X1)))))),
% 0.22/0.53    inference(negated_conjecture,[],[f11])).
% 0.22/0.53  fof(f11,conjecture,(
% 0.22/0.53    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) => (r1_tarski(X1,X2) => r1_tarski(k8_setfam_1(X0,X2),k8_setfam_1(X0,X1)))))),
% 0.22/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t59_setfam_1)).
% 0.22/0.53  fof(f53,plain,(
% 0.22/0.53    spl3_3),
% 0.22/0.53    inference(avatar_split_clause,[],[f27,f51])).
% 0.22/0.53  fof(f27,plain,(
% 0.22/0.53    m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0)))),
% 0.22/0.53    inference(cnf_transformation,[],[f24])).
% 0.22/0.53  fof(f49,plain,(
% 0.22/0.53    spl3_2),
% 0.22/0.53    inference(avatar_split_clause,[],[f28,f47])).
% 0.22/0.53  fof(f28,plain,(
% 0.22/0.53    r1_tarski(sK1,sK2)),
% 0.22/0.53    inference(cnf_transformation,[],[f24])).
% 0.22/0.53  fof(f45,plain,(
% 0.22/0.53    ~spl3_1),
% 0.22/0.53    inference(avatar_split_clause,[],[f29,f43])).
% 0.22/0.53  fof(f29,plain,(
% 0.22/0.53    ~r1_tarski(k8_setfam_1(sK0,sK2),k8_setfam_1(sK0,sK1))),
% 0.22/0.53    inference(cnf_transformation,[],[f24])).
% 0.22/0.53  % SZS output end Proof for theBenchmark
% 0.22/0.53  % (20015)------------------------------
% 0.22/0.53  % (20015)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.53  % (20015)Termination reason: Refutation
% 0.22/0.53  
% 0.22/0.53  % (20015)Memory used [KB]: 10874
% 0.22/0.53  % (20015)Time elapsed: 0.087 s
% 0.22/0.53  % (20015)------------------------------
% 0.22/0.53  % (20015)------------------------------
% 0.22/0.53  % (20008)Success in time 0.16 s
%------------------------------------------------------------------------------
