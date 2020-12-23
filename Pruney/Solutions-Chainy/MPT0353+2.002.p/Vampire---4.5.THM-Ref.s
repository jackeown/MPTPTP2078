%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:44:20 EST 2020

% Result     : Theorem 1.67s
% Output     : Refutation 1.67s
% Verified   : 
% Statistics : Number of formulae       :   87 ( 143 expanded)
%              Number of leaves         :   22 (  58 expanded)
%              Depth                    :    9
%              Number of atoms          :  195 ( 325 expanded)
%              Number of equality atoms :   64 (  98 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1020,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f47,f52,f57,f90,f104,f199,f471,f476,f787,f947,f1018,f1019])).

fof(f1019,plain,
    ( sK2 != k3_xboole_0(sK0,sK2)
    | k3_xboole_0(sK1,k3_subset_1(sK0,sK2)) != k7_subset_1(sK0,sK1,k3_xboole_0(sK0,sK2))
    | k7_subset_1(sK0,sK1,sK2) = k3_xboole_0(sK1,k3_subset_1(sK0,sK2)) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f1018,plain,
    ( spl4_26
    | spl4_25 ),
    inference(avatar_split_clause,[],[f1014,f940,f944])).

fof(f944,plain,
    ( spl4_26
  <=> sK2 = k3_xboole_0(sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_26])])).

fof(f940,plain,
    ( spl4_25
  <=> r2_hidden(sK3(sK0,sK2,sK2),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_25])])).

fof(f1014,plain,
    ( sK2 = k3_xboole_0(sK0,sK2)
    | spl4_25 ),
    inference(resolution,[],[f942,f139])).

fof(f139,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK3(X0,X1,X1),X1)
      | k3_xboole_0(X0,X1) = X1 ) ),
    inference(factoring,[],[f34])).

fof(f34,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK3(X0,X1,X2),X1)
      | r2_hidden(sK3(X0,X1,X2),X2)
      | k3_xboole_0(X0,X1) = X2 ) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_xboole_0)).

fof(f942,plain,
    ( ~ r2_hidden(sK3(sK0,sK2,sK2),sK2)
    | spl4_25 ),
    inference(avatar_component_clause,[],[f940])).

fof(f947,plain,
    ( ~ spl4_25
    | spl4_26
    | ~ spl4_3 ),
    inference(avatar_split_clause,[],[f938,f54,f944,f940])).

fof(f54,plain,
    ( spl4_3
  <=> m1_subset_1(sK2,k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f938,plain,
    ( sK2 = k3_xboole_0(sK0,sK2)
    | ~ r2_hidden(sK3(sK0,sK2,sK2),sK2)
    | ~ spl4_3 ),
    inference(duplicate_literal_removal,[],[f934])).

fof(f934,plain,
    ( sK2 = k3_xboole_0(sK0,sK2)
    | ~ r2_hidden(sK3(sK0,sK2,sK2),sK2)
    | ~ r2_hidden(sK3(sK0,sK2,sK2),sK2)
    | sK2 = k3_xboole_0(sK0,sK2)
    | ~ spl4_3 ),
    inference(resolution,[],[f219,f32])).

fof(f32,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(sK3(X0,X1,X2),X0)
      | ~ r2_hidden(sK3(X0,X1,X2),X1)
      | ~ r2_hidden(sK3(X0,X1,X2),X2)
      | k3_xboole_0(X0,X1) = X2 ) ),
    inference(cnf_transformation,[],[f2])).

fof(f219,plain,
    ( ! [X13] :
        ( r2_hidden(sK3(X13,sK2,sK2),sK0)
        | sK2 = k3_xboole_0(X13,sK2) )
    | ~ spl4_3 ),
    inference(resolution,[],[f139,f65])).

fof(f65,plain,
    ( ! [X1] :
        ( ~ r2_hidden(X1,sK2)
        | r2_hidden(X1,sK0) )
    | ~ spl4_3 ),
    inference(resolution,[],[f27,f56])).

fof(f56,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(sK0))
    | ~ spl4_3 ),
    inference(avatar_component_clause,[],[f54])).

fof(f27,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ r2_hidden(X2,X1)
      | r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
          | ~ r2_hidden(X2,X1) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( r2_hidden(X2,X1)
         => r2_hidden(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_subset_1)).

fof(f787,plain,
    ( spl4_24
    | ~ spl4_1
    | ~ spl4_6
    | ~ spl4_13 ),
    inference(avatar_split_clause,[],[f786,f468,f101,f44,f749])).

fof(f749,plain,
    ( spl4_24
  <=> k3_xboole_0(sK1,k3_subset_1(sK0,sK2)) = k7_subset_1(sK0,sK1,k3_xboole_0(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_24])])).

fof(f44,plain,
    ( spl4_1
  <=> m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f101,plain,
    ( spl4_6
  <=> k3_subset_1(sK0,sK2) = k5_xboole_0(sK0,k3_xboole_0(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).

fof(f468,plain,
    ( spl4_13
  <=> sK1 = k3_xboole_0(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_13])])).

fof(f786,plain,
    ( k3_xboole_0(sK1,k3_subset_1(sK0,sK2)) = k7_subset_1(sK0,sK1,k3_xboole_0(sK0,sK2))
    | ~ spl4_1
    | ~ spl4_6
    | ~ spl4_13 ),
    inference(forward_demodulation,[],[f755,f24])).

fof(f24,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f755,plain,
    ( k3_xboole_0(k3_subset_1(sK0,sK2),sK1) = k7_subset_1(sK0,sK1,k3_xboole_0(sK0,sK2))
    | ~ spl4_1
    | ~ spl4_6
    | ~ spl4_13 ),
    inference(superposition,[],[f548,f103])).

fof(f103,plain,
    ( k3_subset_1(sK0,sK2) = k5_xboole_0(sK0,k3_xboole_0(sK0,sK2))
    | ~ spl4_6 ),
    inference(avatar_component_clause,[],[f101])).

fof(f548,plain,
    ( ! [X6] : k3_xboole_0(k5_xboole_0(sK0,X6),sK1) = k7_subset_1(sK0,sK1,X6)
    | ~ spl4_1
    | ~ spl4_13 ),
    inference(forward_demodulation,[],[f518,f105])).

fof(f105,plain,
    ( ! [X0] : k7_subset_1(sK0,sK1,X0) = k5_xboole_0(sK1,k3_xboole_0(sK1,X0))
    | ~ spl4_1 ),
    inference(resolution,[],[f39,f46])).

fof(f46,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(sK0))
    | ~ spl4_1 ),
    inference(avatar_component_clause,[],[f44])).

fof(f39,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k7_subset_1(X0,X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ) ),
    inference(definition_unfolding,[],[f29,f25])).

fof(f25,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f29,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

fof(f518,plain,
    ( ! [X6] : k3_xboole_0(k5_xboole_0(sK0,X6),sK1) = k5_xboole_0(sK1,k3_xboole_0(sK1,X6))
    | ~ spl4_13 ),
    inference(superposition,[],[f72,f470])).

fof(f470,plain,
    ( sK1 = k3_xboole_0(sK0,sK1)
    | ~ spl4_13 ),
    inference(avatar_component_clause,[],[f468])).

fof(f72,plain,(
    ! [X4,X2,X3] : k3_xboole_0(k5_xboole_0(X4,X2),X3) = k5_xboole_0(k3_xboole_0(X4,X3),k3_xboole_0(X3,X2)) ),
    inference(superposition,[],[f28,f24])).

fof(f28,plain,(
    ! [X2,X0,X1] : k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X2,X1)) = k3_xboole_0(k5_xboole_0(X0,X2),X1) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] : k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X2,X1)) = k3_xboole_0(k5_xboole_0(X0,X2),X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t112_xboole_1)).

fof(f476,plain,
    ( spl4_13
    | spl4_12 ),
    inference(avatar_split_clause,[],[f472,f464,f468])).

fof(f464,plain,
    ( spl4_12
  <=> r2_hidden(sK3(sK0,sK1,sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).

fof(f472,plain,
    ( sK1 = k3_xboole_0(sK0,sK1)
    | spl4_12 ),
    inference(resolution,[],[f466,f139])).

fof(f466,plain,
    ( ~ r2_hidden(sK3(sK0,sK1,sK1),sK1)
    | spl4_12 ),
    inference(avatar_component_clause,[],[f464])).

fof(f471,plain,
    ( ~ spl4_12
    | spl4_13
    | ~ spl4_1 ),
    inference(avatar_split_clause,[],[f462,f44,f468,f464])).

fof(f462,plain,
    ( sK1 = k3_xboole_0(sK0,sK1)
    | ~ r2_hidden(sK3(sK0,sK1,sK1),sK1)
    | ~ spl4_1 ),
    inference(duplicate_literal_removal,[],[f460])).

fof(f460,plain,
    ( sK1 = k3_xboole_0(sK0,sK1)
    | ~ r2_hidden(sK3(sK0,sK1,sK1),sK1)
    | ~ r2_hidden(sK3(sK0,sK1,sK1),sK1)
    | sK1 = k3_xboole_0(sK0,sK1)
    | ~ spl4_1 ),
    inference(resolution,[],[f218,f32])).

fof(f218,plain,
    ( ! [X12] :
        ( r2_hidden(sK3(X12,sK1,sK1),sK0)
        | sK1 = k3_xboole_0(X12,sK1) )
    | ~ spl4_1 ),
    inference(resolution,[],[f139,f64])).

fof(f64,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,sK1)
        | r2_hidden(X0,sK0) )
    | ~ spl4_1 ),
    inference(resolution,[],[f27,f46])).

fof(f199,plain,
    ( ~ spl4_11
    | spl4_4 ),
    inference(avatar_split_clause,[],[f193,f87,f195])).

fof(f195,plain,
    ( spl4_11
  <=> k7_subset_1(sK0,sK1,sK2) = k3_xboole_0(sK1,k3_subset_1(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).

fof(f87,plain,
    ( spl4_4
  <=> k7_subset_1(sK0,sK1,sK2) = k3_xboole_0(k3_subset_1(sK0,sK2),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f193,plain,
    ( k7_subset_1(sK0,sK1,sK2) != k3_xboole_0(sK1,k3_subset_1(sK0,sK2))
    | spl4_4 ),
    inference(superposition,[],[f89,f24])).

fof(f89,plain,
    ( k7_subset_1(sK0,sK1,sK2) != k3_xboole_0(k3_subset_1(sK0,sK2),sK1)
    | spl4_4 ),
    inference(avatar_component_clause,[],[f87])).

fof(f104,plain,
    ( spl4_6
    | ~ spl4_3 ),
    inference(avatar_split_clause,[],[f94,f54,f101])).

fof(f94,plain,
    ( k3_subset_1(sK0,sK2) = k5_xboole_0(sK0,k3_xboole_0(sK0,sK2))
    | ~ spl4_3 ),
    inference(resolution,[],[f38,f56])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k3_subset_1(X0,X1) ) ),
    inference(definition_unfolding,[],[f26,f25])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

fof(f90,plain,
    ( ~ spl4_4
    | ~ spl4_1
    | spl4_2 ),
    inference(avatar_split_clause,[],[f84,f49,f44,f87])).

fof(f49,plain,
    ( spl4_2
  <=> k7_subset_1(sK0,sK1,sK2) = k9_subset_1(sK0,sK1,k3_subset_1(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f84,plain,
    ( k7_subset_1(sK0,sK1,sK2) != k3_xboole_0(k3_subset_1(sK0,sK2),sK1)
    | ~ spl4_1
    | spl4_2 ),
    inference(superposition,[],[f51,f81])).

fof(f81,plain,
    ( ! [X0] : k3_xboole_0(X0,sK1) = k9_subset_1(sK0,sK1,X0)
    | ~ spl4_1 ),
    inference(forward_demodulation,[],[f79,f66])).

fof(f66,plain,
    ( ! [X0] : k9_subset_1(sK0,X0,sK1) = k3_xboole_0(X0,sK1)
    | ~ spl4_1 ),
    inference(resolution,[],[f30,f46])).

fof(f30,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

fof(f79,plain,
    ( ! [X0] : k9_subset_1(sK0,X0,sK1) = k9_subset_1(sK0,sK1,X0)
    | ~ spl4_1 ),
    inference(resolution,[],[f31,f46])).

fof(f31,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | k9_subset_1(X0,X1,X2) = k9_subset_1(X0,X2,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( k9_subset_1(X0,X1,X2) = k9_subset_1(X0,X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k9_subset_1(X0,X1,X2) = k9_subset_1(X0,X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k9_subset_1)).

fof(f51,plain,
    ( k7_subset_1(sK0,sK1,sK2) != k9_subset_1(sK0,sK1,k3_subset_1(sK0,sK2))
    | spl4_2 ),
    inference(avatar_component_clause,[],[f49])).

fof(f57,plain,(
    spl4_3 ),
    inference(avatar_split_clause,[],[f20,f54])).

fof(f20,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( k7_subset_1(X0,X1,X2) != k9_subset_1(X0,X1,k3_subset_1(X0,X2))
          & m1_subset_1(X2,k1_zfmisc_1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(X0))
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(X0))
           => k7_subset_1(X0,X1,X2) = k9_subset_1(X0,X1,k3_subset_1(X0,X2)) ) ) ),
    inference(negated_conjecture,[],[f11])).

fof(f11,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X0))
         => k7_subset_1(X0,X1,X2) = k9_subset_1(X0,X1,k3_subset_1(X0,X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t32_subset_1)).

fof(f52,plain,(
    ~ spl4_2 ),
    inference(avatar_split_clause,[],[f21,f49])).

fof(f21,plain,(
    k7_subset_1(sK0,sK1,sK2) != k9_subset_1(sK0,sK1,k3_subset_1(sK0,sK2)) ),
    inference(cnf_transformation,[],[f14])).

fof(f47,plain,(
    spl4_1 ),
    inference(avatar_split_clause,[],[f22,f44])).

fof(f22,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f14])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n008.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 17:25:00 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.48  % (30800)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.50  % (30798)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.21/0.50  % (30814)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.21/0.50  % (30792)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.50  % (30792)Refutation not found, incomplete strategy% (30792)------------------------------
% 0.21/0.50  % (30792)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  % (30792)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.50  
% 0.21/0.50  % (30792)Memory used [KB]: 6268
% 0.21/0.50  % (30792)Time elapsed: 0.096 s
% 0.21/0.50  % (30792)------------------------------
% 0.21/0.50  % (30792)------------------------------
% 0.21/0.51  % (30809)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.21/0.51  % (30806)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.21/0.51  % (30798)Refutation not found, incomplete strategy% (30798)------------------------------
% 0.21/0.51  % (30798)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (30798)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.51  
% 0.21/0.51  % (30798)Memory used [KB]: 10618
% 0.21/0.51  % (30798)Time elapsed: 0.104 s
% 0.21/0.51  % (30798)------------------------------
% 0.21/0.51  % (30798)------------------------------
% 0.21/0.51  % (30801)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.21/0.51  % (30799)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.21/0.52  % (30810)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.21/0.52  % (30790)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.53  % (30790)Refutation not found, incomplete strategy% (30790)------------------------------
% 0.21/0.53  % (30790)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (30790)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (30790)Memory used [KB]: 10746
% 0.21/0.53  % (30790)Time elapsed: 0.116 s
% 0.21/0.53  % (30790)------------------------------
% 0.21/0.53  % (30790)------------------------------
% 0.21/0.53  % (30788)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.21/0.53  % (30788)Refutation not found, incomplete strategy% (30788)------------------------------
% 0.21/0.53  % (30788)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (30788)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (30788)Memory used [KB]: 1663
% 0.21/0.53  % (30788)Time elapsed: 0.116 s
% 0.21/0.53  % (30788)------------------------------
% 0.21/0.53  % (30788)------------------------------
% 0.21/0.53  % (30789)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.21/0.53  % (30793)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.21/0.53  % (30791)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.21/0.53  % (30811)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.21/0.53  % (30812)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.21/0.53  % (30802)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.21/0.54  % (30805)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.21/0.54  % (30804)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.21/0.54  % (30799)Refutation not found, incomplete strategy% (30799)------------------------------
% 0.21/0.54  % (30799)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (30799)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (30799)Memory used [KB]: 10618
% 0.21/0.54  % (30799)Time elapsed: 0.126 s
% 0.21/0.54  % (30799)------------------------------
% 0.21/0.54  % (30799)------------------------------
% 0.21/0.54  % (30805)Refutation not found, incomplete strategy% (30805)------------------------------
% 0.21/0.54  % (30805)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (30805)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (30805)Memory used [KB]: 10618
% 0.21/0.54  % (30805)Time elapsed: 0.128 s
% 0.21/0.54  % (30805)------------------------------
% 0.21/0.54  % (30805)------------------------------
% 0.21/0.54  % (30813)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.21/0.54  % (30803)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.21/0.54  % (30817)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.21/0.54  % (30810)Refutation not found, incomplete strategy% (30810)------------------------------
% 0.21/0.54  % (30810)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (30808)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.21/0.54  % (30794)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.21/0.54  % (30796)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.21/0.54  % (30815)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.21/0.54  % (30795)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.21/0.55  % (30810)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.55  
% 0.21/0.55  % (30810)Memory used [KB]: 10746
% 0.21/0.55  % (30810)Time elapsed: 0.105 s
% 0.21/0.55  % (30810)------------------------------
% 0.21/0.55  % (30810)------------------------------
% 1.56/0.56  % (30807)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 1.56/0.56  % (30797)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 1.56/0.56  % (30816)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 1.56/0.57  % (30797)Refutation not found, incomplete strategy% (30797)------------------------------
% 1.56/0.57  % (30797)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.67/0.57  % (30797)Termination reason: Refutation not found, incomplete strategy
% 1.67/0.57  
% 1.67/0.57  % (30797)Memory used [KB]: 10746
% 1.67/0.57  % (30797)Time elapsed: 0.161 s
% 1.67/0.57  % (30797)------------------------------
% 1.67/0.57  % (30797)------------------------------
% 1.67/0.60  % (30804)Refutation found. Thanks to Tanya!
% 1.67/0.60  % SZS status Theorem for theBenchmark
% 1.67/0.62  % SZS output start Proof for theBenchmark
% 1.67/0.62  fof(f1020,plain,(
% 1.67/0.62    $false),
% 1.67/0.62    inference(avatar_sat_refutation,[],[f47,f52,f57,f90,f104,f199,f471,f476,f787,f947,f1018,f1019])).
% 1.67/0.62  fof(f1019,plain,(
% 1.67/0.62    sK2 != k3_xboole_0(sK0,sK2) | k3_xboole_0(sK1,k3_subset_1(sK0,sK2)) != k7_subset_1(sK0,sK1,k3_xboole_0(sK0,sK2)) | k7_subset_1(sK0,sK1,sK2) = k3_xboole_0(sK1,k3_subset_1(sK0,sK2))),
% 1.67/0.62    introduced(theory_tautology_sat_conflict,[])).
% 1.67/0.62  fof(f1018,plain,(
% 1.67/0.62    spl4_26 | spl4_25),
% 1.67/0.62    inference(avatar_split_clause,[],[f1014,f940,f944])).
% 1.67/0.62  fof(f944,plain,(
% 1.67/0.62    spl4_26 <=> sK2 = k3_xboole_0(sK0,sK2)),
% 1.67/0.62    introduced(avatar_definition,[new_symbols(naming,[spl4_26])])).
% 1.67/0.62  fof(f940,plain,(
% 1.67/0.62    spl4_25 <=> r2_hidden(sK3(sK0,sK2,sK2),sK2)),
% 1.67/0.62    introduced(avatar_definition,[new_symbols(naming,[spl4_25])])).
% 1.67/0.62  fof(f1014,plain,(
% 1.67/0.62    sK2 = k3_xboole_0(sK0,sK2) | spl4_25),
% 1.67/0.62    inference(resolution,[],[f942,f139])).
% 1.67/0.62  fof(f139,plain,(
% 1.67/0.62    ( ! [X0,X1] : (r2_hidden(sK3(X0,X1,X1),X1) | k3_xboole_0(X0,X1) = X1) )),
% 1.67/0.62    inference(factoring,[],[f34])).
% 1.67/0.62  fof(f34,plain,(
% 1.67/0.62    ( ! [X2,X0,X1] : (r2_hidden(sK3(X0,X1,X2),X1) | r2_hidden(sK3(X0,X1,X2),X2) | k3_xboole_0(X0,X1) = X2) )),
% 1.67/0.62    inference(cnf_transformation,[],[f2])).
% 1.67/0.62  fof(f2,axiom,(
% 1.67/0.62    ! [X0,X1,X2] : (k3_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 1.67/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_xboole_0)).
% 1.67/0.62  fof(f942,plain,(
% 1.67/0.62    ~r2_hidden(sK3(sK0,sK2,sK2),sK2) | spl4_25),
% 1.67/0.62    inference(avatar_component_clause,[],[f940])).
% 1.67/0.62  fof(f947,plain,(
% 1.67/0.62    ~spl4_25 | spl4_26 | ~spl4_3),
% 1.67/0.62    inference(avatar_split_clause,[],[f938,f54,f944,f940])).
% 1.67/0.62  fof(f54,plain,(
% 1.67/0.62    spl4_3 <=> m1_subset_1(sK2,k1_zfmisc_1(sK0))),
% 1.67/0.62    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 1.67/0.62  fof(f938,plain,(
% 1.67/0.62    sK2 = k3_xboole_0(sK0,sK2) | ~r2_hidden(sK3(sK0,sK2,sK2),sK2) | ~spl4_3),
% 1.67/0.62    inference(duplicate_literal_removal,[],[f934])).
% 1.67/0.62  fof(f934,plain,(
% 1.67/0.62    sK2 = k3_xboole_0(sK0,sK2) | ~r2_hidden(sK3(sK0,sK2,sK2),sK2) | ~r2_hidden(sK3(sK0,sK2,sK2),sK2) | sK2 = k3_xboole_0(sK0,sK2) | ~spl4_3),
% 1.67/0.62    inference(resolution,[],[f219,f32])).
% 1.67/0.62  fof(f32,plain,(
% 1.67/0.62    ( ! [X2,X0,X1] : (~r2_hidden(sK3(X0,X1,X2),X0) | ~r2_hidden(sK3(X0,X1,X2),X1) | ~r2_hidden(sK3(X0,X1,X2),X2) | k3_xboole_0(X0,X1) = X2) )),
% 1.67/0.62    inference(cnf_transformation,[],[f2])).
% 1.67/0.62  fof(f219,plain,(
% 1.67/0.62    ( ! [X13] : (r2_hidden(sK3(X13,sK2,sK2),sK0) | sK2 = k3_xboole_0(X13,sK2)) ) | ~spl4_3),
% 1.67/0.62    inference(resolution,[],[f139,f65])).
% 1.67/0.62  fof(f65,plain,(
% 1.67/0.62    ( ! [X1] : (~r2_hidden(X1,sK2) | r2_hidden(X1,sK0)) ) | ~spl4_3),
% 1.67/0.62    inference(resolution,[],[f27,f56])).
% 1.67/0.62  fof(f56,plain,(
% 1.67/0.62    m1_subset_1(sK2,k1_zfmisc_1(sK0)) | ~spl4_3),
% 1.67/0.62    inference(avatar_component_clause,[],[f54])).
% 1.67/0.62  fof(f27,plain,(
% 1.67/0.62    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~r2_hidden(X2,X1) | r2_hidden(X2,X0)) )),
% 1.67/0.62    inference(cnf_transformation,[],[f16])).
% 1.67/0.62  fof(f16,plain,(
% 1.67/0.62    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) | ~r2_hidden(X2,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.67/0.62    inference(ennf_transformation,[],[f8])).
% 1.67/0.62  fof(f8,axiom,(
% 1.67/0.62    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (r2_hidden(X2,X1) => r2_hidden(X2,X0)))),
% 1.67/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_subset_1)).
% 1.67/0.62  fof(f787,plain,(
% 1.67/0.62    spl4_24 | ~spl4_1 | ~spl4_6 | ~spl4_13),
% 1.67/0.62    inference(avatar_split_clause,[],[f786,f468,f101,f44,f749])).
% 1.67/0.62  fof(f749,plain,(
% 1.67/0.62    spl4_24 <=> k3_xboole_0(sK1,k3_subset_1(sK0,sK2)) = k7_subset_1(sK0,sK1,k3_xboole_0(sK0,sK2))),
% 1.67/0.62    introduced(avatar_definition,[new_symbols(naming,[spl4_24])])).
% 1.67/0.62  fof(f44,plain,(
% 1.67/0.62    spl4_1 <=> m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 1.67/0.62    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 1.67/0.62  fof(f101,plain,(
% 1.67/0.62    spl4_6 <=> k3_subset_1(sK0,sK2) = k5_xboole_0(sK0,k3_xboole_0(sK0,sK2))),
% 1.67/0.62    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).
% 1.67/0.62  fof(f468,plain,(
% 1.67/0.62    spl4_13 <=> sK1 = k3_xboole_0(sK0,sK1)),
% 1.67/0.62    introduced(avatar_definition,[new_symbols(naming,[spl4_13])])).
% 1.67/0.62  fof(f786,plain,(
% 1.67/0.62    k3_xboole_0(sK1,k3_subset_1(sK0,sK2)) = k7_subset_1(sK0,sK1,k3_xboole_0(sK0,sK2)) | (~spl4_1 | ~spl4_6 | ~spl4_13)),
% 1.67/0.62    inference(forward_demodulation,[],[f755,f24])).
% 1.67/0.62  fof(f24,plain,(
% 1.67/0.62    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 1.67/0.62    inference(cnf_transformation,[],[f1])).
% 1.67/0.62  fof(f1,axiom,(
% 1.67/0.62    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 1.67/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 1.67/0.62  fof(f755,plain,(
% 1.67/0.62    k3_xboole_0(k3_subset_1(sK0,sK2),sK1) = k7_subset_1(sK0,sK1,k3_xboole_0(sK0,sK2)) | (~spl4_1 | ~spl4_6 | ~spl4_13)),
% 1.67/0.62    inference(superposition,[],[f548,f103])).
% 1.67/0.62  fof(f103,plain,(
% 1.67/0.62    k3_subset_1(sK0,sK2) = k5_xboole_0(sK0,k3_xboole_0(sK0,sK2)) | ~spl4_6),
% 1.67/0.62    inference(avatar_component_clause,[],[f101])).
% 1.67/0.62  fof(f548,plain,(
% 1.67/0.62    ( ! [X6] : (k3_xboole_0(k5_xboole_0(sK0,X6),sK1) = k7_subset_1(sK0,sK1,X6)) ) | (~spl4_1 | ~spl4_13)),
% 1.67/0.62    inference(forward_demodulation,[],[f518,f105])).
% 1.67/0.62  fof(f105,plain,(
% 1.67/0.62    ( ! [X0] : (k7_subset_1(sK0,sK1,X0) = k5_xboole_0(sK1,k3_xboole_0(sK1,X0))) ) | ~spl4_1),
% 1.67/0.62    inference(resolution,[],[f39,f46])).
% 1.67/0.62  fof(f46,plain,(
% 1.67/0.62    m1_subset_1(sK1,k1_zfmisc_1(sK0)) | ~spl4_1),
% 1.67/0.62    inference(avatar_component_clause,[],[f44])).
% 1.67/0.62  fof(f39,plain,(
% 1.67/0.62    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k7_subset_1(X0,X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2))) )),
% 1.67/0.62    inference(definition_unfolding,[],[f29,f25])).
% 1.67/0.62  fof(f25,plain,(
% 1.67/0.62    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 1.67/0.62    inference(cnf_transformation,[],[f4])).
% 1.67/0.62  fof(f4,axiom,(
% 1.67/0.62    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 1.67/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).
% 1.67/0.62  fof(f29,plain,(
% 1.67/0.62    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)) )),
% 1.67/0.62    inference(cnf_transformation,[],[f17])).
% 1.67/0.62  fof(f17,plain,(
% 1.67/0.62    ! [X0,X1,X2] : (k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.67/0.62    inference(ennf_transformation,[],[f9])).
% 1.67/0.62  fof(f9,axiom,(
% 1.67/0.62    ! [X0,X1,X2] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2))),
% 1.67/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_subset_1)).
% 1.67/0.62  fof(f518,plain,(
% 1.67/0.62    ( ! [X6] : (k3_xboole_0(k5_xboole_0(sK0,X6),sK1) = k5_xboole_0(sK1,k3_xboole_0(sK1,X6))) ) | ~spl4_13),
% 1.67/0.62    inference(superposition,[],[f72,f470])).
% 1.67/0.62  fof(f470,plain,(
% 1.67/0.62    sK1 = k3_xboole_0(sK0,sK1) | ~spl4_13),
% 1.67/0.62    inference(avatar_component_clause,[],[f468])).
% 1.67/0.62  fof(f72,plain,(
% 1.67/0.62    ( ! [X4,X2,X3] : (k3_xboole_0(k5_xboole_0(X4,X2),X3) = k5_xboole_0(k3_xboole_0(X4,X3),k3_xboole_0(X3,X2))) )),
% 1.67/0.62    inference(superposition,[],[f28,f24])).
% 1.67/0.62  fof(f28,plain,(
% 1.67/0.62    ( ! [X2,X0,X1] : (k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X2,X1)) = k3_xboole_0(k5_xboole_0(X0,X2),X1)) )),
% 1.67/0.62    inference(cnf_transformation,[],[f5])).
% 1.67/0.62  fof(f5,axiom,(
% 1.67/0.62    ! [X0,X1,X2] : k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X2,X1)) = k3_xboole_0(k5_xboole_0(X0,X2),X1)),
% 1.67/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t112_xboole_1)).
% 1.67/0.62  fof(f476,plain,(
% 1.67/0.62    spl4_13 | spl4_12),
% 1.67/0.62    inference(avatar_split_clause,[],[f472,f464,f468])).
% 1.67/0.62  fof(f464,plain,(
% 1.67/0.62    spl4_12 <=> r2_hidden(sK3(sK0,sK1,sK1),sK1)),
% 1.67/0.62    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).
% 1.67/0.62  fof(f472,plain,(
% 1.67/0.62    sK1 = k3_xboole_0(sK0,sK1) | spl4_12),
% 1.67/0.62    inference(resolution,[],[f466,f139])).
% 1.67/0.62  fof(f466,plain,(
% 1.67/0.62    ~r2_hidden(sK3(sK0,sK1,sK1),sK1) | spl4_12),
% 1.67/0.62    inference(avatar_component_clause,[],[f464])).
% 1.67/0.62  fof(f471,plain,(
% 1.67/0.62    ~spl4_12 | spl4_13 | ~spl4_1),
% 1.67/0.62    inference(avatar_split_clause,[],[f462,f44,f468,f464])).
% 1.67/0.62  fof(f462,plain,(
% 1.67/0.62    sK1 = k3_xboole_0(sK0,sK1) | ~r2_hidden(sK3(sK0,sK1,sK1),sK1) | ~spl4_1),
% 1.67/0.62    inference(duplicate_literal_removal,[],[f460])).
% 1.67/0.62  fof(f460,plain,(
% 1.67/0.62    sK1 = k3_xboole_0(sK0,sK1) | ~r2_hidden(sK3(sK0,sK1,sK1),sK1) | ~r2_hidden(sK3(sK0,sK1,sK1),sK1) | sK1 = k3_xboole_0(sK0,sK1) | ~spl4_1),
% 1.67/0.62    inference(resolution,[],[f218,f32])).
% 1.67/0.62  fof(f218,plain,(
% 1.67/0.62    ( ! [X12] : (r2_hidden(sK3(X12,sK1,sK1),sK0) | sK1 = k3_xboole_0(X12,sK1)) ) | ~spl4_1),
% 1.67/0.62    inference(resolution,[],[f139,f64])).
% 1.67/0.62  fof(f64,plain,(
% 1.67/0.62    ( ! [X0] : (~r2_hidden(X0,sK1) | r2_hidden(X0,sK0)) ) | ~spl4_1),
% 1.67/0.62    inference(resolution,[],[f27,f46])).
% 1.67/0.62  fof(f199,plain,(
% 1.67/0.62    ~spl4_11 | spl4_4),
% 1.67/0.62    inference(avatar_split_clause,[],[f193,f87,f195])).
% 1.67/0.62  fof(f195,plain,(
% 1.67/0.62    spl4_11 <=> k7_subset_1(sK0,sK1,sK2) = k3_xboole_0(sK1,k3_subset_1(sK0,sK2))),
% 1.67/0.62    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).
% 1.67/0.62  fof(f87,plain,(
% 1.67/0.62    spl4_4 <=> k7_subset_1(sK0,sK1,sK2) = k3_xboole_0(k3_subset_1(sK0,sK2),sK1)),
% 1.67/0.62    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 1.67/0.62  fof(f193,plain,(
% 1.67/0.62    k7_subset_1(sK0,sK1,sK2) != k3_xboole_0(sK1,k3_subset_1(sK0,sK2)) | spl4_4),
% 1.67/0.62    inference(superposition,[],[f89,f24])).
% 1.67/0.62  fof(f89,plain,(
% 1.67/0.62    k7_subset_1(sK0,sK1,sK2) != k3_xboole_0(k3_subset_1(sK0,sK2),sK1) | spl4_4),
% 1.67/0.62    inference(avatar_component_clause,[],[f87])).
% 1.67/0.62  fof(f104,plain,(
% 1.67/0.62    spl4_6 | ~spl4_3),
% 1.67/0.62    inference(avatar_split_clause,[],[f94,f54,f101])).
% 1.67/0.62  fof(f94,plain,(
% 1.67/0.62    k3_subset_1(sK0,sK2) = k5_xboole_0(sK0,k3_xboole_0(sK0,sK2)) | ~spl4_3),
% 1.67/0.62    inference(resolution,[],[f38,f56])).
% 1.67/0.62  fof(f38,plain,(
% 1.67/0.62    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k3_subset_1(X0,X1)) )),
% 1.67/0.62    inference(definition_unfolding,[],[f26,f25])).
% 1.67/0.62  fof(f26,plain,(
% 1.67/0.62    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)) )),
% 1.67/0.62    inference(cnf_transformation,[],[f15])).
% 1.67/0.62  fof(f15,plain,(
% 1.67/0.62    ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.67/0.62    inference(ennf_transformation,[],[f7])).
% 1.67/0.62  fof(f7,axiom,(
% 1.67/0.62    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1))),
% 1.67/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).
% 1.67/0.62  fof(f90,plain,(
% 1.67/0.62    ~spl4_4 | ~spl4_1 | spl4_2),
% 1.67/0.62    inference(avatar_split_clause,[],[f84,f49,f44,f87])).
% 1.67/0.62  fof(f49,plain,(
% 1.67/0.62    spl4_2 <=> k7_subset_1(sK0,sK1,sK2) = k9_subset_1(sK0,sK1,k3_subset_1(sK0,sK2))),
% 1.67/0.62    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 1.67/0.62  fof(f84,plain,(
% 1.67/0.62    k7_subset_1(sK0,sK1,sK2) != k3_xboole_0(k3_subset_1(sK0,sK2),sK1) | (~spl4_1 | spl4_2)),
% 1.67/0.62    inference(superposition,[],[f51,f81])).
% 1.67/0.62  fof(f81,plain,(
% 1.67/0.62    ( ! [X0] : (k3_xboole_0(X0,sK1) = k9_subset_1(sK0,sK1,X0)) ) | ~spl4_1),
% 1.67/0.62    inference(forward_demodulation,[],[f79,f66])).
% 1.67/0.62  fof(f66,plain,(
% 1.67/0.62    ( ! [X0] : (k9_subset_1(sK0,X0,sK1) = k3_xboole_0(X0,sK1)) ) | ~spl4_1),
% 1.67/0.62    inference(resolution,[],[f30,f46])).
% 1.67/0.62  fof(f30,plain,(
% 1.67/0.62    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(X0)) | k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)) )),
% 1.67/0.62    inference(cnf_transformation,[],[f18])).
% 1.67/0.62  fof(f18,plain,(
% 1.67/0.62    ! [X0,X1,X2] : (k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 1.67/0.62    inference(ennf_transformation,[],[f10])).
% 1.67/0.62  fof(f10,axiom,(
% 1.67/0.62    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2))),
% 1.67/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k9_subset_1)).
% 1.67/0.62  fof(f79,plain,(
% 1.67/0.62    ( ! [X0] : (k9_subset_1(sK0,X0,sK1) = k9_subset_1(sK0,sK1,X0)) ) | ~spl4_1),
% 1.67/0.62    inference(resolution,[],[f31,f46])).
% 1.67/0.62  fof(f31,plain,(
% 1.67/0.62    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(X0)) | k9_subset_1(X0,X1,X2) = k9_subset_1(X0,X2,X1)) )),
% 1.67/0.62    inference(cnf_transformation,[],[f19])).
% 1.67/0.62  fof(f19,plain,(
% 1.67/0.62    ! [X0,X1,X2] : (k9_subset_1(X0,X1,X2) = k9_subset_1(X0,X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 1.67/0.62    inference(ennf_transformation,[],[f6])).
% 1.67/0.62  fof(f6,axiom,(
% 1.67/0.62    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => k9_subset_1(X0,X1,X2) = k9_subset_1(X0,X2,X1))),
% 1.67/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k9_subset_1)).
% 1.67/0.62  fof(f51,plain,(
% 1.67/0.62    k7_subset_1(sK0,sK1,sK2) != k9_subset_1(sK0,sK1,k3_subset_1(sK0,sK2)) | spl4_2),
% 1.67/0.62    inference(avatar_component_clause,[],[f49])).
% 1.67/0.62  fof(f57,plain,(
% 1.67/0.62    spl4_3),
% 1.67/0.62    inference(avatar_split_clause,[],[f20,f54])).
% 1.67/0.62  fof(f20,plain,(
% 1.67/0.62    m1_subset_1(sK2,k1_zfmisc_1(sK0))),
% 1.67/0.62    inference(cnf_transformation,[],[f14])).
% 1.67/0.62  fof(f14,plain,(
% 1.67/0.62    ? [X0,X1] : (? [X2] : (k7_subset_1(X0,X1,X2) != k9_subset_1(X0,X1,k3_subset_1(X0,X2)) & m1_subset_1(X2,k1_zfmisc_1(X0))) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.67/0.62    inference(ennf_transformation,[],[f12])).
% 1.67/0.62  fof(f12,negated_conjecture,(
% 1.67/0.62    ~! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => k7_subset_1(X0,X1,X2) = k9_subset_1(X0,X1,k3_subset_1(X0,X2))))),
% 1.67/0.62    inference(negated_conjecture,[],[f11])).
% 1.67/0.62  fof(f11,conjecture,(
% 1.67/0.62    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => k7_subset_1(X0,X1,X2) = k9_subset_1(X0,X1,k3_subset_1(X0,X2))))),
% 1.67/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t32_subset_1)).
% 1.67/0.62  fof(f52,plain,(
% 1.67/0.62    ~spl4_2),
% 1.67/0.62    inference(avatar_split_clause,[],[f21,f49])).
% 1.67/0.62  fof(f21,plain,(
% 1.67/0.62    k7_subset_1(sK0,sK1,sK2) != k9_subset_1(sK0,sK1,k3_subset_1(sK0,sK2))),
% 1.67/0.62    inference(cnf_transformation,[],[f14])).
% 1.67/0.62  fof(f47,plain,(
% 1.67/0.62    spl4_1),
% 1.67/0.62    inference(avatar_split_clause,[],[f22,f44])).
% 1.67/0.62  fof(f22,plain,(
% 1.67/0.62    m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 1.67/0.62    inference(cnf_transformation,[],[f14])).
% 1.67/0.62  % SZS output end Proof for theBenchmark
% 1.67/0.62  % (30804)------------------------------
% 1.67/0.62  % (30804)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.67/0.62  % (30804)Termination reason: Refutation
% 1.67/0.62  
% 1.67/0.62  % (30804)Memory used [KB]: 11641
% 1.67/0.62  % (30804)Time elapsed: 0.195 s
% 1.67/0.62  % (30804)------------------------------
% 1.67/0.62  % (30804)------------------------------
% 1.67/0.62  % (30787)Success in time 0.262 s
%------------------------------------------------------------------------------
