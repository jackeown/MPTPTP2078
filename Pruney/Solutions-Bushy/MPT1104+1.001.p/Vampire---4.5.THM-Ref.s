%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1104+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n028.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:49:16 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   97 ( 145 expanded)
%              Number of leaves         :   26 (  59 expanded)
%              Depth                    :    6
%              Number of atoms          :  241 ( 429 expanded)
%              Number of equality atoms :   54 ( 112 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f144,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f34,f38,f42,f46,f50,f54,f58,f62,f66,f74,f78,f91,f101,f105,f114,f118,f124,f136,f143])).

fof(f143,plain,
    ( ~ spl3_2
    | spl3_16
    | ~ spl3_18
    | ~ spl3_19
    | ~ spl3_21 ),
    inference(avatar_contradiction_clause,[],[f142])).

fof(f142,plain,
    ( $false
    | ~ spl3_2
    | spl3_16
    | ~ spl3_18
    | ~ spl3_19
    | ~ spl3_21 ),
    inference(subsumption_resolution,[],[f141,f100])).

fof(f100,plain,
    ( sK2 != k4_xboole_0(k2_struct_0(sK0),sK1)
    | spl3_16 ),
    inference(avatar_component_clause,[],[f99])).

fof(f99,plain,
    ( spl3_16
  <=> sK2 = k4_xboole_0(k2_struct_0(sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_16])])).

fof(f141,plain,
    ( sK2 = k4_xboole_0(k2_struct_0(sK0),sK1)
    | ~ spl3_2
    | ~ spl3_18
    | ~ spl3_19
    | ~ spl3_21 ),
    inference(forward_demodulation,[],[f139,f129])).

fof(f129,plain,
    ( sK2 = k4_xboole_0(sK2,sK1)
    | ~ spl3_2
    | ~ spl3_19 ),
    inference(resolution,[],[f123,f37])).

fof(f37,plain,
    ( r1_xboole_0(sK1,sK2)
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f36])).

fof(f36,plain,
    ( spl3_2
  <=> r1_xboole_0(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f123,plain,
    ( ! [X0,X1] :
        ( ~ r1_xboole_0(X1,X0)
        | k4_xboole_0(X0,X1) = X0 )
    | ~ spl3_19 ),
    inference(avatar_component_clause,[],[f122])).

fof(f122,plain,
    ( spl3_19
  <=> ! [X1,X0] :
        ( k4_xboole_0(X0,X1) = X0
        | ~ r1_xboole_0(X1,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_19])])).

fof(f139,plain,
    ( k4_xboole_0(k2_struct_0(sK0),sK1) = k4_xboole_0(sK2,sK1)
    | ~ spl3_18
    | ~ spl3_21 ),
    inference(superposition,[],[f135,f117])).

fof(f117,plain,
    ( k2_struct_0(sK0) = k2_xboole_0(sK1,sK2)
    | ~ spl3_18 ),
    inference(avatar_component_clause,[],[f116])).

fof(f116,plain,
    ( spl3_18
  <=> k2_struct_0(sK0) = k2_xboole_0(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_18])])).

fof(f135,plain,
    ( ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X1,X0),X1)
    | ~ spl3_21 ),
    inference(avatar_component_clause,[],[f134])).

fof(f134,plain,
    ( spl3_21
  <=> ! [X1,X0] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X1,X0),X1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_21])])).

fof(f136,plain,
    ( spl3_21
    | ~ spl3_8
    | ~ spl3_12 ),
    inference(avatar_split_clause,[],[f85,f76,f60,f134])).

fof(f60,plain,
    ( spl3_8
  <=> ! [X1,X0] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).

fof(f76,plain,
    ( spl3_12
  <=> ! [X1,X0] : k4_xboole_0(k2_xboole_0(X0,X1),X1) = k4_xboole_0(X0,X1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).

fof(f85,plain,
    ( ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X1,X0),X1)
    | ~ spl3_8
    | ~ spl3_12 ),
    inference(superposition,[],[f77,f61])).

fof(f61,plain,
    ( ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)
    | ~ spl3_8 ),
    inference(avatar_component_clause,[],[f60])).

fof(f77,plain,
    ( ! [X0,X1] : k4_xboole_0(k2_xboole_0(X0,X1),X1) = k4_xboole_0(X0,X1)
    | ~ spl3_12 ),
    inference(avatar_component_clause,[],[f76])).

fof(f124,plain,
    ( spl3_19
    | ~ spl3_7
    | ~ spl3_11 ),
    inference(avatar_split_clause,[],[f80,f72,f56,f122])).

fof(f56,plain,
    ( spl3_7
  <=> ! [X1,X0] :
        ( ~ r1_xboole_0(X0,X1)
        | r1_xboole_0(X1,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f72,plain,
    ( spl3_11
  <=> ! [X1,X0] :
        ( k4_xboole_0(X0,X1) = X0
        | ~ r1_xboole_0(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).

fof(f80,plain,
    ( ! [X0,X1] :
        ( k4_xboole_0(X0,X1) = X0
        | ~ r1_xboole_0(X1,X0) )
    | ~ spl3_7
    | ~ spl3_11 ),
    inference(resolution,[],[f73,f57])).

fof(f57,plain,
    ( ! [X0,X1] :
        ( r1_xboole_0(X1,X0)
        | ~ r1_xboole_0(X0,X1) )
    | ~ spl3_7 ),
    inference(avatar_component_clause,[],[f56])).

fof(f73,plain,
    ( ! [X0,X1] :
        ( ~ r1_xboole_0(X0,X1)
        | k4_xboole_0(X0,X1) = X0 )
    | ~ spl3_11 ),
    inference(avatar_component_clause,[],[f72])).

fof(f118,plain,
    ( spl3_18
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_5
    | ~ spl3_17 ),
    inference(avatar_split_clause,[],[f109,f103,f48,f44,f40,f116])).

fof(f40,plain,
    ( spl3_3
  <=> m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f44,plain,
    ( spl3_4
  <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f48,plain,
    ( spl3_5
  <=> k2_struct_0(sK0) = k4_subset_1(u1_struct_0(sK0),sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f103,plain,
    ( spl3_17
  <=> ! [X1,X0,X2] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
        | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
        | k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_17])])).

fof(f109,plain,
    ( k2_struct_0(sK0) = k2_xboole_0(sK1,sK2)
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_5
    | ~ spl3_17 ),
    inference(subsumption_resolution,[],[f108,f45])).

fof(f45,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f44])).

fof(f108,plain,
    ( k2_struct_0(sK0) = k2_xboole_0(sK1,sK2)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl3_3
    | ~ spl3_5
    | ~ spl3_17 ),
    inference(subsumption_resolution,[],[f106,f41])).

fof(f41,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f40])).

fof(f106,plain,
    ( k2_struct_0(sK0) = k2_xboole_0(sK1,sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl3_5
    | ~ spl3_17 ),
    inference(superposition,[],[f104,f49])).

fof(f49,plain,
    ( k2_struct_0(sK0) = k4_subset_1(u1_struct_0(sK0),sK1,sK2)
    | ~ spl3_5 ),
    inference(avatar_component_clause,[],[f48])).

fof(f104,plain,
    ( ! [X2,X0,X1] :
        ( k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)
        | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
        | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
    | ~ spl3_17 ),
    inference(avatar_component_clause,[],[f103])).

fof(f114,plain,
    ( ~ spl3_1
    | ~ spl3_9
    | spl3_15 ),
    inference(avatar_contradiction_clause,[],[f113])).

fof(f113,plain,
    ( $false
    | ~ spl3_1
    | ~ spl3_9
    | spl3_15 ),
    inference(subsumption_resolution,[],[f111,f33])).

fof(f33,plain,
    ( l1_struct_0(sK0)
    | ~ spl3_1 ),
    inference(avatar_component_clause,[],[f32])).

fof(f32,plain,
    ( spl3_1
  <=> l1_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f111,plain,
    ( ~ l1_struct_0(sK0)
    | ~ spl3_9
    | spl3_15 ),
    inference(resolution,[],[f97,f65])).

fof(f65,plain,
    ( ! [X0] :
        ( m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0)))
        | ~ l1_struct_0(X0) )
    | ~ spl3_9 ),
    inference(avatar_component_clause,[],[f64])).

fof(f64,plain,
    ( spl3_9
  <=> ! [X0] :
        ( ~ l1_struct_0(X0)
        | m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).

fof(f97,plain,
    ( ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | spl3_15 ),
    inference(avatar_component_clause,[],[f96])).

fof(f96,plain,
    ( spl3_15
  <=> m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_15])])).

fof(f105,plain,(
    spl3_17 ),
    inference(avatar_split_clause,[],[f30,f103])).

fof(f30,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X0))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

fof(f101,plain,
    ( ~ spl3_15
    | ~ spl3_16
    | spl3_6
    | ~ spl3_14 ),
    inference(avatar_split_clause,[],[f94,f89,f52,f99,f96])).

fof(f52,plain,
    ( spl3_6
  <=> sK2 = k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f89,plain,
    ( spl3_14
  <=> ! [X1,X0,X2] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
        | k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).

fof(f94,plain,
    ( sK2 != k4_xboole_0(k2_struct_0(sK0),sK1)
    | ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | spl3_6
    | ~ spl3_14 ),
    inference(superposition,[],[f53,f90])).

fof(f90,plain,
    ( ! [X2,X0,X1] :
        ( k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)
        | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
    | ~ spl3_14 ),
    inference(avatar_component_clause,[],[f89])).

fof(f53,plain,
    ( sK2 != k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1)
    | spl3_6 ),
    inference(avatar_component_clause,[],[f52])).

fof(f91,plain,(
    spl3_14 ),
    inference(avatar_split_clause,[],[f29,f89])).

fof(f29,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

fof(f78,plain,(
    spl3_12 ),
    inference(avatar_split_clause,[],[f25,f76])).

fof(f25,plain,(
    ! [X0,X1] : k4_xboole_0(k2_xboole_0(X0,X1),X1) = k4_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k4_xboole_0(k2_xboole_0(X0,X1),X1) = k4_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t40_xboole_1)).

fof(f74,plain,(
    spl3_11 ),
    inference(avatar_split_clause,[],[f28,f72])).

fof(f28,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = X0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k4_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).

fof(f66,plain,(
    spl3_9 ),
    inference(avatar_split_clause,[],[f23,f64])).

fof(f23,plain,(
    ! [X0] :
      ( ~ l1_struct_0(X0)
      | m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_struct_0)).

fof(f62,plain,(
    spl3_8 ),
    inference(avatar_split_clause,[],[f24,f60])).

fof(f24,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(f58,plain,(
    spl3_7 ),
    inference(avatar_split_clause,[],[f26,f56])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | r1_xboole_0(X1,X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => r1_xboole_0(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

fof(f54,plain,(
    ~ spl3_6 ),
    inference(avatar_split_clause,[],[f20,f52])).

fof(f20,plain,(
    sK2 != k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1) != X2
              & r1_xboole_0(X1,X2)
              & k2_struct_0(X0) = k4_subset_1(u1_struct_0(X0),X1,X2)
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_struct_0(X0) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1) != X2
              & r1_xboole_0(X1,X2)
              & k2_struct_0(X0) = k4_subset_1(u1_struct_0(X0),X1,X2)
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,negated_conjecture,(
    ~ ! [X0] :
        ( l1_struct_0(X0)
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => ( ( r1_xboole_0(X1,X2)
                    & k2_struct_0(X0) = k4_subset_1(u1_struct_0(X0),X1,X2) )
                 => k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1) = X2 ) ) ) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f8,conjecture,(
    ! [X0] :
      ( l1_struct_0(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( ( r1_xboole_0(X1,X2)
                  & k2_struct_0(X0) = k4_subset_1(u1_struct_0(X0),X1,X2) )
               => k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1) = X2 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_pre_topc)).

fof(f50,plain,(
    spl3_5 ),
    inference(avatar_split_clause,[],[f18,f48])).

fof(f18,plain,(
    k2_struct_0(sK0) = k4_subset_1(u1_struct_0(sK0),sK1,sK2) ),
    inference(cnf_transformation,[],[f11])).

fof(f46,plain,(
    spl3_4 ),
    inference(avatar_split_clause,[],[f21,f44])).

fof(f21,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f11])).

fof(f42,plain,(
    spl3_3 ),
    inference(avatar_split_clause,[],[f17,f40])).

fof(f17,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f11])).

fof(f38,plain,(
    spl3_2 ),
    inference(avatar_split_clause,[],[f19,f36])).

fof(f19,plain,(
    r1_xboole_0(sK1,sK2) ),
    inference(cnf_transformation,[],[f11])).

fof(f34,plain,(
    spl3_1 ),
    inference(avatar_split_clause,[],[f22,f32])).

fof(f22,plain,(
    l1_struct_0(sK0) ),
    inference(cnf_transformation,[],[f11])).

%------------------------------------------------------------------------------
