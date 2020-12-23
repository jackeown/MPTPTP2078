%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : tex_2__t36_tex_2.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:38:31 EDT 2019

% Result     : Theorem 2.37s
% Output     : Refutation 2.37s
% Verified   : 
% Statistics : Number of formulae       :  224 ( 364 expanded)
%              Number of leaves         :   53 ( 129 expanded)
%              Depth                    :   18
%              Number of atoms          :  675 (1049 expanded)
%              Number of equality atoms :   87 ( 129 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f25092,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f132,f139,f146,f160,f167,f176,f190,f203,f206,f225,f306,f312,f320,f342,f376,f461,f1138,f1147,f22892,f22926,f24459,f24532,f24538,f24957,f25086])).

fof(f25086,plain,
    ( ~ spl7_4
    | ~ spl7_14
    | spl7_19
    | ~ spl7_28
    | ~ spl7_42
    | ~ spl7_48
    | ~ spl7_74 ),
    inference(avatar_contradiction_clause,[],[f25085])).

fof(f25085,plain,
    ( $false
    | ~ spl7_4
    | ~ spl7_14
    | ~ spl7_19
    | ~ spl7_28
    | ~ spl7_42
    | ~ spl7_48
    | ~ spl7_74 ),
    inference(subsumption_resolution,[],[f25084,f419])).

fof(f419,plain,
    ( k3_xboole_0(u1_struct_0(sK0),k1_tarski(sK1)) = k1_tarski(sK1)
    | ~ spl7_48 ),
    inference(avatar_component_clause,[],[f418])).

fof(f418,plain,
    ( spl7_48
  <=> k3_xboole_0(u1_struct_0(sK0),k1_tarski(sK1)) = k1_tarski(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_48])])).

fof(f25084,plain,
    ( k3_xboole_0(u1_struct_0(sK0),k1_tarski(sK1)) != k1_tarski(sK1)
    | ~ spl7_4
    | ~ spl7_14
    | ~ spl7_19
    | ~ spl7_28
    | ~ spl7_42
    | ~ spl7_74 ),
    inference(subsumption_resolution,[],[f25078,f739])).

fof(f739,plain,
    ( m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl7_74 ),
    inference(avatar_component_clause,[],[f738])).

fof(f738,plain,
    ( spl7_74
  <=> m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_74])])).

fof(f25078,plain,
    ( ~ m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | k3_xboole_0(u1_struct_0(sK0),k1_tarski(sK1)) != k1_tarski(sK1)
    | ~ spl7_4
    | ~ spl7_14
    | ~ spl7_19
    | ~ spl7_28
    | ~ spl7_42 ),
    inference(resolution,[],[f25076,f189])).

fof(f189,plain,
    ( v3_pre_topc(u1_struct_0(sK0),sK0)
    | ~ spl7_14 ),
    inference(avatar_component_clause,[],[f188])).

fof(f188,plain,
    ( spl7_14
  <=> v3_pre_topc(u1_struct_0(sK0),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_14])])).

fof(f25076,plain,
    ( ! [X0] :
        ( ~ v3_pre_topc(X0,sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | k3_xboole_0(X0,k1_tarski(sK1)) != k1_tarski(sK1) )
    | ~ spl7_4
    | ~ spl7_19
    | ~ spl7_28
    | ~ spl7_42 ),
    inference(forward_demodulation,[],[f924,f375])).

fof(f375,plain,
    ( k1_tarski(sK1) = sK2(sK0,k1_tarski(sK1))
    | ~ spl7_42 ),
    inference(avatar_component_clause,[],[f374])).

fof(f374,plain,
    ( spl7_42
  <=> k1_tarski(sK1) = sK2(sK0,k1_tarski(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_42])])).

fof(f924,plain,
    ( ! [X0] :
        ( k3_xboole_0(X0,k1_tarski(sK1)) != sK2(sK0,k1_tarski(sK1))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v3_pre_topc(X0,sK0) )
    | ~ spl7_4
    | ~ spl7_19
    | ~ spl7_28 ),
    inference(forward_demodulation,[],[f363,f448])).

fof(f448,plain,
    ( ! [X1] : k3_xboole_0(X1,k1_tarski(sK1)) = k9_subset_1(u1_struct_0(sK0),X1,k1_tarski(sK1))
    | ~ spl7_28 ),
    inference(superposition,[],[f356,f316])).

fof(f316,plain,
    ( ! [X0] : k9_subset_1(u1_struct_0(sK0),X0,k1_tarski(sK1)) = k9_subset_1(u1_struct_0(sK0),k1_tarski(sK1),X0)
    | ~ spl7_28 ),
    inference(resolution,[],[f266,f119])).

fof(f119,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | k9_subset_1(X0,X1,X2) = k9_subset_1(X0,X2,X1) ) ),
    inference(cnf_transformation,[],[f74])).

fof(f74,plain,(
    ! [X0,X1,X2] :
      ( k9_subset_1(X0,X1,X2) = k9_subset_1(X0,X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k9_subset_1(X0,X1,X2) = k9_subset_1(X0,X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/tex_2__t36_tex_2.p',commutativity_k9_subset_1)).

fof(f266,plain,
    ( m1_subset_1(k1_tarski(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl7_28 ),
    inference(avatar_component_clause,[],[f265])).

fof(f265,plain,
    ( spl7_28
  <=> m1_subset_1(k1_tarski(sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_28])])).

fof(f356,plain,
    ( ! [X1] : k3_xboole_0(X1,k1_tarski(sK1)) = k9_subset_1(u1_struct_0(sK0),k1_tarski(sK1),X1)
    | ~ spl7_28 ),
    inference(subsumption_resolution,[],[f348,f266])).

fof(f348,plain,
    ( ! [X1] :
        ( k3_xboole_0(X1,k1_tarski(sK1)) = k9_subset_1(u1_struct_0(sK0),k1_tarski(sK1),X1)
        | ~ m1_subset_1(k1_tarski(sK1),k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl7_28 ),
    inference(superposition,[],[f316,f118])).

fof(f118,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f73])).

fof(f73,plain,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f31])).

fof(f31,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/tex_2__t36_tex_2.p',redefinition_k9_subset_1)).

fof(f363,plain,
    ( ! [X0] :
        ( k9_subset_1(u1_struct_0(sK0),X0,k1_tarski(sK1)) != sK2(sK0,k1_tarski(sK1))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v3_pre_topc(X0,sK0) )
    | ~ spl7_4
    | ~ spl7_19
    | ~ spl7_28 ),
    inference(subsumption_resolution,[],[f362,f202])).

fof(f202,plain,
    ( ~ v2_tex_2(k1_tarski(sK1),sK0)
    | ~ spl7_19 ),
    inference(avatar_component_clause,[],[f201])).

fof(f201,plain,
    ( spl7_19
  <=> ~ v2_tex_2(k1_tarski(sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_19])])).

fof(f362,plain,
    ( ! [X0] :
        ( k9_subset_1(u1_struct_0(sK0),X0,k1_tarski(sK1)) != sK2(sK0,k1_tarski(sK1))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v3_pre_topc(X0,sK0)
        | v2_tex_2(k1_tarski(sK1),sK0) )
    | ~ spl7_4
    | ~ spl7_28 ),
    inference(subsumption_resolution,[],[f361,f145])).

fof(f145,plain,
    ( l1_pre_topc(sK0)
    | ~ spl7_4 ),
    inference(avatar_component_clause,[],[f144])).

fof(f144,plain,
    ( spl7_4
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_4])])).

fof(f361,plain,
    ( ! [X0] :
        ( k9_subset_1(u1_struct_0(sK0),X0,k1_tarski(sK1)) != sK2(sK0,k1_tarski(sK1))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v3_pre_topc(X0,sK0)
        | ~ l1_pre_topc(sK0)
        | v2_tex_2(k1_tarski(sK1),sK0) )
    | ~ spl7_28 ),
    inference(subsumption_resolution,[],[f353,f266])).

fof(f353,plain,
    ( ! [X0] :
        ( k9_subset_1(u1_struct_0(sK0),X0,k1_tarski(sK1)) != sK2(sK0,k1_tarski(sK1))
        | ~ m1_subset_1(k1_tarski(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v3_pre_topc(X0,sK0)
        | ~ l1_pre_topc(sK0)
        | v2_tex_2(k1_tarski(sK1),sK0) )
    | ~ spl7_28 ),
    inference(superposition,[],[f86,f316])).

fof(f86,plain,(
    ! [X0,X3,X1] :
      ( k9_subset_1(u1_struct_0(X0),X1,X3) != sK2(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v3_pre_topc(X3,X0)
      | ~ l1_pre_topc(X0)
      | v2_tex_2(X1,X0) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f48,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_tex_2(X1,X0)
          <=> ! [X2] :
                ( ? [X3] :
                    ( k9_subset_1(u1_struct_0(X0),X1,X3) = X2
                    & v3_pre_topc(X3,X0)
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                | ~ r1_tarski(X2,X1)
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f47])).

fof(f47,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_tex_2(X1,X0)
          <=> ! [X2] :
                ( ? [X3] :
                    ( k9_subset_1(u1_struct_0(X0),X1,X3) = X2
                    & v3_pre_topc(X3,X0)
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                | ~ r1_tarski(X2,X1)
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v2_tex_2(X1,X0)
          <=> ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => ~ ( ! [X3] :
                        ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                       => ~ ( k9_subset_1(u1_struct_0(X0),X1,X3) = X2
                            & v3_pre_topc(X3,X0) ) )
                    & r1_tarski(X2,X1) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/tex_2__t36_tex_2.p',d5_tex_2)).

fof(f24957,plain,(
    spl7_89 ),
    inference(avatar_contradiction_clause,[],[f24956])).

fof(f24956,plain,
    ( $false
    | ~ spl7_89 ),
    inference(subsumption_resolution,[],[f920,f84])).

fof(f84,plain,(
    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f34])).

fof(f34,axiom,(
    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/tex_2__t36_tex_2.p',t2_boole)).

fof(f920,plain,
    ( k3_xboole_0(k1_tarski(sK1),k1_xboole_0) != k1_xboole_0
    | ~ spl7_89 ),
    inference(avatar_component_clause,[],[f919])).

fof(f919,plain,
    ( spl7_89
  <=> k3_xboole_0(k1_tarski(sK1),k1_xboole_0) != k1_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_89])])).

fof(f24538,plain,
    ( k1_struct_0(sK0) != k1_xboole_0
    | k3_xboole_0(k1_tarski(sK1),k1_xboole_0) != k1_xboole_0
    | k3_xboole_0(k1_tarski(sK1),k1_struct_0(sK0)) = k1_xboole_0 ),
    introduced(theory_axiom,[])).

fof(f24532,plain,
    ( spl7_500
    | ~ spl7_498 ),
    inference(avatar_split_clause,[],[f24465,f24450,f24530])).

fof(f24530,plain,
    ( spl7_500
  <=> k1_struct_0(sK0) = k1_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_500])])).

fof(f24450,plain,
    ( spl7_498
  <=> v1_xboole_0(k1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_498])])).

fof(f24465,plain,
    ( k1_struct_0(sK0) = k1_xboole_0
    | ~ spl7_498 ),
    inference(resolution,[],[f24451,f96])).

fof(f96,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f53])).

fof(f53,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f40])).

fof(f40,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/tex_2__t36_tex_2.p',t6_boole)).

fof(f24451,plain,
    ( v1_xboole_0(k1_struct_0(sK0))
    | ~ spl7_498 ),
    inference(avatar_component_clause,[],[f24450])).

fof(f24459,plain,
    ( ~ spl7_12
    | spl7_499 ),
    inference(avatar_contradiction_clause,[],[f24458])).

fof(f24458,plain,
    ( $false
    | ~ spl7_12
    | ~ spl7_499 ),
    inference(subsumption_resolution,[],[f24456,f180])).

fof(f180,plain,
    ( l1_struct_0(sK0)
    | ~ spl7_12 ),
    inference(avatar_component_clause,[],[f179])).

fof(f179,plain,
    ( spl7_12
  <=> l1_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_12])])).

fof(f24456,plain,
    ( ~ l1_struct_0(sK0)
    | ~ spl7_499 ),
    inference(resolution,[],[f24454,f92])).

fof(f92,plain,(
    ! [X0] :
      ( v1_xboole_0(k1_struct_0(X0))
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f49,plain,(
    ! [X0] :
      ( v1_xboole_0(k1_struct_0(X0))
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f27])).

fof(f27,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => v1_xboole_0(k1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/tex_2__t36_tex_2.p',fc3_struct_0)).

fof(f24454,plain,
    ( ~ v1_xboole_0(k1_struct_0(sK0))
    | ~ spl7_499 ),
    inference(avatar_component_clause,[],[f24453])).

fof(f24453,plain,
    ( spl7_499
  <=> ~ v1_xboole_0(k1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_499])])).

fof(f22926,plain,
    ( ~ spl7_463
    | ~ spl7_6
    | spl7_17
    | ~ spl7_40
    | spl7_461 ),
    inference(avatar_split_clause,[],[f22898,f22890,f368,f192,f158,f22924])).

fof(f22924,plain,
    ( spl7_463
  <=> k3_xboole_0(k1_tarski(sK1),k1_struct_0(sK0)) != k1_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_463])])).

fof(f158,plain,
    ( spl7_6
  <=> m1_subset_1(sK1,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_6])])).

fof(f192,plain,
    ( spl7_17
  <=> ~ v1_xboole_0(u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_17])])).

fof(f368,plain,
    ( spl7_40
  <=> k1_xboole_0 = sK2(sK0,k1_tarski(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_40])])).

fof(f22890,plain,
    ( spl7_461
  <=> k3_xboole_0(k6_domain_1(u1_struct_0(sK0),sK1),k1_struct_0(sK0)) != sK2(sK0,k6_domain_1(u1_struct_0(sK0),sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_461])])).

fof(f22898,plain,
    ( k3_xboole_0(k1_tarski(sK1),k1_struct_0(sK0)) != k1_xboole_0
    | ~ spl7_6
    | ~ spl7_17
    | ~ spl7_40
    | ~ spl7_461 ),
    inference(forward_demodulation,[],[f22897,f369])).

fof(f369,plain,
    ( k1_xboole_0 = sK2(sK0,k1_tarski(sK1))
    | ~ spl7_40 ),
    inference(avatar_component_clause,[],[f368])).

fof(f22897,plain,
    ( k3_xboole_0(k1_tarski(sK1),k1_struct_0(sK0)) != sK2(sK0,k1_tarski(sK1))
    | ~ spl7_6
    | ~ spl7_17
    | ~ spl7_461 ),
    inference(subsumption_resolution,[],[f22896,f193])).

fof(f193,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK0))
    | ~ spl7_17 ),
    inference(avatar_component_clause,[],[f192])).

fof(f22896,plain,
    ( k3_xboole_0(k1_tarski(sK1),k1_struct_0(sK0)) != sK2(sK0,k1_tarski(sK1))
    | v1_xboole_0(u1_struct_0(sK0))
    | ~ spl7_6
    | ~ spl7_461 ),
    inference(subsumption_resolution,[],[f22895,f159])).

fof(f159,plain,
    ( m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ spl7_6 ),
    inference(avatar_component_clause,[],[f158])).

fof(f22895,plain,
    ( k3_xboole_0(k1_tarski(sK1),k1_struct_0(sK0)) != sK2(sK0,k1_tarski(sK1))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | v1_xboole_0(u1_struct_0(sK0))
    | ~ spl7_461 ),
    inference(superposition,[],[f22891,f107])).

fof(f107,plain,(
    ! [X0,X1] :
      ( k6_domain_1(X0,X1) = k1_tarski(X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f66])).

fof(f66,plain,(
    ! [X0,X1] :
      ( k6_domain_1(X0,X1) = k1_tarski(X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f65])).

fof(f65,plain,(
    ! [X0,X1] :
      ( k6_domain_1(X0,X1) = k1_tarski(X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f30])).

fof(f30,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,X0)
        & ~ v1_xboole_0(X0) )
     => k6_domain_1(X0,X1) = k1_tarski(X1) ) ),
    file('/export/starexec/sandbox/benchmark/tex_2__t36_tex_2.p',redefinition_k6_domain_1)).

fof(f22891,plain,
    ( k3_xboole_0(k6_domain_1(u1_struct_0(sK0),sK1),k1_struct_0(sK0)) != sK2(sK0,k6_domain_1(u1_struct_0(sK0),sK1))
    | ~ spl7_461 ),
    inference(avatar_component_clause,[],[f22890])).

fof(f22892,plain,
    ( ~ spl7_461
    | ~ spl7_2
    | ~ spl7_4
    | spl7_9
    | ~ spl7_12
    | ~ spl7_34 ),
    inference(avatar_split_clause,[],[f15449,f288,f179,f165,f144,f137,f22890])).

fof(f137,plain,
    ( spl7_2
  <=> v2_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).

fof(f165,plain,
    ( spl7_9
  <=> ~ v2_tex_2(k6_domain_1(u1_struct_0(sK0),sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_9])])).

fof(f288,plain,
    ( spl7_34
  <=> m1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_34])])).

fof(f15449,plain,
    ( k3_xboole_0(k6_domain_1(u1_struct_0(sK0),sK1),k1_struct_0(sK0)) != sK2(sK0,k6_domain_1(u1_struct_0(sK0),sK1))
    | ~ spl7_2
    | ~ spl7_4
    | ~ spl7_9
    | ~ spl7_12
    | ~ spl7_34 ),
    inference(subsumption_resolution,[],[f15447,f180])).

fof(f15447,plain,
    ( k3_xboole_0(k6_domain_1(u1_struct_0(sK0),sK1),k1_struct_0(sK0)) != sK2(sK0,k6_domain_1(u1_struct_0(sK0),sK1))
    | ~ l1_struct_0(sK0)
    | ~ spl7_2
    | ~ spl7_4
    | ~ spl7_9
    | ~ spl7_34 ),
    inference(duplicate_literal_removal,[],[f15445])).

fof(f15445,plain,
    ( k3_xboole_0(k6_domain_1(u1_struct_0(sK0),sK1),k1_struct_0(sK0)) != sK2(sK0,k6_domain_1(u1_struct_0(sK0),sK1))
    | ~ l1_struct_0(sK0)
    | ~ l1_struct_0(sK0)
    | ~ spl7_2
    | ~ spl7_4
    | ~ spl7_9
    | ~ spl7_34 ),
    inference(resolution,[],[f5770,f95])).

fof(f95,plain,(
    ! [X0] :
      ( m1_subset_1(k1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f52,plain,(
    ! [X0] :
      ( m1_subset_1(k1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => m1_subset_1(k1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox/benchmark/tex_2__t36_tex_2.p',dt_k1_struct_0)).

fof(f5770,plain,
    ( ! [X2] :
        ( ~ m1_subset_1(k1_struct_0(X2),k1_zfmisc_1(u1_struct_0(sK0)))
        | k3_xboole_0(k6_domain_1(u1_struct_0(sK0),sK1),k1_struct_0(X2)) != sK2(sK0,k6_domain_1(u1_struct_0(sK0),sK1))
        | ~ l1_struct_0(X2) )
    | ~ spl7_2
    | ~ spl7_4
    | ~ spl7_9
    | ~ spl7_34 ),
    inference(resolution,[],[f3011,f92])).

fof(f3011,plain,
    ( ! [X0] :
        ( ~ v1_xboole_0(X0)
        | k3_xboole_0(k6_domain_1(u1_struct_0(sK0),sK1),X0) != sK2(sK0,k6_domain_1(u1_struct_0(sK0),sK1))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl7_2
    | ~ spl7_4
    | ~ spl7_9
    | ~ spl7_34 ),
    inference(duplicate_literal_removal,[],[f3005])).

fof(f3005,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | k3_xboole_0(k6_domain_1(u1_struct_0(sK0),sK1),X0) != sK2(sK0,k6_domain_1(u1_struct_0(sK0),sK1))
        | ~ v1_xboole_0(X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl7_2
    | ~ spl7_4
    | ~ spl7_9
    | ~ spl7_34 ),
    inference(resolution,[],[f1486,f152])).

fof(f152,plain,
    ( ! [X0] :
        ( v3_pre_topc(X0,sK0)
        | ~ v1_xboole_0(X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl7_2
    | ~ spl7_4 ),
    inference(subsumption_resolution,[],[f147,f138])).

fof(f138,plain,
    ( v2_pre_topc(sK0)
    | ~ spl7_2 ),
    inference(avatar_component_clause,[],[f137])).

fof(f147,plain,
    ( ! [X0] :
        ( ~ v2_pre_topc(sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v1_xboole_0(X0)
        | v3_pre_topc(X0,sK0) )
    | ~ spl7_4 ),
    inference(resolution,[],[f145,f99])).

fof(f99,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v1_xboole_0(X1)
      | v3_pre_topc(X1,X0) ) ),
    inference(cnf_transformation,[],[f59])).

fof(f59,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v3_pre_topc(X1,X0)
          | ~ v1_xboole_0(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f58])).

fof(f58,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v3_pre_topc(X1,X0)
          | ~ v1_xboole_0(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v1_xboole_0(X1)
           => v3_pre_topc(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/tex_2__t36_tex_2.p',cc1_tops_1)).

fof(f1486,plain,
    ( ! [X0] :
        ( ~ v3_pre_topc(X0,sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | k3_xboole_0(k6_domain_1(u1_struct_0(sK0),sK1),X0) != sK2(sK0,k6_domain_1(u1_struct_0(sK0),sK1)) )
    | ~ spl7_4
    | ~ spl7_9
    | ~ spl7_34 ),
    inference(superposition,[],[f545,f102])).

fof(f102,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/tex_2__t36_tex_2.p',commutativity_k3_xboole_0)).

fof(f545,plain,
    ( ! [X2] :
        ( k3_xboole_0(X2,k6_domain_1(u1_struct_0(sK0),sK1)) != sK2(sK0,k6_domain_1(u1_struct_0(sK0),sK1))
        | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v3_pre_topc(X2,sK0) )
    | ~ spl7_4
    | ~ spl7_9
    | ~ spl7_34 ),
    inference(subsumption_resolution,[],[f544,f166])).

fof(f166,plain,
    ( ~ v2_tex_2(k6_domain_1(u1_struct_0(sK0),sK1),sK0)
    | ~ spl7_9 ),
    inference(avatar_component_clause,[],[f165])).

fof(f544,plain,
    ( ! [X2] :
        ( k3_xboole_0(X2,k6_domain_1(u1_struct_0(sK0),sK1)) != sK2(sK0,k6_domain_1(u1_struct_0(sK0),sK1))
        | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v3_pre_topc(X2,sK0)
        | v2_tex_2(k6_domain_1(u1_struct_0(sK0),sK1),sK0) )
    | ~ spl7_4
    | ~ spl7_34 ),
    inference(subsumption_resolution,[],[f543,f145])).

fof(f543,plain,
    ( ! [X2] :
        ( k3_xboole_0(X2,k6_domain_1(u1_struct_0(sK0),sK1)) != sK2(sK0,k6_domain_1(u1_struct_0(sK0),sK1))
        | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v3_pre_topc(X2,sK0)
        | ~ l1_pre_topc(sK0)
        | v2_tex_2(k6_domain_1(u1_struct_0(sK0),sK1),sK0) )
    | ~ spl7_34 ),
    inference(subsumption_resolution,[],[f539,f289])).

fof(f289,plain,
    ( m1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl7_34 ),
    inference(avatar_component_clause,[],[f288])).

fof(f539,plain,
    ( ! [X2] :
        ( k3_xboole_0(X2,k6_domain_1(u1_struct_0(sK0),sK1)) != sK2(sK0,k6_domain_1(u1_struct_0(sK0),sK1))
        | ~ m1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v3_pre_topc(X2,sK0)
        | ~ l1_pre_topc(sK0)
        | v2_tex_2(k6_domain_1(u1_struct_0(sK0),sK1),sK0) )
    | ~ spl7_34 ),
    inference(superposition,[],[f86,f404])).

fof(f404,plain,
    ( ! [X1] : k3_xboole_0(X1,k6_domain_1(u1_struct_0(sK0),sK1)) = k9_subset_1(u1_struct_0(sK0),k6_domain_1(u1_struct_0(sK0),sK1),X1)
    | ~ spl7_34 ),
    inference(subsumption_resolution,[],[f395,f289])).

fof(f395,plain,
    ( ! [X1] :
        ( k3_xboole_0(X1,k6_domain_1(u1_struct_0(sK0),sK1)) = k9_subset_1(u1_struct_0(sK0),k6_domain_1(u1_struct_0(sK0),sK1),X1)
        | ~ m1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl7_34 ),
    inference(superposition,[],[f307,f118])).

fof(f307,plain,
    ( ! [X0] : k9_subset_1(u1_struct_0(sK0),X0,k6_domain_1(u1_struct_0(sK0),sK1)) = k9_subset_1(u1_struct_0(sK0),k6_domain_1(u1_struct_0(sK0),sK1),X0)
    | ~ spl7_34 ),
    inference(resolution,[],[f289,f119])).

fof(f1147,plain,
    ( ~ spl7_12
    | spl7_75
    | ~ spl7_112 ),
    inference(avatar_contradiction_clause,[],[f1146])).

fof(f1146,plain,
    ( $false
    | ~ spl7_12
    | ~ spl7_75
    | ~ spl7_112 ),
    inference(subsumption_resolution,[],[f1145,f180])).

fof(f1145,plain,
    ( ~ l1_struct_0(sK0)
    | ~ spl7_75
    | ~ spl7_112 ),
    inference(subsumption_resolution,[],[f1142,f742])).

fof(f742,plain,
    ( ~ m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl7_75 ),
    inference(avatar_component_clause,[],[f741])).

fof(f741,plain,
    ( spl7_75
  <=> ~ m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_75])])).

fof(f1142,plain,
    ( m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_struct_0(sK0)
    | ~ spl7_112 ),
    inference(superposition,[],[f1129,f93])).

fof(f93,plain,(
    ! [X0] :
      ( u1_struct_0(X0) = k2_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f50,plain,(
    ! [X0] :
      ( u1_struct_0(X0) = k2_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => u1_struct_0(X0) = k2_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/tex_2__t36_tex_2.p',d3_struct_0)).

fof(f1129,plain,
    ( m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl7_112 ),
    inference(avatar_component_clause,[],[f1128])).

fof(f1128,plain,
    ( spl7_112
  <=> m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_112])])).

fof(f1138,plain,
    ( ~ spl7_12
    | spl7_113 ),
    inference(avatar_contradiction_clause,[],[f1137])).

fof(f1137,plain,
    ( $false
    | ~ spl7_12
    | ~ spl7_113 ),
    inference(subsumption_resolution,[],[f1134,f180])).

fof(f1134,plain,
    ( ~ l1_struct_0(sK0)
    | ~ spl7_113 ),
    inference(resolution,[],[f1132,f94])).

fof(f94,plain,(
    ! [X0] :
      ( m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f51,plain,(
    ! [X0] :
      ( m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox/benchmark/tex_2__t36_tex_2.p',dt_k2_struct_0)).

fof(f1132,plain,
    ( ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl7_113 ),
    inference(avatar_component_clause,[],[f1131])).

fof(f1131,plain,
    ( spl7_113
  <=> ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_113])])).

fof(f461,plain,
    ( spl7_48
    | ~ spl7_38 ),
    inference(avatar_split_clause,[],[f347,f340,f418])).

fof(f340,plain,
    ( spl7_38
  <=> k3_xboole_0(k1_tarski(sK1),u1_struct_0(sK0)) = k1_tarski(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_38])])).

fof(f347,plain,
    ( k3_xboole_0(u1_struct_0(sK0),k1_tarski(sK1)) = k1_tarski(sK1)
    | ~ spl7_38 ),
    inference(superposition,[],[f102,f341])).

fof(f341,plain,
    ( k3_xboole_0(k1_tarski(sK1),u1_struct_0(sK0)) = k1_tarski(sK1)
    | ~ spl7_38 ),
    inference(avatar_component_clause,[],[f340])).

fof(f376,plain,
    ( spl7_40
    | spl7_42
    | ~ spl7_4
    | spl7_19
    | ~ spl7_28 ),
    inference(avatar_split_clause,[],[f317,f265,f201,f144,f374,f368])).

fof(f317,plain,
    ( k1_tarski(sK1) = sK2(sK0,k1_tarski(sK1))
    | k1_xboole_0 = sK2(sK0,k1_tarski(sK1))
    | ~ spl7_4
    | ~ spl7_19
    | ~ spl7_28 ),
    inference(subsumption_resolution,[],[f315,f202])).

fof(f315,plain,
    ( v2_tex_2(k1_tarski(sK1),sK0)
    | k1_tarski(sK1) = sK2(sK0,k1_tarski(sK1))
    | k1_xboole_0 = sK2(sK0,k1_tarski(sK1))
    | ~ spl7_4
    | ~ spl7_28 ),
    inference(resolution,[],[f266,f209])).

fof(f209,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(k1_tarski(X1),k1_zfmisc_1(u1_struct_0(sK0)))
        | v2_tex_2(k1_tarski(X1),sK0)
        | k1_tarski(X1) = sK2(sK0,k1_tarski(X1))
        | k1_xboole_0 = sK2(sK0,k1_tarski(X1)) )
    | ~ spl7_4 ),
    inference(resolution,[],[f151,f109])).

fof(f109,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,k1_tarski(X1))
      | k1_tarski(X1) = X0
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,k1_tarski(X1))
    <=> ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/tex_2__t36_tex_2.p',t39_zfmisc_1)).

fof(f151,plain,
    ( ! [X5] :
        ( r1_tarski(sK2(sK0,X5),X5)
        | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(sK0)))
        | v2_tex_2(X5,sK0) )
    | ~ spl7_4 ),
    inference(resolution,[],[f145,f91])).

fof(f91,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | r1_tarski(sK2(X0,X1),X1)
      | v2_tex_2(X1,X0) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f342,plain,
    ( spl7_38
    | ~ spl7_30 ),
    inference(avatar_split_clause,[],[f329,f273,f340])).

fof(f273,plain,
    ( spl7_30
  <=> r1_tarski(k1_tarski(sK1),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_30])])).

fof(f329,plain,
    ( k3_xboole_0(k1_tarski(sK1),u1_struct_0(sK0)) = k1_tarski(sK1)
    | ~ spl7_30 ),
    inference(resolution,[],[f274,f103])).

fof(f103,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k3_xboole_0(X0,X1) = X0 ) ),
    inference(cnf_transformation,[],[f60])).

fof(f60,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f33])).

fof(f33,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/tex_2__t36_tex_2.p',t28_xboole_1)).

fof(f274,plain,
    ( r1_tarski(k1_tarski(sK1),u1_struct_0(sK0))
    | ~ spl7_30 ),
    inference(avatar_component_clause,[],[f273])).

fof(f320,plain,
    ( ~ spl7_28
    | spl7_31 ),
    inference(avatar_contradiction_clause,[],[f319])).

fof(f319,plain,
    ( $false
    | ~ spl7_28
    | ~ spl7_31 ),
    inference(subsumption_resolution,[],[f280,f266])).

fof(f280,plain,
    ( ~ m1_subset_1(k1_tarski(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl7_31 ),
    inference(resolution,[],[f277,f113])).

fof(f113,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/tex_2__t36_tex_2.p',t3_subset)).

fof(f277,plain,
    ( ~ r1_tarski(k1_tarski(sK1),u1_struct_0(sK0))
    | ~ spl7_31 ),
    inference(avatar_component_clause,[],[f276])).

fof(f276,plain,
    ( spl7_31
  <=> ~ r1_tarski(k1_tarski(sK1),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_31])])).

fof(f312,plain,
    ( ~ spl7_6
    | spl7_17
    | spl7_29
    | ~ spl7_34 ),
    inference(avatar_contradiction_clause,[],[f311])).

fof(f311,plain,
    ( $false
    | ~ spl7_6
    | ~ spl7_17
    | ~ spl7_29
    | ~ spl7_34 ),
    inference(subsumption_resolution,[],[f310,f193])).

fof(f310,plain,
    ( v1_xboole_0(u1_struct_0(sK0))
    | ~ spl7_6
    | ~ spl7_29
    | ~ spl7_34 ),
    inference(subsumption_resolution,[],[f309,f159])).

fof(f309,plain,
    ( ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | v1_xboole_0(u1_struct_0(sK0))
    | ~ spl7_29
    | ~ spl7_34 ),
    inference(subsumption_resolution,[],[f308,f269])).

fof(f269,plain,
    ( ~ m1_subset_1(k1_tarski(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl7_29 ),
    inference(avatar_component_clause,[],[f268])).

fof(f268,plain,
    ( spl7_29
  <=> ~ m1_subset_1(k1_tarski(sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_29])])).

fof(f308,plain,
    ( m1_subset_1(k1_tarski(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | v1_xboole_0(u1_struct_0(sK0))
    | ~ spl7_34 ),
    inference(superposition,[],[f289,f107])).

fof(f306,plain,
    ( ~ spl7_6
    | spl7_17
    | spl7_35 ),
    inference(avatar_contradiction_clause,[],[f305])).

fof(f305,plain,
    ( $false
    | ~ spl7_6
    | ~ spl7_17
    | ~ spl7_35 ),
    inference(subsumption_resolution,[],[f304,f193])).

fof(f304,plain,
    ( v1_xboole_0(u1_struct_0(sK0))
    | ~ spl7_6
    | ~ spl7_35 ),
    inference(subsumption_resolution,[],[f301,f159])).

fof(f301,plain,
    ( ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | v1_xboole_0(u1_struct_0(sK0))
    | ~ spl7_35 ),
    inference(resolution,[],[f292,f108])).

fof(f108,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f68])).

fof(f68,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f67])).

fof(f67,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,X0)
        & ~ v1_xboole_0(X0) )
     => m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/tex_2__t36_tex_2.p',dt_k6_domain_1)).

fof(f292,plain,
    ( ~ m1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl7_35 ),
    inference(avatar_component_clause,[],[f291])).

fof(f291,plain,
    ( spl7_35
  <=> ~ m1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_35])])).

fof(f225,plain,
    ( spl7_1
    | ~ spl7_12
    | ~ spl7_16 ),
    inference(avatar_contradiction_clause,[],[f224])).

fof(f224,plain,
    ( $false
    | ~ spl7_1
    | ~ spl7_12
    | ~ spl7_16 ),
    inference(subsumption_resolution,[],[f223,f131])).

fof(f131,plain,
    ( ~ v2_struct_0(sK0)
    | ~ spl7_1 ),
    inference(avatar_component_clause,[],[f130])).

fof(f130,plain,
    ( spl7_1
  <=> ~ v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).

fof(f223,plain,
    ( v2_struct_0(sK0)
    | ~ spl7_12
    | ~ spl7_16 ),
    inference(subsumption_resolution,[],[f220,f180])).

fof(f220,plain,
    ( ~ l1_struct_0(sK0)
    | v2_struct_0(sK0)
    | ~ spl7_16 ),
    inference(resolution,[],[f196,f97])).

fof(f97,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f55,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f54])).

fof(f54,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f26])).

fof(f26,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/tex_2__t36_tex_2.p',fc2_struct_0)).

fof(f196,plain,
    ( v1_xboole_0(u1_struct_0(sK0))
    | ~ spl7_16 ),
    inference(avatar_component_clause,[],[f195])).

fof(f195,plain,
    ( spl7_16
  <=> v1_xboole_0(u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_16])])).

fof(f206,plain,
    ( ~ spl7_4
    | spl7_13 ),
    inference(avatar_contradiction_clause,[],[f205])).

fof(f205,plain,
    ( $false
    | ~ spl7_4
    | ~ spl7_13 ),
    inference(subsumption_resolution,[],[f204,f145])).

fof(f204,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ spl7_13 ),
    inference(resolution,[],[f183,f85])).

fof(f85,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/tex_2__t36_tex_2.p',dt_l1_pre_topc)).

fof(f183,plain,
    ( ~ l1_struct_0(sK0)
    | ~ spl7_13 ),
    inference(avatar_component_clause,[],[f182])).

fof(f182,plain,
    ( spl7_13
  <=> ~ l1_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_13])])).

fof(f203,plain,
    ( spl7_16
    | ~ spl7_19
    | ~ spl7_6
    | spl7_9 ),
    inference(avatar_split_clause,[],[f169,f165,f158,f201,f195])).

fof(f169,plain,
    ( ~ v2_tex_2(k1_tarski(sK1),sK0)
    | v1_xboole_0(u1_struct_0(sK0))
    | ~ spl7_6
    | ~ spl7_9 ),
    inference(subsumption_resolution,[],[f168,f159])).

fof(f168,plain,
    ( ~ v2_tex_2(k1_tarski(sK1),sK0)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | v1_xboole_0(u1_struct_0(sK0))
    | ~ spl7_9 ),
    inference(superposition,[],[f166,f107])).

fof(f190,plain,
    ( ~ spl7_13
    | spl7_14
    | ~ spl7_10 ),
    inference(avatar_split_clause,[],[f177,f174,f188,f182])).

fof(f174,plain,
    ( spl7_10
  <=> v3_pre_topc(k2_struct_0(sK0),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_10])])).

fof(f177,plain,
    ( v3_pre_topc(u1_struct_0(sK0),sK0)
    | ~ l1_struct_0(sK0)
    | ~ spl7_10 ),
    inference(superposition,[],[f175,f93])).

fof(f175,plain,
    ( v3_pre_topc(k2_struct_0(sK0),sK0)
    | ~ spl7_10 ),
    inference(avatar_component_clause,[],[f174])).

fof(f176,plain,
    ( spl7_10
    | ~ spl7_2
    | ~ spl7_4 ),
    inference(avatar_split_clause,[],[f153,f144,f137,f174])).

fof(f153,plain,
    ( v3_pre_topc(k2_struct_0(sK0),sK0)
    | ~ spl7_2
    | ~ spl7_4 ),
    inference(subsumption_resolution,[],[f148,f138])).

fof(f148,plain,
    ( ~ v2_pre_topc(sK0)
    | v3_pre_topc(k2_struct_0(sK0),sK0)
    | ~ spl7_4 ),
    inference(resolution,[],[f145,f98])).

fof(f98,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v3_pre_topc(k2_struct_0(X0),X0) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f57,plain,(
    ! [X0] :
      ( v3_pre_topc(k2_struct_0(X0),X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f56])).

fof(f56,plain,(
    ! [X0] :
      ( v3_pre_topc(k2_struct_0(X0),X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f25])).

fof(f25,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => v3_pre_topc(k2_struct_0(X0),X0) ) ),
    file('/export/starexec/sandbox/benchmark/tex_2__t36_tex_2.p',fc10_tops_1)).

fof(f167,plain,(
    ~ spl7_9 ),
    inference(avatar_split_clause,[],[f79,f165])).

fof(f79,plain,(
    ~ v2_tex_2(k6_domain_1(u1_struct_0(sK0),sK1),sK0) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0)
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f44])).

fof(f44,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0)
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0) ) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/tex_2__t36_tex_2.p',t36_tex_2)).

fof(f160,plain,(
    spl7_6 ),
    inference(avatar_split_clause,[],[f78,f158])).

fof(f78,plain,(
    m1_subset_1(sK1,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f45])).

fof(f146,plain,(
    spl7_4 ),
    inference(avatar_split_clause,[],[f82,f144])).

fof(f82,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f45])).

fof(f139,plain,(
    spl7_2 ),
    inference(avatar_split_clause,[],[f81,f137])).

fof(f81,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f45])).

fof(f132,plain,(
    ~ spl7_1 ),
    inference(avatar_split_clause,[],[f80,f130])).

fof(f80,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f45])).
%------------------------------------------------------------------------------
