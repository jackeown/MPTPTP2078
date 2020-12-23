%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:03:11 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  197 ( 359 expanded)
%              Number of leaves         :   47 ( 156 expanded)
%              Depth                    :   10
%              Number of atoms          :  634 (1249 expanded)
%              Number of equality atoms :  103 ( 212 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1008,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f112,f117,f122,f137,f146,f164,f193,f246,f263,f328,f334,f347,f369,f513,f529,f632,f642,f776,f814,f819,f845,f859,f868,f881,f886,f890,f900,f910,f932,f944,f1001,f1006,f1007])).

fof(f1007,plain,
    ( k1_xboole_0 != sK0
    | sK3 != k7_relat_1(sK3,sK0)
    | sK0 != sK2
    | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f1006,plain,
    ( k1_xboole_0 != sK0
    | sK3 != k7_relat_1(sK3,sK0)
    | sK0 != sK2
    | v1_funct_2(k7_relat_1(sK3,sK2),sK2,sK1)
    | ~ v1_funct_2(sK3,sK0,sK1) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f1001,plain,
    ( ~ spl4_8
    | spl4_19 ),
    inference(avatar_contradiction_clause,[],[f1000])).

fof(f1000,plain,
    ( $false
    | ~ spl4_8
    | spl4_19 ),
    inference(subsumption_resolution,[],[f992,f65])).

fof(f65,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f992,plain,
    ( ~ r1_tarski(k1_xboole_0,sK2)
    | ~ spl4_8
    | spl4_19 ),
    inference(backward_demodulation,[],[f262,f145])).

fof(f145,plain,
    ( k1_xboole_0 = sK0
    | ~ spl4_8 ),
    inference(avatar_component_clause,[],[f143])).

fof(f143,plain,
    ( spl4_8
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).

fof(f262,plain,
    ( ~ r1_tarski(sK0,sK2)
    | spl4_19 ),
    inference(avatar_component_clause,[],[f260])).

fof(f260,plain,
    ( spl4_19
  <=> r1_tarski(sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_19])])).

fof(f944,plain,
    ( ~ spl4_84
    | spl4_85
    | ~ spl4_89 ),
    inference(avatar_contradiction_clause,[],[f943])).

fof(f943,plain,
    ( $false
    | ~ spl4_84
    | spl4_85
    | ~ spl4_89 ),
    inference(subsumption_resolution,[],[f939,f909])).

fof(f909,plain,
    ( ~ m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | spl4_85 ),
    inference(avatar_component_clause,[],[f907])).

fof(f907,plain,
    ( spl4_85
  <=> m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_85])])).

fof(f939,plain,
    ( m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ spl4_84
    | ~ spl4_89 ),
    inference(resolution,[],[f931,f889])).

fof(f889,plain,
    ( ! [X0] : r1_tarski(k2_relat_1(k7_relat_1(sK3,X0)),sK1)
    | ~ spl4_84 ),
    inference(avatar_component_clause,[],[f888])).

fof(f888,plain,
    ( spl4_84
  <=> ! [X0] : r1_tarski(k2_relat_1(k7_relat_1(sK3,X0)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_84])])).

fof(f931,plain,
    ( ! [X6] :
        ( ~ r1_tarski(k2_relat_1(k7_relat_1(sK3,sK2)),X6)
        | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,X6))) )
    | ~ spl4_89 ),
    inference(avatar_component_clause,[],[f930])).

fof(f930,plain,
    ( spl4_89
  <=> ! [X6] :
        ( m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,X6)))
        | ~ r1_tarski(k2_relat_1(k7_relat_1(sK3,sK2)),X6) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_89])])).

fof(f932,plain,
    ( spl4_89
    | ~ spl4_76
    | ~ spl4_82 ),
    inference(avatar_split_clause,[],[f924,f879,f816,f930])).

fof(f816,plain,
    ( spl4_76
  <=> sK2 = k1_relat_1(k7_relat_1(sK3,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_76])])).

fof(f879,plain,
    ( spl4_82
  <=> ! [X6] :
        ( m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k7_relat_1(sK3,sK2)),X6)))
        | ~ r1_tarski(k2_relat_1(k7_relat_1(sK3,sK2)),X6) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_82])])).

fof(f924,plain,
    ( ! [X6] :
        ( m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,X6)))
        | ~ r1_tarski(k2_relat_1(k7_relat_1(sK3,sK2)),X6) )
    | ~ spl4_76
    | ~ spl4_82 ),
    inference(forward_demodulation,[],[f880,f818])).

fof(f818,plain,
    ( sK2 = k1_relat_1(k7_relat_1(sK3,sK2))
    | ~ spl4_76 ),
    inference(avatar_component_clause,[],[f816])).

fof(f880,plain,
    ( ! [X6] :
        ( m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k7_relat_1(sK3,sK2)),X6)))
        | ~ r1_tarski(k2_relat_1(k7_relat_1(sK3,sK2)),X6) )
    | ~ spl4_82 ),
    inference(avatar_component_clause,[],[f879])).

fof(f910,plain,
    ( ~ spl4_85
    | spl4_26
    | ~ spl4_56 ),
    inference(avatar_split_clause,[],[f901,f630,f325,f907])).

fof(f325,plain,
    ( spl4_26
  <=> m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_26])])).

fof(f630,plain,
    ( spl4_56
  <=> ! [X0] : k7_relat_1(sK3,X0) = k2_partfun1(sK0,sK1,sK3,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_56])])).

fof(f901,plain,
    ( ~ m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | spl4_26
    | ~ spl4_56 ),
    inference(forward_demodulation,[],[f327,f631])).

fof(f631,plain,
    ( ! [X0] : k7_relat_1(sK3,X0) = k2_partfun1(sK0,sK1,sK3,X0)
    | ~ spl4_56 ),
    inference(avatar_component_clause,[],[f630])).

fof(f327,plain,
    ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | spl4_26 ),
    inference(avatar_component_clause,[],[f325])).

fof(f900,plain,
    ( spl4_58
    | ~ spl4_83
    | ~ spl4_84 ),
    inference(avatar_contradiction_clause,[],[f899])).

fof(f899,plain,
    ( $false
    | spl4_58
    | ~ spl4_83
    | ~ spl4_84 ),
    inference(subsumption_resolution,[],[f894,f641])).

fof(f641,plain,
    ( ~ v1_funct_2(k7_relat_1(sK3,sK2),sK2,sK1)
    | spl4_58 ),
    inference(avatar_component_clause,[],[f639])).

fof(f639,plain,
    ( spl4_58
  <=> v1_funct_2(k7_relat_1(sK3,sK2),sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_58])])).

fof(f894,plain,
    ( v1_funct_2(k7_relat_1(sK3,sK2),sK2,sK1)
    | ~ spl4_83
    | ~ spl4_84 ),
    inference(resolution,[],[f889,f885])).

fof(f885,plain,
    ( ! [X10] :
        ( ~ r1_tarski(k2_relat_1(k7_relat_1(sK3,sK2)),X10)
        | v1_funct_2(k7_relat_1(sK3,sK2),sK2,X10) )
    | ~ spl4_83 ),
    inference(avatar_component_clause,[],[f884])).

fof(f884,plain,
    ( spl4_83
  <=> ! [X10] :
        ( v1_funct_2(k7_relat_1(sK3,sK2),sK2,X10)
        | ~ r1_tarski(k2_relat_1(k7_relat_1(sK3,sK2)),X10) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_83])])).

fof(f890,plain,
    ( spl4_84
    | ~ spl4_77
    | ~ spl4_79 ),
    inference(avatar_split_clause,[],[f871,f857,f843,f888])).

fof(f843,plain,
    ( spl4_77
  <=> ! [X6] : v1_relat_1(k7_relat_1(sK3,X6)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_77])])).

fof(f857,plain,
    ( spl4_79
  <=> ! [X4] : v5_relat_1(k7_relat_1(sK3,X4),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_79])])).

fof(f871,plain,
    ( ! [X0] : r1_tarski(k2_relat_1(k7_relat_1(sK3,X0)),sK1)
    | ~ spl4_77
    | ~ spl4_79 ),
    inference(subsumption_resolution,[],[f869,f844])).

fof(f844,plain,
    ( ! [X6] : v1_relat_1(k7_relat_1(sK3,X6))
    | ~ spl4_77 ),
    inference(avatar_component_clause,[],[f843])).

fof(f869,plain,
    ( ! [X0] :
        ( r1_tarski(k2_relat_1(k7_relat_1(sK3,X0)),sK1)
        | ~ v1_relat_1(k7_relat_1(sK3,X0)) )
    | ~ spl4_79 ),
    inference(resolution,[],[f858,f70])).

fof(f70,plain,(
    ! [X0,X1] :
      ( ~ v5_relat_1(X1,X0)
      | r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( ( ( v5_relat_1(X1,X0)
          | ~ r1_tarski(k2_relat_1(X1),X0) )
        & ( r1_tarski(k2_relat_1(X1),X0)
          | ~ v5_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).

fof(f858,plain,
    ( ! [X4] : v5_relat_1(k7_relat_1(sK3,X4),sK1)
    | ~ spl4_79 ),
    inference(avatar_component_clause,[],[f857])).

fof(f886,plain,
    ( spl4_83
    | ~ spl4_76
    | ~ spl4_81 ),
    inference(avatar_split_clause,[],[f882,f866,f816,f884])).

fof(f866,plain,
    ( spl4_81
  <=> ! [X10] :
        ( v1_funct_2(k7_relat_1(sK3,sK2),k1_relat_1(k7_relat_1(sK3,sK2)),X10)
        | ~ r1_tarski(k2_relat_1(k7_relat_1(sK3,sK2)),X10) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_81])])).

fof(f882,plain,
    ( ! [X10] :
        ( v1_funct_2(k7_relat_1(sK3,sK2),sK2,X10)
        | ~ r1_tarski(k2_relat_1(k7_relat_1(sK3,sK2)),X10) )
    | ~ spl4_76
    | ~ spl4_81 ),
    inference(backward_demodulation,[],[f867,f818])).

fof(f867,plain,
    ( ! [X10] :
        ( v1_funct_2(k7_relat_1(sK3,sK2),k1_relat_1(k7_relat_1(sK3,sK2)),X10)
        | ~ r1_tarski(k2_relat_1(k7_relat_1(sK3,sK2)),X10) )
    | ~ spl4_81 ),
    inference(avatar_component_clause,[],[f866])).

fof(f881,plain,
    ( spl4_82
    | ~ spl4_24
    | ~ spl4_56
    | ~ spl4_77 ),
    inference(avatar_split_clause,[],[f877,f843,f630,f317,f879])).

fof(f317,plain,
    ( spl4_24
  <=> v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_24])])).

fof(f877,plain,
    ( ! [X6] :
        ( m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k7_relat_1(sK3,sK2)),X6)))
        | ~ r1_tarski(k2_relat_1(k7_relat_1(sK3,sK2)),X6) )
    | ~ spl4_24
    | ~ spl4_56
    | ~ spl4_77 ),
    inference(subsumption_resolution,[],[f833,f844])).

fof(f833,plain,
    ( ! [X6] :
        ( ~ v1_relat_1(k7_relat_1(sK3,sK2))
        | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k7_relat_1(sK3,sK2)),X6)))
        | ~ r1_tarski(k2_relat_1(k7_relat_1(sK3,sK2)),X6) )
    | ~ spl4_24
    | ~ spl4_56 ),
    inference(forward_demodulation,[],[f832,f631])).

fof(f832,plain,
    ( ! [X6] :
        ( m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k7_relat_1(sK3,sK2)),X6)))
        | ~ r1_tarski(k2_relat_1(k7_relat_1(sK3,sK2)),X6)
        | ~ v1_relat_1(k2_partfun1(sK0,sK1,sK3,sK2)) )
    | ~ spl4_24
    | ~ spl4_56 ),
    inference(forward_demodulation,[],[f831,f631])).

fof(f831,plain,
    ( ! [X6] :
        ( ~ r1_tarski(k2_relat_1(k7_relat_1(sK3,sK2)),X6)
        | m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_partfun1(sK0,sK1,sK3,sK2)),X6)))
        | ~ v1_relat_1(k2_partfun1(sK0,sK1,sK3,sK2)) )
    | ~ spl4_24
    | ~ spl4_56 ),
    inference(forward_demodulation,[],[f339,f631])).

fof(f339,plain,
    ( ! [X6] :
        ( ~ r1_tarski(k2_relat_1(k2_partfun1(sK0,sK1,sK3,sK2)),X6)
        | m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_partfun1(sK0,sK1,sK3,sK2)),X6)))
        | ~ v1_relat_1(k2_partfun1(sK0,sK1,sK3,sK2)) )
    | ~ spl4_24 ),
    inference(resolution,[],[f318,f74])).

fof(f74,plain,(
    ! [X0,X1] :
      ( ~ v1_funct_1(X1)
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
        & v1_funct_2(X1,k1_relat_1(X1),X0)
        & v1_funct_1(X1) )
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
        & v1_funct_2(X1,k1_relat_1(X1),X0)
        & v1_funct_1(X1) )
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( r1_tarski(k2_relat_1(X1),X0)
       => ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
          & v1_funct_2(X1,k1_relat_1(X1),X0)
          & v1_funct_1(X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_funct_2)).

fof(f318,plain,
    ( v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))
    | ~ spl4_24 ),
    inference(avatar_component_clause,[],[f317])).

fof(f868,plain,
    ( spl4_81
    | ~ spl4_24
    | ~ spl4_56
    | ~ spl4_77 ),
    inference(avatar_split_clause,[],[f860,f843,f630,f317,f866])).

fof(f860,plain,
    ( ! [X10] :
        ( v1_funct_2(k7_relat_1(sK3,sK2),k1_relat_1(k7_relat_1(sK3,sK2)),X10)
        | ~ r1_tarski(k2_relat_1(k7_relat_1(sK3,sK2)),X10) )
    | ~ spl4_24
    | ~ spl4_56
    | ~ spl4_77 ),
    inference(subsumption_resolution,[],[f836,f844])).

fof(f836,plain,
    ( ! [X10] :
        ( ~ v1_relat_1(k7_relat_1(sK3,sK2))
        | v1_funct_2(k7_relat_1(sK3,sK2),k1_relat_1(k7_relat_1(sK3,sK2)),X10)
        | ~ r1_tarski(k2_relat_1(k7_relat_1(sK3,sK2)),X10) )
    | ~ spl4_24
    | ~ spl4_56 ),
    inference(forward_demodulation,[],[f835,f631])).

fof(f835,plain,
    ( ! [X10] :
        ( v1_funct_2(k7_relat_1(sK3,sK2),k1_relat_1(k7_relat_1(sK3,sK2)),X10)
        | ~ r1_tarski(k2_relat_1(k7_relat_1(sK3,sK2)),X10)
        | ~ v1_relat_1(k2_partfun1(sK0,sK1,sK3,sK2)) )
    | ~ spl4_24
    | ~ spl4_56 ),
    inference(forward_demodulation,[],[f834,f631])).

fof(f834,plain,
    ( ! [X10] :
        ( ~ r1_tarski(k2_relat_1(k7_relat_1(sK3,sK2)),X10)
        | v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),k1_relat_1(k2_partfun1(sK0,sK1,sK3,sK2)),X10)
        | ~ v1_relat_1(k2_partfun1(sK0,sK1,sK3,sK2)) )
    | ~ spl4_24
    | ~ spl4_56 ),
    inference(forward_demodulation,[],[f341,f631])).

fof(f341,plain,
    ( ! [X10] :
        ( ~ r1_tarski(k2_relat_1(k2_partfun1(sK0,sK1,sK3,sK2)),X10)
        | v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),k1_relat_1(k2_partfun1(sK0,sK1,sK3,sK2)),X10)
        | ~ v1_relat_1(k2_partfun1(sK0,sK1,sK3,sK2)) )
    | ~ spl4_24 ),
    inference(resolution,[],[f318,f73])).

fof(f73,plain,(
    ! [X0,X1] :
      ( ~ v1_funct_1(X1)
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | v1_funct_2(X1,k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f859,plain,
    ( spl4_79
    | ~ spl4_75 ),
    inference(avatar_split_clause,[],[f825,f812,f857])).

fof(f812,plain,
    ( spl4_75
  <=> ! [X0] : m1_subset_1(k7_relat_1(sK3,X0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_75])])).

fof(f825,plain,
    ( ! [X4] : v5_relat_1(k7_relat_1(sK3,X4),sK1)
    | ~ spl4_75 ),
    inference(resolution,[],[f813,f87])).

fof(f87,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v5_relat_1(X2,X1) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f813,plain,
    ( ! [X0] : m1_subset_1(k7_relat_1(sK3,X0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl4_75 ),
    inference(avatar_component_clause,[],[f812])).

fof(f845,plain,
    ( spl4_77
    | ~ spl4_75 ),
    inference(avatar_split_clause,[],[f827,f812,f843])).

fof(f827,plain,
    ( ! [X6] : v1_relat_1(k7_relat_1(sK3,X6))
    | ~ spl4_75 ),
    inference(resolution,[],[f813,f84])).

fof(f84,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f819,plain,
    ( spl4_76
    | ~ spl4_2
    | ~ spl4_68 ),
    inference(avatar_split_clause,[],[f780,f774,f114,f816])).

fof(f114,plain,
    ( spl4_2
  <=> r1_tarski(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f774,plain,
    ( spl4_68
  <=> ! [X0] :
        ( ~ r1_tarski(X0,sK0)
        | k1_relat_1(k7_relat_1(sK3,X0)) = X0 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_68])])).

fof(f780,plain,
    ( sK2 = k1_relat_1(k7_relat_1(sK3,sK2))
    | ~ spl4_2
    | ~ spl4_68 ),
    inference(resolution,[],[f775,f116])).

fof(f116,plain,
    ( r1_tarski(sK2,sK0)
    | ~ spl4_2 ),
    inference(avatar_component_clause,[],[f114])).

fof(f775,plain,
    ( ! [X0] :
        ( ~ r1_tarski(X0,sK0)
        | k1_relat_1(k7_relat_1(sK3,X0)) = X0 )
    | ~ spl4_68 ),
    inference(avatar_component_clause,[],[f774])).

fof(f814,plain,
    ( spl4_75
    | ~ spl4_6
    | ~ spl4_42
    | ~ spl4_56 ),
    inference(avatar_split_clause,[],[f810,f630,f527,f134,f812])).

fof(f134,plain,
    ( spl4_6
  <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).

fof(f527,plain,
    ( spl4_42
  <=> ! [X1,X0,X2] :
        ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | m1_subset_1(k2_partfun1(X0,X1,sK3,X2),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_42])])).

fof(f810,plain,
    ( ! [X0] : m1_subset_1(k7_relat_1(sK3,X0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl4_6
    | ~ spl4_42
    | ~ spl4_56 ),
    inference(forward_demodulation,[],[f543,f631])).

fof(f543,plain,
    ( ! [X0] : m1_subset_1(k2_partfun1(sK0,sK1,sK3,X0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl4_6
    | ~ spl4_42 ),
    inference(resolution,[],[f528,f136])).

fof(f136,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl4_6 ),
    inference(avatar_component_clause,[],[f134])).

fof(f528,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | m1_subset_1(k2_partfun1(X0,X1,sK3,X2),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
    | ~ spl4_42 ),
    inference(avatar_component_clause,[],[f527])).

fof(f776,plain,
    ( spl4_68
    | ~ spl4_10
    | ~ spl4_30 ),
    inference(avatar_split_clause,[],[f772,f366,f161,f774])).

fof(f161,plain,
    ( spl4_10
  <=> v1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).

fof(f366,plain,
    ( spl4_30
  <=> sK0 = k1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_30])])).

fof(f772,plain,
    ( ! [X0] :
        ( ~ r1_tarski(X0,sK0)
        | k1_relat_1(k7_relat_1(sK3,X0)) = X0 )
    | ~ spl4_10
    | ~ spl4_30 ),
    inference(forward_demodulation,[],[f221,f368])).

fof(f368,plain,
    ( sK0 = k1_relat_1(sK3)
    | ~ spl4_30 ),
    inference(avatar_component_clause,[],[f366])).

fof(f221,plain,
    ( ! [X0] :
        ( ~ r1_tarski(X0,k1_relat_1(sK3))
        | k1_relat_1(k7_relat_1(sK3,X0)) = X0 )
    | ~ spl4_10 ),
    inference(resolution,[],[f69,f163])).

fof(f163,plain,
    ( v1_relat_1(sK3)
    | ~ spl4_10 ),
    inference(avatar_component_clause,[],[f161])).

fof(f69,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | k1_relat_1(k7_relat_1(X1,X0)) = X0 ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(X0,k1_relat_1(X1))
       => k1_relat_1(k7_relat_1(X1,X0)) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_relat_1)).

fof(f642,plain,
    ( ~ spl4_58
    | ~ spl4_6
    | spl4_25
    | ~ spl4_39 ),
    inference(avatar_split_clause,[],[f623,f511,f321,f134,f639])).

fof(f321,plain,
    ( spl4_25
  <=> v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_25])])).

fof(f511,plain,
    ( spl4_39
  <=> ! [X1,X0,X2] :
        ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | k2_partfun1(X0,X1,sK3,X2) = k7_relat_1(sK3,X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_39])])).

fof(f623,plain,
    ( ~ v1_funct_2(k7_relat_1(sK3,sK2),sK2,sK1)
    | ~ spl4_6
    | spl4_25
    | ~ spl4_39 ),
    inference(backward_demodulation,[],[f323,f518])).

fof(f518,plain,
    ( ! [X0] : k7_relat_1(sK3,X0) = k2_partfun1(sK0,sK1,sK3,X0)
    | ~ spl4_6
    | ~ spl4_39 ),
    inference(resolution,[],[f512,f136])).

fof(f512,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | k2_partfun1(X0,X1,sK3,X2) = k7_relat_1(sK3,X2) )
    | ~ spl4_39 ),
    inference(avatar_component_clause,[],[f511])).

fof(f323,plain,
    ( ~ v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1)
    | spl4_25 ),
    inference(avatar_component_clause,[],[f321])).

fof(f632,plain,
    ( spl4_56
    | ~ spl4_6
    | ~ spl4_39 ),
    inference(avatar_split_clause,[],[f518,f511,f134,f630])).

fof(f529,plain,
    ( spl4_42
    | ~ spl4_1 ),
    inference(avatar_split_clause,[],[f286,f109,f527])).

fof(f109,plain,
    ( spl4_1
  <=> v1_funct_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f286,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | m1_subset_1(k2_partfun1(X0,X1,sK3,X2),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
    | ~ spl4_1 ),
    inference(resolution,[],[f98,f111])).

fof(f111,plain,
    ( v1_funct_1(sK3)
    | ~ spl4_1 ),
    inference(avatar_component_clause,[],[f109])).

fof(f98,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(k2_partfun1(X0,X1,X2,X3)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f46])).

fof(f46,plain,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(k2_partfun1(X0,X1,X2,X3)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => ( m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(k2_partfun1(X0,X1,X2,X3)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_partfun1)).

fof(f513,plain,
    ( spl4_39
    | ~ spl4_1 ),
    inference(avatar_split_clause,[],[f280,f109,f511])).

fof(f280,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | k2_partfun1(X0,X1,sK3,X2) = k7_relat_1(sK3,X2) )
    | ~ spl4_1 ),
    inference(resolution,[],[f96,f111])).

fof(f96,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0,X1,X2,X3] :
      ( k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f44])).

fof(f44,plain,(
    ! [X0,X1,X2,X3] :
      ( k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_partfun1)).

fof(f369,plain,
    ( spl4_30
    | ~ spl4_6
    | ~ spl4_28 ),
    inference(avatar_split_clause,[],[f364,f344,f134,f366])).

fof(f344,plain,
    ( spl4_28
  <=> sK0 = k1_relset_1(sK0,sK1,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_28])])).

fof(f364,plain,
    ( sK0 = k1_relat_1(sK3)
    | ~ spl4_6
    | ~ spl4_28 ),
    inference(forward_demodulation,[],[f234,f346])).

fof(f346,plain,
    ( sK0 = k1_relset_1(sK0,sK1,sK3)
    | ~ spl4_28 ),
    inference(avatar_component_clause,[],[f344])).

fof(f234,plain,
    ( k1_relat_1(sK3) = k1_relset_1(sK0,sK1,sK3)
    | ~ spl4_6 ),
    inference(resolution,[],[f85,f136])).

fof(f85,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f347,plain,
    ( spl4_28
    | ~ spl4_3
    | ~ spl4_6
    | spl4_7 ),
    inference(avatar_split_clause,[],[f305,f139,f134,f119,f344])).

fof(f119,plain,
    ( spl4_3
  <=> v1_funct_2(sK3,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f139,plain,
    ( spl4_7
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).

fof(f305,plain,
    ( sK0 = k1_relset_1(sK0,sK1,sK3)
    | ~ spl4_3
    | ~ spl4_6
    | spl4_7 ),
    inference(subsumption_resolution,[],[f304,f136])).

fof(f304,plain,
    ( sK0 = k1_relset_1(sK0,sK1,sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl4_3
    | spl4_7 ),
    inference(subsumption_resolution,[],[f302,f141])).

fof(f141,plain,
    ( k1_xboole_0 != sK1
    | spl4_7 ),
    inference(avatar_component_clause,[],[f139])).

fof(f302,plain,
    ( sK0 = k1_relset_1(sK0,sK1,sK3)
    | k1_xboole_0 = sK1
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl4_3 ),
    inference(resolution,[],[f88,f121])).

fof(f121,plain,
    ( v1_funct_2(sK3,sK0,sK1)
    | ~ spl4_3 ),
    inference(avatar_component_clause,[],[f119])).

fof(f88,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_2(X2,X0,X1)
      | k1_relset_1(X0,X1,X2) = X0
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f56])).

fof(f56,plain,(
    ! [X0,X1,X2] :
      ( ( ( ( ( v1_funct_2(X2,X0,X1)
              | k1_xboole_0 != X2 )
            & ( k1_xboole_0 = X2
              | ~ v1_funct_2(X2,X0,X1) ) )
          | k1_xboole_0 = X0
          | k1_xboole_0 != X1 )
        & ( ( ( v1_funct_2(X2,X0,X1)
              | k1_relset_1(X0,X1,X2) != X0 )
            & ( k1_relset_1(X0,X1,X2) = X0
              | ~ v1_funct_2(X2,X0,X1) ) )
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 ) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(nnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1,X2] :
      ( ( ( ( v1_funct_2(X2,X0,X1)
          <=> k1_xboole_0 = X2 )
          | k1_xboole_0 = X0
          | k1_xboole_0 != X1 )
        & ( ( v1_funct_2(X2,X0,X1)
          <=> k1_relset_1(X0,X1,X2) = X0 )
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 ) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f38])).

fof(f38,plain,(
    ! [X0,X1,X2] :
      ( ( ( ( v1_funct_2(X2,X0,X1)
          <=> k1_xboole_0 = X2 )
          | k1_xboole_0 = X0
          | k1_xboole_0 != X1 )
        & ( ( v1_funct_2(X2,X0,X1)
          <=> k1_relset_1(X0,X1,X2) = X0 )
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 ) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( ( k1_xboole_0 = X1
         => ( ( v1_funct_2(X2,X0,X1)
            <=> k1_xboole_0 = X2 )
            | k1_xboole_0 = X0 ) )
        & ( ( k1_xboole_0 = X1
           => k1_xboole_0 = X0 )
         => ( v1_funct_2(X2,X0,X1)
          <=> k1_relset_1(X0,X1,X2) = X0 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_funct_2)).

fof(f334,plain,
    ( ~ spl4_1
    | ~ spl4_6
    | spl4_24 ),
    inference(avatar_contradiction_clause,[],[f333])).

fof(f333,plain,
    ( $false
    | ~ spl4_1
    | ~ spl4_6
    | spl4_24 ),
    inference(unit_resulting_resolution,[],[f111,f136,f319,f97])).

fof(f97,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_funct_1(k2_partfun1(X0,X1,X2,X3)) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f319,plain,
    ( ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))
    | spl4_24 ),
    inference(avatar_component_clause,[],[f317])).

fof(f328,plain,
    ( ~ spl4_24
    | ~ spl4_25
    | ~ spl4_26 ),
    inference(avatar_split_clause,[],[f62,f325,f321,f317])).

fof(f62,plain,
    ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1)
    | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) ),
    inference(cnf_transformation,[],[f49])).

fof(f49,plain,
    ( ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
      | ~ v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1)
      | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) )
    & ( k1_xboole_0 = sK0
      | k1_xboole_0 != sK1 )
    & r1_tarski(sK2,sK0)
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    & v1_funct_2(sK3,sK0,sK1)
    & v1_funct_1(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f24,f48])).

fof(f48,plain,
    ( ? [X0,X1,X2,X3] :
        ( ( ~ m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
          | ~ v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1)
          | ~ v1_funct_1(k2_partfun1(X0,X1,X3,X2)) )
        & ( k1_xboole_0 = X0
          | k1_xboole_0 != X1 )
        & r1_tarski(X2,X0)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
   => ( ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
        | ~ v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1)
        | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) )
      & ( k1_xboole_0 = sK0
        | k1_xboole_0 != sK1 )
      & r1_tarski(sK2,sK0)
      & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      & v1_funct_2(sK3,sK0,sK1)
      & v1_funct_1(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,(
    ? [X0,X1,X2,X3] :
      ( ( ~ m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
        | ~ v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1)
        | ~ v1_funct_1(k2_partfun1(X0,X1,X3,X2)) )
      & ( k1_xboole_0 = X0
        | k1_xboole_0 != X1 )
      & r1_tarski(X2,X0)
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X3,X0,X1)
      & v1_funct_1(X3) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ? [X0,X1,X2,X3] :
      ( ( ~ m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
        | ~ v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1)
        | ~ v1_funct_1(k2_partfun1(X0,X1,X3,X2)) )
      & ( k1_xboole_0 = X0
        | k1_xboole_0 != X1 )
      & r1_tarski(X2,X0)
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X3,X0,X1)
      & v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X3,X0,X1)
          & v1_funct_1(X3) )
       => ( r1_tarski(X2,X0)
         => ( ( m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
              & v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1)
              & v1_funct_1(k2_partfun1(X0,X1,X3,X2)) )
            | ( k1_xboole_0 != X0
              & k1_xboole_0 = X1 ) ) ) ) ),
    inference(negated_conjecture,[],[f21])).

fof(f21,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
     => ( r1_tarski(X2,X0)
       => ( ( m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
            & v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1)
            & v1_funct_1(k2_partfun1(X0,X1,X3,X2)) )
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_funct_2)).

fof(f263,plain,
    ( spl4_18
    | ~ spl4_19
    | ~ spl4_2 ),
    inference(avatar_split_clause,[],[f177,f114,f260,f256])).

fof(f256,plain,
    ( spl4_18
  <=> sK0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_18])])).

fof(f177,plain,
    ( ~ r1_tarski(sK0,sK2)
    | sK0 = sK2
    | ~ spl4_2 ),
    inference(resolution,[],[f78,f116])).

fof(f78,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r1_tarski(X1,X0)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f51])).

fof(f51,plain,(
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

fof(f246,plain,
    ( spl4_16
    | ~ spl4_10
    | ~ spl4_13 ),
    inference(avatar_split_clause,[],[f212,f190,f161,f243])).

fof(f243,plain,
    ( spl4_16
  <=> sK3 = k7_relat_1(sK3,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_16])])).

fof(f190,plain,
    ( spl4_13
  <=> v4_relat_1(sK3,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_13])])).

fof(f212,plain,
    ( sK3 = k7_relat_1(sK3,sK0)
    | ~ spl4_10
    | ~ spl4_13 ),
    inference(subsumption_resolution,[],[f211,f163])).

fof(f211,plain,
    ( sK3 = k7_relat_1(sK3,sK0)
    | ~ v1_relat_1(sK3)
    | ~ spl4_13 ),
    inference(resolution,[],[f75,f192])).

fof(f192,plain,
    ( v4_relat_1(sK3,sK0)
    | ~ spl4_13 ),
    inference(avatar_component_clause,[],[f190])).

fof(f75,plain,(
    ! [X0,X1] :
      ( ~ v4_relat_1(X1,X0)
      | k7_relat_1(X1,X0) = X1
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f33])).

% (2166)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_364 on theBenchmark
% (2139)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
fof(f33,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => k7_relat_1(X1,X0) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t209_relat_1)).

fof(f193,plain,
    ( spl4_13
    | ~ spl4_6 ),
    inference(avatar_split_clause,[],[f185,f134,f190])).

fof(f185,plain,
    ( v4_relat_1(sK3,sK0)
    | ~ spl4_6 ),
    inference(resolution,[],[f86,f136])).

fof(f86,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v4_relat_1(X2,X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f164,plain,
    ( spl4_10
    | ~ spl4_6 ),
    inference(avatar_split_clause,[],[f156,f134,f161])).

fof(f156,plain,
    ( v1_relat_1(sK3)
    | ~ spl4_6 ),
    inference(resolution,[],[f84,f136])).

fof(f146,plain,
    ( ~ spl4_7
    | spl4_8 ),
    inference(avatar_split_clause,[],[f61,f143,f139])).

fof(f61,plain,
    ( k1_xboole_0 = sK0
    | k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f49])).

fof(f137,plain,(
    spl4_6 ),
    inference(avatar_split_clause,[],[f59,f134])).

fof(f59,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f49])).

fof(f122,plain,(
    spl4_3 ),
    inference(avatar_split_clause,[],[f58,f119])).

fof(f58,plain,(
    v1_funct_2(sK3,sK0,sK1) ),
    inference(cnf_transformation,[],[f49])).

fof(f117,plain,(
    spl4_2 ),
    inference(avatar_split_clause,[],[f60,f114])).

fof(f60,plain,(
    r1_tarski(sK2,sK0) ),
    inference(cnf_transformation,[],[f49])).

fof(f112,plain,(
    spl4_1 ),
    inference(avatar_split_clause,[],[f57,f109])).

fof(f57,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f49])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 16:08:54 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.47  % (2143)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.20/0.48  % (2142)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.20/0.49  % (2153)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 0.20/0.49  % (2144)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.20/0.50  % (2161)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 0.20/0.50  % (2146)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 0.20/0.51  % (2152)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 0.20/0.51  % (2141)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 0.20/0.51  % (2159)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 0.20/0.51  % (2164)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 0.20/0.52  % (2145)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.20/0.52  % (2149)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
% 0.20/0.52  % (2158)lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_145 on theBenchmark
% 0.20/0.52  % (2155)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 0.20/0.52  % (2151)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 0.20/0.52  % (2163)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 0.20/0.53  % (2160)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 0.20/0.53  % (2154)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.20/0.53  % (2162)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 0.20/0.53  % (2147)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 0.20/0.53  % (2150)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 0.20/0.53  % (2148)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 0.20/0.53  % (2142)Refutation found. Thanks to Tanya!
% 0.20/0.53  % SZS status Theorem for theBenchmark
% 0.20/0.53  % SZS output start Proof for theBenchmark
% 0.20/0.53  fof(f1008,plain,(
% 0.20/0.53    $false),
% 0.20/0.53    inference(avatar_sat_refutation,[],[f112,f117,f122,f137,f146,f164,f193,f246,f263,f328,f334,f347,f369,f513,f529,f632,f642,f776,f814,f819,f845,f859,f868,f881,f886,f890,f900,f910,f932,f944,f1001,f1006,f1007])).
% 0.20/0.53  fof(f1007,plain,(
% 0.20/0.53    k1_xboole_0 != sK0 | sK3 != k7_relat_1(sK3,sK0) | sK0 != sK2 | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.20/0.53    introduced(theory_tautology_sat_conflict,[])).
% 0.20/0.53  fof(f1006,plain,(
% 0.20/0.53    k1_xboole_0 != sK0 | sK3 != k7_relat_1(sK3,sK0) | sK0 != sK2 | v1_funct_2(k7_relat_1(sK3,sK2),sK2,sK1) | ~v1_funct_2(sK3,sK0,sK1)),
% 0.20/0.53    introduced(theory_tautology_sat_conflict,[])).
% 0.20/0.53  fof(f1001,plain,(
% 0.20/0.53    ~spl4_8 | spl4_19),
% 0.20/0.53    inference(avatar_contradiction_clause,[],[f1000])).
% 0.20/0.53  fof(f1000,plain,(
% 0.20/0.53    $false | (~spl4_8 | spl4_19)),
% 0.20/0.53    inference(subsumption_resolution,[],[f992,f65])).
% 0.20/0.53  fof(f65,plain,(
% 0.20/0.53    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 0.20/0.53    inference(cnf_transformation,[],[f3])).
% 0.20/0.53  fof(f3,axiom,(
% 0.20/0.53    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 0.20/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).
% 0.20/0.53  fof(f992,plain,(
% 0.20/0.53    ~r1_tarski(k1_xboole_0,sK2) | (~spl4_8 | spl4_19)),
% 0.20/0.53    inference(backward_demodulation,[],[f262,f145])).
% 0.20/0.53  fof(f145,plain,(
% 0.20/0.53    k1_xboole_0 = sK0 | ~spl4_8),
% 0.20/0.53    inference(avatar_component_clause,[],[f143])).
% 0.20/0.53  fof(f143,plain,(
% 0.20/0.53    spl4_8 <=> k1_xboole_0 = sK0),
% 0.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).
% 0.20/0.53  fof(f262,plain,(
% 0.20/0.53    ~r1_tarski(sK0,sK2) | spl4_19),
% 0.20/0.53    inference(avatar_component_clause,[],[f260])).
% 0.20/0.53  fof(f260,plain,(
% 0.20/0.53    spl4_19 <=> r1_tarski(sK0,sK2)),
% 0.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl4_19])])).
% 0.20/0.53  fof(f944,plain,(
% 0.20/0.53    ~spl4_84 | spl4_85 | ~spl4_89),
% 0.20/0.53    inference(avatar_contradiction_clause,[],[f943])).
% 0.20/0.53  fof(f943,plain,(
% 0.20/0.53    $false | (~spl4_84 | spl4_85 | ~spl4_89)),
% 0.20/0.53    inference(subsumption_resolution,[],[f939,f909])).
% 0.20/0.53  fof(f909,plain,(
% 0.20/0.53    ~m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | spl4_85),
% 0.20/0.53    inference(avatar_component_clause,[],[f907])).
% 0.20/0.53  fof(f907,plain,(
% 0.20/0.53    spl4_85 <=> m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))),
% 0.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl4_85])])).
% 0.20/0.53  fof(f939,plain,(
% 0.20/0.53    m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | (~spl4_84 | ~spl4_89)),
% 0.20/0.53    inference(resolution,[],[f931,f889])).
% 0.20/0.53  fof(f889,plain,(
% 0.20/0.53    ( ! [X0] : (r1_tarski(k2_relat_1(k7_relat_1(sK3,X0)),sK1)) ) | ~spl4_84),
% 0.20/0.53    inference(avatar_component_clause,[],[f888])).
% 0.20/0.53  fof(f888,plain,(
% 0.20/0.53    spl4_84 <=> ! [X0] : r1_tarski(k2_relat_1(k7_relat_1(sK3,X0)),sK1)),
% 0.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl4_84])])).
% 0.20/0.53  fof(f931,plain,(
% 0.20/0.53    ( ! [X6] : (~r1_tarski(k2_relat_1(k7_relat_1(sK3,sK2)),X6) | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,X6)))) ) | ~spl4_89),
% 0.20/0.53    inference(avatar_component_clause,[],[f930])).
% 0.20/0.53  fof(f930,plain,(
% 0.20/0.53    spl4_89 <=> ! [X6] : (m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,X6))) | ~r1_tarski(k2_relat_1(k7_relat_1(sK3,sK2)),X6))),
% 0.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl4_89])])).
% 0.20/0.53  fof(f932,plain,(
% 0.20/0.53    spl4_89 | ~spl4_76 | ~spl4_82),
% 0.20/0.53    inference(avatar_split_clause,[],[f924,f879,f816,f930])).
% 0.20/0.53  fof(f816,plain,(
% 0.20/0.53    spl4_76 <=> sK2 = k1_relat_1(k7_relat_1(sK3,sK2))),
% 0.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl4_76])])).
% 0.20/0.53  fof(f879,plain,(
% 0.20/0.53    spl4_82 <=> ! [X6] : (m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k7_relat_1(sK3,sK2)),X6))) | ~r1_tarski(k2_relat_1(k7_relat_1(sK3,sK2)),X6))),
% 0.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl4_82])])).
% 0.20/0.53  fof(f924,plain,(
% 0.20/0.53    ( ! [X6] : (m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,X6))) | ~r1_tarski(k2_relat_1(k7_relat_1(sK3,sK2)),X6)) ) | (~spl4_76 | ~spl4_82)),
% 0.20/0.53    inference(forward_demodulation,[],[f880,f818])).
% 0.20/0.53  fof(f818,plain,(
% 0.20/0.53    sK2 = k1_relat_1(k7_relat_1(sK3,sK2)) | ~spl4_76),
% 0.20/0.53    inference(avatar_component_clause,[],[f816])).
% 0.20/0.53  fof(f880,plain,(
% 0.20/0.53    ( ! [X6] : (m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k7_relat_1(sK3,sK2)),X6))) | ~r1_tarski(k2_relat_1(k7_relat_1(sK3,sK2)),X6)) ) | ~spl4_82),
% 0.20/0.53    inference(avatar_component_clause,[],[f879])).
% 0.20/0.53  fof(f910,plain,(
% 0.20/0.53    ~spl4_85 | spl4_26 | ~spl4_56),
% 0.20/0.53    inference(avatar_split_clause,[],[f901,f630,f325,f907])).
% 0.20/0.53  fof(f325,plain,(
% 0.20/0.53    spl4_26 <=> m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))),
% 0.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl4_26])])).
% 0.20/0.53  fof(f630,plain,(
% 0.20/0.53    spl4_56 <=> ! [X0] : k7_relat_1(sK3,X0) = k2_partfun1(sK0,sK1,sK3,X0)),
% 0.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl4_56])])).
% 0.20/0.53  fof(f901,plain,(
% 0.20/0.53    ~m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | (spl4_26 | ~spl4_56)),
% 0.20/0.53    inference(forward_demodulation,[],[f327,f631])).
% 0.20/0.53  fof(f631,plain,(
% 0.20/0.53    ( ! [X0] : (k7_relat_1(sK3,X0) = k2_partfun1(sK0,sK1,sK3,X0)) ) | ~spl4_56),
% 0.20/0.53    inference(avatar_component_clause,[],[f630])).
% 0.20/0.53  fof(f327,plain,(
% 0.20/0.53    ~m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | spl4_26),
% 0.20/0.53    inference(avatar_component_clause,[],[f325])).
% 0.20/0.53  fof(f900,plain,(
% 0.20/0.53    spl4_58 | ~spl4_83 | ~spl4_84),
% 0.20/0.53    inference(avatar_contradiction_clause,[],[f899])).
% 0.20/0.53  fof(f899,plain,(
% 0.20/0.53    $false | (spl4_58 | ~spl4_83 | ~spl4_84)),
% 0.20/0.53    inference(subsumption_resolution,[],[f894,f641])).
% 0.20/0.53  fof(f641,plain,(
% 0.20/0.53    ~v1_funct_2(k7_relat_1(sK3,sK2),sK2,sK1) | spl4_58),
% 0.20/0.53    inference(avatar_component_clause,[],[f639])).
% 0.20/0.53  fof(f639,plain,(
% 0.20/0.53    spl4_58 <=> v1_funct_2(k7_relat_1(sK3,sK2),sK2,sK1)),
% 0.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl4_58])])).
% 0.20/0.53  fof(f894,plain,(
% 0.20/0.53    v1_funct_2(k7_relat_1(sK3,sK2),sK2,sK1) | (~spl4_83 | ~spl4_84)),
% 0.20/0.53    inference(resolution,[],[f889,f885])).
% 0.20/0.53  fof(f885,plain,(
% 0.20/0.53    ( ! [X10] : (~r1_tarski(k2_relat_1(k7_relat_1(sK3,sK2)),X10) | v1_funct_2(k7_relat_1(sK3,sK2),sK2,X10)) ) | ~spl4_83),
% 0.20/0.53    inference(avatar_component_clause,[],[f884])).
% 0.20/0.53  fof(f884,plain,(
% 0.20/0.53    spl4_83 <=> ! [X10] : (v1_funct_2(k7_relat_1(sK3,sK2),sK2,X10) | ~r1_tarski(k2_relat_1(k7_relat_1(sK3,sK2)),X10))),
% 0.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl4_83])])).
% 0.20/0.53  fof(f890,plain,(
% 0.20/0.53    spl4_84 | ~spl4_77 | ~spl4_79),
% 0.20/0.53    inference(avatar_split_clause,[],[f871,f857,f843,f888])).
% 0.20/0.53  fof(f843,plain,(
% 0.20/0.53    spl4_77 <=> ! [X6] : v1_relat_1(k7_relat_1(sK3,X6))),
% 0.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl4_77])])).
% 0.20/0.53  fof(f857,plain,(
% 0.20/0.53    spl4_79 <=> ! [X4] : v5_relat_1(k7_relat_1(sK3,X4),sK1)),
% 0.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl4_79])])).
% 0.20/0.53  fof(f871,plain,(
% 0.20/0.53    ( ! [X0] : (r1_tarski(k2_relat_1(k7_relat_1(sK3,X0)),sK1)) ) | (~spl4_77 | ~spl4_79)),
% 0.20/0.53    inference(subsumption_resolution,[],[f869,f844])).
% 0.20/0.53  fof(f844,plain,(
% 0.20/0.53    ( ! [X6] : (v1_relat_1(k7_relat_1(sK3,X6))) ) | ~spl4_77),
% 0.20/0.53    inference(avatar_component_clause,[],[f843])).
% 0.20/0.53  fof(f869,plain,(
% 0.20/0.53    ( ! [X0] : (r1_tarski(k2_relat_1(k7_relat_1(sK3,X0)),sK1) | ~v1_relat_1(k7_relat_1(sK3,X0))) ) | ~spl4_79),
% 0.20/0.53    inference(resolution,[],[f858,f70])).
% 0.20/0.53  fof(f70,plain,(
% 0.20/0.53    ( ! [X0,X1] : (~v5_relat_1(X1,X0) | r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 0.20/0.53    inference(cnf_transformation,[],[f50])).
% 0.20/0.53  fof(f50,plain,(
% 0.20/0.53    ! [X0,X1] : (((v5_relat_1(X1,X0) | ~r1_tarski(k2_relat_1(X1),X0)) & (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 0.20/0.53    inference(nnf_transformation,[],[f30])).
% 0.20/0.53  fof(f30,plain,(
% 0.20/0.53    ! [X0,X1] : ((v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.20/0.53    inference(ennf_transformation,[],[f8])).
% 0.20/0.53  fof(f8,axiom,(
% 0.20/0.53    ! [X0,X1] : (v1_relat_1(X1) => (v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)))),
% 0.20/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).
% 0.20/0.53  fof(f858,plain,(
% 0.20/0.53    ( ! [X4] : (v5_relat_1(k7_relat_1(sK3,X4),sK1)) ) | ~spl4_79),
% 0.20/0.53    inference(avatar_component_clause,[],[f857])).
% 0.20/0.53  fof(f886,plain,(
% 0.20/0.53    spl4_83 | ~spl4_76 | ~spl4_81),
% 0.20/0.53    inference(avatar_split_clause,[],[f882,f866,f816,f884])).
% 0.20/0.53  fof(f866,plain,(
% 0.20/0.53    spl4_81 <=> ! [X10] : (v1_funct_2(k7_relat_1(sK3,sK2),k1_relat_1(k7_relat_1(sK3,sK2)),X10) | ~r1_tarski(k2_relat_1(k7_relat_1(sK3,sK2)),X10))),
% 0.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl4_81])])).
% 0.20/0.53  fof(f882,plain,(
% 0.20/0.53    ( ! [X10] : (v1_funct_2(k7_relat_1(sK3,sK2),sK2,X10) | ~r1_tarski(k2_relat_1(k7_relat_1(sK3,sK2)),X10)) ) | (~spl4_76 | ~spl4_81)),
% 0.20/0.53    inference(backward_demodulation,[],[f867,f818])).
% 0.20/0.53  fof(f867,plain,(
% 0.20/0.53    ( ! [X10] : (v1_funct_2(k7_relat_1(sK3,sK2),k1_relat_1(k7_relat_1(sK3,sK2)),X10) | ~r1_tarski(k2_relat_1(k7_relat_1(sK3,sK2)),X10)) ) | ~spl4_81),
% 0.20/0.53    inference(avatar_component_clause,[],[f866])).
% 0.20/0.53  fof(f881,plain,(
% 0.20/0.53    spl4_82 | ~spl4_24 | ~spl4_56 | ~spl4_77),
% 0.20/0.53    inference(avatar_split_clause,[],[f877,f843,f630,f317,f879])).
% 0.20/0.53  fof(f317,plain,(
% 0.20/0.53    spl4_24 <=> v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))),
% 0.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl4_24])])).
% 0.20/0.53  fof(f877,plain,(
% 0.20/0.53    ( ! [X6] : (m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k7_relat_1(sK3,sK2)),X6))) | ~r1_tarski(k2_relat_1(k7_relat_1(sK3,sK2)),X6)) ) | (~spl4_24 | ~spl4_56 | ~spl4_77)),
% 0.20/0.53    inference(subsumption_resolution,[],[f833,f844])).
% 0.20/0.53  fof(f833,plain,(
% 0.20/0.53    ( ! [X6] : (~v1_relat_1(k7_relat_1(sK3,sK2)) | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k7_relat_1(sK3,sK2)),X6))) | ~r1_tarski(k2_relat_1(k7_relat_1(sK3,sK2)),X6)) ) | (~spl4_24 | ~spl4_56)),
% 0.20/0.53    inference(forward_demodulation,[],[f832,f631])).
% 0.20/0.53  fof(f832,plain,(
% 0.20/0.53    ( ! [X6] : (m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k7_relat_1(sK3,sK2)),X6))) | ~r1_tarski(k2_relat_1(k7_relat_1(sK3,sK2)),X6) | ~v1_relat_1(k2_partfun1(sK0,sK1,sK3,sK2))) ) | (~spl4_24 | ~spl4_56)),
% 0.20/0.53    inference(forward_demodulation,[],[f831,f631])).
% 0.20/0.53  fof(f831,plain,(
% 0.20/0.53    ( ! [X6] : (~r1_tarski(k2_relat_1(k7_relat_1(sK3,sK2)),X6) | m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_partfun1(sK0,sK1,sK3,sK2)),X6))) | ~v1_relat_1(k2_partfun1(sK0,sK1,sK3,sK2))) ) | (~spl4_24 | ~spl4_56)),
% 0.20/0.53    inference(forward_demodulation,[],[f339,f631])).
% 0.20/0.53  fof(f339,plain,(
% 0.20/0.53    ( ! [X6] : (~r1_tarski(k2_relat_1(k2_partfun1(sK0,sK1,sK3,sK2)),X6) | m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_partfun1(sK0,sK1,sK3,sK2)),X6))) | ~v1_relat_1(k2_partfun1(sK0,sK1,sK3,sK2))) ) | ~spl4_24),
% 0.20/0.53    inference(resolution,[],[f318,f74])).
% 0.20/0.53  fof(f74,plain,(
% 0.20/0.53    ( ! [X0,X1] : (~v1_funct_1(X1) | ~r1_tarski(k2_relat_1(X1),X0) | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) | ~v1_relat_1(X1)) )),
% 0.20/0.53    inference(cnf_transformation,[],[f32])).
% 0.20/0.53  fof(f32,plain,(
% 0.20/0.53    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) & v1_funct_2(X1,k1_relat_1(X1),X0) & v1_funct_1(X1)) | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 0.20/0.53    inference(flattening,[],[f31])).
% 0.20/0.53  fof(f31,plain,(
% 0.20/0.53    ! [X0,X1] : (((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) & v1_funct_2(X1,k1_relat_1(X1),X0) & v1_funct_1(X1)) | ~r1_tarski(k2_relat_1(X1),X0)) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 0.20/0.53    inference(ennf_transformation,[],[f20])).
% 0.20/0.53  fof(f20,axiom,(
% 0.20/0.53    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (r1_tarski(k2_relat_1(X1),X0) => (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) & v1_funct_2(X1,k1_relat_1(X1),X0) & v1_funct_1(X1))))),
% 0.20/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_funct_2)).
% 0.20/0.53  fof(f318,plain,(
% 0.20/0.53    v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) | ~spl4_24),
% 0.20/0.53    inference(avatar_component_clause,[],[f317])).
% 0.20/0.53  fof(f868,plain,(
% 0.20/0.53    spl4_81 | ~spl4_24 | ~spl4_56 | ~spl4_77),
% 0.20/0.53    inference(avatar_split_clause,[],[f860,f843,f630,f317,f866])).
% 0.20/0.53  fof(f860,plain,(
% 0.20/0.53    ( ! [X10] : (v1_funct_2(k7_relat_1(sK3,sK2),k1_relat_1(k7_relat_1(sK3,sK2)),X10) | ~r1_tarski(k2_relat_1(k7_relat_1(sK3,sK2)),X10)) ) | (~spl4_24 | ~spl4_56 | ~spl4_77)),
% 0.20/0.53    inference(subsumption_resolution,[],[f836,f844])).
% 0.20/0.53  fof(f836,plain,(
% 0.20/0.53    ( ! [X10] : (~v1_relat_1(k7_relat_1(sK3,sK2)) | v1_funct_2(k7_relat_1(sK3,sK2),k1_relat_1(k7_relat_1(sK3,sK2)),X10) | ~r1_tarski(k2_relat_1(k7_relat_1(sK3,sK2)),X10)) ) | (~spl4_24 | ~spl4_56)),
% 0.20/0.53    inference(forward_demodulation,[],[f835,f631])).
% 0.20/0.53  fof(f835,plain,(
% 0.20/0.53    ( ! [X10] : (v1_funct_2(k7_relat_1(sK3,sK2),k1_relat_1(k7_relat_1(sK3,sK2)),X10) | ~r1_tarski(k2_relat_1(k7_relat_1(sK3,sK2)),X10) | ~v1_relat_1(k2_partfun1(sK0,sK1,sK3,sK2))) ) | (~spl4_24 | ~spl4_56)),
% 0.20/0.53    inference(forward_demodulation,[],[f834,f631])).
% 0.20/0.53  fof(f834,plain,(
% 0.20/0.53    ( ! [X10] : (~r1_tarski(k2_relat_1(k7_relat_1(sK3,sK2)),X10) | v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),k1_relat_1(k2_partfun1(sK0,sK1,sK3,sK2)),X10) | ~v1_relat_1(k2_partfun1(sK0,sK1,sK3,sK2))) ) | (~spl4_24 | ~spl4_56)),
% 0.20/0.53    inference(forward_demodulation,[],[f341,f631])).
% 0.20/0.53  fof(f341,plain,(
% 0.20/0.53    ( ! [X10] : (~r1_tarski(k2_relat_1(k2_partfun1(sK0,sK1,sK3,sK2)),X10) | v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),k1_relat_1(k2_partfun1(sK0,sK1,sK3,sK2)),X10) | ~v1_relat_1(k2_partfun1(sK0,sK1,sK3,sK2))) ) | ~spl4_24),
% 0.20/0.53    inference(resolution,[],[f318,f73])).
% 0.20/0.53  fof(f73,plain,(
% 0.20/0.53    ( ! [X0,X1] : (~v1_funct_1(X1) | ~r1_tarski(k2_relat_1(X1),X0) | v1_funct_2(X1,k1_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 0.20/0.53    inference(cnf_transformation,[],[f32])).
% 0.20/0.53  fof(f859,plain,(
% 0.20/0.53    spl4_79 | ~spl4_75),
% 0.20/0.53    inference(avatar_split_clause,[],[f825,f812,f857])).
% 0.20/0.53  fof(f812,plain,(
% 0.20/0.53    spl4_75 <=> ! [X0] : m1_subset_1(k7_relat_1(sK3,X0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl4_75])])).
% 0.20/0.53  fof(f825,plain,(
% 0.20/0.53    ( ! [X4] : (v5_relat_1(k7_relat_1(sK3,X4),sK1)) ) | ~spl4_75),
% 0.20/0.53    inference(resolution,[],[f813,f87])).
% 0.20/0.53  fof(f87,plain,(
% 0.20/0.53    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v5_relat_1(X2,X1)) )),
% 0.20/0.53    inference(cnf_transformation,[],[f37])).
% 0.20/0.53  fof(f37,plain,(
% 0.20/0.53    ! [X0,X1,X2] : ((v5_relat_1(X2,X1) & v4_relat_1(X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.53    inference(ennf_transformation,[],[f15])).
% 0.20/0.53  fof(f15,axiom,(
% 0.20/0.53    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 0.20/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).
% 0.20/0.53  fof(f813,plain,(
% 0.20/0.53    ( ! [X0] : (m1_subset_1(k7_relat_1(sK3,X0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))) ) | ~spl4_75),
% 0.20/0.53    inference(avatar_component_clause,[],[f812])).
% 0.20/0.53  fof(f845,plain,(
% 0.20/0.53    spl4_77 | ~spl4_75),
% 0.20/0.53    inference(avatar_split_clause,[],[f827,f812,f843])).
% 0.20/0.53  fof(f827,plain,(
% 0.20/0.53    ( ! [X6] : (v1_relat_1(k7_relat_1(sK3,X6))) ) | ~spl4_75),
% 0.20/0.53    inference(resolution,[],[f813,f84])).
% 0.20/0.53  fof(f84,plain,(
% 0.20/0.53    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)) )),
% 0.20/0.53    inference(cnf_transformation,[],[f35])).
% 0.20/0.53  fof(f35,plain,(
% 0.20/0.53    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.53    inference(ennf_transformation,[],[f14])).
% 0.20/0.53  fof(f14,axiom,(
% 0.20/0.53    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 0.20/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).
% 0.20/0.53  fof(f819,plain,(
% 0.20/0.53    spl4_76 | ~spl4_2 | ~spl4_68),
% 0.20/0.53    inference(avatar_split_clause,[],[f780,f774,f114,f816])).
% 0.20/0.53  fof(f114,plain,(
% 0.20/0.53    spl4_2 <=> r1_tarski(sK2,sK0)),
% 0.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 0.20/0.53  fof(f774,plain,(
% 0.20/0.53    spl4_68 <=> ! [X0] : (~r1_tarski(X0,sK0) | k1_relat_1(k7_relat_1(sK3,X0)) = X0)),
% 0.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl4_68])])).
% 0.20/0.53  fof(f780,plain,(
% 0.20/0.53    sK2 = k1_relat_1(k7_relat_1(sK3,sK2)) | (~spl4_2 | ~spl4_68)),
% 0.20/0.53    inference(resolution,[],[f775,f116])).
% 0.20/0.53  fof(f116,plain,(
% 0.20/0.53    r1_tarski(sK2,sK0) | ~spl4_2),
% 0.20/0.53    inference(avatar_component_clause,[],[f114])).
% 0.20/0.53  fof(f775,plain,(
% 0.20/0.53    ( ! [X0] : (~r1_tarski(X0,sK0) | k1_relat_1(k7_relat_1(sK3,X0)) = X0) ) | ~spl4_68),
% 0.20/0.53    inference(avatar_component_clause,[],[f774])).
% 0.20/0.53  fof(f814,plain,(
% 0.20/0.53    spl4_75 | ~spl4_6 | ~spl4_42 | ~spl4_56),
% 0.20/0.53    inference(avatar_split_clause,[],[f810,f630,f527,f134,f812])).
% 0.20/0.53  fof(f134,plain,(
% 0.20/0.53    spl4_6 <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).
% 0.20/0.53  fof(f527,plain,(
% 0.20/0.53    spl4_42 <=> ! [X1,X0,X2] : (~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | m1_subset_1(k2_partfun1(X0,X1,sK3,X2),k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl4_42])])).
% 0.20/0.53  fof(f810,plain,(
% 0.20/0.53    ( ! [X0] : (m1_subset_1(k7_relat_1(sK3,X0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))) ) | (~spl4_6 | ~spl4_42 | ~spl4_56)),
% 0.20/0.53    inference(forward_demodulation,[],[f543,f631])).
% 0.20/0.53  fof(f543,plain,(
% 0.20/0.53    ( ! [X0] : (m1_subset_1(k2_partfun1(sK0,sK1,sK3,X0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))) ) | (~spl4_6 | ~spl4_42)),
% 0.20/0.53    inference(resolution,[],[f528,f136])).
% 0.20/0.53  fof(f136,plain,(
% 0.20/0.53    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~spl4_6),
% 0.20/0.53    inference(avatar_component_clause,[],[f134])).
% 0.20/0.53  fof(f528,plain,(
% 0.20/0.53    ( ! [X2,X0,X1] : (~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | m1_subset_1(k2_partfun1(X0,X1,sK3,X2),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) ) | ~spl4_42),
% 0.20/0.53    inference(avatar_component_clause,[],[f527])).
% 0.20/0.53  fof(f776,plain,(
% 0.20/0.53    spl4_68 | ~spl4_10 | ~spl4_30),
% 0.20/0.53    inference(avatar_split_clause,[],[f772,f366,f161,f774])).
% 0.20/0.53  fof(f161,plain,(
% 0.20/0.53    spl4_10 <=> v1_relat_1(sK3)),
% 0.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).
% 0.20/0.53  fof(f366,plain,(
% 0.20/0.53    spl4_30 <=> sK0 = k1_relat_1(sK3)),
% 0.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl4_30])])).
% 0.20/0.53  fof(f772,plain,(
% 0.20/0.53    ( ! [X0] : (~r1_tarski(X0,sK0) | k1_relat_1(k7_relat_1(sK3,X0)) = X0) ) | (~spl4_10 | ~spl4_30)),
% 0.20/0.53    inference(forward_demodulation,[],[f221,f368])).
% 0.20/0.53  fof(f368,plain,(
% 0.20/0.53    sK0 = k1_relat_1(sK3) | ~spl4_30),
% 0.20/0.53    inference(avatar_component_clause,[],[f366])).
% 0.20/0.53  fof(f221,plain,(
% 0.20/0.53    ( ! [X0] : (~r1_tarski(X0,k1_relat_1(sK3)) | k1_relat_1(k7_relat_1(sK3,X0)) = X0) ) | ~spl4_10),
% 0.20/0.53    inference(resolution,[],[f69,f163])).
% 0.20/0.53  fof(f163,plain,(
% 0.20/0.53    v1_relat_1(sK3) | ~spl4_10),
% 0.20/0.53    inference(avatar_component_clause,[],[f161])).
% 0.20/0.53  fof(f69,plain,(
% 0.20/0.53    ( ! [X0,X1] : (~v1_relat_1(X1) | ~r1_tarski(X0,k1_relat_1(X1)) | k1_relat_1(k7_relat_1(X1,X0)) = X0) )),
% 0.20/0.53    inference(cnf_transformation,[],[f29])).
% 0.20/0.53  fof(f29,plain,(
% 0.20/0.53    ! [X0,X1] : (k1_relat_1(k7_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k1_relat_1(X1)) | ~v1_relat_1(X1))),
% 0.20/0.53    inference(flattening,[],[f28])).
% 0.20/0.53  fof(f28,plain,(
% 0.20/0.53    ! [X0,X1] : ((k1_relat_1(k7_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k1_relat_1(X1))) | ~v1_relat_1(X1))),
% 0.20/0.53    inference(ennf_transformation,[],[f11])).
% 0.20/0.53  fof(f11,axiom,(
% 0.20/0.53    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(X0,k1_relat_1(X1)) => k1_relat_1(k7_relat_1(X1,X0)) = X0))),
% 0.20/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_relat_1)).
% 0.20/0.53  fof(f642,plain,(
% 0.20/0.53    ~spl4_58 | ~spl4_6 | spl4_25 | ~spl4_39),
% 0.20/0.53    inference(avatar_split_clause,[],[f623,f511,f321,f134,f639])).
% 0.20/0.53  fof(f321,plain,(
% 0.20/0.53    spl4_25 <=> v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1)),
% 0.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl4_25])])).
% 0.20/0.53  fof(f511,plain,(
% 0.20/0.53    spl4_39 <=> ! [X1,X0,X2] : (~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_partfun1(X0,X1,sK3,X2) = k7_relat_1(sK3,X2))),
% 0.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl4_39])])).
% 0.20/0.53  fof(f623,plain,(
% 0.20/0.53    ~v1_funct_2(k7_relat_1(sK3,sK2),sK2,sK1) | (~spl4_6 | spl4_25 | ~spl4_39)),
% 0.20/0.53    inference(backward_demodulation,[],[f323,f518])).
% 0.20/0.53  fof(f518,plain,(
% 0.20/0.53    ( ! [X0] : (k7_relat_1(sK3,X0) = k2_partfun1(sK0,sK1,sK3,X0)) ) | (~spl4_6 | ~spl4_39)),
% 0.20/0.53    inference(resolution,[],[f512,f136])).
% 0.20/0.53  fof(f512,plain,(
% 0.20/0.53    ( ! [X2,X0,X1] : (~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_partfun1(X0,X1,sK3,X2) = k7_relat_1(sK3,X2)) ) | ~spl4_39),
% 0.20/0.53    inference(avatar_component_clause,[],[f511])).
% 0.20/0.53  fof(f323,plain,(
% 0.20/0.53    ~v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1) | spl4_25),
% 0.20/0.53    inference(avatar_component_clause,[],[f321])).
% 0.20/0.53  fof(f632,plain,(
% 0.20/0.53    spl4_56 | ~spl4_6 | ~spl4_39),
% 0.20/0.53    inference(avatar_split_clause,[],[f518,f511,f134,f630])).
% 0.20/0.53  fof(f529,plain,(
% 0.20/0.53    spl4_42 | ~spl4_1),
% 0.20/0.53    inference(avatar_split_clause,[],[f286,f109,f527])).
% 0.20/0.53  fof(f109,plain,(
% 0.20/0.53    spl4_1 <=> v1_funct_1(sK3)),
% 0.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 0.20/0.53  fof(f286,plain,(
% 0.20/0.53    ( ! [X2,X0,X1] : (~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | m1_subset_1(k2_partfun1(X0,X1,sK3,X2),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) ) | ~spl4_1),
% 0.20/0.53    inference(resolution,[],[f98,f111])).
% 0.20/0.53  fof(f111,plain,(
% 0.20/0.53    v1_funct_1(sK3) | ~spl4_1),
% 0.20/0.53    inference(avatar_component_clause,[],[f109])).
% 0.20/0.53  fof(f98,plain,(
% 0.20/0.53    ( ! [X2,X0,X3,X1] : (~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.20/0.53    inference(cnf_transformation,[],[f47])).
% 0.20/0.53  fof(f47,plain,(
% 0.20/0.53    ! [X0,X1,X2,X3] : ((m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(k2_partfun1(X0,X1,X2,X3))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 0.20/0.53    inference(flattening,[],[f46])).
% 0.20/0.53  fof(f46,plain,(
% 0.20/0.53    ! [X0,X1,X2,X3] : ((m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(k2_partfun1(X0,X1,X2,X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 0.20/0.53    inference(ennf_transformation,[],[f18])).
% 0.20/0.53  fof(f18,axiom,(
% 0.20/0.53    ! [X0,X1,X2,X3] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => (m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(k2_partfun1(X0,X1,X2,X3))))),
% 0.20/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_partfun1)).
% 0.20/0.53  fof(f513,plain,(
% 0.20/0.53    spl4_39 | ~spl4_1),
% 0.20/0.53    inference(avatar_split_clause,[],[f280,f109,f511])).
% 0.20/0.53  fof(f280,plain,(
% 0.20/0.53    ( ! [X2,X0,X1] : (~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_partfun1(X0,X1,sK3,X2) = k7_relat_1(sK3,X2)) ) | ~spl4_1),
% 0.20/0.53    inference(resolution,[],[f96,f111])).
% 0.20/0.53  fof(f96,plain,(
% 0.20/0.53    ( ! [X2,X0,X3,X1] : (~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3)) )),
% 0.20/0.53    inference(cnf_transformation,[],[f45])).
% 0.20/0.53  fof(f45,plain,(
% 0.20/0.53    ! [X0,X1,X2,X3] : (k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 0.20/0.53    inference(flattening,[],[f44])).
% 0.20/0.53  fof(f44,plain,(
% 0.20/0.53    ! [X0,X1,X2,X3] : (k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 0.20/0.53    inference(ennf_transformation,[],[f19])).
% 0.20/0.53  fof(f19,axiom,(
% 0.20/0.53    ! [X0,X1,X2,X3] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3))),
% 0.20/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_partfun1)).
% 0.20/0.53  fof(f369,plain,(
% 0.20/0.53    spl4_30 | ~spl4_6 | ~spl4_28),
% 0.20/0.53    inference(avatar_split_clause,[],[f364,f344,f134,f366])).
% 0.20/0.53  fof(f344,plain,(
% 0.20/0.53    spl4_28 <=> sK0 = k1_relset_1(sK0,sK1,sK3)),
% 0.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl4_28])])).
% 0.20/0.53  fof(f364,plain,(
% 0.20/0.53    sK0 = k1_relat_1(sK3) | (~spl4_6 | ~spl4_28)),
% 0.20/0.53    inference(forward_demodulation,[],[f234,f346])).
% 0.20/0.53  fof(f346,plain,(
% 0.20/0.53    sK0 = k1_relset_1(sK0,sK1,sK3) | ~spl4_28),
% 0.20/0.53    inference(avatar_component_clause,[],[f344])).
% 0.20/0.53  fof(f234,plain,(
% 0.20/0.53    k1_relat_1(sK3) = k1_relset_1(sK0,sK1,sK3) | ~spl4_6),
% 0.20/0.53    inference(resolution,[],[f85,f136])).
% 0.20/0.53  fof(f85,plain,(
% 0.20/0.53    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_relset_1(X0,X1,X2) = k1_relat_1(X2)) )),
% 0.20/0.53    inference(cnf_transformation,[],[f36])).
% 0.20/0.53  fof(f36,plain,(
% 0.20/0.53    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.53    inference(ennf_transformation,[],[f16])).
% 0.20/0.53  fof(f16,axiom,(
% 0.20/0.53    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 0.20/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 0.20/0.53  fof(f347,plain,(
% 0.20/0.53    spl4_28 | ~spl4_3 | ~spl4_6 | spl4_7),
% 0.20/0.53    inference(avatar_split_clause,[],[f305,f139,f134,f119,f344])).
% 0.20/0.53  fof(f119,plain,(
% 0.20/0.53    spl4_3 <=> v1_funct_2(sK3,sK0,sK1)),
% 0.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 0.20/0.53  fof(f139,plain,(
% 0.20/0.53    spl4_7 <=> k1_xboole_0 = sK1),
% 0.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).
% 0.20/0.53  fof(f305,plain,(
% 0.20/0.53    sK0 = k1_relset_1(sK0,sK1,sK3) | (~spl4_3 | ~spl4_6 | spl4_7)),
% 0.20/0.53    inference(subsumption_resolution,[],[f304,f136])).
% 0.20/0.53  fof(f304,plain,(
% 0.20/0.53    sK0 = k1_relset_1(sK0,sK1,sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | (~spl4_3 | spl4_7)),
% 0.20/0.53    inference(subsumption_resolution,[],[f302,f141])).
% 0.20/0.53  fof(f141,plain,(
% 0.20/0.53    k1_xboole_0 != sK1 | spl4_7),
% 0.20/0.53    inference(avatar_component_clause,[],[f139])).
% 0.20/0.53  fof(f302,plain,(
% 0.20/0.53    sK0 = k1_relset_1(sK0,sK1,sK3) | k1_xboole_0 = sK1 | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~spl4_3),
% 0.20/0.53    inference(resolution,[],[f88,f121])).
% 0.20/0.53  fof(f121,plain,(
% 0.20/0.53    v1_funct_2(sK3,sK0,sK1) | ~spl4_3),
% 0.20/0.53    inference(avatar_component_clause,[],[f119])).
% 0.20/0.53  fof(f88,plain,(
% 0.20/0.53    ( ! [X2,X0,X1] : (~v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) = X0 | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.20/0.53    inference(cnf_transformation,[],[f56])).
% 0.20/0.53  fof(f56,plain,(
% 0.20/0.53    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.53    inference(nnf_transformation,[],[f39])).
% 0.20/0.53  fof(f39,plain,(
% 0.20/0.53    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.53    inference(flattening,[],[f38])).
% 0.20/0.53  fof(f38,plain,(
% 0.20/0.53    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.53    inference(ennf_transformation,[],[f17])).
% 0.20/0.53  fof(f17,axiom,(
% 0.20/0.53    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 0.20/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_funct_2)).
% 0.20/0.53  fof(f334,plain,(
% 0.20/0.53    ~spl4_1 | ~spl4_6 | spl4_24),
% 0.20/0.53    inference(avatar_contradiction_clause,[],[f333])).
% 0.20/0.53  fof(f333,plain,(
% 0.20/0.53    $false | (~spl4_1 | ~spl4_6 | spl4_24)),
% 0.20/0.53    inference(unit_resulting_resolution,[],[f111,f136,f319,f97])).
% 0.20/0.53  fof(f97,plain,(
% 0.20/0.53    ( ! [X2,X0,X3,X1] : (~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_funct_1(k2_partfun1(X0,X1,X2,X3))) )),
% 0.20/0.53    inference(cnf_transformation,[],[f47])).
% 0.20/0.53  fof(f319,plain,(
% 0.20/0.53    ~v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) | spl4_24),
% 0.20/0.53    inference(avatar_component_clause,[],[f317])).
% 0.20/0.53  fof(f328,plain,(
% 0.20/0.53    ~spl4_24 | ~spl4_25 | ~spl4_26),
% 0.20/0.53    inference(avatar_split_clause,[],[f62,f325,f321,f317])).
% 0.20/0.53  fof(f62,plain,(
% 0.20/0.53    ~m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1) | ~v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))),
% 0.20/0.53    inference(cnf_transformation,[],[f49])).
% 0.20/0.53  fof(f49,plain,(
% 0.20/0.53    (~m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1) | ~v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))) & (k1_xboole_0 = sK0 | k1_xboole_0 != sK1) & r1_tarski(sK2,sK0) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK3,sK0,sK1) & v1_funct_1(sK3)),
% 0.20/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f24,f48])).
% 0.20/0.53  fof(f48,plain,(
% 0.20/0.53    ? [X0,X1,X2,X3] : ((~m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1) | ~v1_funct_1(k2_partfun1(X0,X1,X3,X2))) & (k1_xboole_0 = X0 | k1_xboole_0 != X1) & r1_tarski(X2,X0) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ((~m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1) | ~v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))) & (k1_xboole_0 = sK0 | k1_xboole_0 != sK1) & r1_tarski(sK2,sK0) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK3,sK0,sK1) & v1_funct_1(sK3))),
% 0.20/0.53    introduced(choice_axiom,[])).
% 0.20/0.53  fof(f24,plain,(
% 0.20/0.53    ? [X0,X1,X2,X3] : ((~m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1) | ~v1_funct_1(k2_partfun1(X0,X1,X3,X2))) & (k1_xboole_0 = X0 | k1_xboole_0 != X1) & r1_tarski(X2,X0) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3))),
% 0.20/0.53    inference(flattening,[],[f23])).
% 0.20/0.53  fof(f23,plain,(
% 0.20/0.53    ? [X0,X1,X2,X3] : ((((~m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1) | ~v1_funct_1(k2_partfun1(X0,X1,X3,X2))) & (k1_xboole_0 = X0 | k1_xboole_0 != X1)) & r1_tarski(X2,X0)) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)))),
% 0.20/0.53    inference(ennf_transformation,[],[f22])).
% 0.20/0.53  fof(f22,negated_conjecture,(
% 0.20/0.53    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r1_tarski(X2,X0) => ((m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1) & v1_funct_1(k2_partfun1(X0,X1,X3,X2))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))))),
% 0.20/0.53    inference(negated_conjecture,[],[f21])).
% 0.20/0.53  fof(f21,conjecture,(
% 0.20/0.53    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r1_tarski(X2,X0) => ((m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1) & v1_funct_1(k2_partfun1(X0,X1,X3,X2))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))))),
% 0.20/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_funct_2)).
% 0.20/0.54  fof(f263,plain,(
% 0.20/0.54    spl4_18 | ~spl4_19 | ~spl4_2),
% 0.20/0.54    inference(avatar_split_clause,[],[f177,f114,f260,f256])).
% 0.20/0.54  fof(f256,plain,(
% 0.20/0.54    spl4_18 <=> sK0 = sK2),
% 0.20/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_18])])).
% 0.20/0.54  fof(f177,plain,(
% 0.20/0.54    ~r1_tarski(sK0,sK2) | sK0 = sK2 | ~spl4_2),
% 0.20/0.54    inference(resolution,[],[f78,f116])).
% 0.20/0.54  fof(f78,plain,(
% 0.20/0.54    ( ! [X0,X1] : (~r1_tarski(X0,X1) | ~r1_tarski(X1,X0) | X0 = X1) )),
% 0.20/0.54    inference(cnf_transformation,[],[f52])).
% 0.20/0.54  fof(f52,plain,(
% 0.20/0.54    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.20/0.54    inference(flattening,[],[f51])).
% 0.20/0.54  fof(f51,plain,(
% 0.20/0.54    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.20/0.54    inference(nnf_transformation,[],[f1])).
% 0.20/0.54  fof(f1,axiom,(
% 0.20/0.54    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.20/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.20/0.54  fof(f246,plain,(
% 0.20/0.54    spl4_16 | ~spl4_10 | ~spl4_13),
% 0.20/0.54    inference(avatar_split_clause,[],[f212,f190,f161,f243])).
% 0.20/0.54  fof(f243,plain,(
% 0.20/0.54    spl4_16 <=> sK3 = k7_relat_1(sK3,sK0)),
% 0.20/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_16])])).
% 0.20/0.54  fof(f190,plain,(
% 0.20/0.54    spl4_13 <=> v4_relat_1(sK3,sK0)),
% 0.20/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_13])])).
% 0.20/0.54  fof(f212,plain,(
% 0.20/0.54    sK3 = k7_relat_1(sK3,sK0) | (~spl4_10 | ~spl4_13)),
% 0.20/0.54    inference(subsumption_resolution,[],[f211,f163])).
% 0.20/0.54  fof(f211,plain,(
% 0.20/0.54    sK3 = k7_relat_1(sK3,sK0) | ~v1_relat_1(sK3) | ~spl4_13),
% 0.20/0.54    inference(resolution,[],[f75,f192])).
% 0.20/0.54  fof(f192,plain,(
% 0.20/0.54    v4_relat_1(sK3,sK0) | ~spl4_13),
% 0.20/0.54    inference(avatar_component_clause,[],[f190])).
% 0.20/0.54  fof(f75,plain,(
% 0.20/0.54    ( ! [X0,X1] : (~v4_relat_1(X1,X0) | k7_relat_1(X1,X0) = X1 | ~v1_relat_1(X1)) )),
% 0.20/0.54    inference(cnf_transformation,[],[f34])).
% 0.20/0.55  fof(f34,plain,(
% 0.20/0.55    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 0.20/0.55    inference(flattening,[],[f33])).
% 0.20/0.55  % (2166)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_364 on theBenchmark
% 0.20/0.55  % (2139)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 0.20/0.55  fof(f33,plain,(
% 0.20/0.55    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 0.20/0.55    inference(ennf_transformation,[],[f9])).
% 0.20/0.55  fof(f9,axiom,(
% 0.20/0.55    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => k7_relat_1(X1,X0) = X1)),
% 0.20/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t209_relat_1)).
% 0.20/0.55  fof(f193,plain,(
% 0.20/0.55    spl4_13 | ~spl4_6),
% 0.20/0.55    inference(avatar_split_clause,[],[f185,f134,f190])).
% 0.20/0.55  fof(f185,plain,(
% 0.20/0.55    v4_relat_1(sK3,sK0) | ~spl4_6),
% 0.20/0.55    inference(resolution,[],[f86,f136])).
% 0.20/0.55  fof(f86,plain,(
% 0.20/0.55    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v4_relat_1(X2,X0)) )),
% 0.20/0.55    inference(cnf_transformation,[],[f37])).
% 0.20/0.55  fof(f164,plain,(
% 0.20/0.55    spl4_10 | ~spl4_6),
% 0.20/0.55    inference(avatar_split_clause,[],[f156,f134,f161])).
% 0.20/0.55  fof(f156,plain,(
% 0.20/0.55    v1_relat_1(sK3) | ~spl4_6),
% 0.20/0.55    inference(resolution,[],[f84,f136])).
% 0.20/0.55  fof(f146,plain,(
% 0.20/0.55    ~spl4_7 | spl4_8),
% 0.20/0.55    inference(avatar_split_clause,[],[f61,f143,f139])).
% 0.20/0.55  fof(f61,plain,(
% 0.20/0.55    k1_xboole_0 = sK0 | k1_xboole_0 != sK1),
% 0.20/0.55    inference(cnf_transformation,[],[f49])).
% 0.20/0.55  fof(f137,plain,(
% 0.20/0.55    spl4_6),
% 0.20/0.55    inference(avatar_split_clause,[],[f59,f134])).
% 0.20/0.55  fof(f59,plain,(
% 0.20/0.55    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.20/0.55    inference(cnf_transformation,[],[f49])).
% 0.20/0.55  fof(f122,plain,(
% 0.20/0.55    spl4_3),
% 0.20/0.55    inference(avatar_split_clause,[],[f58,f119])).
% 0.20/0.55  fof(f58,plain,(
% 0.20/0.55    v1_funct_2(sK3,sK0,sK1)),
% 0.20/0.55    inference(cnf_transformation,[],[f49])).
% 0.20/0.55  fof(f117,plain,(
% 0.20/0.55    spl4_2),
% 0.20/0.55    inference(avatar_split_clause,[],[f60,f114])).
% 0.20/0.55  fof(f60,plain,(
% 0.20/0.55    r1_tarski(sK2,sK0)),
% 0.20/0.55    inference(cnf_transformation,[],[f49])).
% 0.20/0.55  fof(f112,plain,(
% 0.20/0.55    spl4_1),
% 0.20/0.55    inference(avatar_split_clause,[],[f57,f109])).
% 0.20/0.55  fof(f57,plain,(
% 0.20/0.55    v1_funct_1(sK3)),
% 0.20/0.55    inference(cnf_transformation,[],[f49])).
% 0.20/0.55  % SZS output end Proof for theBenchmark
% 0.20/0.55  % (2142)------------------------------
% 0.20/0.55  % (2142)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.55  % (2142)Termination reason: Refutation
% 0.20/0.55  
% 0.20/0.55  % (2142)Memory used [KB]: 6780
% 0.20/0.55  % (2142)Time elapsed: 0.134 s
% 0.20/0.55  % (2142)------------------------------
% 0.20/0.55  % (2142)------------------------------
% 0.20/0.56  % (2134)Success in time 0.198 s
% 0.20/0.56  % (2157)lrs+4_5:4_av=off:bd=off:er=filter:lma=on:lwlo=on:nwc=1:stl=30:sp=occurrence:updr=off_230 on theBenchmark
% 0.20/0.56  % (2165)dis+2_128_add=large:afp=100000:afq=1.4:amm=sco:anc=none:lma=on:nm=2:newcnf=on:nwc=1:nicw=on:sas=z3:sos=theory:sac=on:updr=off_288 on theBenchmark
%------------------------------------------------------------------------------
