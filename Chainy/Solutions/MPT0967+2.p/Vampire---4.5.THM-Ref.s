%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0967+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:10:00 EST 2020

% Result     : Theorem 6.10s
% Output     : Refutation 6.50s
% Verified   : 
% Statistics : Number of formulae       :  174 ( 301 expanded)
%              Number of leaves         :   37 ( 100 expanded)
%              Depth                    :   13
%              Number of atoms          :  533 (1375 expanded)
%              Number of equality atoms :  114 ( 317 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f8639,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f2394,f2403,f2404,f2518,f3229,f3801,f3844,f4965,f6856,f6889,f6926,f7285,f7412,f7587,f8564,f8587,f8616])).

fof(f8616,plain,
    ( spl75_2
    | ~ spl75_5
    | ~ spl75_118
    | ~ spl75_282
    | ~ spl75_292 ),
    inference(avatar_contradiction_clause,[],[f8615])).

fof(f8615,plain,
    ( $false
    | spl75_2
    | ~ spl75_5
    | ~ spl75_118
    | ~ spl75_282
    | ~ spl75_292 ),
    inference(subsumption_resolution,[],[f8614,f7768])).

fof(f7768,plain,
    ( ! [X12] : v1_funct_2(k1_xboole_0,k1_xboole_0,X12)
    | ~ spl75_282
    | ~ spl75_292 ),
    inference(subsumption_resolution,[],[f7767,f1913])).

fof(f1913,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f89])).

fof(f89,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f7767,plain,
    ( ! [X12] :
        ( ~ r1_tarski(k1_xboole_0,X12)
        | v1_funct_2(k1_xboole_0,k1_xboole_0,X12) )
    | ~ spl75_282
    | ~ spl75_292 ),
    inference(forward_demodulation,[],[f7766,f2334])).

fof(f2334,plain,(
    k1_xboole_0 = k2_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f856])).

fof(f856,axiom,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    & k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

fof(f7766,plain,
    ( ! [X12] :
        ( v1_funct_2(k1_xboole_0,k1_xboole_0,X12)
        | ~ r1_tarski(k2_relat_1(k1_xboole_0),X12) )
    | ~ spl75_282
    | ~ spl75_292 ),
    inference(forward_demodulation,[],[f7765,f2333])).

fof(f2333,plain,(
    k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f856])).

fof(f7765,plain,
    ( ! [X12] :
        ( v1_funct_2(k1_xboole_0,k1_relat_1(k1_xboole_0),X12)
        | ~ r1_tarski(k2_relat_1(k1_xboole_0),X12) )
    | ~ spl75_282
    | ~ spl75_292 ),
    inference(subsumption_resolution,[],[f7611,f7300])).

fof(f7300,plain,
    ( v1_relat_1(k1_xboole_0)
    | ~ spl75_282 ),
    inference(avatar_component_clause,[],[f7299])).

fof(f7299,plain,
    ( spl75_282
  <=> v1_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl75_282])])).

fof(f7611,plain,
    ( ! [X12] :
        ( v1_funct_2(k1_xboole_0,k1_relat_1(k1_xboole_0),X12)
        | ~ r1_tarski(k2_relat_1(k1_xboole_0),X12)
        | ~ v1_relat_1(k1_xboole_0) )
    | ~ spl75_292 ),
    inference(resolution,[],[f7389,f2010])).

fof(f2010,plain,(
    ! [X0,X1] :
      ( v1_funct_2(X1,k1_relat_1(X1),X0)
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f1551])).

fof(f1551,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
        & v1_funct_2(X1,k1_relat_1(X1),X0)
        & v1_funct_1(X1) )
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f1550])).

fof(f1550,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
        & v1_funct_2(X1,k1_relat_1(X1),X0)
        & v1_funct_1(X1) )
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f1478])).

fof(f1478,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( r1_tarski(k2_relat_1(X1),X0)
       => ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
          & v1_funct_2(X1,k1_relat_1(X1),X0)
          & v1_funct_1(X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_funct_2)).

fof(f7389,plain,
    ( v1_funct_1(k1_xboole_0)
    | ~ spl75_292 ),
    inference(avatar_component_clause,[],[f7388])).

fof(f7388,plain,
    ( spl75_292
  <=> v1_funct_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl75_292])])).

fof(f8614,plain,
    ( ~ v1_funct_2(k1_xboole_0,k1_xboole_0,sK4)
    | spl75_2
    | ~ spl75_5
    | ~ spl75_118 ),
    inference(forward_demodulation,[],[f8591,f2402])).

fof(f2402,plain,
    ( k1_xboole_0 = sK2
    | ~ spl75_5 ),
    inference(avatar_component_clause,[],[f2400])).

fof(f2400,plain,
    ( spl75_5
  <=> k1_xboole_0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl75_5])])).

fof(f8591,plain,
    ( ~ v1_funct_2(k1_xboole_0,sK2,sK4)
    | spl75_2
    | ~ spl75_118 ),
    inference(superposition,[],[f2389,f3156])).

fof(f3156,plain,
    ( k1_xboole_0 = sK5
    | ~ spl75_118 ),
    inference(avatar_component_clause,[],[f3154])).

fof(f3154,plain,
    ( spl75_118
  <=> k1_xboole_0 = sK5 ),
    introduced(avatar_definition,[new_symbols(naming,[spl75_118])])).

fof(f2389,plain,
    ( ~ v1_funct_2(sK5,sK2,sK4)
    | spl75_2 ),
    inference(avatar_component_clause,[],[f2387])).

fof(f2387,plain,
    ( spl75_2
  <=> v1_funct_2(sK5,sK2,sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl75_2])])).

fof(f8587,plain,
    ( spl75_213
    | ~ spl75_4 ),
    inference(avatar_split_clause,[],[f7005,f2396,f5414])).

fof(f5414,plain,
    ( spl75_213
  <=> r1_tarski(sK5,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl75_213])])).

fof(f2396,plain,
    ( spl75_4
  <=> k1_xboole_0 = sK3 ),
    introduced(avatar_definition,[new_symbols(naming,[spl75_4])])).

fof(f7005,plain,
    ( r1_tarski(sK5,k1_xboole_0)
    | ~ spl75_4 ),
    inference(forward_demodulation,[],[f6991,f2339])).

fof(f2339,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f1970])).

fof(f1970,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f1764])).

fof(f1764,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f1763])).

fof(f1763,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f329])).

fof(f329,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f6991,plain,
    ( r1_tarski(sK5,k2_zfmisc_1(sK2,k1_xboole_0))
    | ~ spl75_4 ),
    inference(superposition,[],[f2986,f2397])).

fof(f2397,plain,
    ( k1_xboole_0 = sK3
    | ~ spl75_4 ),
    inference(avatar_component_clause,[],[f2396])).

fof(f2986,plain,(
    r1_tarski(sK5,k2_zfmisc_1(sK2,sK3)) ),
    inference(resolution,[],[f1907,f1925])).

fof(f1925,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f1742])).

fof(f1742,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f609])).

fof(f609,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f1907,plain,(
    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) ),
    inference(cnf_transformation,[],[f1731])).

fof(f1731,plain,
    ( ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK4)))
      | ~ v1_funct_2(sK5,sK2,sK4)
      | ~ v1_funct_1(sK5) )
    & ( k1_xboole_0 = sK2
      | k1_xboole_0 != sK3 )
    & r1_tarski(sK3,sK4)
    & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
    & v1_funct_2(sK5,sK2,sK3)
    & v1_funct_1(sK5) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5])],[f1491,f1730])).

fof(f1730,plain,
    ( ? [X0,X1,X2,X3] :
        ( ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
          | ~ v1_funct_2(X3,X0,X2)
          | ~ v1_funct_1(X3) )
        & ( k1_xboole_0 = X0
          | k1_xboole_0 != X1 )
        & r1_tarski(X1,X2)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
   => ( ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK4)))
        | ~ v1_funct_2(sK5,sK2,sK4)
        | ~ v1_funct_1(sK5) )
      & ( k1_xboole_0 = sK2
        | k1_xboole_0 != sK3 )
      & r1_tarski(sK3,sK4)
      & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
      & v1_funct_2(sK5,sK2,sK3)
      & v1_funct_1(sK5) ) ),
    introduced(choice_axiom,[])).

fof(f1491,plain,(
    ? [X0,X1,X2,X3] :
      ( ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
        | ~ v1_funct_2(X3,X0,X2)
        | ~ v1_funct_1(X3) )
      & ( k1_xboole_0 = X0
        | k1_xboole_0 != X1 )
      & r1_tarski(X1,X2)
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X3,X0,X1)
      & v1_funct_1(X3) ) ),
    inference(flattening,[],[f1490])).

fof(f1490,plain,(
    ? [X0,X1,X2,X3] :
      ( ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
        | ~ v1_funct_2(X3,X0,X2)
        | ~ v1_funct_1(X3) )
      & ( k1_xboole_0 = X0
        | k1_xboole_0 != X1 )
      & r1_tarski(X1,X2)
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X3,X0,X1)
      & v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f1484])).

fof(f1484,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X3,X0,X1)
          & v1_funct_1(X3) )
       => ( r1_tarski(X1,X2)
         => ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
              & v1_funct_2(X3,X0,X2)
              & v1_funct_1(X3) )
            | ( k1_xboole_0 != X0
              & k1_xboole_0 = X1 ) ) ) ) ),
    inference(negated_conjecture,[],[f1483])).

fof(f1483,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
     => ( r1_tarski(X1,X2)
       => ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
            & v1_funct_2(X3,X0,X2)
            & v1_funct_1(X3) )
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t9_funct_2)).

fof(f8564,plain,
    ( spl75_118
    | ~ spl75_213 ),
    inference(avatar_contradiction_clause,[],[f8563])).

fof(f8563,plain,
    ( $false
    | spl75_118
    | ~ spl75_213 ),
    inference(subsumption_resolution,[],[f8562,f1913])).

fof(f8562,plain,
    ( ~ r1_tarski(k1_xboole_0,sK5)
    | spl75_118
    | ~ spl75_213 ),
    inference(subsumption_resolution,[],[f8460,f3155])).

fof(f3155,plain,
    ( k1_xboole_0 != sK5
    | spl75_118 ),
    inference(avatar_component_clause,[],[f3154])).

fof(f8460,plain,
    ( k1_xboole_0 = sK5
    | ~ r1_tarski(k1_xboole_0,sK5)
    | ~ spl75_213 ),
    inference(resolution,[],[f5415,f1921])).

fof(f1921,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f1739])).

fof(f1739,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f1738])).

fof(f1738,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f37])).

fof(f37,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f5415,plain,
    ( r1_tarski(sK5,k1_xboole_0)
    | ~ spl75_213 ),
    inference(avatar_component_clause,[],[f5414])).

fof(f7587,plain,
    ( ~ spl75_11
    | spl75_292 ),
    inference(avatar_contradiction_clause,[],[f7586])).

fof(f7586,plain,
    ( $false
    | ~ spl75_11
    | spl75_292 ),
    inference(subsumption_resolution,[],[f7517,f1949])).

fof(f1949,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f522])).

fof(f522,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

fof(f7517,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK5))
    | ~ spl75_11
    | spl75_292 ),
    inference(resolution,[],[f7390,f2517])).

fof(f2517,plain,
    ( ! [X14] :
        ( v1_funct_1(X14)
        | ~ m1_subset_1(X14,k1_zfmisc_1(sK5)) )
    | ~ spl75_11 ),
    inference(avatar_component_clause,[],[f2516])).

fof(f2516,plain,
    ( spl75_11
  <=> ! [X14] :
        ( v1_funct_1(X14)
        | ~ m1_subset_1(X14,k1_zfmisc_1(sK5)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl75_11])])).

fof(f7390,plain,
    ( ~ v1_funct_1(k1_xboole_0)
    | spl75_292 ),
    inference(avatar_component_clause,[],[f7388])).

fof(f7412,plain,
    ( spl75_282
    | ~ spl75_4
    | ~ spl75_90 ),
    inference(avatar_split_clause,[],[f7411,f2878,f2396,f7299])).

fof(f2878,plain,
    ( spl75_90
  <=> v1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl75_90])])).

fof(f7411,plain,
    ( v1_relat_1(k1_xboole_0)
    | ~ spl75_4
    | ~ spl75_90 ),
    inference(forward_demodulation,[],[f2879,f2397])).

fof(f2879,plain,
    ( v1_relat_1(sK3)
    | ~ spl75_90 ),
    inference(avatar_component_clause,[],[f2878])).

fof(f7285,plain,
    ( ~ spl75_4
    | spl75_90 ),
    inference(avatar_contradiction_clause,[],[f7284])).

fof(f7284,plain,
    ( $false
    | ~ spl75_4
    | spl75_90 ),
    inference(subsumption_resolution,[],[f7213,f1979])).

fof(f1979,plain,(
    ! [X0,X1] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ),
    inference(cnf_transformation,[],[f1248])).

fof(f1248,axiom,(
    ! [X0,X1] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_relset_1)).

fof(f7213,plain,
    ( ! [X0,X1] : ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ spl75_4
    | spl75_90 ),
    inference(resolution,[],[f6988,f1963])).

fof(f1963,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f1532])).

fof(f1532,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f1210])).

fof(f1210,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f6988,plain,
    ( ~ v1_relat_1(k1_xboole_0)
    | ~ spl75_4
    | spl75_90 ),
    inference(superposition,[],[f2880,f2397])).

fof(f2880,plain,
    ( ~ v1_relat_1(sK3)
    | spl75_90 ),
    inference(avatar_component_clause,[],[f2878])).

fof(f6926,plain,
    ( spl75_259
    | ~ spl75_145 ),
    inference(avatar_split_clause,[],[f6925,f3816,f6750])).

fof(f6750,plain,
    ( spl75_259
  <=> sK2 = k1_relat_1(sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl75_259])])).

fof(f3816,plain,
    ( spl75_145
  <=> sK2 = k1_relset_1(sK2,sK3,sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl75_145])])).

fof(f6925,plain,
    ( sK2 = k1_relat_1(sK5)
    | ~ spl75_145 ),
    inference(subsumption_resolution,[],[f6788,f1907])).

fof(f6788,plain,
    ( sK2 = k1_relat_1(sK5)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
    | ~ spl75_145 ),
    inference(superposition,[],[f3818,f2237])).

fof(f2237,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f1659])).

fof(f1659,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f1227])).

fof(f1227,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f3818,plain,
    ( sK2 = k1_relset_1(sK2,sK3,sK5)
    | ~ spl75_145 ),
    inference(avatar_component_clause,[],[f3816])).

fof(f6889,plain,
    ( ~ spl75_3
    | ~ spl75_259
    | spl75_141 ),
    inference(avatar_split_clause,[],[f6777,f3798,f6750,f2391])).

fof(f2391,plain,
    ( spl75_3
  <=> m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK4))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl75_3])])).

fof(f3798,plain,
    ( spl75_141
  <=> sK2 = k1_relset_1(sK2,sK4,sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl75_141])])).

fof(f6777,plain,
    ( sK2 != k1_relat_1(sK5)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK4)))
    | spl75_141 ),
    inference(superposition,[],[f3800,f2237])).

fof(f3800,plain,
    ( sK2 != k1_relset_1(sK2,sK4,sK5)
    | spl75_141 ),
    inference(avatar_component_clause,[],[f3798])).

fof(f6856,plain,
    ( spl75_3
    | ~ spl75_6 ),
    inference(avatar_contradiction_clause,[],[f6855])).

fof(f6855,plain,
    ( $false
    | spl75_3
    | ~ spl75_6 ),
    inference(subsumption_resolution,[],[f6810,f5758])).

fof(f5758,plain,
    ( ~ r1_tarski(k2_relat_1(sK5),sK4)
    | spl75_3
    | ~ spl75_6 ),
    inference(subsumption_resolution,[],[f5757,f2495])).

fof(f2495,plain,
    ( v1_relat_1(sK5)
    | ~ spl75_6 ),
    inference(avatar_component_clause,[],[f2494])).

fof(f2494,plain,
    ( spl75_6
  <=> v1_relat_1(sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl75_6])])).

fof(f5757,plain,
    ( ~ r1_tarski(k2_relat_1(sK5),sK4)
    | ~ v1_relat_1(sK5)
    | spl75_3
    | ~ spl75_6 ),
    inference(subsumption_resolution,[],[f5744,f4186])).

fof(f4186,plain,
    ( r1_tarski(k1_relat_1(sK5),sK2)
    | ~ spl75_6 ),
    inference(subsumption_resolution,[],[f4169,f2495])).

fof(f4169,plain,
    ( r1_tarski(k1_relat_1(sK5),sK2)
    | ~ v1_relat_1(sK5) ),
    inference(resolution,[],[f2982,f2292])).

fof(f2292,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(X1),X0)
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f1895])).

fof(f1895,plain,(
    ! [X0,X1] :
      ( ( ( v4_relat_1(X1,X0)
          | ~ r1_tarski(k1_relat_1(X1),X0) )
        & ( r1_tarski(k1_relat_1(X1),X0)
          | ~ v4_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f1699])).

fof(f1699,plain,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f651])).

fof(f651,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d18_relat_1)).

fof(f2982,plain,(
    v4_relat_1(sK5,sK2) ),
    inference(resolution,[],[f1907,f2263])).

fof(f2263,plain,(
    ! [X2,X0,X1] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f1688])).

fof(f1688,plain,(
    ! [X0,X1,X2] :
      ( ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f1211])).

fof(f1211,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f5744,plain,
    ( ~ r1_tarski(k2_relat_1(sK5),sK4)
    | ~ r1_tarski(k1_relat_1(sK5),sK2)
    | ~ v1_relat_1(sK5)
    | spl75_3 ),
    inference(resolution,[],[f2393,f2303])).

fof(f2303,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f1704])).

fof(f1704,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f1703])).

fof(f1703,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f1240])).

fof(f1240,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( ( r1_tarski(k2_relat_1(X2),X1)
          & r1_tarski(k1_relat_1(X2),X0) )
       => m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_relset_1)).

fof(f2393,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK4)))
    | spl75_3 ),
    inference(avatar_component_clause,[],[f2391])).

fof(f6810,plain,
    ( r1_tarski(k2_relat_1(sK5),sK4)
    | ~ spl75_6 ),
    inference(resolution,[],[f4210,f2829])).

fof(f2829,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,sK3)
      | r1_tarski(X0,sK4) ) ),
    inference(resolution,[],[f1908,f1914])).

fof(f1914,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f1495])).

fof(f1495,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f1494])).

fof(f1494,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f77])).

fof(f77,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).

fof(f1908,plain,(
    r1_tarski(sK3,sK4) ),
    inference(cnf_transformation,[],[f1731])).

fof(f4210,plain,
    ( r1_tarski(k2_relat_1(sK5),sK3)
    | ~ spl75_6 ),
    inference(subsumption_resolution,[],[f4198,f2495])).

fof(f4198,plain,
    ( r1_tarski(k2_relat_1(sK5),sK3)
    | ~ v1_relat_1(sK5) ),
    inference(resolution,[],[f2983,f2255])).

fof(f2255,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(X1),X0)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f1884])).

fof(f1884,plain,(
    ! [X0,X1] :
      ( ( ( v5_relat_1(X1,X0)
          | ~ r1_tarski(k2_relat_1(X1),X0) )
        & ( r1_tarski(k2_relat_1(X1),X0)
          | ~ v5_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f1681])).

fof(f1681,plain,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f652])).

fof(f652,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).

fof(f2983,plain,(
    v5_relat_1(sK5,sK3) ),
    inference(resolution,[],[f1907,f2264])).

fof(f2264,plain,(
    ! [X2,X0,X1] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f1688])).

fof(f4965,plain,
    ( ~ spl75_140
    | spl75_4 ),
    inference(avatar_split_clause,[],[f4964,f2396,f3794])).

fof(f3794,plain,
    ( spl75_140
  <=> k1_xboole_0 = sK4 ),
    introduced(avatar_definition,[new_symbols(naming,[spl75_140])])).

fof(f4964,plain,
    ( k1_xboole_0 != sK4
    | spl75_4 ),
    inference(subsumption_resolution,[],[f4932,f2398])).

fof(f2398,plain,
    ( k1_xboole_0 != sK3
    | spl75_4 ),
    inference(avatar_component_clause,[],[f2396])).

fof(f4932,plain,
    ( k1_xboole_0 != sK4
    | k1_xboole_0 = sK3 ),
    inference(superposition,[],[f2057,f2856])).

fof(f2856,plain,(
    sK4 = k2_xboole_0(sK3,sK4) ),
    inference(resolution,[],[f1908,f2060])).

fof(f2060,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f1582])).

fof(f1582,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f68])).

fof(f68,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

fof(f2057,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = X0
      | k2_xboole_0(X0,X1) != k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f1579])).

fof(f1579,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = X0
      | k2_xboole_0(X0,X1) != k1_xboole_0 ) ),
    inference(ennf_transformation,[],[f71])).

fof(f71,axiom,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = k1_xboole_0
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t15_xboole_1)).

fof(f3844,plain,
    ( spl75_4
    | spl75_145 ),
    inference(avatar_split_clause,[],[f3685,f3816,f2396])).

fof(f3685,plain,
    ( sK2 = k1_relset_1(sK2,sK3,sK5)
    | k1_xboole_0 = sK3 ),
    inference(subsumption_resolution,[],[f2899,f1907])).

fof(f2899,plain,
    ( sK2 = k1_relset_1(sK2,sK3,sK5)
    | k1_xboole_0 = sK3
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) ),
    inference(resolution,[],[f1906,f1997])).

fof(f1997,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f1767])).

fof(f1767,plain,(
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
    inference(nnf_transformation,[],[f1549])).

fof(f1549,plain,(
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
    inference(flattening,[],[f1548])).

fof(f1548,plain,(
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
    inference(ennf_transformation,[],[f1471])).

fof(f1471,axiom,(
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

fof(f1906,plain,(
    v1_funct_2(sK5,sK2,sK3) ),
    inference(cnf_transformation,[],[f1731])).

fof(f3801,plain,
    ( ~ spl75_3
    | spl75_140
    | ~ spl75_141
    | spl75_2 ),
    inference(avatar_split_clause,[],[f2915,f2387,f3798,f3794,f2391])).

fof(f2915,plain,
    ( sK2 != k1_relset_1(sK2,sK4,sK5)
    | k1_xboole_0 = sK4
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK4)))
    | spl75_2 ),
    inference(resolution,[],[f2389,f1999])).

fof(f1999,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(X2,X0,X1)
      | k1_relset_1(X0,X1,X2) != X0
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f1767])).

fof(f3229,plain,(
    spl75_6 ),
    inference(avatar_split_clause,[],[f2949,f2494])).

fof(f2949,plain,(
    v1_relat_1(sK5) ),
    inference(resolution,[],[f1907,f1963])).

fof(f2518,plain,
    ( ~ spl75_6
    | spl75_11
    | ~ spl75_1 ),
    inference(avatar_split_clause,[],[f2413,f2383,f2516,f2494])).

fof(f2383,plain,
    ( spl75_1
  <=> v1_funct_1(sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl75_1])])).

fof(f2413,plain,
    ( ! [X14] :
        ( v1_funct_1(X14)
        | ~ m1_subset_1(X14,k1_zfmisc_1(sK5))
        | ~ v1_relat_1(sK5) )
    | ~ spl75_1 ),
    inference(resolution,[],[f2384,f2017])).

fof(f2017,plain,(
    ! [X0,X1] :
      ( v1_funct_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f1555])).

fof(f1555,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_funct_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f1554])).

fof(f1554,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_funct_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f892])).

fof(f892,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_funct_1(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc3_funct_1)).

fof(f2384,plain,
    ( v1_funct_1(sK5)
    | ~ spl75_1 ),
    inference(avatar_component_clause,[],[f2383])).

fof(f2404,plain,(
    spl75_1 ),
    inference(avatar_split_clause,[],[f1905,f2383])).

fof(f1905,plain,(
    v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f1731])).

fof(f2403,plain,
    ( ~ spl75_4
    | spl75_5 ),
    inference(avatar_split_clause,[],[f1909,f2400,f2396])).

fof(f1909,plain,
    ( k1_xboole_0 = sK2
    | k1_xboole_0 != sK3 ),
    inference(cnf_transformation,[],[f1731])).

fof(f2394,plain,
    ( ~ spl75_1
    | ~ spl75_2
    | ~ spl75_3 ),
    inference(avatar_split_clause,[],[f1910,f2391,f2387,f2383])).

fof(f1910,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK4)))
    | ~ v1_funct_2(sK5,sK2,sK4)
    | ~ v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f1731])).
%------------------------------------------------------------------------------
