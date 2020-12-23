%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:03:11 EST 2020

% Result     : Theorem 1.46s
% Output     : Refutation 1.46s
% Verified   : 
% Statistics : Number of formulae       :  186 ( 922 expanded)
%              Number of leaves         :   30 ( 212 expanded)
%              Depth                    :   19
%              Number of atoms          :  517 (4175 expanded)
%              Number of equality atoms :   85 ( 819 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2538,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f111,f160,f170,f184,f265,f442,f731,f864,f927,f961,f1297,f1484,f1889,f2229,f2364,f2535])).

fof(f2535,plain,
    ( ~ spl4_2
    | spl4_3
    | ~ spl4_19
    | ~ spl4_29 ),
    inference(avatar_contradiction_clause,[],[f2523])).

fof(f2523,plain,
    ( $false
    | ~ spl4_2
    | spl4_3
    | ~ spl4_19
    | ~ spl4_29 ),
    inference(resolution,[],[f2385,f1184])).

fof(f1184,plain,
    ( ! [X0] : r1_tarski(k1_xboole_0,X0)
    | ~ spl4_19 ),
    inference(resolution,[],[f794,f51])).

fof(f51,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

fof(f794,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        | r1_tarski(k1_xboole_0,X0) )
    | ~ spl4_19 ),
    inference(resolution,[],[f756,f70])).

fof(f70,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v5_relat_1(X2,X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f756,plain,
    ( ! [X2] :
        ( ~ v5_relat_1(k1_xboole_0,X2)
        | r1_tarski(k1_xboole_0,X2) )
    | ~ spl4_19 ),
    inference(forward_demodulation,[],[f745,f50])).

fof(f50,plain,(
    k1_xboole_0 = k2_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    & k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

fof(f745,plain,
    ( ! [X2] :
        ( r1_tarski(k2_relat_1(k1_xboole_0),X2)
        | ~ v5_relat_1(k1_xboole_0,X2) )
    | ~ spl4_19 ),
    inference(resolution,[],[f705,f55])).

fof(f55,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | r1_tarski(k2_relat_1(X1),X0)
      | ~ v5_relat_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
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

fof(f705,plain,
    ( v1_relat_1(k1_xboole_0)
    | ~ spl4_19 ),
    inference(avatar_component_clause,[],[f704])).

fof(f704,plain,
    ( spl4_19
  <=> v1_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_19])])).

fof(f2385,plain,
    ( ~ r1_tarski(k1_xboole_0,k1_xboole_0)
    | ~ spl4_2
    | spl4_3
    | ~ spl4_29 ),
    inference(forward_demodulation,[],[f2384,f2247])).

fof(f2247,plain,
    ( k1_xboole_0 = sK3
    | ~ spl4_2
    | ~ spl4_29 ),
    inference(forward_demodulation,[],[f2246,f83])).

fof(f83,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f65])).

fof(f65,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != X1
      | k1_xboole_0 = k2_zfmisc_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f2246,plain,
    ( sK3 = k2_zfmisc_1(sK0,k1_xboole_0)
    | ~ spl4_2
    | ~ spl4_29 ),
    inference(forward_demodulation,[],[f956,f109])).

fof(f109,plain,
    ( k1_xboole_0 = sK1
    | ~ spl4_2 ),
    inference(avatar_component_clause,[],[f108])).

fof(f108,plain,
    ( spl4_2
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f956,plain,
    ( sK3 = k2_zfmisc_1(sK0,sK1)
    | ~ spl4_29 ),
    inference(avatar_component_clause,[],[f954])).

fof(f954,plain,
    ( spl4_29
  <=> sK3 = k2_zfmisc_1(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_29])])).

fof(f2384,plain,
    ( ~ r1_tarski(sK3,k1_xboole_0)
    | ~ spl4_2
    | spl4_3 ),
    inference(forward_demodulation,[],[f2383,f83])).

fof(f2383,plain,
    ( ~ r1_tarski(sK3,k2_zfmisc_1(sK2,k1_xboole_0))
    | ~ spl4_2
    | spl4_3 ),
    inference(forward_demodulation,[],[f1775,f109])).

fof(f1775,plain,
    ( ~ r1_tarski(sK3,k2_zfmisc_1(sK2,sK1))
    | spl4_3 ),
    inference(resolution,[],[f1750,f61])).

fof(f61,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f1750,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | spl4_3 ),
    inference(resolution,[],[f1014,f568])).

fof(f568,plain,
    ( ~ m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | spl4_3 ),
    inference(backward_demodulation,[],[f151,f123])).

fof(f123,plain,(
    ! [X0] : k2_partfun1(sK0,sK1,sK3,X0) = k7_relat_1(sK3,X0) ),
    inference(global_subsumption,[],[f44,f117])).

fof(f117,plain,(
    ! [X0] :
      ( ~ v1_funct_1(sK3)
      | k2_partfun1(sK0,sK1,sK3,X0) = k7_relat_1(sK3,X0) ) ),
    inference(resolution,[],[f46,f78])).

fof(f78,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1,X2,X3] :
      ( k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f38])).

fof(f38,plain,(
    ! [X0,X1,X2,X3] :
      ( k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_partfun1)).

fof(f46,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
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
    inference(flattening,[],[f21])).

fof(f21,plain,(
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
    inference(ennf_transformation,[],[f20])).

fof(f20,negated_conjecture,(
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
    inference(negated_conjecture,[],[f19])).

fof(f19,conjecture,(
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

fof(f44,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f22])).

fof(f151,plain,
    ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | spl4_3 ),
    inference(avatar_component_clause,[],[f149])).

fof(f149,plain,
    ( spl4_3
  <=> m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f1014,plain,(
    ! [X4,X5,X3] :
      ( m1_subset_1(k7_relat_1(sK3,X5),k1_zfmisc_1(k2_zfmisc_1(X3,X4)))
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) ) ),
    inference(global_subsumption,[],[f44,f1012])).

fof(f1012,plain,(
    ! [X4,X5,X3] :
      ( m1_subset_1(k7_relat_1(sK3,X5),k1_zfmisc_1(k2_zfmisc_1(X3,X4)))
      | ~ v1_funct_1(sK3)
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) ) ),
    inference(duplicate_literal_removal,[],[f1011])).

fof(f1011,plain,(
    ! [X4,X5,X3] :
      ( m1_subset_1(k7_relat_1(sK3,X5),k1_zfmisc_1(k2_zfmisc_1(X3,X4)))
      | ~ v1_funct_1(sK3)
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) ) ),
    inference(superposition,[],[f80,f92])).

fof(f92,plain,(
    ! [X6,X8,X7] :
      ( k2_partfun1(X6,X7,sK3,X8) = k7_relat_1(sK3,X8)
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X6,X7))) ) ),
    inference(resolution,[],[f44,f78])).

fof(f80,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(k2_partfun1(X0,X1,X2,X3)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f40])).

fof(f40,plain,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(k2_partfun1(X0,X1,X2,X3)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => ( m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(k2_partfun1(X0,X1,X2,X3)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_partfun1)).

fof(f2364,plain,
    ( ~ spl4_1
    | ~ spl4_2
    | spl4_4
    | ~ spl4_6
    | ~ spl4_19
    | ~ spl4_25
    | ~ spl4_40 ),
    inference(avatar_contradiction_clause,[],[f2353])).

fof(f2353,plain,
    ( $false
    | ~ spl4_1
    | ~ spl4_2
    | spl4_4
    | ~ spl4_6
    | ~ spl4_19
    | ~ spl4_25
    | ~ spl4_40 ),
    inference(resolution,[],[f2184,f1198])).

fof(f1198,plain,
    ( ! [X9] : v1_funct_2(k1_xboole_0,k1_xboole_0,X9)
    | ~ spl4_19
    | ~ spl4_25 ),
    inference(subsumption_resolution,[],[f863,f1184])).

fof(f863,plain,
    ( ! [X9] :
        ( v1_funct_2(k1_xboole_0,k1_xboole_0,X9)
        | ~ r1_tarski(k1_xboole_0,X9) )
    | ~ spl4_25 ),
    inference(avatar_component_clause,[],[f862])).

fof(f862,plain,
    ( spl4_25
  <=> ! [X9] :
        ( v1_funct_2(k1_xboole_0,k1_xboole_0,X9)
        | ~ r1_tarski(k1_xboole_0,X9) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_25])])).

fof(f2184,plain,
    ( ~ v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0)
    | ~ spl4_1
    | ~ spl4_2
    | spl4_4
    | ~ spl4_6
    | ~ spl4_19
    | ~ spl4_40 ),
    inference(forward_demodulation,[],[f2183,f1500])).

fof(f1500,plain,
    ( k1_xboole_0 = k7_relat_1(sK3,k1_xboole_0)
    | ~ spl4_19
    | ~ spl4_40 ),
    inference(resolution,[],[f1483,f1229])).

fof(f1229,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0))
        | k1_xboole_0 = X0 )
    | ~ spl4_19 ),
    inference(resolution,[],[f1200,f62])).

fof(f62,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f6])).

fof(f1200,plain,
    ( ! [X1] :
        ( ~ r1_tarski(X1,k1_xboole_0)
        | k1_xboole_0 = X1 )
    | ~ spl4_19 ),
    inference(resolution,[],[f1184,f60])).

fof(f60,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r1_tarski(X1,X0)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f1483,plain,
    ( m1_subset_1(k7_relat_1(sK3,k1_xboole_0),k1_zfmisc_1(k1_xboole_0))
    | ~ spl4_40 ),
    inference(avatar_component_clause,[],[f1481])).

fof(f1481,plain,
    ( spl4_40
  <=> m1_subset_1(k7_relat_1(sK3,k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_40])])).

fof(f2183,plain,
    ( ~ v1_funct_2(k7_relat_1(sK3,k1_xboole_0),k1_xboole_0,k1_xboole_0)
    | ~ spl4_1
    | ~ spl4_2
    | spl4_4
    | ~ spl4_6 ),
    inference(backward_demodulation,[],[f2108,f1980])).

fof(f1980,plain,
    ( k1_xboole_0 = sK2
    | ~ spl4_1
    | ~ spl4_6 ),
    inference(forward_demodulation,[],[f165,f106])).

fof(f106,plain,
    ( k1_xboole_0 = sK0
    | ~ spl4_1 ),
    inference(avatar_component_clause,[],[f104])).

fof(f104,plain,
    ( spl4_1
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f165,plain,
    ( sK0 = sK2
    | ~ spl4_6 ),
    inference(avatar_component_clause,[],[f163])).

fof(f163,plain,
    ( spl4_6
  <=> sK0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).

fof(f2108,plain,
    ( ~ v1_funct_2(k7_relat_1(sK3,sK2),sK2,k1_xboole_0)
    | ~ spl4_2
    | spl4_4 ),
    inference(forward_demodulation,[],[f569,f109])).

fof(f569,plain,
    ( ~ v1_funct_2(k7_relat_1(sK3,sK2),sK2,sK1)
    | spl4_4 ),
    inference(backward_demodulation,[],[f155,f123])).

fof(f155,plain,
    ( ~ v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1)
    | spl4_4 ),
    inference(avatar_component_clause,[],[f153])).

fof(f153,plain,
    ( spl4_4
  <=> v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f2229,plain,
    ( ~ spl4_1
    | ~ spl4_19
    | spl4_30 ),
    inference(avatar_contradiction_clause,[],[f2221])).

fof(f2221,plain,
    ( $false
    | ~ spl4_1
    | ~ spl4_19
    | spl4_30 ),
    inference(resolution,[],[f1936,f1184])).

fof(f1936,plain,
    ( ~ r1_tarski(k1_xboole_0,sK3)
    | ~ spl4_1
    | spl4_30 ),
    inference(forward_demodulation,[],[f1923,f84])).

fof(f84,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f64])).

fof(f64,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != X0
      | k1_xboole_0 = k2_zfmisc_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f4])).

fof(f1923,plain,
    ( ~ r1_tarski(k2_zfmisc_1(k1_xboole_0,sK1),sK3)
    | ~ spl4_1
    | spl4_30 ),
    inference(backward_demodulation,[],[f960,f106])).

fof(f960,plain,
    ( ~ r1_tarski(k2_zfmisc_1(sK0,sK1),sK3)
    | spl4_30 ),
    inference(avatar_component_clause,[],[f958])).

fof(f958,plain,
    ( spl4_30
  <=> r1_tarski(k2_zfmisc_1(sK0,sK1),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_30])])).

fof(f1889,plain,
    ( spl4_3
    | ~ spl4_13 ),
    inference(avatar_contradiction_clause,[],[f1887])).

fof(f1887,plain,
    ( $false
    | spl4_3
    | ~ spl4_13 ),
    inference(subsumption_resolution,[],[f47,f1880])).

fof(f1880,plain,
    ( ~ r1_tarski(sK2,sK0)
    | spl4_3
    | ~ spl4_13 ),
    inference(resolution,[],[f1624,f603])).

fof(f603,plain,
    ( ~ r1_tarski(k7_relat_1(sK3,sK2),k2_zfmisc_1(sK2,sK1))
    | spl4_3 ),
    inference(resolution,[],[f568,f61])).

fof(f1624,plain,
    ( ! [X0] :
        ( r1_tarski(k7_relat_1(sK3,X0),k2_zfmisc_1(X0,sK1))
        | ~ r1_tarski(X0,sK0) )
    | ~ spl4_13 ),
    inference(superposition,[],[f1469,f952])).

fof(f952,plain,
    ( ! [X3] :
        ( k1_relat_1(k7_relat_1(sK3,X3)) = X3
        | ~ r1_tarski(X3,sK0) )
    | ~ spl4_13 ),
    inference(forward_demodulation,[],[f129,f264])).

fof(f264,plain,
    ( sK0 = k1_relat_1(sK3)
    | ~ spl4_13 ),
    inference(avatar_component_clause,[],[f262])).

fof(f262,plain,
    ( spl4_13
  <=> sK0 = k1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_13])])).

fof(f129,plain,(
    ! [X3] :
      ( ~ r1_tarski(X3,k1_relat_1(sK3))
      | k1_relat_1(k7_relat_1(sK3,X3)) = X3 ) ),
    inference(resolution,[],[f112,f53])).

fof(f53,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | k1_relat_1(k7_relat_1(X1,X0)) = X0 ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(X0,k1_relat_1(X1))
       => k1_relat_1(k7_relat_1(X1,X0)) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_relat_1)).

fof(f112,plain,(
    v1_relat_1(sK3) ),
    inference(resolution,[],[f46,f67])).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f1469,plain,(
    ! [X11] : r1_tarski(k7_relat_1(sK3,X11),k2_zfmisc_1(k1_relat_1(k7_relat_1(sK3,X11)),sK1)) ),
    inference(resolution,[],[f647,f62])).

fof(f647,plain,(
    ! [X1] : m1_subset_1(k7_relat_1(sK3,X1),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k7_relat_1(sK3,X1)),sK1))) ),
    inference(global_subsumption,[],[f185,f619,f642])).

fof(f642,plain,(
    ! [X1] :
      ( ~ v1_relat_1(k7_relat_1(sK3,X1))
      | ~ v1_funct_1(k7_relat_1(sK3,X1))
      | m1_subset_1(k7_relat_1(sK3,X1),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k7_relat_1(sK3,X1)),sK1))) ) ),
    inference(resolution,[],[f640,f57])).

fof(f57,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
        & v1_funct_2(X1,k1_relat_1(X1),X0)
        & v1_funct_1(X1) )
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
        & v1_funct_2(X1,k1_relat_1(X1),X0)
        & v1_funct_1(X1) )
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( r1_tarski(k2_relat_1(X1),X0)
       => ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
          & v1_funct_2(X1,k1_relat_1(X1),X0)
          & v1_funct_1(X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_funct_2)).

fof(f640,plain,(
    ! [X0] : r1_tarski(k2_relat_1(k7_relat_1(sK3,X0)),sK1) ),
    inference(global_subsumption,[],[f619,f639])).

fof(f639,plain,(
    ! [X0] :
      ( ~ v1_relat_1(k7_relat_1(sK3,X0))
      | r1_tarski(k2_relat_1(k7_relat_1(sK3,X0)),sK1) ) ),
    inference(resolution,[],[f621,f55])).

fof(f621,plain,(
    ! [X2] : v5_relat_1(k7_relat_1(sK3,X2),sK1) ),
    inference(resolution,[],[f573,f70])).

fof(f573,plain,(
    ! [X1] : m1_subset_1(k7_relat_1(sK3,X1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(global_subsumption,[],[f44,f46,f572])).

fof(f572,plain,(
    ! [X1] :
      ( m1_subset_1(k7_relat_1(sK3,X1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      | ~ v1_funct_1(sK3)
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ) ),
    inference(superposition,[],[f80,f123])).

fof(f619,plain,(
    ! [X0] : v1_relat_1(k7_relat_1(sK3,X0)) ),
    inference(resolution,[],[f573,f67])).

fof(f185,plain,(
    ! [X0] : v1_funct_1(k7_relat_1(sK3,X0)) ),
    inference(global_subsumption,[],[f44,f46,f183])).

fof(f183,plain,(
    ! [X0] :
      ( v1_funct_1(k7_relat_1(sK3,X0))
      | ~ v1_funct_1(sK3)
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ) ),
    inference(superposition,[],[f124,f78])).

fof(f124,plain,(
    ! [X1] : v1_funct_1(k2_partfun1(sK0,sK1,sK3,X1)) ),
    inference(global_subsumption,[],[f44,f118])).

fof(f118,plain,(
    ! [X1] :
      ( ~ v1_funct_1(sK3)
      | v1_funct_1(k2_partfun1(sK0,sK1,sK3,X1)) ) ),
    inference(resolution,[],[f46,f79])).

fof(f79,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_funct_1(k2_partfun1(X0,X1,X2,X3)) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f47,plain,(
    r1_tarski(sK2,sK0) ),
    inference(cnf_transformation,[],[f22])).

fof(f1484,plain,
    ( ~ spl4_28
    | spl4_40
    | ~ spl4_19 ),
    inference(avatar_split_clause,[],[f1479,f704,f1481,f901])).

fof(f901,plain,
    ( spl4_28
  <=> v1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_28])])).

fof(f1479,plain,
    ( m1_subset_1(k7_relat_1(sK3,k1_xboole_0),k1_zfmisc_1(k1_xboole_0))
    | ~ v1_relat_1(sK3)
    | ~ spl4_19 ),
    inference(forward_demodulation,[],[f1473,f84])).

fof(f1473,plain,
    ( m1_subset_1(k7_relat_1(sK3,k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1)))
    | ~ v1_relat_1(sK3)
    | ~ spl4_19 ),
    inference(superposition,[],[f647,f1203])).

fof(f1203,plain,
    ( ! [X3] :
        ( k1_xboole_0 = k1_relat_1(k7_relat_1(X3,k1_xboole_0))
        | ~ v1_relat_1(X3) )
    | ~ spl4_19 ),
    inference(resolution,[],[f1184,f53])).

fof(f1297,plain,
    ( spl4_4
    | ~ spl4_13 ),
    inference(avatar_contradiction_clause,[],[f1295])).

fof(f1295,plain,
    ( $false
    | spl4_4
    | ~ spl4_13 ),
    inference(subsumption_resolution,[],[f47,f1291])).

fof(f1291,plain,
    ( ~ r1_tarski(sK2,sK0)
    | spl4_4
    | ~ spl4_13 ),
    inference(resolution,[],[f1029,f569])).

fof(f1029,plain,
    ( ! [X0] :
        ( v1_funct_2(k7_relat_1(sK3,X0),X0,sK1)
        | ~ r1_tarski(X0,sK0) )
    | ~ spl4_13 ),
    inference(superposition,[],[f646,f952])).

fof(f646,plain,(
    ! [X0] : v1_funct_2(k7_relat_1(sK3,X0),k1_relat_1(k7_relat_1(sK3,X0)),sK1) ),
    inference(global_subsumption,[],[f185,f619,f641])).

fof(f641,plain,(
    ! [X0] :
      ( ~ v1_relat_1(k7_relat_1(sK3,X0))
      | ~ v1_funct_1(k7_relat_1(sK3,X0))
      | v1_funct_2(k7_relat_1(sK3,X0),k1_relat_1(k7_relat_1(sK3,X0)),sK1) ) ),
    inference(resolution,[],[f640,f56])).

fof(f56,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | v1_funct_2(X1,k1_relat_1(X1),X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f961,plain,
    ( spl4_29
    | ~ spl4_30 ),
    inference(avatar_split_clause,[],[f144,f958,f954])).

fof(f144,plain,
    ( ~ r1_tarski(k2_zfmisc_1(sK0,sK1),sK3)
    | sK3 = k2_zfmisc_1(sK0,sK1) ),
    inference(resolution,[],[f120,f60])).

fof(f120,plain,(
    r1_tarski(sK3,k2_zfmisc_1(sK0,sK1)) ),
    inference(resolution,[],[f46,f62])).

fof(f927,plain,(
    spl4_28 ),
    inference(avatar_split_clause,[],[f112,f901])).

fof(f864,plain,
    ( ~ spl4_19
    | spl4_25 ),
    inference(avatar_split_clause,[],[f226,f862,f704])).

fof(f226,plain,(
    ! [X9] :
      ( v1_funct_2(k1_xboole_0,k1_xboole_0,X9)
      | ~ r1_tarski(k1_xboole_0,X9)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(forward_demodulation,[],[f225,f49])).

fof(f49,plain,(
    k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f9])).

fof(f225,plain,(
    ! [X9] :
      ( ~ r1_tarski(k1_xboole_0,X9)
      | ~ v1_relat_1(k1_xboole_0)
      | v1_funct_2(k1_xboole_0,k1_relat_1(k1_xboole_0),X9) ) ),
    inference(forward_demodulation,[],[f215,f50])).

fof(f215,plain,(
    ! [X9] :
      ( ~ v1_relat_1(k1_xboole_0)
      | ~ r1_tarski(k2_relat_1(k1_xboole_0),X9)
      | v1_funct_2(k1_xboole_0,k1_relat_1(k1_xboole_0),X9) ) ),
    inference(resolution,[],[f211,f56])).

fof(f211,plain,(
    v1_funct_1(k1_xboole_0) ),
    inference(resolution,[],[f133,f51])).

fof(f133,plain,(
    ! [X4] :
      ( ~ m1_subset_1(X4,k1_zfmisc_1(sK3))
      | v1_funct_1(X4) ) ),
    inference(global_subsumption,[],[f95,f112])).

fof(f95,plain,(
    ! [X11] :
      ( ~ v1_relat_1(sK3)
      | ~ m1_subset_1(X11,k1_zfmisc_1(sK3))
      | v1_funct_1(X11) ) ),
    inference(resolution,[],[f44,f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | v1_funct_1(X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_funct_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_funct_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_funct_1(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc3_funct_1)).

fof(f731,plain,(
    spl4_19 ),
    inference(avatar_contradiction_clause,[],[f719])).

fof(f719,plain,
    ( $false
    | spl4_19 ),
    inference(resolution,[],[f708,f51])).

fof(f708,plain,
    ( ! [X0,X1] : ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | spl4_19 ),
    inference(resolution,[],[f706,f67])).

fof(f706,plain,
    ( ~ v1_relat_1(k1_xboole_0)
    | spl4_19 ),
    inference(avatar_component_clause,[],[f704])).

fof(f442,plain,
    ( ~ spl4_1
    | spl4_7 ),
    inference(avatar_contradiction_clause,[],[f433])).

fof(f433,plain,
    ( $false
    | ~ spl4_1
    | spl4_7 ),
    inference(resolution,[],[f277,f51])).

fof(f277,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK2))
    | ~ spl4_1
    | spl4_7 ),
    inference(backward_demodulation,[],[f171,f106])).

fof(f171,plain,
    ( ~ m1_subset_1(sK0,k1_zfmisc_1(sK2))
    | spl4_7 ),
    inference(resolution,[],[f169,f62])).

fof(f169,plain,
    ( ~ r1_tarski(sK0,sK2)
    | spl4_7 ),
    inference(avatar_component_clause,[],[f167])).

fof(f167,plain,
    ( spl4_7
  <=> r1_tarski(sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).

fof(f265,plain,
    ( spl4_2
    | spl4_13 ),
    inference(avatar_split_clause,[],[f239,f262,f108])).

fof(f239,plain,
    ( sK0 = k1_relat_1(sK3)
    | k1_xboole_0 = sK1 ),
    inference(global_subsumption,[],[f45,f46,f236])).

fof(f236,plain,
    ( sK0 = k1_relat_1(sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | k1_xboole_0 = sK1
    | ~ v1_funct_2(sK3,sK0,sK1) ),
    inference(superposition,[],[f113,f76])).

fof(f76,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_xboole_0 = X1
      | k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
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
    inference(flattening,[],[f34])).

fof(f34,plain,(
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
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
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

fof(f113,plain,(
    k1_relat_1(sK3) = k1_relset_1(sK0,sK1,sK3) ),
    inference(resolution,[],[f46,f68])).

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f45,plain,(
    v1_funct_2(sK3,sK0,sK1) ),
    inference(cnf_transformation,[],[f22])).

fof(f184,plain,(
    spl4_5 ),
    inference(avatar_contradiction_clause,[],[f176])).

fof(f176,plain,
    ( $false
    | spl4_5 ),
    inference(subsumption_resolution,[],[f159,f124])).

fof(f159,plain,
    ( ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))
    | spl4_5 ),
    inference(avatar_component_clause,[],[f157])).

fof(f157,plain,
    ( spl4_5
  <=> v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f170,plain,
    ( spl4_6
    | ~ spl4_7 ),
    inference(avatar_split_clause,[],[f97,f167,f163])).

fof(f97,plain,
    ( ~ r1_tarski(sK0,sK2)
    | sK0 = sK2 ),
    inference(resolution,[],[f47,f60])).

fof(f160,plain,
    ( ~ spl4_3
    | ~ spl4_4
    | ~ spl4_5 ),
    inference(avatar_split_clause,[],[f42,f157,f153,f149])).

fof(f42,plain,
    ( ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))
    | ~ v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1)
    | ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) ),
    inference(cnf_transformation,[],[f22])).

fof(f111,plain,
    ( spl4_1
    | ~ spl4_2 ),
    inference(avatar_split_clause,[],[f43,f108,f104])).

fof(f43,plain,
    ( k1_xboole_0 != sK1
    | k1_xboole_0 = sK0 ),
    inference(cnf_transformation,[],[f22])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n006.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 16:19:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.47  % (24861)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.48  % (24881)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 0.21/0.49  % (24861)Refutation not found, incomplete strategy% (24861)------------------------------
% 0.21/0.49  % (24861)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.49  % (24861)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.49  
% 0.21/0.49  % (24861)Memory used [KB]: 10874
% 0.21/0.49  % (24861)Time elapsed: 0.077 s
% 0.21/0.49  % (24861)------------------------------
% 0.21/0.49  % (24861)------------------------------
% 0.21/0.49  % (24863)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.21/0.50  % (24860)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 0.21/0.50  % (24872)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 0.21/0.51  % (24880)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 0.21/0.51  % (24865)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.21/0.51  % (24866)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.21/0.51  % (24875)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.21/0.51  % (24867)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 0.21/0.51  % (24869)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 0.21/0.51  % (24886)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_364 on theBenchmark
% 0.21/0.51  % (24862)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.21/0.52  % (24873)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 0.21/0.52  % (24871)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 0.21/0.52  % (24884)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 0.21/0.52  % (24882)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 0.21/0.53  % (24876)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 0.21/0.53  % (24883)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 0.21/0.53  % (24870)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
% 0.21/0.53  % (24877)lrs+4_5:4_av=off:bd=off:er=filter:lma=on:lwlo=on:nwc=1:stl=30:sp=occurrence:updr=off_230 on theBenchmark
% 0.21/0.53  % (24874)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 0.21/0.54  % (24878)lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_145 on theBenchmark
% 0.21/0.54  % (24879)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 1.46/0.54  % (24881)Refutation found. Thanks to Tanya!
% 1.46/0.54  % SZS status Theorem for theBenchmark
% 1.46/0.54  % SZS output start Proof for theBenchmark
% 1.46/0.54  fof(f2538,plain,(
% 1.46/0.54    $false),
% 1.46/0.54    inference(avatar_sat_refutation,[],[f111,f160,f170,f184,f265,f442,f731,f864,f927,f961,f1297,f1484,f1889,f2229,f2364,f2535])).
% 1.46/0.54  fof(f2535,plain,(
% 1.46/0.54    ~spl4_2 | spl4_3 | ~spl4_19 | ~spl4_29),
% 1.46/0.54    inference(avatar_contradiction_clause,[],[f2523])).
% 1.46/0.54  fof(f2523,plain,(
% 1.46/0.54    $false | (~spl4_2 | spl4_3 | ~spl4_19 | ~spl4_29)),
% 1.46/0.54    inference(resolution,[],[f2385,f1184])).
% 1.46/0.54  fof(f1184,plain,(
% 1.46/0.54    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) ) | ~spl4_19),
% 1.46/0.54    inference(resolution,[],[f794,f51])).
% 1.46/0.54  fof(f51,plain,(
% 1.46/0.54    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 1.46/0.54    inference(cnf_transformation,[],[f5])).
% 1.46/0.54  fof(f5,axiom,(
% 1.46/0.54    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 1.46/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).
% 1.46/0.54  fof(f794,plain,(
% 1.46/0.54    ( ! [X0,X1] : (~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | r1_tarski(k1_xboole_0,X0)) ) | ~spl4_19),
% 1.46/0.54    inference(resolution,[],[f756,f70])).
% 1.46/0.54  fof(f70,plain,(
% 1.46/0.54    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v5_relat_1(X2,X1)) )),
% 1.46/0.54    inference(cnf_transformation,[],[f33])).
% 1.46/0.54  fof(f33,plain,(
% 1.46/0.54    ! [X0,X1,X2] : ((v5_relat_1(X2,X1) & v4_relat_1(X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.46/0.54    inference(ennf_transformation,[],[f13])).
% 1.46/0.54  fof(f13,axiom,(
% 1.46/0.54    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 1.46/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).
% 1.46/0.54  fof(f756,plain,(
% 1.46/0.54    ( ! [X2] : (~v5_relat_1(k1_xboole_0,X2) | r1_tarski(k1_xboole_0,X2)) ) | ~spl4_19),
% 1.46/0.54    inference(forward_demodulation,[],[f745,f50])).
% 1.46/0.54  fof(f50,plain,(
% 1.46/0.54    k1_xboole_0 = k2_relat_1(k1_xboole_0)),
% 1.46/0.54    inference(cnf_transformation,[],[f9])).
% 1.46/0.54  fof(f9,axiom,(
% 1.46/0.54    k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 1.46/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).
% 1.46/0.54  fof(f745,plain,(
% 1.46/0.54    ( ! [X2] : (r1_tarski(k2_relat_1(k1_xboole_0),X2) | ~v5_relat_1(k1_xboole_0,X2)) ) | ~spl4_19),
% 1.46/0.54    inference(resolution,[],[f705,f55])).
% 1.46/0.54  fof(f55,plain,(
% 1.46/0.54    ( ! [X0,X1] : (~v1_relat_1(X1) | r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0)) )),
% 1.46/0.54    inference(cnf_transformation,[],[f27])).
% 1.46/0.54  fof(f27,plain,(
% 1.46/0.54    ! [X0,X1] : ((v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 1.46/0.54    inference(ennf_transformation,[],[f8])).
% 1.46/0.54  fof(f8,axiom,(
% 1.46/0.54    ! [X0,X1] : (v1_relat_1(X1) => (v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)))),
% 1.46/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).
% 1.46/0.54  fof(f705,plain,(
% 1.46/0.54    v1_relat_1(k1_xboole_0) | ~spl4_19),
% 1.46/0.54    inference(avatar_component_clause,[],[f704])).
% 1.46/0.54  fof(f704,plain,(
% 1.46/0.54    spl4_19 <=> v1_relat_1(k1_xboole_0)),
% 1.46/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_19])])).
% 1.46/0.54  fof(f2385,plain,(
% 1.46/0.54    ~r1_tarski(k1_xboole_0,k1_xboole_0) | (~spl4_2 | spl4_3 | ~spl4_29)),
% 1.46/0.54    inference(forward_demodulation,[],[f2384,f2247])).
% 1.46/0.54  fof(f2247,plain,(
% 1.46/0.54    k1_xboole_0 = sK3 | (~spl4_2 | ~spl4_29)),
% 1.46/0.54    inference(forward_demodulation,[],[f2246,f83])).
% 1.46/0.54  fof(f83,plain,(
% 1.46/0.54    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 1.46/0.54    inference(equality_resolution,[],[f65])).
% 1.46/0.54  fof(f65,plain,(
% 1.46/0.54    ( ! [X0,X1] : (k1_xboole_0 != X1 | k1_xboole_0 = k2_zfmisc_1(X0,X1)) )),
% 1.46/0.54    inference(cnf_transformation,[],[f4])).
% 1.46/0.54  fof(f4,axiom,(
% 1.46/0.54    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 1.46/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 1.46/0.54  fof(f2246,plain,(
% 1.46/0.54    sK3 = k2_zfmisc_1(sK0,k1_xboole_0) | (~spl4_2 | ~spl4_29)),
% 1.46/0.54    inference(forward_demodulation,[],[f956,f109])).
% 1.46/0.54  fof(f109,plain,(
% 1.46/0.54    k1_xboole_0 = sK1 | ~spl4_2),
% 1.46/0.54    inference(avatar_component_clause,[],[f108])).
% 1.46/0.54  fof(f108,plain,(
% 1.46/0.54    spl4_2 <=> k1_xboole_0 = sK1),
% 1.46/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 1.46/0.54  fof(f956,plain,(
% 1.46/0.54    sK3 = k2_zfmisc_1(sK0,sK1) | ~spl4_29),
% 1.46/0.54    inference(avatar_component_clause,[],[f954])).
% 1.46/0.54  fof(f954,plain,(
% 1.46/0.54    spl4_29 <=> sK3 = k2_zfmisc_1(sK0,sK1)),
% 1.46/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_29])])).
% 1.46/0.54  fof(f2384,plain,(
% 1.46/0.54    ~r1_tarski(sK3,k1_xboole_0) | (~spl4_2 | spl4_3)),
% 1.46/0.54    inference(forward_demodulation,[],[f2383,f83])).
% 1.46/0.54  fof(f2383,plain,(
% 1.46/0.54    ~r1_tarski(sK3,k2_zfmisc_1(sK2,k1_xboole_0)) | (~spl4_2 | spl4_3)),
% 1.46/0.54    inference(forward_demodulation,[],[f1775,f109])).
% 1.46/0.54  fof(f1775,plain,(
% 1.46/0.54    ~r1_tarski(sK3,k2_zfmisc_1(sK2,sK1)) | spl4_3),
% 1.46/0.54    inference(resolution,[],[f1750,f61])).
% 1.46/0.54  fof(f61,plain,(
% 1.46/0.54    ( ! [X0,X1] : (~r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 1.46/0.54    inference(cnf_transformation,[],[f6])).
% 1.46/0.54  fof(f6,axiom,(
% 1.46/0.54    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 1.46/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).
% 1.46/0.54  fof(f1750,plain,(
% 1.46/0.54    ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | spl4_3),
% 1.46/0.54    inference(resolution,[],[f1014,f568])).
% 1.46/0.54  fof(f568,plain,(
% 1.46/0.54    ~m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | spl4_3),
% 1.46/0.54    inference(backward_demodulation,[],[f151,f123])).
% 1.46/0.54  fof(f123,plain,(
% 1.46/0.54    ( ! [X0] : (k2_partfun1(sK0,sK1,sK3,X0) = k7_relat_1(sK3,X0)) )),
% 1.46/0.54    inference(global_subsumption,[],[f44,f117])).
% 1.46/0.54  fof(f117,plain,(
% 1.46/0.54    ( ! [X0] : (~v1_funct_1(sK3) | k2_partfun1(sK0,sK1,sK3,X0) = k7_relat_1(sK3,X0)) )),
% 1.46/0.54    inference(resolution,[],[f46,f78])).
% 1.46/0.54  fof(f78,plain,(
% 1.46/0.54    ( ! [X2,X0,X3,X1] : (~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3)) )),
% 1.46/0.54    inference(cnf_transformation,[],[f39])).
% 1.46/0.54  fof(f39,plain,(
% 1.46/0.54    ! [X0,X1,X2,X3] : (k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 1.46/0.54    inference(flattening,[],[f38])).
% 1.46/0.54  fof(f38,plain,(
% 1.46/0.54    ! [X0,X1,X2,X3] : (k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 1.46/0.54    inference(ennf_transformation,[],[f17])).
% 1.46/0.54  fof(f17,axiom,(
% 1.46/0.54    ! [X0,X1,X2,X3] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3))),
% 1.46/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_partfun1)).
% 1.46/0.54  fof(f46,plain,(
% 1.46/0.54    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 1.46/0.54    inference(cnf_transformation,[],[f22])).
% 1.46/0.54  fof(f22,plain,(
% 1.46/0.54    ? [X0,X1,X2,X3] : ((~m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1) | ~v1_funct_1(k2_partfun1(X0,X1,X3,X2))) & (k1_xboole_0 = X0 | k1_xboole_0 != X1) & r1_tarski(X2,X0) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3))),
% 1.46/0.54    inference(flattening,[],[f21])).
% 1.46/0.54  fof(f21,plain,(
% 1.46/0.54    ? [X0,X1,X2,X3] : ((((~m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1) | ~v1_funct_1(k2_partfun1(X0,X1,X3,X2))) & (k1_xboole_0 = X0 | k1_xboole_0 != X1)) & r1_tarski(X2,X0)) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)))),
% 1.46/0.54    inference(ennf_transformation,[],[f20])).
% 1.46/0.54  fof(f20,negated_conjecture,(
% 1.46/0.54    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r1_tarski(X2,X0) => ((m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1) & v1_funct_1(k2_partfun1(X0,X1,X3,X2))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))))),
% 1.46/0.54    inference(negated_conjecture,[],[f19])).
% 1.46/0.54  fof(f19,conjecture,(
% 1.46/0.54    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r1_tarski(X2,X0) => ((m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1) & v1_funct_1(k2_partfun1(X0,X1,X3,X2))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))))),
% 1.46/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_funct_2)).
% 1.46/0.54  fof(f44,plain,(
% 1.46/0.54    v1_funct_1(sK3)),
% 1.46/0.54    inference(cnf_transformation,[],[f22])).
% 1.46/0.54  fof(f151,plain,(
% 1.46/0.54    ~m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | spl4_3),
% 1.46/0.54    inference(avatar_component_clause,[],[f149])).
% 1.46/0.54  fof(f149,plain,(
% 1.46/0.54    spl4_3 <=> m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))),
% 1.46/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 1.46/0.54  fof(f1014,plain,(
% 1.46/0.54    ( ! [X4,X5,X3] : (m1_subset_1(k7_relat_1(sK3,X5),k1_zfmisc_1(k2_zfmisc_1(X3,X4))) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))) )),
% 1.46/0.54    inference(global_subsumption,[],[f44,f1012])).
% 1.46/0.54  fof(f1012,plain,(
% 1.46/0.54    ( ! [X4,X5,X3] : (m1_subset_1(k7_relat_1(sK3,X5),k1_zfmisc_1(k2_zfmisc_1(X3,X4))) | ~v1_funct_1(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))) )),
% 1.46/0.54    inference(duplicate_literal_removal,[],[f1011])).
% 1.46/0.54  fof(f1011,plain,(
% 1.46/0.54    ( ! [X4,X5,X3] : (m1_subset_1(k7_relat_1(sK3,X5),k1_zfmisc_1(k2_zfmisc_1(X3,X4))) | ~v1_funct_1(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))) )),
% 1.46/0.54    inference(superposition,[],[f80,f92])).
% 1.46/0.54  fof(f92,plain,(
% 1.46/0.54    ( ! [X6,X8,X7] : (k2_partfun1(X6,X7,sK3,X8) = k7_relat_1(sK3,X8) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X6,X7)))) )),
% 1.46/0.54    inference(resolution,[],[f44,f78])).
% 1.46/0.54  fof(f80,plain,(
% 1.46/0.54    ( ! [X2,X0,X3,X1] : (~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.46/0.54    inference(cnf_transformation,[],[f41])).
% 1.46/0.54  fof(f41,plain,(
% 1.46/0.54    ! [X0,X1,X2,X3] : ((m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(k2_partfun1(X0,X1,X2,X3))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 1.46/0.54    inference(flattening,[],[f40])).
% 1.46/0.54  fof(f40,plain,(
% 1.46/0.54    ! [X0,X1,X2,X3] : ((m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(k2_partfun1(X0,X1,X2,X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 1.46/0.54    inference(ennf_transformation,[],[f16])).
% 1.46/0.54  fof(f16,axiom,(
% 1.46/0.54    ! [X0,X1,X2,X3] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => (m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(k2_partfun1(X0,X1,X2,X3))))),
% 1.46/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_partfun1)).
% 1.46/0.54  fof(f2364,plain,(
% 1.46/0.54    ~spl4_1 | ~spl4_2 | spl4_4 | ~spl4_6 | ~spl4_19 | ~spl4_25 | ~spl4_40),
% 1.46/0.54    inference(avatar_contradiction_clause,[],[f2353])).
% 1.46/0.54  fof(f2353,plain,(
% 1.46/0.54    $false | (~spl4_1 | ~spl4_2 | spl4_4 | ~spl4_6 | ~spl4_19 | ~spl4_25 | ~spl4_40)),
% 1.46/0.54    inference(resolution,[],[f2184,f1198])).
% 1.46/0.54  fof(f1198,plain,(
% 1.46/0.54    ( ! [X9] : (v1_funct_2(k1_xboole_0,k1_xboole_0,X9)) ) | (~spl4_19 | ~spl4_25)),
% 1.46/0.54    inference(subsumption_resolution,[],[f863,f1184])).
% 1.46/0.54  fof(f863,plain,(
% 1.46/0.54    ( ! [X9] : (v1_funct_2(k1_xboole_0,k1_xboole_0,X9) | ~r1_tarski(k1_xboole_0,X9)) ) | ~spl4_25),
% 1.46/0.54    inference(avatar_component_clause,[],[f862])).
% 1.46/0.54  fof(f862,plain,(
% 1.46/0.54    spl4_25 <=> ! [X9] : (v1_funct_2(k1_xboole_0,k1_xboole_0,X9) | ~r1_tarski(k1_xboole_0,X9))),
% 1.46/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_25])])).
% 1.46/0.54  fof(f2184,plain,(
% 1.46/0.54    ~v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0) | (~spl4_1 | ~spl4_2 | spl4_4 | ~spl4_6 | ~spl4_19 | ~spl4_40)),
% 1.46/0.54    inference(forward_demodulation,[],[f2183,f1500])).
% 1.46/0.54  fof(f1500,plain,(
% 1.46/0.54    k1_xboole_0 = k7_relat_1(sK3,k1_xboole_0) | (~spl4_19 | ~spl4_40)),
% 1.46/0.54    inference(resolution,[],[f1483,f1229])).
% 1.46/0.54  fof(f1229,plain,(
% 1.46/0.54    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) | k1_xboole_0 = X0) ) | ~spl4_19),
% 1.46/0.54    inference(resolution,[],[f1200,f62])).
% 1.46/0.54  fof(f62,plain,(
% 1.46/0.54    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 1.46/0.54    inference(cnf_transformation,[],[f6])).
% 1.46/0.54  fof(f1200,plain,(
% 1.46/0.54    ( ! [X1] : (~r1_tarski(X1,k1_xboole_0) | k1_xboole_0 = X1) ) | ~spl4_19),
% 1.46/0.54    inference(resolution,[],[f1184,f60])).
% 1.46/0.54  fof(f60,plain,(
% 1.46/0.54    ( ! [X0,X1] : (~r1_tarski(X0,X1) | ~r1_tarski(X1,X0) | X0 = X1) )),
% 1.46/0.54    inference(cnf_transformation,[],[f2])).
% 1.46/0.54  fof(f2,axiom,(
% 1.46/0.54    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.46/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 1.46/0.54  fof(f1483,plain,(
% 1.46/0.54    m1_subset_1(k7_relat_1(sK3,k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) | ~spl4_40),
% 1.46/0.54    inference(avatar_component_clause,[],[f1481])).
% 1.46/0.54  fof(f1481,plain,(
% 1.46/0.54    spl4_40 <=> m1_subset_1(k7_relat_1(sK3,k1_xboole_0),k1_zfmisc_1(k1_xboole_0))),
% 1.46/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_40])])).
% 1.46/0.54  fof(f2183,plain,(
% 1.46/0.54    ~v1_funct_2(k7_relat_1(sK3,k1_xboole_0),k1_xboole_0,k1_xboole_0) | (~spl4_1 | ~spl4_2 | spl4_4 | ~spl4_6)),
% 1.46/0.54    inference(backward_demodulation,[],[f2108,f1980])).
% 1.46/0.54  fof(f1980,plain,(
% 1.46/0.54    k1_xboole_0 = sK2 | (~spl4_1 | ~spl4_6)),
% 1.46/0.54    inference(forward_demodulation,[],[f165,f106])).
% 1.46/0.54  fof(f106,plain,(
% 1.46/0.54    k1_xboole_0 = sK0 | ~spl4_1),
% 1.46/0.54    inference(avatar_component_clause,[],[f104])).
% 1.46/0.54  fof(f104,plain,(
% 1.46/0.54    spl4_1 <=> k1_xboole_0 = sK0),
% 1.46/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 1.46/0.54  fof(f165,plain,(
% 1.46/0.54    sK0 = sK2 | ~spl4_6),
% 1.46/0.54    inference(avatar_component_clause,[],[f163])).
% 1.46/0.54  fof(f163,plain,(
% 1.46/0.54    spl4_6 <=> sK0 = sK2),
% 1.46/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).
% 1.46/0.54  fof(f2108,plain,(
% 1.46/0.54    ~v1_funct_2(k7_relat_1(sK3,sK2),sK2,k1_xboole_0) | (~spl4_2 | spl4_4)),
% 1.46/0.54    inference(forward_demodulation,[],[f569,f109])).
% 1.46/0.54  fof(f569,plain,(
% 1.46/0.54    ~v1_funct_2(k7_relat_1(sK3,sK2),sK2,sK1) | spl4_4),
% 1.46/0.54    inference(backward_demodulation,[],[f155,f123])).
% 1.46/0.54  fof(f155,plain,(
% 1.46/0.54    ~v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1) | spl4_4),
% 1.46/0.54    inference(avatar_component_clause,[],[f153])).
% 1.46/0.54  fof(f153,plain,(
% 1.46/0.54    spl4_4 <=> v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1)),
% 1.46/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 1.46/0.54  fof(f2229,plain,(
% 1.46/0.54    ~spl4_1 | ~spl4_19 | spl4_30),
% 1.46/0.54    inference(avatar_contradiction_clause,[],[f2221])).
% 1.46/0.54  fof(f2221,plain,(
% 1.46/0.54    $false | (~spl4_1 | ~spl4_19 | spl4_30)),
% 1.46/0.54    inference(resolution,[],[f1936,f1184])).
% 1.46/0.54  fof(f1936,plain,(
% 1.46/0.54    ~r1_tarski(k1_xboole_0,sK3) | (~spl4_1 | spl4_30)),
% 1.46/0.54    inference(forward_demodulation,[],[f1923,f84])).
% 1.46/0.54  fof(f84,plain,(
% 1.46/0.54    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 1.46/0.54    inference(equality_resolution,[],[f64])).
% 1.46/0.54  fof(f64,plain,(
% 1.46/0.54    ( ! [X0,X1] : (k1_xboole_0 != X0 | k1_xboole_0 = k2_zfmisc_1(X0,X1)) )),
% 1.46/0.54    inference(cnf_transformation,[],[f4])).
% 1.46/0.54  fof(f1923,plain,(
% 1.46/0.54    ~r1_tarski(k2_zfmisc_1(k1_xboole_0,sK1),sK3) | (~spl4_1 | spl4_30)),
% 1.46/0.54    inference(backward_demodulation,[],[f960,f106])).
% 1.46/0.54  fof(f960,plain,(
% 1.46/0.54    ~r1_tarski(k2_zfmisc_1(sK0,sK1),sK3) | spl4_30),
% 1.46/0.54    inference(avatar_component_clause,[],[f958])).
% 1.46/0.54  fof(f958,plain,(
% 1.46/0.54    spl4_30 <=> r1_tarski(k2_zfmisc_1(sK0,sK1),sK3)),
% 1.46/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_30])])).
% 1.46/0.54  fof(f1889,plain,(
% 1.46/0.54    spl4_3 | ~spl4_13),
% 1.46/0.54    inference(avatar_contradiction_clause,[],[f1887])).
% 1.46/0.54  fof(f1887,plain,(
% 1.46/0.54    $false | (spl4_3 | ~spl4_13)),
% 1.46/0.54    inference(subsumption_resolution,[],[f47,f1880])).
% 1.46/0.54  fof(f1880,plain,(
% 1.46/0.54    ~r1_tarski(sK2,sK0) | (spl4_3 | ~spl4_13)),
% 1.46/0.54    inference(resolution,[],[f1624,f603])).
% 1.46/0.54  fof(f603,plain,(
% 1.46/0.54    ~r1_tarski(k7_relat_1(sK3,sK2),k2_zfmisc_1(sK2,sK1)) | spl4_3),
% 1.46/0.54    inference(resolution,[],[f568,f61])).
% 1.46/0.54  fof(f1624,plain,(
% 1.46/0.54    ( ! [X0] : (r1_tarski(k7_relat_1(sK3,X0),k2_zfmisc_1(X0,sK1)) | ~r1_tarski(X0,sK0)) ) | ~spl4_13),
% 1.46/0.54    inference(superposition,[],[f1469,f952])).
% 1.46/0.54  fof(f952,plain,(
% 1.46/0.54    ( ! [X3] : (k1_relat_1(k7_relat_1(sK3,X3)) = X3 | ~r1_tarski(X3,sK0)) ) | ~spl4_13),
% 1.46/0.54    inference(forward_demodulation,[],[f129,f264])).
% 1.46/0.54  fof(f264,plain,(
% 1.46/0.54    sK0 = k1_relat_1(sK3) | ~spl4_13),
% 1.46/0.54    inference(avatar_component_clause,[],[f262])).
% 1.46/0.54  fof(f262,plain,(
% 1.46/0.54    spl4_13 <=> sK0 = k1_relat_1(sK3)),
% 1.46/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_13])])).
% 1.46/0.54  fof(f129,plain,(
% 1.46/0.54    ( ! [X3] : (~r1_tarski(X3,k1_relat_1(sK3)) | k1_relat_1(k7_relat_1(sK3,X3)) = X3) )),
% 1.46/0.54    inference(resolution,[],[f112,f53])).
% 1.46/0.54  fof(f53,plain,(
% 1.46/0.54    ( ! [X0,X1] : (~v1_relat_1(X1) | ~r1_tarski(X0,k1_relat_1(X1)) | k1_relat_1(k7_relat_1(X1,X0)) = X0) )),
% 1.46/0.54    inference(cnf_transformation,[],[f26])).
% 1.46/0.54  fof(f26,plain,(
% 1.46/0.54    ! [X0,X1] : (k1_relat_1(k7_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k1_relat_1(X1)) | ~v1_relat_1(X1))),
% 1.46/0.54    inference(flattening,[],[f25])).
% 1.46/0.54  fof(f25,plain,(
% 1.46/0.54    ! [X0,X1] : ((k1_relat_1(k7_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k1_relat_1(X1))) | ~v1_relat_1(X1))),
% 1.46/0.54    inference(ennf_transformation,[],[f10])).
% 1.46/0.54  fof(f10,axiom,(
% 1.46/0.54    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(X0,k1_relat_1(X1)) => k1_relat_1(k7_relat_1(X1,X0)) = X0))),
% 1.46/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_relat_1)).
% 1.46/0.54  fof(f112,plain,(
% 1.46/0.54    v1_relat_1(sK3)),
% 1.46/0.54    inference(resolution,[],[f46,f67])).
% 1.46/0.54  fof(f67,plain,(
% 1.46/0.54    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)) )),
% 1.46/0.54    inference(cnf_transformation,[],[f31])).
% 1.46/0.54  fof(f31,plain,(
% 1.46/0.54    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.46/0.54    inference(ennf_transformation,[],[f12])).
% 1.46/0.54  fof(f12,axiom,(
% 1.46/0.54    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 1.46/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).
% 1.46/0.54  fof(f1469,plain,(
% 1.46/0.54    ( ! [X11] : (r1_tarski(k7_relat_1(sK3,X11),k2_zfmisc_1(k1_relat_1(k7_relat_1(sK3,X11)),sK1))) )),
% 1.46/0.54    inference(resolution,[],[f647,f62])).
% 1.46/0.54  fof(f647,plain,(
% 1.46/0.54    ( ! [X1] : (m1_subset_1(k7_relat_1(sK3,X1),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k7_relat_1(sK3,X1)),sK1)))) )),
% 1.46/0.54    inference(global_subsumption,[],[f185,f619,f642])).
% 1.46/0.54  fof(f642,plain,(
% 1.46/0.54    ( ! [X1] : (~v1_relat_1(k7_relat_1(sK3,X1)) | ~v1_funct_1(k7_relat_1(sK3,X1)) | m1_subset_1(k7_relat_1(sK3,X1),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k7_relat_1(sK3,X1)),sK1)))) )),
% 1.46/0.54    inference(resolution,[],[f640,f57])).
% 1.46/0.54  fof(f57,plain,(
% 1.46/0.54    ( ! [X0,X1] : (~v1_relat_1(X1) | ~v1_funct_1(X1) | ~r1_tarski(k2_relat_1(X1),X0) | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))) )),
% 1.46/0.54    inference(cnf_transformation,[],[f29])).
% 1.46/0.54  fof(f29,plain,(
% 1.46/0.54    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) & v1_funct_2(X1,k1_relat_1(X1),X0) & v1_funct_1(X1)) | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 1.46/0.54    inference(flattening,[],[f28])).
% 1.46/0.54  fof(f28,plain,(
% 1.46/0.54    ! [X0,X1] : (((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) & v1_funct_2(X1,k1_relat_1(X1),X0) & v1_funct_1(X1)) | ~r1_tarski(k2_relat_1(X1),X0)) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 1.46/0.54    inference(ennf_transformation,[],[f18])).
% 1.46/0.54  fof(f18,axiom,(
% 1.46/0.54    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (r1_tarski(k2_relat_1(X1),X0) => (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) & v1_funct_2(X1,k1_relat_1(X1),X0) & v1_funct_1(X1))))),
% 1.46/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_funct_2)).
% 1.46/0.54  fof(f640,plain,(
% 1.46/0.54    ( ! [X0] : (r1_tarski(k2_relat_1(k7_relat_1(sK3,X0)),sK1)) )),
% 1.46/0.54    inference(global_subsumption,[],[f619,f639])).
% 1.46/0.54  fof(f639,plain,(
% 1.46/0.54    ( ! [X0] : (~v1_relat_1(k7_relat_1(sK3,X0)) | r1_tarski(k2_relat_1(k7_relat_1(sK3,X0)),sK1)) )),
% 1.46/0.54    inference(resolution,[],[f621,f55])).
% 1.46/0.54  fof(f621,plain,(
% 1.46/0.54    ( ! [X2] : (v5_relat_1(k7_relat_1(sK3,X2),sK1)) )),
% 1.46/0.54    inference(resolution,[],[f573,f70])).
% 1.46/0.54  fof(f573,plain,(
% 1.46/0.54    ( ! [X1] : (m1_subset_1(k7_relat_1(sK3,X1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))) )),
% 1.46/0.54    inference(global_subsumption,[],[f44,f46,f572])).
% 1.46/0.54  fof(f572,plain,(
% 1.46/0.54    ( ! [X1] : (m1_subset_1(k7_relat_1(sK3,X1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))) )),
% 1.46/0.54    inference(superposition,[],[f80,f123])).
% 1.46/0.54  fof(f619,plain,(
% 1.46/0.54    ( ! [X0] : (v1_relat_1(k7_relat_1(sK3,X0))) )),
% 1.46/0.54    inference(resolution,[],[f573,f67])).
% 1.46/0.54  fof(f185,plain,(
% 1.46/0.54    ( ! [X0] : (v1_funct_1(k7_relat_1(sK3,X0))) )),
% 1.46/0.54    inference(global_subsumption,[],[f44,f46,f183])).
% 1.46/0.54  fof(f183,plain,(
% 1.46/0.54    ( ! [X0] : (v1_funct_1(k7_relat_1(sK3,X0)) | ~v1_funct_1(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))) )),
% 1.46/0.54    inference(superposition,[],[f124,f78])).
% 1.46/0.54  fof(f124,plain,(
% 1.46/0.54    ( ! [X1] : (v1_funct_1(k2_partfun1(sK0,sK1,sK3,X1))) )),
% 1.46/0.54    inference(global_subsumption,[],[f44,f118])).
% 1.46/0.54  fof(f118,plain,(
% 1.46/0.54    ( ! [X1] : (~v1_funct_1(sK3) | v1_funct_1(k2_partfun1(sK0,sK1,sK3,X1))) )),
% 1.46/0.54    inference(resolution,[],[f46,f79])).
% 1.46/0.54  fof(f79,plain,(
% 1.46/0.54    ( ! [X2,X0,X3,X1] : (~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_funct_1(k2_partfun1(X0,X1,X2,X3))) )),
% 1.46/0.54    inference(cnf_transformation,[],[f41])).
% 1.46/0.54  fof(f47,plain,(
% 1.46/0.54    r1_tarski(sK2,sK0)),
% 1.46/0.54    inference(cnf_transformation,[],[f22])).
% 1.46/0.54  fof(f1484,plain,(
% 1.46/0.54    ~spl4_28 | spl4_40 | ~spl4_19),
% 1.46/0.54    inference(avatar_split_clause,[],[f1479,f704,f1481,f901])).
% 1.46/0.54  fof(f901,plain,(
% 1.46/0.54    spl4_28 <=> v1_relat_1(sK3)),
% 1.46/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_28])])).
% 1.46/0.54  fof(f1479,plain,(
% 1.46/0.54    m1_subset_1(k7_relat_1(sK3,k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) | ~v1_relat_1(sK3) | ~spl4_19),
% 1.46/0.54    inference(forward_demodulation,[],[f1473,f84])).
% 1.46/0.54  fof(f1473,plain,(
% 1.46/0.54    m1_subset_1(k7_relat_1(sK3,k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1))) | ~v1_relat_1(sK3) | ~spl4_19),
% 1.46/0.54    inference(superposition,[],[f647,f1203])).
% 1.46/0.54  fof(f1203,plain,(
% 1.46/0.54    ( ! [X3] : (k1_xboole_0 = k1_relat_1(k7_relat_1(X3,k1_xboole_0)) | ~v1_relat_1(X3)) ) | ~spl4_19),
% 1.46/0.54    inference(resolution,[],[f1184,f53])).
% 1.46/0.54  fof(f1297,plain,(
% 1.46/0.54    spl4_4 | ~spl4_13),
% 1.46/0.54    inference(avatar_contradiction_clause,[],[f1295])).
% 1.46/0.54  fof(f1295,plain,(
% 1.46/0.54    $false | (spl4_4 | ~spl4_13)),
% 1.46/0.54    inference(subsumption_resolution,[],[f47,f1291])).
% 1.46/0.54  fof(f1291,plain,(
% 1.46/0.54    ~r1_tarski(sK2,sK0) | (spl4_4 | ~spl4_13)),
% 1.46/0.54    inference(resolution,[],[f1029,f569])).
% 1.46/0.54  fof(f1029,plain,(
% 1.46/0.54    ( ! [X0] : (v1_funct_2(k7_relat_1(sK3,X0),X0,sK1) | ~r1_tarski(X0,sK0)) ) | ~spl4_13),
% 1.46/0.54    inference(superposition,[],[f646,f952])).
% 1.46/0.55  fof(f646,plain,(
% 1.46/0.55    ( ! [X0] : (v1_funct_2(k7_relat_1(sK3,X0),k1_relat_1(k7_relat_1(sK3,X0)),sK1)) )),
% 1.46/0.55    inference(global_subsumption,[],[f185,f619,f641])).
% 1.46/0.55  fof(f641,plain,(
% 1.46/0.55    ( ! [X0] : (~v1_relat_1(k7_relat_1(sK3,X0)) | ~v1_funct_1(k7_relat_1(sK3,X0)) | v1_funct_2(k7_relat_1(sK3,X0),k1_relat_1(k7_relat_1(sK3,X0)),sK1)) )),
% 1.46/0.55    inference(resolution,[],[f640,f56])).
% 1.46/0.55  fof(f56,plain,(
% 1.46/0.55    ( ! [X0,X1] : (~v1_relat_1(X1) | ~v1_funct_1(X1) | ~r1_tarski(k2_relat_1(X1),X0) | v1_funct_2(X1,k1_relat_1(X1),X0)) )),
% 1.46/0.55    inference(cnf_transformation,[],[f29])).
% 1.46/0.55  fof(f961,plain,(
% 1.46/0.55    spl4_29 | ~spl4_30),
% 1.46/0.55    inference(avatar_split_clause,[],[f144,f958,f954])).
% 1.46/0.55  fof(f144,plain,(
% 1.46/0.55    ~r1_tarski(k2_zfmisc_1(sK0,sK1),sK3) | sK3 = k2_zfmisc_1(sK0,sK1)),
% 1.46/0.55    inference(resolution,[],[f120,f60])).
% 1.46/0.55  fof(f120,plain,(
% 1.46/0.55    r1_tarski(sK3,k2_zfmisc_1(sK0,sK1))),
% 1.46/0.55    inference(resolution,[],[f46,f62])).
% 1.46/0.55  fof(f927,plain,(
% 1.46/0.55    spl4_28),
% 1.46/0.55    inference(avatar_split_clause,[],[f112,f901])).
% 1.46/0.55  fof(f864,plain,(
% 1.46/0.55    ~spl4_19 | spl4_25),
% 1.46/0.55    inference(avatar_split_clause,[],[f226,f862,f704])).
% 1.46/0.55  fof(f226,plain,(
% 1.46/0.55    ( ! [X9] : (v1_funct_2(k1_xboole_0,k1_xboole_0,X9) | ~r1_tarski(k1_xboole_0,X9) | ~v1_relat_1(k1_xboole_0)) )),
% 1.46/0.55    inference(forward_demodulation,[],[f225,f49])).
% 1.46/0.55  fof(f49,plain,(
% 1.46/0.55    k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 1.46/0.55    inference(cnf_transformation,[],[f9])).
% 1.46/0.55  fof(f225,plain,(
% 1.46/0.55    ( ! [X9] : (~r1_tarski(k1_xboole_0,X9) | ~v1_relat_1(k1_xboole_0) | v1_funct_2(k1_xboole_0,k1_relat_1(k1_xboole_0),X9)) )),
% 1.46/0.55    inference(forward_demodulation,[],[f215,f50])).
% 1.46/0.55  fof(f215,plain,(
% 1.46/0.55    ( ! [X9] : (~v1_relat_1(k1_xboole_0) | ~r1_tarski(k2_relat_1(k1_xboole_0),X9) | v1_funct_2(k1_xboole_0,k1_relat_1(k1_xboole_0),X9)) )),
% 1.46/0.55    inference(resolution,[],[f211,f56])).
% 1.46/0.55  fof(f211,plain,(
% 1.46/0.55    v1_funct_1(k1_xboole_0)),
% 1.46/0.55    inference(resolution,[],[f133,f51])).
% 1.46/0.55  fof(f133,plain,(
% 1.46/0.55    ( ! [X4] : (~m1_subset_1(X4,k1_zfmisc_1(sK3)) | v1_funct_1(X4)) )),
% 1.46/0.55    inference(global_subsumption,[],[f95,f112])).
% 1.46/0.55  fof(f95,plain,(
% 1.46/0.55    ( ! [X11] : (~v1_relat_1(sK3) | ~m1_subset_1(X11,k1_zfmisc_1(sK3)) | v1_funct_1(X11)) )),
% 1.46/0.55    inference(resolution,[],[f44,f52])).
% 1.46/0.55  fof(f52,plain,(
% 1.46/0.55    ( ! [X0,X1] : (~v1_relat_1(X0) | ~v1_funct_1(X0) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | v1_funct_1(X1)) )),
% 1.46/0.55    inference(cnf_transformation,[],[f24])).
% 1.46/0.55  fof(f24,plain,(
% 1.46/0.55    ! [X0] : (! [X1] : (v1_funct_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.46/0.55    inference(flattening,[],[f23])).
% 1.46/0.55  fof(f23,plain,(
% 1.46/0.55    ! [X0] : (! [X1] : (v1_funct_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 1.46/0.55    inference(ennf_transformation,[],[f11])).
% 1.46/0.55  fof(f11,axiom,(
% 1.46/0.55    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_funct_1(X1)))),
% 1.46/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc3_funct_1)).
% 1.46/0.55  fof(f731,plain,(
% 1.46/0.55    spl4_19),
% 1.46/0.55    inference(avatar_contradiction_clause,[],[f719])).
% 1.46/0.55  fof(f719,plain,(
% 1.46/0.55    $false | spl4_19),
% 1.46/0.55    inference(resolution,[],[f708,f51])).
% 1.46/0.55  fof(f708,plain,(
% 1.46/0.55    ( ! [X0,X1] : (~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) ) | spl4_19),
% 1.46/0.55    inference(resolution,[],[f706,f67])).
% 1.46/0.55  fof(f706,plain,(
% 1.46/0.55    ~v1_relat_1(k1_xboole_0) | spl4_19),
% 1.46/0.55    inference(avatar_component_clause,[],[f704])).
% 1.46/0.55  fof(f442,plain,(
% 1.46/0.55    ~spl4_1 | spl4_7),
% 1.46/0.55    inference(avatar_contradiction_clause,[],[f433])).
% 1.46/0.55  fof(f433,plain,(
% 1.46/0.55    $false | (~spl4_1 | spl4_7)),
% 1.46/0.55    inference(resolution,[],[f277,f51])).
% 1.46/0.55  fof(f277,plain,(
% 1.46/0.55    ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK2)) | (~spl4_1 | spl4_7)),
% 1.46/0.55    inference(backward_demodulation,[],[f171,f106])).
% 1.46/0.55  fof(f171,plain,(
% 1.46/0.55    ~m1_subset_1(sK0,k1_zfmisc_1(sK2)) | spl4_7),
% 1.46/0.55    inference(resolution,[],[f169,f62])).
% 1.46/0.55  fof(f169,plain,(
% 1.46/0.55    ~r1_tarski(sK0,sK2) | spl4_7),
% 1.46/0.55    inference(avatar_component_clause,[],[f167])).
% 1.46/0.55  fof(f167,plain,(
% 1.46/0.55    spl4_7 <=> r1_tarski(sK0,sK2)),
% 1.46/0.55    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).
% 1.46/0.55  fof(f265,plain,(
% 1.46/0.55    spl4_2 | spl4_13),
% 1.46/0.55    inference(avatar_split_clause,[],[f239,f262,f108])).
% 1.46/0.55  fof(f239,plain,(
% 1.46/0.55    sK0 = k1_relat_1(sK3) | k1_xboole_0 = sK1),
% 1.46/0.55    inference(global_subsumption,[],[f45,f46,f236])).
% 1.46/0.55  fof(f236,plain,(
% 1.46/0.55    sK0 = k1_relat_1(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | k1_xboole_0 = sK1 | ~v1_funct_2(sK3,sK0,sK1)),
% 1.46/0.55    inference(superposition,[],[f113,f76])).
% 1.46/0.55  fof(f76,plain,(
% 1.46/0.55    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_xboole_0 = X1 | k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1)) )),
% 1.46/0.55    inference(cnf_transformation,[],[f35])).
% 1.46/0.55  fof(f35,plain,(
% 1.46/0.55    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.46/0.55    inference(flattening,[],[f34])).
% 1.46/0.55  fof(f34,plain,(
% 1.46/0.55    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.46/0.55    inference(ennf_transformation,[],[f15])).
% 1.46/0.55  fof(f15,axiom,(
% 1.46/0.55    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 1.46/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_funct_2)).
% 1.46/0.55  fof(f113,plain,(
% 1.46/0.55    k1_relat_1(sK3) = k1_relset_1(sK0,sK1,sK3)),
% 1.46/0.55    inference(resolution,[],[f46,f68])).
% 1.46/0.55  fof(f68,plain,(
% 1.46/0.55    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_relset_1(X0,X1,X2) = k1_relat_1(X2)) )),
% 1.46/0.55    inference(cnf_transformation,[],[f32])).
% 1.46/0.55  fof(f32,plain,(
% 1.46/0.55    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.46/0.55    inference(ennf_transformation,[],[f14])).
% 1.46/0.55  fof(f14,axiom,(
% 1.46/0.55    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 1.46/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 1.46/0.55  fof(f45,plain,(
% 1.46/0.55    v1_funct_2(sK3,sK0,sK1)),
% 1.46/0.55    inference(cnf_transformation,[],[f22])).
% 1.46/0.55  fof(f184,plain,(
% 1.46/0.55    spl4_5),
% 1.46/0.55    inference(avatar_contradiction_clause,[],[f176])).
% 1.46/0.55  fof(f176,plain,(
% 1.46/0.55    $false | spl4_5),
% 1.46/0.55    inference(subsumption_resolution,[],[f159,f124])).
% 1.46/0.55  fof(f159,plain,(
% 1.46/0.55    ~v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) | spl4_5),
% 1.46/0.55    inference(avatar_component_clause,[],[f157])).
% 1.46/0.55  fof(f157,plain,(
% 1.46/0.55    spl4_5 <=> v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))),
% 1.46/0.55    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).
% 1.46/0.55  fof(f170,plain,(
% 1.46/0.55    spl4_6 | ~spl4_7),
% 1.46/0.55    inference(avatar_split_clause,[],[f97,f167,f163])).
% 1.46/0.55  fof(f97,plain,(
% 1.46/0.55    ~r1_tarski(sK0,sK2) | sK0 = sK2),
% 1.46/0.55    inference(resolution,[],[f47,f60])).
% 1.46/0.55  fof(f160,plain,(
% 1.46/0.55    ~spl4_3 | ~spl4_4 | ~spl4_5),
% 1.46/0.55    inference(avatar_split_clause,[],[f42,f157,f153,f149])).
% 1.46/0.55  fof(f42,plain,(
% 1.46/0.55    ~v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) | ~v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1) | ~m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))),
% 1.46/0.55    inference(cnf_transformation,[],[f22])).
% 1.46/0.55  fof(f111,plain,(
% 1.46/0.55    spl4_1 | ~spl4_2),
% 1.46/0.55    inference(avatar_split_clause,[],[f43,f108,f104])).
% 1.46/0.55  fof(f43,plain,(
% 1.46/0.55    k1_xboole_0 != sK1 | k1_xboole_0 = sK0),
% 1.46/0.55    inference(cnf_transformation,[],[f22])).
% 1.46/0.55  % SZS output end Proof for theBenchmark
% 1.46/0.55  % (24881)------------------------------
% 1.46/0.55  % (24881)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.46/0.55  % (24881)Termination reason: Refutation
% 1.46/0.55  
% 1.46/0.55  % (24881)Memory used [KB]: 11897
% 1.46/0.55  % (24881)Time elapsed: 0.129 s
% 1.46/0.55  % (24881)------------------------------
% 1.46/0.55  % (24881)------------------------------
% 1.46/0.55  % (24857)Success in time 0.187 s
%------------------------------------------------------------------------------
