%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:00:46 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  170 ( 751 expanded)
%              Number of leaves         :   26 ( 198 expanded)
%              Depth                    :   17
%              Number of atoms          :  514 (3753 expanded)
%              Number of equality atoms :  115 ( 866 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f447,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f75,f84,f86,f101,f129,f192,f210,f215,f225,f233,f251,f253,f265,f280,f429,f440,f446])).

fof(f446,plain,
    ( ~ spl4_4
    | ~ spl4_5
    | ~ spl4_9
    | spl4_10 ),
    inference(avatar_contradiction_clause,[],[f445])).

fof(f445,plain,
    ( $false
    | ~ spl4_4
    | ~ spl4_5
    | ~ spl4_9
    | spl4_10 ),
    inference(subsumption_resolution,[],[f444,f315])).

fof(f315,plain,
    ( v1_funct_2(sK3,k1_xboole_0,k1_xboole_0)
    | ~ spl4_4
    | ~ spl4_5 ),
    inference(forward_demodulation,[],[f308,f83])).

fof(f83,plain,
    ( k1_xboole_0 = sK0
    | ~ spl4_5 ),
    inference(avatar_component_clause,[],[f81])).

fof(f81,plain,
    ( spl4_5
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f308,plain,
    ( v1_funct_2(sK3,sK0,k1_xboole_0)
    | ~ spl4_4 ),
    inference(superposition,[],[f33,f78])).

fof(f78,plain,
    ( k1_xboole_0 = sK1
    | ~ spl4_4 ),
    inference(avatar_component_clause,[],[f77])).

fof(f77,plain,
    ( spl4_4
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f33,plain,(
    v1_funct_2(sK3,sK0,sK1) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,
    ( ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
      | ~ v1_funct_2(sK3,sK0,sK2)
      | ~ v1_funct_1(sK3) )
    & ( k1_xboole_0 = sK0
      | k1_xboole_0 != sK1 )
    & r1_tarski(sK1,sK2)
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    & v1_funct_2(sK3,sK0,sK1)
    & v1_funct_1(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f15,f26])).

fof(f26,plain,
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
   => ( ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
        | ~ v1_funct_2(sK3,sK0,sK2)
        | ~ v1_funct_1(sK3) )
      & ( k1_xboole_0 = sK0
        | k1_xboole_0 != sK1 )
      & r1_tarski(sK1,sK2)
      & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      & v1_funct_2(sK3,sK0,sK1)
      & v1_funct_1(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f15,plain,(
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
    inference(flattening,[],[f14])).

fof(f14,plain,(
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
    inference(ennf_transformation,[],[f12])).

fof(f12,negated_conjecture,(
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
    inference(negated_conjecture,[],[f11])).

fof(f11,conjecture,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t9_funct_2)).

fof(f444,plain,
    ( ~ v1_funct_2(sK3,k1_xboole_0,k1_xboole_0)
    | ~ spl4_4
    | ~ spl4_5
    | ~ spl4_9
    | spl4_10 ),
    inference(forward_demodulation,[],[f443,f83])).

fof(f443,plain,
    ( ~ v1_funct_2(sK3,sK0,k1_xboole_0)
    | ~ spl4_4
    | ~ spl4_9
    | spl4_10 ),
    inference(forward_demodulation,[],[f148,f286])).

fof(f286,plain,
    ( k1_xboole_0 = k2_relat_1(sK3)
    | ~ spl4_4
    | ~ spl4_9 ),
    inference(forward_demodulation,[],[f128,f78])).

fof(f128,plain,
    ( sK1 = k2_relat_1(sK3)
    | ~ spl4_9 ),
    inference(avatar_component_clause,[],[f126])).

fof(f126,plain,
    ( spl4_9
  <=> sK1 = k2_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).

fof(f148,plain,
    ( ~ v1_funct_2(sK3,sK0,k2_relat_1(sK3))
    | spl4_10 ),
    inference(avatar_component_clause,[],[f147])).

fof(f147,plain,
    ( spl4_10
  <=> v1_funct_2(sK3,sK0,k2_relat_1(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).

fof(f440,plain,
    ( ~ spl4_4
    | ~ spl4_5
    | ~ spl4_9
    | ~ spl4_10
    | spl4_12 ),
    inference(avatar_contradiction_clause,[],[f439])).

fof(f439,plain,
    ( $false
    | ~ spl4_4
    | ~ spl4_5
    | ~ spl4_9
    | ~ spl4_10
    | spl4_12 ),
    inference(global_subsumption,[],[f385,f438])).

fof(f438,plain,
    ( k1_xboole_0 != k1_relset_1(k1_xboole_0,k1_xboole_0,sK3)
    | ~ spl4_4
    | ~ spl4_5
    | ~ spl4_9
    | spl4_12 ),
    inference(forward_demodulation,[],[f437,f83])).

fof(f437,plain,
    ( sK0 != k1_relset_1(sK0,k1_xboole_0,sK3)
    | ~ spl4_4
    | ~ spl4_9
    | spl4_12 ),
    inference(forward_demodulation,[],[f157,f286])).

fof(f157,plain,
    ( sK0 != k1_relset_1(sK0,k2_relat_1(sK3),sK3)
    | spl4_12 ),
    inference(avatar_component_clause,[],[f155])).

fof(f155,plain,
    ( spl4_12
  <=> sK0 = k1_relset_1(sK0,k2_relat_1(sK3),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).

fof(f385,plain,
    ( k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,sK3)
    | ~ spl4_4
    | ~ spl4_5
    | ~ spl4_9
    | ~ spl4_10 ),
    inference(forward_demodulation,[],[f384,f286])).

fof(f384,plain,
    ( k1_xboole_0 = k1_relset_1(k1_xboole_0,k2_relat_1(sK3),sK3)
    | ~ spl4_5
    | ~ spl4_10 ),
    inference(subsumption_resolution,[],[f375,f274])).

fof(f274,plain,
    ( v1_funct_2(sK3,k1_xboole_0,k2_relat_1(sK3))
    | ~ spl4_5
    | ~ spl4_10 ),
    inference(superposition,[],[f149,f83])).

fof(f149,plain,
    ( v1_funct_2(sK3,sK0,k2_relat_1(sK3))
    | ~ spl4_10 ),
    inference(avatar_component_clause,[],[f147])).

fof(f375,plain,
    ( ~ v1_funct_2(sK3,k1_xboole_0,k2_relat_1(sK3))
    | k1_xboole_0 = k1_relset_1(k1_xboole_0,k2_relat_1(sK3),sK3)
    | ~ spl4_5 ),
    inference(resolution,[],[f273,f62])).

fof(f62,plain,(
    ! [X2,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
      | ~ v1_funct_2(X2,k1_xboole_0,X1)
      | k1_xboole_0 = k1_relset_1(k1_xboole_0,X1,X2) ) ),
    inference(equality_resolution,[],[f49])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 != X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
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
    inference(nnf_transformation,[],[f21])).

fof(f21,plain,(
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
    inference(flattening,[],[f20])).

fof(f20,plain,(
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
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).

fof(f273,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k2_relat_1(sK3))))
    | ~ spl4_5 ),
    inference(superposition,[],[f138,f83])).

fof(f138,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k2_relat_1(sK3)))) ),
    inference(resolution,[],[f107,f34])).

fof(f34,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f27])).

fof(f107,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k2_relat_1(X0)))) ) ),
    inference(resolution,[],[f55,f56])).

fof(f56,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f55,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r1_tarski(k2_relat_1(X3),X1)
      | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
      | ~ r1_tarski(k2_relat_1(X3),X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
      | ~ r1_tarski(k2_relat_1(X3),X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
     => ( r1_tarski(k2_relat_1(X3),X1)
       => m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t14_relset_1)).

fof(f429,plain,
    ( ~ spl4_5
    | spl4_16
    | ~ spl4_17 ),
    inference(avatar_contradiction_clause,[],[f428])).

fof(f428,plain,
    ( $false
    | ~ spl4_5
    | spl4_16
    | ~ spl4_17 ),
    inference(subsumption_resolution,[],[f427,f293])).

fof(f293,plain,
    ( k1_xboole_0 != k1_relset_1(k1_xboole_0,sK2,sK3)
    | ~ spl4_5
    | spl4_16 ),
    inference(forward_demodulation,[],[f209,f83])).

fof(f209,plain,
    ( sK0 != k1_relset_1(sK0,sK2,sK3)
    | spl4_16 ),
    inference(avatar_component_clause,[],[f207])).

fof(f207,plain,
    ( spl4_16
  <=> sK0 = k1_relset_1(sK0,sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_16])])).

fof(f427,plain,
    ( k1_xboole_0 = k1_relset_1(k1_xboole_0,sK2,sK3)
    | ~ spl4_5
    | ~ spl4_17 ),
    inference(forward_demodulation,[],[f420,f281])).

fof(f281,plain,
    ( k1_xboole_0 = k1_relat_1(sK3)
    | ~ spl4_5
    | ~ spl4_17 ),
    inference(forward_demodulation,[],[f272,f254])).

fof(f254,plain,
    ( k1_xboole_0 = k1_relset_1(k1_xboole_0,sK1,sK3)
    | ~ spl4_5
    | ~ spl4_17 ),
    inference(forward_demodulation,[],[f232,f83])).

fof(f232,plain,
    ( sK0 = k1_relset_1(sK0,sK1,sK3)
    | ~ spl4_17 ),
    inference(avatar_component_clause,[],[f230])).

fof(f230,plain,
    ( spl4_17
  <=> sK0 = k1_relset_1(sK0,sK1,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_17])])).

fof(f272,plain,
    ( k1_relat_1(sK3) = k1_relset_1(k1_xboole_0,sK1,sK3)
    | ~ spl4_5 ),
    inference(superposition,[],[f106,f83])).

fof(f106,plain,(
    k1_relset_1(sK0,sK1,sK3) = k1_relat_1(sK3) ),
    inference(resolution,[],[f46,f34])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f420,plain,
    ( k1_relat_1(sK3) = k1_relset_1(k1_xboole_0,sK2,sK3)
    | ~ spl4_5 ),
    inference(resolution,[],[f275,f46])).

fof(f275,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK2)))
    | ~ spl4_5 ),
    inference(superposition,[],[f188,f83])).

fof(f188,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) ),
    inference(resolution,[],[f166,f138])).

fof(f166,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,sK2))) ) ),
    inference(resolution,[],[f116,f55])).

fof(f116,plain,(
    r1_tarski(k2_relat_1(sK3),sK2) ),
    inference(resolution,[],[f113,f103])).

fof(f103,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,sK1)
      | r1_tarski(X0,sK2) ) ),
    inference(resolution,[],[f54,f35])).

fof(f35,plain,(
    r1_tarski(sK1,sK2) ),
    inference(cnf_transformation,[],[f27])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X1,X2)
      | r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).

fof(f113,plain,(
    r1_tarski(k2_relat_1(sK3),sK1) ),
    inference(subsumption_resolution,[],[f112,f88])).

fof(f88,plain,(
    v1_relat_1(sK3) ),
    inference(subsumption_resolution,[],[f87,f40])).

fof(f40,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f87,plain,
    ( v1_relat_1(sK3)
    | ~ v1_relat_1(k2_zfmisc_1(sK0,sK1)) ),
    inference(resolution,[],[f39,f34])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

fof(f112,plain,
    ( r1_tarski(k2_relat_1(sK3),sK1)
    | ~ v1_relat_1(sK3) ),
    inference(resolution,[],[f102,f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ~ v5_relat_1(X1,X0)
      | r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( ( v5_relat_1(X1,X0)
          | ~ r1_tarski(k2_relat_1(X1),X0) )
        & ( r1_tarski(k2_relat_1(X1),X0)
          | ~ v5_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).

fof(f102,plain,(
    v5_relat_1(sK3,sK1) ),
    inference(resolution,[],[f47,f34])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v5_relat_1(X2,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v5_relat_1(X2,X1) ) ),
    inference(pure_predicate_removal,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f280,plain,
    ( spl4_2
    | ~ spl4_5
    | ~ spl4_7
    | ~ spl4_15 ),
    inference(avatar_contradiction_clause,[],[f279])).

fof(f279,plain,
    ( $false
    | spl4_2
    | ~ spl4_5
    | ~ spl4_7
    | ~ spl4_15 ),
    inference(subsumption_resolution,[],[f278,f276])).

fof(f276,plain,
    ( v1_funct_2(sK3,k1_xboole_0,k1_xboole_0)
    | ~ spl4_5
    | ~ spl4_7
    | ~ spl4_15 ),
    inference(forward_demodulation,[],[f269,f260])).

fof(f260,plain,
    ( k1_xboole_0 = sK1
    | ~ spl4_7
    | ~ spl4_15 ),
    inference(forward_demodulation,[],[f100,f205])).

fof(f205,plain,
    ( k1_xboole_0 = sK2
    | ~ spl4_15 ),
    inference(avatar_component_clause,[],[f203])).

fof(f203,plain,
    ( spl4_15
  <=> k1_xboole_0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_15])])).

fof(f100,plain,
    ( sK1 = sK2
    | ~ spl4_7 ),
    inference(avatar_component_clause,[],[f98])).

fof(f98,plain,
    ( spl4_7
  <=> sK1 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).

fof(f269,plain,
    ( v1_funct_2(sK3,k1_xboole_0,sK1)
    | ~ spl4_5 ),
    inference(superposition,[],[f33,f83])).

fof(f278,plain,
    ( ~ v1_funct_2(sK3,k1_xboole_0,k1_xboole_0)
    | spl4_2
    | ~ spl4_5
    | ~ spl4_15 ),
    inference(forward_demodulation,[],[f271,f205])).

fof(f271,plain,
    ( ~ v1_funct_2(sK3,k1_xboole_0,sK2)
    | spl4_2
    | ~ spl4_5 ),
    inference(superposition,[],[f70,f83])).

fof(f70,plain,
    ( ~ v1_funct_2(sK3,sK0,sK2)
    | spl4_2 ),
    inference(avatar_component_clause,[],[f68])).

fof(f68,plain,
    ( spl4_2
  <=> v1_funct_2(sK3,sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f265,plain,
    ( spl4_4
    | ~ spl4_7
    | ~ spl4_15 ),
    inference(avatar_contradiction_clause,[],[f264])).

fof(f264,plain,
    ( $false
    | spl4_4
    | ~ spl4_7
    | ~ spl4_15 ),
    inference(global_subsumption,[],[f260,f79])).

fof(f79,plain,
    ( k1_xboole_0 != sK1
    | spl4_4 ),
    inference(avatar_component_clause,[],[f77])).

fof(f253,plain,
    ( ~ spl4_4
    | spl4_8 ),
    inference(avatar_contradiction_clause,[],[f252])).

fof(f252,plain,
    ( $false
    | ~ spl4_4
    | spl4_8 ),
    inference(subsumption_resolution,[],[f244,f38])).

fof(f38,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f244,plain,
    ( ~ r1_tarski(k1_xboole_0,k2_relat_1(sK3))
    | ~ spl4_4
    | spl4_8 ),
    inference(superposition,[],[f124,f78])).

fof(f124,plain,
    ( ~ r1_tarski(sK1,k2_relat_1(sK3))
    | spl4_8 ),
    inference(avatar_component_clause,[],[f122])).

fof(f122,plain,
    ( spl4_8
  <=> r1_tarski(sK1,k2_relat_1(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).

fof(f251,plain,
    ( ~ spl4_4
    | ~ spl4_5
    | ~ spl4_12
    | spl4_17 ),
    inference(avatar_contradiction_clause,[],[f250])).

fof(f250,plain,
    ( $false
    | ~ spl4_4
    | ~ spl4_5
    | ~ spl4_12
    | spl4_17 ),
    inference(subsumption_resolution,[],[f249,f235])).

fof(f235,plain,
    ( k1_xboole_0 != k1_relset_1(k1_xboole_0,k1_xboole_0,sK3)
    | ~ spl4_4
    | ~ spl4_5
    | spl4_17 ),
    inference(forward_demodulation,[],[f234,f83])).

fof(f234,plain,
    ( sK0 != k1_relset_1(sK0,k1_xboole_0,sK3)
    | ~ spl4_4
    | spl4_17 ),
    inference(forward_demodulation,[],[f231,f78])).

fof(f231,plain,
    ( sK0 != k1_relset_1(sK0,sK1,sK3)
    | spl4_17 ),
    inference(avatar_component_clause,[],[f230])).

fof(f249,plain,
    ( k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,sK3)
    | ~ spl4_4
    | ~ spl4_5
    | ~ spl4_12 ),
    inference(forward_demodulation,[],[f248,f83])).

fof(f248,plain,
    ( sK0 = k1_relset_1(k1_xboole_0,k1_xboole_0,sK3)
    | ~ spl4_4
    | ~ spl4_5
    | ~ spl4_12 ),
    inference(forward_demodulation,[],[f247,f228])).

fof(f228,plain,
    ( sK0 = k1_relat_1(sK3)
    | ~ spl4_12 ),
    inference(forward_demodulation,[],[f143,f156])).

fof(f156,plain,
    ( sK0 = k1_relset_1(sK0,k2_relat_1(sK3),sK3)
    | ~ spl4_12 ),
    inference(avatar_component_clause,[],[f155])).

fof(f143,plain,(
    k1_relat_1(sK3) = k1_relset_1(sK0,k2_relat_1(sK3),sK3) ),
    inference(resolution,[],[f138,f46])).

fof(f247,plain,
    ( k1_relat_1(sK3) = k1_relset_1(k1_xboole_0,k1_xboole_0,sK3)
    | ~ spl4_4
    | ~ spl4_5 ),
    inference(forward_demodulation,[],[f242,f83])).

fof(f242,plain,
    ( k1_relat_1(sK3) = k1_relset_1(sK0,k1_xboole_0,sK3)
    | ~ spl4_4 ),
    inference(superposition,[],[f106,f78])).

fof(f233,plain,
    ( spl4_17
    | spl4_4 ),
    inference(avatar_split_clause,[],[f109,f77,f230])).

fof(f109,plain,
    ( k1_xboole_0 = sK1
    | sK0 = k1_relset_1(sK0,sK1,sK3) ),
    inference(subsumption_resolution,[],[f108,f33])).

fof(f108,plain,
    ( ~ v1_funct_2(sK3,sK0,sK1)
    | k1_xboole_0 = sK1
    | sK0 = k1_relset_1(sK0,sK1,sK3) ),
    inference(resolution,[],[f48,f34])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | k1_relset_1(X0,X1,X2) = X0 ) ),
    inference(cnf_transformation,[],[f31])).

fof(f225,plain,
    ( spl4_6
    | ~ spl4_15 ),
    inference(avatar_contradiction_clause,[],[f224])).

fof(f224,plain,
    ( $false
    | spl4_6
    | ~ spl4_15 ),
    inference(subsumption_resolution,[],[f218,f38])).

fof(f218,plain,
    ( ~ r1_tarski(k1_xboole_0,sK1)
    | spl4_6
    | ~ spl4_15 ),
    inference(superposition,[],[f96,f205])).

fof(f96,plain,
    ( ~ r1_tarski(sK2,sK1)
    | spl4_6 ),
    inference(avatar_component_clause,[],[f94])).

fof(f94,plain,
    ( spl4_6
  <=> r1_tarski(sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).

fof(f215,plain,
    ( spl4_2
    | spl4_4
    | spl4_15 ),
    inference(avatar_contradiction_clause,[],[f214])).

fof(f214,plain,
    ( $false
    | spl4_2
    | spl4_4
    | spl4_15 ),
    inference(global_subsumption,[],[f201,f211,f204])).

fof(f204,plain,
    ( k1_xboole_0 != sK2
    | spl4_15 ),
    inference(avatar_component_clause,[],[f203])).

fof(f211,plain,
    ( sK0 = k1_relset_1(sK0,sK2,sK3)
    | spl4_4 ),
    inference(forward_demodulation,[],[f198,f130])).

fof(f130,plain,
    ( sK0 = k1_relat_1(sK3)
    | spl4_4 ),
    inference(superposition,[],[f106,f110])).

fof(f110,plain,
    ( sK0 = k1_relset_1(sK0,sK1,sK3)
    | spl4_4 ),
    inference(subsumption_resolution,[],[f109,f79])).

fof(f198,plain,(
    k1_relat_1(sK3) = k1_relset_1(sK0,sK2,sK3) ),
    inference(resolution,[],[f188,f46])).

fof(f201,plain,
    ( sK0 != k1_relset_1(sK0,sK2,sK3)
    | k1_xboole_0 = sK2
    | spl4_2 ),
    inference(subsumption_resolution,[],[f196,f70])).

fof(f196,plain,
    ( sK0 != k1_relset_1(sK0,sK2,sK3)
    | k1_xboole_0 = sK2
    | v1_funct_2(sK3,sK0,sK2) ),
    inference(resolution,[],[f188,f50])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_relset_1(X0,X1,X2) != X0
      | k1_xboole_0 = X1
      | v1_funct_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f210,plain,
    ( spl4_15
    | ~ spl4_16
    | spl4_2 ),
    inference(avatar_split_clause,[],[f201,f68,f207,f203])).

fof(f192,plain,(
    spl4_3 ),
    inference(avatar_contradiction_clause,[],[f191])).

fof(f191,plain,
    ( $false
    | spl4_3 ),
    inference(subsumption_resolution,[],[f188,f74])).

fof(f74,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
    | spl4_3 ),
    inference(avatar_component_clause,[],[f72])).

fof(f72,plain,
    ( spl4_3
  <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f129,plain,
    ( ~ spl4_8
    | spl4_9 ),
    inference(avatar_split_clause,[],[f120,f126,f122])).

fof(f120,plain,
    ( sK1 = k2_relat_1(sK3)
    | ~ r1_tarski(sK1,k2_relat_1(sK3)) ),
    inference(resolution,[],[f113,f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f101,plain,
    ( ~ spl4_6
    | spl4_7 ),
    inference(avatar_split_clause,[],[f90,f98,f94])).

fof(f90,plain,
    ( sK1 = sK2
    | ~ r1_tarski(sK2,sK1) ),
    inference(resolution,[],[f45,f35])).

fof(f86,plain,(
    spl4_1 ),
    inference(avatar_contradiction_clause,[],[f85])).

fof(f85,plain,
    ( $false
    | spl4_1 ),
    inference(subsumption_resolution,[],[f66,f32])).

fof(f32,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f27])).

fof(f66,plain,
    ( ~ v1_funct_1(sK3)
    | spl4_1 ),
    inference(avatar_component_clause,[],[f64])).

fof(f64,plain,
    ( spl4_1
  <=> v1_funct_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f84,plain,
    ( ~ spl4_4
    | spl4_5 ),
    inference(avatar_split_clause,[],[f36,f81,f77])).

fof(f36,plain,
    ( k1_xboole_0 = sK0
    | k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f27])).

fof(f75,plain,
    ( ~ spl4_1
    | ~ spl4_2
    | ~ spl4_3 ),
    inference(avatar_split_clause,[],[f37,f72,f68,f64])).

fof(f37,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
    | ~ v1_funct_2(sK3,sK0,sK2)
    | ~ v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f27])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n023.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 20:32:50 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.46  % (31888)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 0.22/0.46  % (31880)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 0.22/0.48  % (31880)Refutation found. Thanks to Tanya!
% 0.22/0.48  % SZS status Theorem for theBenchmark
% 0.22/0.48  % SZS output start Proof for theBenchmark
% 0.22/0.48  fof(f447,plain,(
% 0.22/0.48    $false),
% 0.22/0.48    inference(avatar_sat_refutation,[],[f75,f84,f86,f101,f129,f192,f210,f215,f225,f233,f251,f253,f265,f280,f429,f440,f446])).
% 0.22/0.48  fof(f446,plain,(
% 0.22/0.48    ~spl4_4 | ~spl4_5 | ~spl4_9 | spl4_10),
% 0.22/0.48    inference(avatar_contradiction_clause,[],[f445])).
% 0.22/0.48  fof(f445,plain,(
% 0.22/0.48    $false | (~spl4_4 | ~spl4_5 | ~spl4_9 | spl4_10)),
% 0.22/0.48    inference(subsumption_resolution,[],[f444,f315])).
% 0.22/0.48  fof(f315,plain,(
% 0.22/0.48    v1_funct_2(sK3,k1_xboole_0,k1_xboole_0) | (~spl4_4 | ~spl4_5)),
% 0.22/0.48    inference(forward_demodulation,[],[f308,f83])).
% 0.22/0.48  fof(f83,plain,(
% 0.22/0.48    k1_xboole_0 = sK0 | ~spl4_5),
% 0.22/0.48    inference(avatar_component_clause,[],[f81])).
% 0.22/0.48  fof(f81,plain,(
% 0.22/0.48    spl4_5 <=> k1_xboole_0 = sK0),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).
% 0.22/0.48  fof(f308,plain,(
% 0.22/0.48    v1_funct_2(sK3,sK0,k1_xboole_0) | ~spl4_4),
% 0.22/0.48    inference(superposition,[],[f33,f78])).
% 0.22/0.48  fof(f78,plain,(
% 0.22/0.48    k1_xboole_0 = sK1 | ~spl4_4),
% 0.22/0.48    inference(avatar_component_clause,[],[f77])).
% 0.22/0.48  fof(f77,plain,(
% 0.22/0.48    spl4_4 <=> k1_xboole_0 = sK1),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 0.22/0.48  fof(f33,plain,(
% 0.22/0.48    v1_funct_2(sK3,sK0,sK1)),
% 0.22/0.48    inference(cnf_transformation,[],[f27])).
% 0.22/0.48  fof(f27,plain,(
% 0.22/0.48    (~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) | ~v1_funct_2(sK3,sK0,sK2) | ~v1_funct_1(sK3)) & (k1_xboole_0 = sK0 | k1_xboole_0 != sK1) & r1_tarski(sK1,sK2) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK3,sK0,sK1) & v1_funct_1(sK3)),
% 0.22/0.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f15,f26])).
% 0.22/0.48  fof(f26,plain,(
% 0.22/0.48    ? [X0,X1,X2,X3] : ((~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) | ~v1_funct_2(X3,X0,X2) | ~v1_funct_1(X3)) & (k1_xboole_0 = X0 | k1_xboole_0 != X1) & r1_tarski(X1,X2) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ((~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) | ~v1_funct_2(sK3,sK0,sK2) | ~v1_funct_1(sK3)) & (k1_xboole_0 = sK0 | k1_xboole_0 != sK1) & r1_tarski(sK1,sK2) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK3,sK0,sK1) & v1_funct_1(sK3))),
% 0.22/0.48    introduced(choice_axiom,[])).
% 0.22/0.48  fof(f15,plain,(
% 0.22/0.48    ? [X0,X1,X2,X3] : ((~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) | ~v1_funct_2(X3,X0,X2) | ~v1_funct_1(X3)) & (k1_xboole_0 = X0 | k1_xboole_0 != X1) & r1_tarski(X1,X2) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3))),
% 0.22/0.48    inference(flattening,[],[f14])).
% 0.22/0.48  fof(f14,plain,(
% 0.22/0.48    ? [X0,X1,X2,X3] : ((((~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) | ~v1_funct_2(X3,X0,X2) | ~v1_funct_1(X3)) & (k1_xboole_0 = X0 | k1_xboole_0 != X1)) & r1_tarski(X1,X2)) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)))),
% 0.22/0.48    inference(ennf_transformation,[],[f12])).
% 0.22/0.48  fof(f12,negated_conjecture,(
% 0.22/0.48    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r1_tarski(X1,X2) => ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) & v1_funct_2(X3,X0,X2) & v1_funct_1(X3)) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))))),
% 0.22/0.48    inference(negated_conjecture,[],[f11])).
% 0.22/0.48  fof(f11,conjecture,(
% 0.22/0.48    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r1_tarski(X1,X2) => ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) & v1_funct_2(X3,X0,X2) & v1_funct_1(X3)) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))))),
% 0.22/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t9_funct_2)).
% 0.22/0.48  fof(f444,plain,(
% 0.22/0.48    ~v1_funct_2(sK3,k1_xboole_0,k1_xboole_0) | (~spl4_4 | ~spl4_5 | ~spl4_9 | spl4_10)),
% 0.22/0.48    inference(forward_demodulation,[],[f443,f83])).
% 0.22/0.48  fof(f443,plain,(
% 0.22/0.48    ~v1_funct_2(sK3,sK0,k1_xboole_0) | (~spl4_4 | ~spl4_9 | spl4_10)),
% 0.22/0.48    inference(forward_demodulation,[],[f148,f286])).
% 0.22/0.48  fof(f286,plain,(
% 0.22/0.48    k1_xboole_0 = k2_relat_1(sK3) | (~spl4_4 | ~spl4_9)),
% 0.22/0.48    inference(forward_demodulation,[],[f128,f78])).
% 0.22/0.48  fof(f128,plain,(
% 0.22/0.48    sK1 = k2_relat_1(sK3) | ~spl4_9),
% 0.22/0.48    inference(avatar_component_clause,[],[f126])).
% 0.22/0.48  fof(f126,plain,(
% 0.22/0.48    spl4_9 <=> sK1 = k2_relat_1(sK3)),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).
% 0.22/0.49  fof(f148,plain,(
% 0.22/0.49    ~v1_funct_2(sK3,sK0,k2_relat_1(sK3)) | spl4_10),
% 0.22/0.49    inference(avatar_component_clause,[],[f147])).
% 0.22/0.49  fof(f147,plain,(
% 0.22/0.49    spl4_10 <=> v1_funct_2(sK3,sK0,k2_relat_1(sK3))),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).
% 0.22/0.49  fof(f440,plain,(
% 0.22/0.49    ~spl4_4 | ~spl4_5 | ~spl4_9 | ~spl4_10 | spl4_12),
% 0.22/0.49    inference(avatar_contradiction_clause,[],[f439])).
% 0.22/0.49  fof(f439,plain,(
% 0.22/0.49    $false | (~spl4_4 | ~spl4_5 | ~spl4_9 | ~spl4_10 | spl4_12)),
% 0.22/0.49    inference(global_subsumption,[],[f385,f438])).
% 0.22/0.49  fof(f438,plain,(
% 0.22/0.49    k1_xboole_0 != k1_relset_1(k1_xboole_0,k1_xboole_0,sK3) | (~spl4_4 | ~spl4_5 | ~spl4_9 | spl4_12)),
% 0.22/0.49    inference(forward_demodulation,[],[f437,f83])).
% 0.22/0.49  fof(f437,plain,(
% 0.22/0.49    sK0 != k1_relset_1(sK0,k1_xboole_0,sK3) | (~spl4_4 | ~spl4_9 | spl4_12)),
% 0.22/0.49    inference(forward_demodulation,[],[f157,f286])).
% 0.22/0.49  fof(f157,plain,(
% 0.22/0.49    sK0 != k1_relset_1(sK0,k2_relat_1(sK3),sK3) | spl4_12),
% 0.22/0.49    inference(avatar_component_clause,[],[f155])).
% 0.22/0.49  fof(f155,plain,(
% 0.22/0.49    spl4_12 <=> sK0 = k1_relset_1(sK0,k2_relat_1(sK3),sK3)),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).
% 0.22/0.49  fof(f385,plain,(
% 0.22/0.49    k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,sK3) | (~spl4_4 | ~spl4_5 | ~spl4_9 | ~spl4_10)),
% 0.22/0.49    inference(forward_demodulation,[],[f384,f286])).
% 0.22/0.49  fof(f384,plain,(
% 0.22/0.49    k1_xboole_0 = k1_relset_1(k1_xboole_0,k2_relat_1(sK3),sK3) | (~spl4_5 | ~spl4_10)),
% 0.22/0.49    inference(subsumption_resolution,[],[f375,f274])).
% 0.22/0.49  fof(f274,plain,(
% 0.22/0.49    v1_funct_2(sK3,k1_xboole_0,k2_relat_1(sK3)) | (~spl4_5 | ~spl4_10)),
% 0.22/0.49    inference(superposition,[],[f149,f83])).
% 0.22/0.49  fof(f149,plain,(
% 0.22/0.49    v1_funct_2(sK3,sK0,k2_relat_1(sK3)) | ~spl4_10),
% 0.22/0.49    inference(avatar_component_clause,[],[f147])).
% 0.22/0.49  fof(f375,plain,(
% 0.22/0.49    ~v1_funct_2(sK3,k1_xboole_0,k2_relat_1(sK3)) | k1_xboole_0 = k1_relset_1(k1_xboole_0,k2_relat_1(sK3),sK3) | ~spl4_5),
% 0.22/0.49    inference(resolution,[],[f273,f62])).
% 0.22/0.49  fof(f62,plain,(
% 0.22/0.49    ( ! [X2,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) | ~v1_funct_2(X2,k1_xboole_0,X1) | k1_xboole_0 = k1_relset_1(k1_xboole_0,X1,X2)) )),
% 0.22/0.49    inference(equality_resolution,[],[f49])).
% 0.22/0.49  fof(f49,plain,(
% 0.22/0.49    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 != X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.22/0.49    inference(cnf_transformation,[],[f31])).
% 0.22/0.49  fof(f31,plain,(
% 0.22/0.49    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.49    inference(nnf_transformation,[],[f21])).
% 0.22/0.49  fof(f21,plain,(
% 0.22/0.49    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.49    inference(flattening,[],[f20])).
% 0.22/0.49  fof(f20,plain,(
% 0.22/0.49    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.49    inference(ennf_transformation,[],[f10])).
% 0.22/0.49  fof(f10,axiom,(
% 0.22/0.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 0.22/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).
% 0.22/0.49  fof(f273,plain,(
% 0.22/0.49    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k2_relat_1(sK3)))) | ~spl4_5),
% 0.22/0.49    inference(superposition,[],[f138,f83])).
% 0.22/0.49  fof(f138,plain,(
% 0.22/0.49    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k2_relat_1(sK3))))),
% 0.22/0.49    inference(resolution,[],[f107,f34])).
% 0.22/0.49  fof(f34,plain,(
% 0.22/0.49    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.22/0.49    inference(cnf_transformation,[],[f27])).
% 0.22/0.49  fof(f107,plain,(
% 0.22/0.49    ( ! [X2,X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k2_relat_1(X0))))) )),
% 0.22/0.49    inference(resolution,[],[f55,f56])).
% 0.22/0.49  fof(f56,plain,(
% 0.22/0.49    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 0.22/0.49    inference(equality_resolution,[],[f44])).
% 0.22/0.49  fof(f44,plain,(
% 0.22/0.49    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 0.22/0.49    inference(cnf_transformation,[],[f30])).
% 0.22/0.49  fof(f30,plain,(
% 0.22/0.49    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.22/0.49    inference(flattening,[],[f29])).
% 0.22/0.49  fof(f29,plain,(
% 0.22/0.49    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.22/0.49    inference(nnf_transformation,[],[f1])).
% 0.22/0.49  fof(f1,axiom,(
% 0.22/0.49    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.22/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.22/0.49  fof(f55,plain,(
% 0.22/0.49    ( ! [X2,X0,X3,X1] : (~r1_tarski(k2_relat_1(X3),X1) | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))) )),
% 0.22/0.49    inference(cnf_transformation,[],[f25])).
% 0.22/0.49  fof(f25,plain,(
% 0.22/0.49    ! [X0,X1,X2,X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~r1_tarski(k2_relat_1(X3),X1) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))))),
% 0.22/0.49    inference(flattening,[],[f24])).
% 0.22/0.49  fof(f24,plain,(
% 0.22/0.49    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~r1_tarski(k2_relat_1(X3),X1)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))))),
% 0.22/0.49    inference(ennf_transformation,[],[f9])).
% 0.22/0.49  fof(f9,axiom,(
% 0.22/0.49    ! [X0,X1,X2,X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) => (r1_tarski(k2_relat_1(X3),X1) => m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))))),
% 0.22/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t14_relset_1)).
% 0.22/0.49  fof(f429,plain,(
% 0.22/0.49    ~spl4_5 | spl4_16 | ~spl4_17),
% 0.22/0.49    inference(avatar_contradiction_clause,[],[f428])).
% 0.22/0.49  fof(f428,plain,(
% 0.22/0.49    $false | (~spl4_5 | spl4_16 | ~spl4_17)),
% 0.22/0.49    inference(subsumption_resolution,[],[f427,f293])).
% 0.22/0.49  fof(f293,plain,(
% 0.22/0.49    k1_xboole_0 != k1_relset_1(k1_xboole_0,sK2,sK3) | (~spl4_5 | spl4_16)),
% 0.22/0.49    inference(forward_demodulation,[],[f209,f83])).
% 0.22/0.49  fof(f209,plain,(
% 0.22/0.49    sK0 != k1_relset_1(sK0,sK2,sK3) | spl4_16),
% 0.22/0.49    inference(avatar_component_clause,[],[f207])).
% 0.22/0.49  fof(f207,plain,(
% 0.22/0.49    spl4_16 <=> sK0 = k1_relset_1(sK0,sK2,sK3)),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_16])])).
% 0.22/0.49  fof(f427,plain,(
% 0.22/0.49    k1_xboole_0 = k1_relset_1(k1_xboole_0,sK2,sK3) | (~spl4_5 | ~spl4_17)),
% 0.22/0.49    inference(forward_demodulation,[],[f420,f281])).
% 0.22/0.49  fof(f281,plain,(
% 0.22/0.49    k1_xboole_0 = k1_relat_1(sK3) | (~spl4_5 | ~spl4_17)),
% 0.22/0.49    inference(forward_demodulation,[],[f272,f254])).
% 0.22/0.49  fof(f254,plain,(
% 0.22/0.49    k1_xboole_0 = k1_relset_1(k1_xboole_0,sK1,sK3) | (~spl4_5 | ~spl4_17)),
% 0.22/0.49    inference(forward_demodulation,[],[f232,f83])).
% 0.22/0.49  fof(f232,plain,(
% 0.22/0.49    sK0 = k1_relset_1(sK0,sK1,sK3) | ~spl4_17),
% 0.22/0.49    inference(avatar_component_clause,[],[f230])).
% 0.22/0.49  fof(f230,plain,(
% 0.22/0.49    spl4_17 <=> sK0 = k1_relset_1(sK0,sK1,sK3)),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_17])])).
% 0.22/0.49  fof(f272,plain,(
% 0.22/0.49    k1_relat_1(sK3) = k1_relset_1(k1_xboole_0,sK1,sK3) | ~spl4_5),
% 0.22/0.49    inference(superposition,[],[f106,f83])).
% 0.22/0.49  fof(f106,plain,(
% 0.22/0.49    k1_relset_1(sK0,sK1,sK3) = k1_relat_1(sK3)),
% 0.22/0.49    inference(resolution,[],[f46,f34])).
% 0.22/0.49  fof(f46,plain,(
% 0.22/0.49    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_relset_1(X0,X1,X2) = k1_relat_1(X2)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f18])).
% 0.22/0.49  fof(f18,plain,(
% 0.22/0.49    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.49    inference(ennf_transformation,[],[f8])).
% 0.22/0.49  fof(f8,axiom,(
% 0.22/0.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 0.22/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 0.22/0.49  fof(f420,plain,(
% 0.22/0.49    k1_relat_1(sK3) = k1_relset_1(k1_xboole_0,sK2,sK3) | ~spl4_5),
% 0.22/0.49    inference(resolution,[],[f275,f46])).
% 0.22/0.49  fof(f275,plain,(
% 0.22/0.49    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK2))) | ~spl4_5),
% 0.22/0.49    inference(superposition,[],[f188,f83])).
% 0.22/0.49  fof(f188,plain,(
% 0.22/0.49    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))),
% 0.22/0.49    inference(resolution,[],[f166,f138])).
% 0.22/0.49  fof(f166,plain,(
% 0.22/0.49    ( ! [X0,X1] : (~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,sK2)))) )),
% 0.22/0.49    inference(resolution,[],[f116,f55])).
% 0.22/0.49  fof(f116,plain,(
% 0.22/0.49    r1_tarski(k2_relat_1(sK3),sK2)),
% 0.22/0.49    inference(resolution,[],[f113,f103])).
% 0.22/0.49  fof(f103,plain,(
% 0.22/0.49    ( ! [X0] : (~r1_tarski(X0,sK1) | r1_tarski(X0,sK2)) )),
% 0.22/0.49    inference(resolution,[],[f54,f35])).
% 0.22/0.49  fof(f35,plain,(
% 0.22/0.49    r1_tarski(sK1,sK2)),
% 0.22/0.49    inference(cnf_transformation,[],[f27])).
% 0.22/0.49  fof(f54,plain,(
% 0.22/0.49    ( ! [X2,X0,X1] : (~r1_tarski(X1,X2) | r1_tarski(X0,X2) | ~r1_tarski(X0,X1)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f23])).
% 0.22/0.49  fof(f23,plain,(
% 0.22/0.49    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1))),
% 0.22/0.49    inference(flattening,[],[f22])).
% 0.22/0.49  fof(f22,plain,(
% 0.22/0.49    ! [X0,X1,X2] : (r1_tarski(X0,X2) | (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)))),
% 0.22/0.49    inference(ennf_transformation,[],[f2])).
% 0.22/0.49  fof(f2,axiom,(
% 0.22/0.49    ! [X0,X1,X2] : ((r1_tarski(X1,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,X2))),
% 0.22/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).
% 0.22/0.49  fof(f113,plain,(
% 0.22/0.49    r1_tarski(k2_relat_1(sK3),sK1)),
% 0.22/0.49    inference(subsumption_resolution,[],[f112,f88])).
% 0.22/0.49  fof(f88,plain,(
% 0.22/0.49    v1_relat_1(sK3)),
% 0.22/0.49    inference(subsumption_resolution,[],[f87,f40])).
% 0.22/0.49  fof(f40,plain,(
% 0.22/0.49    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 0.22/0.49    inference(cnf_transformation,[],[f6])).
% 0.22/0.49  fof(f6,axiom,(
% 0.22/0.49    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 0.22/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).
% 0.22/0.49  fof(f87,plain,(
% 0.22/0.49    v1_relat_1(sK3) | ~v1_relat_1(k2_zfmisc_1(sK0,sK1))),
% 0.22/0.49    inference(resolution,[],[f39,f34])).
% 0.22/0.49  fof(f39,plain,(
% 0.22/0.49    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f16])).
% 0.22/0.49  fof(f16,plain,(
% 0.22/0.49    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 0.22/0.49    inference(ennf_transformation,[],[f4])).
% 0.22/0.49  fof(f4,axiom,(
% 0.22/0.49    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 0.22/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).
% 0.22/0.49  fof(f112,plain,(
% 0.22/0.49    r1_tarski(k2_relat_1(sK3),sK1) | ~v1_relat_1(sK3)),
% 0.22/0.49    inference(resolution,[],[f102,f41])).
% 0.22/0.49  fof(f41,plain,(
% 0.22/0.49    ( ! [X0,X1] : (~v5_relat_1(X1,X0) | r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f28])).
% 0.22/0.49  fof(f28,plain,(
% 0.22/0.49    ! [X0,X1] : (((v5_relat_1(X1,X0) | ~r1_tarski(k2_relat_1(X1),X0)) & (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 0.22/0.49    inference(nnf_transformation,[],[f17])).
% 0.22/0.49  fof(f17,plain,(
% 0.22/0.49    ! [X0,X1] : ((v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.22/0.49    inference(ennf_transformation,[],[f5])).
% 0.22/0.49  fof(f5,axiom,(
% 0.22/0.49    ! [X0,X1] : (v1_relat_1(X1) => (v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)))),
% 0.22/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).
% 0.22/0.49  fof(f102,plain,(
% 0.22/0.49    v5_relat_1(sK3,sK1)),
% 0.22/0.49    inference(resolution,[],[f47,f34])).
% 0.22/0.49  fof(f47,plain,(
% 0.22/0.49    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v5_relat_1(X2,X1)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f19])).
% 0.22/0.49  fof(f19,plain,(
% 0.22/0.49    ! [X0,X1,X2] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.49    inference(ennf_transformation,[],[f13])).
% 0.22/0.49  fof(f13,plain,(
% 0.22/0.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v5_relat_1(X2,X1))),
% 0.22/0.49    inference(pure_predicate_removal,[],[f7])).
% 0.22/0.49  fof(f7,axiom,(
% 0.22/0.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 0.22/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).
% 0.22/0.49  fof(f280,plain,(
% 0.22/0.49    spl4_2 | ~spl4_5 | ~spl4_7 | ~spl4_15),
% 0.22/0.49    inference(avatar_contradiction_clause,[],[f279])).
% 0.22/0.49  fof(f279,plain,(
% 0.22/0.49    $false | (spl4_2 | ~spl4_5 | ~spl4_7 | ~spl4_15)),
% 0.22/0.49    inference(subsumption_resolution,[],[f278,f276])).
% 0.22/0.49  fof(f276,plain,(
% 0.22/0.49    v1_funct_2(sK3,k1_xboole_0,k1_xboole_0) | (~spl4_5 | ~spl4_7 | ~spl4_15)),
% 0.22/0.49    inference(forward_demodulation,[],[f269,f260])).
% 0.22/0.49  fof(f260,plain,(
% 0.22/0.49    k1_xboole_0 = sK1 | (~spl4_7 | ~spl4_15)),
% 0.22/0.49    inference(forward_demodulation,[],[f100,f205])).
% 0.22/0.49  fof(f205,plain,(
% 0.22/0.49    k1_xboole_0 = sK2 | ~spl4_15),
% 0.22/0.49    inference(avatar_component_clause,[],[f203])).
% 0.22/0.49  fof(f203,plain,(
% 0.22/0.49    spl4_15 <=> k1_xboole_0 = sK2),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_15])])).
% 0.22/0.49  fof(f100,plain,(
% 0.22/0.49    sK1 = sK2 | ~spl4_7),
% 0.22/0.49    inference(avatar_component_clause,[],[f98])).
% 0.22/0.49  fof(f98,plain,(
% 0.22/0.49    spl4_7 <=> sK1 = sK2),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).
% 0.22/0.49  fof(f269,plain,(
% 0.22/0.49    v1_funct_2(sK3,k1_xboole_0,sK1) | ~spl4_5),
% 0.22/0.49    inference(superposition,[],[f33,f83])).
% 0.22/0.49  fof(f278,plain,(
% 0.22/0.49    ~v1_funct_2(sK3,k1_xboole_0,k1_xboole_0) | (spl4_2 | ~spl4_5 | ~spl4_15)),
% 0.22/0.49    inference(forward_demodulation,[],[f271,f205])).
% 0.22/0.49  fof(f271,plain,(
% 0.22/0.49    ~v1_funct_2(sK3,k1_xboole_0,sK2) | (spl4_2 | ~spl4_5)),
% 0.22/0.49    inference(superposition,[],[f70,f83])).
% 0.22/0.49  fof(f70,plain,(
% 0.22/0.49    ~v1_funct_2(sK3,sK0,sK2) | spl4_2),
% 0.22/0.49    inference(avatar_component_clause,[],[f68])).
% 0.22/0.49  fof(f68,plain,(
% 0.22/0.49    spl4_2 <=> v1_funct_2(sK3,sK0,sK2)),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 0.22/0.49  fof(f265,plain,(
% 0.22/0.49    spl4_4 | ~spl4_7 | ~spl4_15),
% 0.22/0.49    inference(avatar_contradiction_clause,[],[f264])).
% 0.22/0.49  fof(f264,plain,(
% 0.22/0.49    $false | (spl4_4 | ~spl4_7 | ~spl4_15)),
% 0.22/0.49    inference(global_subsumption,[],[f260,f79])).
% 0.22/0.49  fof(f79,plain,(
% 0.22/0.49    k1_xboole_0 != sK1 | spl4_4),
% 0.22/0.49    inference(avatar_component_clause,[],[f77])).
% 0.22/0.49  fof(f253,plain,(
% 0.22/0.49    ~spl4_4 | spl4_8),
% 0.22/0.49    inference(avatar_contradiction_clause,[],[f252])).
% 0.22/0.49  fof(f252,plain,(
% 0.22/0.49    $false | (~spl4_4 | spl4_8)),
% 0.22/0.49    inference(subsumption_resolution,[],[f244,f38])).
% 0.22/0.49  fof(f38,plain,(
% 0.22/0.49    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f3])).
% 0.22/0.49  fof(f3,axiom,(
% 0.22/0.49    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 0.22/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).
% 0.22/0.49  fof(f244,plain,(
% 0.22/0.49    ~r1_tarski(k1_xboole_0,k2_relat_1(sK3)) | (~spl4_4 | spl4_8)),
% 0.22/0.49    inference(superposition,[],[f124,f78])).
% 0.22/0.49  fof(f124,plain,(
% 0.22/0.49    ~r1_tarski(sK1,k2_relat_1(sK3)) | spl4_8),
% 0.22/0.49    inference(avatar_component_clause,[],[f122])).
% 0.22/0.49  fof(f122,plain,(
% 0.22/0.49    spl4_8 <=> r1_tarski(sK1,k2_relat_1(sK3))),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).
% 0.22/0.49  fof(f251,plain,(
% 0.22/0.49    ~spl4_4 | ~spl4_5 | ~spl4_12 | spl4_17),
% 0.22/0.49    inference(avatar_contradiction_clause,[],[f250])).
% 0.22/0.49  fof(f250,plain,(
% 0.22/0.49    $false | (~spl4_4 | ~spl4_5 | ~spl4_12 | spl4_17)),
% 0.22/0.49    inference(subsumption_resolution,[],[f249,f235])).
% 0.22/0.49  fof(f235,plain,(
% 0.22/0.49    k1_xboole_0 != k1_relset_1(k1_xboole_0,k1_xboole_0,sK3) | (~spl4_4 | ~spl4_5 | spl4_17)),
% 0.22/0.49    inference(forward_demodulation,[],[f234,f83])).
% 0.22/0.49  fof(f234,plain,(
% 0.22/0.49    sK0 != k1_relset_1(sK0,k1_xboole_0,sK3) | (~spl4_4 | spl4_17)),
% 0.22/0.49    inference(forward_demodulation,[],[f231,f78])).
% 0.22/0.49  fof(f231,plain,(
% 0.22/0.49    sK0 != k1_relset_1(sK0,sK1,sK3) | spl4_17),
% 0.22/0.49    inference(avatar_component_clause,[],[f230])).
% 0.22/0.49  fof(f249,plain,(
% 0.22/0.49    k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,sK3) | (~spl4_4 | ~spl4_5 | ~spl4_12)),
% 0.22/0.49    inference(forward_demodulation,[],[f248,f83])).
% 0.22/0.49  fof(f248,plain,(
% 0.22/0.49    sK0 = k1_relset_1(k1_xboole_0,k1_xboole_0,sK3) | (~spl4_4 | ~spl4_5 | ~spl4_12)),
% 0.22/0.49    inference(forward_demodulation,[],[f247,f228])).
% 0.22/0.49  fof(f228,plain,(
% 0.22/0.49    sK0 = k1_relat_1(sK3) | ~spl4_12),
% 0.22/0.49    inference(forward_demodulation,[],[f143,f156])).
% 0.22/0.49  fof(f156,plain,(
% 0.22/0.49    sK0 = k1_relset_1(sK0,k2_relat_1(sK3),sK3) | ~spl4_12),
% 0.22/0.49    inference(avatar_component_clause,[],[f155])).
% 0.22/0.49  fof(f143,plain,(
% 0.22/0.49    k1_relat_1(sK3) = k1_relset_1(sK0,k2_relat_1(sK3),sK3)),
% 0.22/0.49    inference(resolution,[],[f138,f46])).
% 0.22/0.49  fof(f247,plain,(
% 0.22/0.49    k1_relat_1(sK3) = k1_relset_1(k1_xboole_0,k1_xboole_0,sK3) | (~spl4_4 | ~spl4_5)),
% 0.22/0.49    inference(forward_demodulation,[],[f242,f83])).
% 0.22/0.49  fof(f242,plain,(
% 0.22/0.49    k1_relat_1(sK3) = k1_relset_1(sK0,k1_xboole_0,sK3) | ~spl4_4),
% 0.22/0.49    inference(superposition,[],[f106,f78])).
% 0.22/0.49  fof(f233,plain,(
% 0.22/0.49    spl4_17 | spl4_4),
% 0.22/0.49    inference(avatar_split_clause,[],[f109,f77,f230])).
% 0.22/0.49  fof(f109,plain,(
% 0.22/0.49    k1_xboole_0 = sK1 | sK0 = k1_relset_1(sK0,sK1,sK3)),
% 0.22/0.49    inference(subsumption_resolution,[],[f108,f33])).
% 0.22/0.49  fof(f108,plain,(
% 0.22/0.49    ~v1_funct_2(sK3,sK0,sK1) | k1_xboole_0 = sK1 | sK0 = k1_relset_1(sK0,sK1,sK3)),
% 0.22/0.49    inference(resolution,[],[f48,f34])).
% 0.22/0.49  fof(f48,plain,(
% 0.22/0.49    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | k1_relset_1(X0,X1,X2) = X0) )),
% 0.22/0.49    inference(cnf_transformation,[],[f31])).
% 0.22/0.49  fof(f225,plain,(
% 0.22/0.49    spl4_6 | ~spl4_15),
% 0.22/0.49    inference(avatar_contradiction_clause,[],[f224])).
% 0.22/0.49  fof(f224,plain,(
% 0.22/0.49    $false | (spl4_6 | ~spl4_15)),
% 0.22/0.49    inference(subsumption_resolution,[],[f218,f38])).
% 0.22/0.49  fof(f218,plain,(
% 0.22/0.49    ~r1_tarski(k1_xboole_0,sK1) | (spl4_6 | ~spl4_15)),
% 0.22/0.49    inference(superposition,[],[f96,f205])).
% 0.22/0.49  fof(f96,plain,(
% 0.22/0.49    ~r1_tarski(sK2,sK1) | spl4_6),
% 0.22/0.49    inference(avatar_component_clause,[],[f94])).
% 0.22/0.49  fof(f94,plain,(
% 0.22/0.49    spl4_6 <=> r1_tarski(sK2,sK1)),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).
% 0.22/0.49  fof(f215,plain,(
% 0.22/0.49    spl4_2 | spl4_4 | spl4_15),
% 0.22/0.49    inference(avatar_contradiction_clause,[],[f214])).
% 0.22/0.49  fof(f214,plain,(
% 0.22/0.49    $false | (spl4_2 | spl4_4 | spl4_15)),
% 0.22/0.49    inference(global_subsumption,[],[f201,f211,f204])).
% 0.22/0.49  fof(f204,plain,(
% 0.22/0.49    k1_xboole_0 != sK2 | spl4_15),
% 0.22/0.49    inference(avatar_component_clause,[],[f203])).
% 0.22/0.49  fof(f211,plain,(
% 0.22/0.49    sK0 = k1_relset_1(sK0,sK2,sK3) | spl4_4),
% 0.22/0.49    inference(forward_demodulation,[],[f198,f130])).
% 0.22/0.49  fof(f130,plain,(
% 0.22/0.49    sK0 = k1_relat_1(sK3) | spl4_4),
% 0.22/0.49    inference(superposition,[],[f106,f110])).
% 0.22/0.49  fof(f110,plain,(
% 0.22/0.49    sK0 = k1_relset_1(sK0,sK1,sK3) | spl4_4),
% 0.22/0.49    inference(subsumption_resolution,[],[f109,f79])).
% 0.22/0.49  fof(f198,plain,(
% 0.22/0.49    k1_relat_1(sK3) = k1_relset_1(sK0,sK2,sK3)),
% 0.22/0.49    inference(resolution,[],[f188,f46])).
% 0.22/0.49  fof(f201,plain,(
% 0.22/0.49    sK0 != k1_relset_1(sK0,sK2,sK3) | k1_xboole_0 = sK2 | spl4_2),
% 0.22/0.49    inference(subsumption_resolution,[],[f196,f70])).
% 0.22/0.49  fof(f196,plain,(
% 0.22/0.49    sK0 != k1_relset_1(sK0,sK2,sK3) | k1_xboole_0 = sK2 | v1_funct_2(sK3,sK0,sK2)),
% 0.22/0.49    inference(resolution,[],[f188,f50])).
% 0.22/0.49  fof(f50,plain,(
% 0.22/0.49    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_relset_1(X0,X1,X2) != X0 | k1_xboole_0 = X1 | v1_funct_2(X2,X0,X1)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f31])).
% 0.22/0.49  fof(f210,plain,(
% 0.22/0.49    spl4_15 | ~spl4_16 | spl4_2),
% 0.22/0.49    inference(avatar_split_clause,[],[f201,f68,f207,f203])).
% 0.22/0.49  fof(f192,plain,(
% 0.22/0.49    spl4_3),
% 0.22/0.49    inference(avatar_contradiction_clause,[],[f191])).
% 0.22/0.49  fof(f191,plain,(
% 0.22/0.49    $false | spl4_3),
% 0.22/0.49    inference(subsumption_resolution,[],[f188,f74])).
% 0.22/0.49  fof(f74,plain,(
% 0.22/0.49    ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) | spl4_3),
% 0.22/0.49    inference(avatar_component_clause,[],[f72])).
% 0.22/0.49  fof(f72,plain,(
% 0.22/0.49    spl4_3 <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 0.22/0.49  fof(f129,plain,(
% 0.22/0.49    ~spl4_8 | spl4_9),
% 0.22/0.49    inference(avatar_split_clause,[],[f120,f126,f122])).
% 0.22/0.49  fof(f120,plain,(
% 0.22/0.49    sK1 = k2_relat_1(sK3) | ~r1_tarski(sK1,k2_relat_1(sK3))),
% 0.22/0.49    inference(resolution,[],[f113,f45])).
% 0.22/0.49  fof(f45,plain,(
% 0.22/0.49    ( ! [X0,X1] : (~r1_tarski(X1,X0) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f30])).
% 0.22/0.49  fof(f101,plain,(
% 0.22/0.49    ~spl4_6 | spl4_7),
% 0.22/0.49    inference(avatar_split_clause,[],[f90,f98,f94])).
% 0.22/0.49  fof(f90,plain,(
% 0.22/0.49    sK1 = sK2 | ~r1_tarski(sK2,sK1)),
% 0.22/0.49    inference(resolution,[],[f45,f35])).
% 0.22/0.49  fof(f86,plain,(
% 0.22/0.49    spl4_1),
% 0.22/0.49    inference(avatar_contradiction_clause,[],[f85])).
% 0.22/0.49  fof(f85,plain,(
% 0.22/0.49    $false | spl4_1),
% 0.22/0.49    inference(subsumption_resolution,[],[f66,f32])).
% 0.22/0.49  fof(f32,plain,(
% 0.22/0.49    v1_funct_1(sK3)),
% 0.22/0.49    inference(cnf_transformation,[],[f27])).
% 0.22/0.49  fof(f66,plain,(
% 0.22/0.49    ~v1_funct_1(sK3) | spl4_1),
% 0.22/0.49    inference(avatar_component_clause,[],[f64])).
% 0.22/0.49  fof(f64,plain,(
% 0.22/0.49    spl4_1 <=> v1_funct_1(sK3)),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 0.22/0.49  fof(f84,plain,(
% 0.22/0.49    ~spl4_4 | spl4_5),
% 0.22/0.49    inference(avatar_split_clause,[],[f36,f81,f77])).
% 0.22/0.49  fof(f36,plain,(
% 0.22/0.49    k1_xboole_0 = sK0 | k1_xboole_0 != sK1),
% 0.22/0.49    inference(cnf_transformation,[],[f27])).
% 0.22/0.49  fof(f75,plain,(
% 0.22/0.49    ~spl4_1 | ~spl4_2 | ~spl4_3),
% 0.22/0.49    inference(avatar_split_clause,[],[f37,f72,f68,f64])).
% 0.22/0.49  fof(f37,plain,(
% 0.22/0.49    ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) | ~v1_funct_2(sK3,sK0,sK2) | ~v1_funct_1(sK3)),
% 0.22/0.49    inference(cnf_transformation,[],[f27])).
% 0.22/0.49  % SZS output end Proof for theBenchmark
% 0.22/0.49  % (31880)------------------------------
% 0.22/0.49  % (31880)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.49  % (31880)Termination reason: Refutation
% 0.22/0.49  
% 0.22/0.49  % (31880)Memory used [KB]: 10874
% 0.22/0.49  % (31880)Time elapsed: 0.076 s
% 0.22/0.49  % (31880)------------------------------
% 0.22/0.49  % (31880)------------------------------
% 0.22/0.49  % (31869)Success in time 0.128 s
%------------------------------------------------------------------------------
