%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:03:14 EST 2020

% Result     : Theorem 1.60s
% Output     : Refutation 1.60s
% Verified   : 
% Statistics : Number of formulae       :  149 ( 762 expanded)
%              Number of leaves         :   23 ( 192 expanded)
%              Depth                    :   19
%              Number of atoms          :  457 (4573 expanded)
%              Number of equality atoms :  109 (1020 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f828,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f99,f108,f136,f179,f594,f666,f744,f803,f827])).

fof(f827,plain,
    ( spl4_2
    | ~ spl4_4
    | ~ spl4_5
    | ~ spl4_9 ),
    inference(avatar_contradiction_clause,[],[f826])).

fof(f826,plain,
    ( $false
    | spl4_2
    | ~ spl4_4
    | ~ spl4_5
    | ~ spl4_9 ),
    inference(subsumption_resolution,[],[f825,f720])).

fof(f720,plain,
    ( v1_funct_2(sK3,k1_xboole_0,k1_xboole_0)
    | ~ spl4_4
    | ~ spl4_5 ),
    inference(forward_demodulation,[],[f698,f107])).

fof(f107,plain,
    ( k1_xboole_0 = sK0
    | ~ spl4_5 ),
    inference(avatar_component_clause,[],[f105])).

fof(f105,plain,
    ( spl4_5
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f698,plain,
    ( v1_funct_2(sK3,sK0,k1_xboole_0)
    | ~ spl4_4 ),
    inference(superposition,[],[f45,f102])).

fof(f102,plain,
    ( k1_xboole_0 = sK1
    | ~ spl4_4 ),
    inference(avatar_component_clause,[],[f101])).

fof(f101,plain,
    ( spl4_4
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f45,plain,(
    v1_funct_2(sK3,sK0,sK1) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,
    ( ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
      | ~ v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1)
      | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) )
    & ( k1_xboole_0 = sK0
      | k1_xboole_0 != sK1 )
    & r1_tarski(sK2,sK0)
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    & v1_funct_2(sK3,sK0,sK1)
    & v1_funct_1(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f18,f36])).

fof(f36,plain,
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

fof(f18,plain,(
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
    inference(flattening,[],[f17])).

fof(f17,plain,(
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
    inference(ennf_transformation,[],[f16])).

fof(f16,negated_conjecture,(
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
    inference(negated_conjecture,[],[f15])).

fof(f15,conjecture,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_funct_2)).

fof(f825,plain,
    ( ~ v1_funct_2(sK3,k1_xboole_0,k1_xboole_0)
    | spl4_2
    | ~ spl4_4
    | ~ spl4_5
    | ~ spl4_9 ),
    inference(forward_demodulation,[],[f823,f791])).

fof(f791,plain,
    ( sK3 = k7_relat_1(sK3,k1_xboole_0)
    | ~ spl4_5 ),
    inference(superposition,[],[f172,f107])).

fof(f172,plain,(
    sK3 = k7_relat_1(sK3,sK0) ),
    inference(subsumption_resolution,[],[f171,f121])).

fof(f121,plain,(
    v1_relat_1(sK3) ),
    inference(resolution,[],[f65,f46])).

fof(f46,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f37])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f171,plain,
    ( sK3 = k7_relat_1(sK3,sK0)
    | ~ v1_relat_1(sK3) ),
    inference(resolution,[],[f138,f58])).

fof(f58,plain,(
    ! [X0,X1] :
      ( ~ v4_relat_1(X1,X0)
      | k7_relat_1(X1,X0) = X1
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => k7_relat_1(X1,X0) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t209_relat_1)).

fof(f138,plain,(
    v4_relat_1(sK3,sK0) ),
    inference(resolution,[],[f67,f46])).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v4_relat_1(X2,X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f823,plain,
    ( ~ v1_funct_2(k7_relat_1(sK3,k1_xboole_0),k1_xboole_0,k1_xboole_0)
    | spl4_2
    | ~ spl4_4
    | ~ spl4_5
    | ~ spl4_9 ),
    inference(superposition,[],[f769,f814])).

fof(f814,plain,
    ( k1_xboole_0 = sK2
    | ~ spl4_5
    | ~ spl4_9 ),
    inference(forward_demodulation,[],[f135,f107])).

fof(f135,plain,
    ( sK0 = sK2
    | ~ spl4_9 ),
    inference(avatar_component_clause,[],[f133])).

fof(f133,plain,
    ( spl4_9
  <=> sK0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).

fof(f769,plain,
    ( ~ v1_funct_2(k7_relat_1(sK3,sK2),sK2,k1_xboole_0)
    | spl4_2
    | ~ spl4_4
    | ~ spl4_5 ),
    inference(forward_demodulation,[],[f768,f726])).

fof(f726,plain,
    ( ! [X0] : k7_relat_1(sK3,X0) = k2_partfun1(k1_xboole_0,k1_xboole_0,sK3,X0)
    | ~ spl4_4
    | ~ spl4_5 ),
    inference(forward_demodulation,[],[f704,f107])).

fof(f704,plain,
    ( ! [X0] : k7_relat_1(sK3,X0) = k2_partfun1(sK0,k1_xboole_0,sK3,X0)
    | ~ spl4_4 ),
    inference(superposition,[],[f160,f102])).

fof(f160,plain,(
    ! [X0] : k7_relat_1(sK3,X0) = k2_partfun1(sK0,sK1,sK3,X0) ),
    inference(subsumption_resolution,[],[f157,f44])).

fof(f44,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f37])).

fof(f157,plain,(
    ! [X0] :
      ( k7_relat_1(sK3,X0) = k2_partfun1(sK0,sK1,sK3,X0)
      | ~ v1_funct_1(sK3) ) ),
    inference(resolution,[],[f75,f46])).

fof(f75,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2,X3] :
      ( k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2,X3] :
      ( k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_partfun1)).

fof(f768,plain,
    ( ~ v1_funct_2(k2_partfun1(k1_xboole_0,k1_xboole_0,sK3,sK2),sK2,k1_xboole_0)
    | spl4_2
    | ~ spl4_4
    | ~ spl4_5 ),
    inference(forward_demodulation,[],[f767,f107])).

fof(f767,plain,
    ( ~ v1_funct_2(k2_partfun1(sK0,k1_xboole_0,sK3,sK2),sK2,k1_xboole_0)
    | spl4_2
    | ~ spl4_4 ),
    inference(forward_demodulation,[],[f94,f102])).

fof(f94,plain,
    ( ~ v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1)
    | spl4_2 ),
    inference(avatar_component_clause,[],[f92])).

fof(f92,plain,
    ( spl4_2
  <=> v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f803,plain,
    ( ~ spl4_5
    | spl4_8 ),
    inference(avatar_contradiction_clause,[],[f802])).

fof(f802,plain,
    ( $false
    | ~ spl4_5
    | spl4_8 ),
    inference(subsumption_resolution,[],[f785,f50])).

fof(f50,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f785,plain,
    ( ~ r1_tarski(k1_xboole_0,sK2)
    | ~ spl4_5
    | spl4_8 ),
    inference(superposition,[],[f131,f107])).

fof(f131,plain,
    ( ~ r1_tarski(sK0,sK2)
    | spl4_8 ),
    inference(avatar_component_clause,[],[f129])).

fof(f129,plain,
    ( spl4_8
  <=> r1_tarski(sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).

fof(f744,plain,
    ( spl4_3
    | ~ spl4_4 ),
    inference(avatar_contradiction_clause,[],[f743])).

fof(f743,plain,
    ( $false
    | spl4_3
    | ~ spl4_4 ),
    inference(subsumption_resolution,[],[f730,f739])).

fof(f739,plain,
    ( ! [X0] : m1_subset_1(k7_relat_1(sK3,X0),k1_zfmisc_1(k1_xboole_0))
    | ~ spl4_4 ),
    inference(forward_demodulation,[],[f715,f80])).

fof(f80,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f64])).

fof(f64,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f715,plain,
    ( ! [X0] : m1_subset_1(k7_relat_1(sK3,X0),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k7_relat_1(sK3,X0)),k1_xboole_0)))
    | ~ spl4_4 ),
    inference(superposition,[],[f317,f102])).

fof(f317,plain,(
    ! [X0] : m1_subset_1(k7_relat_1(sK3,X0),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k7_relat_1(sK3,X0)),sK1))) ),
    inference(subsumption_resolution,[],[f316,f137])).

fof(f137,plain,(
    ! [X0] : v1_relat_1(k7_relat_1(sK3,X0)) ),
    inference(resolution,[],[f121,f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | v1_relat_1(k7_relat_1(X0,X1)) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X0)
     => v1_relat_1(k7_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_relat_1)).

fof(f316,plain,(
    ! [X0] :
      ( m1_subset_1(k7_relat_1(sK3,X0),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k7_relat_1(sK3,X0)),sK1)))
      | ~ v1_relat_1(k7_relat_1(sK3,X0)) ) ),
    inference(subsumption_resolution,[],[f311,f198])).

fof(f198,plain,(
    ! [X0] : v1_funct_1(k7_relat_1(sK3,X0)) ),
    inference(superposition,[],[f155,f160])).

fof(f155,plain,(
    ! [X0] : v1_funct_1(k2_partfun1(sK0,sK1,sK3,X0)) ),
    inference(subsumption_resolution,[],[f152,f44])).

fof(f152,plain,(
    ! [X0] :
      ( v1_funct_1(k2_partfun1(sK0,sK1,sK3,X0))
      | ~ v1_funct_1(sK3) ) ),
    inference(resolution,[],[f76,f46])).

fof(f76,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_funct_1(k2_partfun1(X0,X1,X2,X3))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(k2_partfun1(X0,X1,X2,X3)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(k2_partfun1(X0,X1,X2,X3)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => ( m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(k2_partfun1(X0,X1,X2,X3)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_partfun1)).

fof(f311,plain,(
    ! [X0] :
      ( m1_subset_1(k7_relat_1(sK3,X0),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k7_relat_1(sK3,X0)),sK1)))
      | ~ v1_funct_1(k7_relat_1(sK3,X0))
      | ~ v1_relat_1(k7_relat_1(sK3,X0)) ) ),
    inference(resolution,[],[f255,f57])).

fof(f57,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k2_relat_1(X1),X0)
      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
        & v1_funct_2(X1,k1_relat_1(X1),X0)
        & v1_funct_1(X1) )
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
        & v1_funct_2(X1,k1_relat_1(X1),X0)
        & v1_funct_1(X1) )
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( r1_tarski(k2_relat_1(X1),X0)
       => ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
          & v1_funct_2(X1,k1_relat_1(X1),X0)
          & v1_funct_1(X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_funct_2)).

fof(f255,plain,(
    ! [X0] : r1_tarski(k2_relat_1(k7_relat_1(sK3,X0)),sK1) ),
    inference(subsumption_resolution,[],[f253,f137])).

fof(f253,plain,(
    ! [X0] :
      ( r1_tarski(k2_relat_1(k7_relat_1(sK3,X0)),sK1)
      | ~ v1_relat_1(k7_relat_1(sK3,X0)) ) ),
    inference(resolution,[],[f186,f53])).

fof(f53,plain,(
    ! [X0,X1] :
      ( ~ v5_relat_1(X1,X0)
      | r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( ( v5_relat_1(X1,X0)
          | ~ r1_tarski(k2_relat_1(X1),X0) )
        & ( r1_tarski(k2_relat_1(X1),X0)
          | ~ v5_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).

fof(f186,plain,(
    ! [X3] : v5_relat_1(k7_relat_1(sK3,X3),sK1) ),
    inference(resolution,[],[f165,f68])).

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v5_relat_1(X2,X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f165,plain,(
    ! [X0] : m1_subset_1(k7_relat_1(sK3,X0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(forward_demodulation,[],[f164,f160])).

fof(f164,plain,(
    ! [X0] : m1_subset_1(k2_partfun1(sK0,sK1,sK3,X0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(subsumption_resolution,[],[f161,f44])).

fof(f161,plain,(
    ! [X0] :
      ( m1_subset_1(k2_partfun1(sK0,sK1,sK3,X0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      | ~ v1_funct_1(sK3) ) ),
    inference(resolution,[],[f77,f46])).

fof(f77,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f730,plain,
    ( ~ m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k1_xboole_0))
    | spl4_3
    | ~ spl4_4 ),
    inference(forward_demodulation,[],[f709,f80])).

fof(f709,plain,
    ( ~ m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,k1_xboole_0)))
    | spl4_3
    | ~ spl4_4 ),
    inference(superposition,[],[f196,f102])).

fof(f196,plain,
    ( ~ m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | spl4_3 ),
    inference(superposition,[],[f98,f160])).

fof(f98,plain,
    ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | spl4_3 ),
    inference(avatar_component_clause,[],[f96])).

fof(f96,plain,
    ( spl4_3
  <=> m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f666,plain,
    ( spl4_3
    | spl4_4 ),
    inference(avatar_contradiction_clause,[],[f665])).

fof(f665,plain,
    ( $false
    | spl4_3
    | spl4_4 ),
    inference(subsumption_resolution,[],[f650,f196])).

fof(f650,plain,
    ( m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | spl4_4 ),
    inference(superposition,[],[f317,f367])).

fof(f367,plain,
    ( sK2 = k1_relat_1(k7_relat_1(sK3,sK2))
    | spl4_4 ),
    inference(resolution,[],[f229,f47])).

fof(f47,plain,(
    r1_tarski(sK2,sK0) ),
    inference(cnf_transformation,[],[f37])).

fof(f229,plain,
    ( ! [X0] :
        ( ~ r1_tarski(X0,sK0)
        | k1_relat_1(k7_relat_1(sK3,X0)) = X0 )
    | spl4_4 ),
    inference(subsumption_resolution,[],[f228,f121])).

fof(f228,plain,
    ( ! [X0] :
        ( ~ r1_tarski(X0,sK0)
        | k1_relat_1(k7_relat_1(sK3,X0)) = X0
        | ~ v1_relat_1(sK3) )
    | spl4_4 ),
    inference(superposition,[],[f52,f180])).

fof(f180,plain,
    ( sK0 = k1_relat_1(sK3)
    | spl4_4 ),
    inference(superposition,[],[f149,f170])).

fof(f170,plain,
    ( sK0 = k1_relset_1(sK0,sK1,sK3)
    | spl4_4 ),
    inference(subsumption_resolution,[],[f169,f103])).

fof(f103,plain,
    ( k1_xboole_0 != sK1
    | spl4_4 ),
    inference(avatar_component_clause,[],[f101])).

fof(f169,plain,
    ( k1_xboole_0 = sK1
    | sK0 = k1_relset_1(sK0,sK1,sK3) ),
    inference(subsumption_resolution,[],[f166,f45])).

fof(f166,plain,
    ( ~ v1_funct_2(sK3,sK0,sK1)
    | k1_xboole_0 = sK1
    | sK0 = k1_relset_1(sK0,sK1,sK3) ),
    inference(resolution,[],[f69,f46])).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | k1_relset_1(X0,X1,X2) = X0 ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
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
    inference(nnf_transformation,[],[f31])).

fof(f31,plain,(
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
    inference(flattening,[],[f30])).

fof(f30,plain,(
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
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
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

fof(f149,plain,(
    k1_relset_1(sK0,sK1,sK3) = k1_relat_1(sK3) ),
    inference(resolution,[],[f66,f46])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f52,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,k1_relat_1(X1))
      | k1_relat_1(k7_relat_1(X1,X0)) = X0
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(X0,k1_relat_1(X1))
       => k1_relat_1(k7_relat_1(X1,X0)) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_relat_1)).

fof(f594,plain,
    ( spl4_2
    | spl4_4 ),
    inference(avatar_contradiction_clause,[],[f593])).

fof(f593,plain,
    ( $false
    | spl4_2
    | spl4_4 ),
    inference(subsumption_resolution,[],[f591,f197])).

fof(f197,plain,
    ( ~ v1_funct_2(k7_relat_1(sK3,sK2),sK2,sK1)
    | spl4_2 ),
    inference(superposition,[],[f94,f160])).

fof(f591,plain,
    ( v1_funct_2(k7_relat_1(sK3,sK2),sK2,sK1)
    | spl4_4 ),
    inference(superposition,[],[f319,f367])).

fof(f319,plain,(
    ! [X1] : v1_funct_2(k7_relat_1(sK3,X1),k1_relat_1(k7_relat_1(sK3,X1)),sK1) ),
    inference(subsumption_resolution,[],[f318,f137])).

fof(f318,plain,(
    ! [X1] :
      ( v1_funct_2(k7_relat_1(sK3,X1),k1_relat_1(k7_relat_1(sK3,X1)),sK1)
      | ~ v1_relat_1(k7_relat_1(sK3,X1)) ) ),
    inference(subsumption_resolution,[],[f312,f198])).

fof(f312,plain,(
    ! [X1] :
      ( v1_funct_2(k7_relat_1(sK3,X1),k1_relat_1(k7_relat_1(sK3,X1)),sK1)
      | ~ v1_funct_1(k7_relat_1(sK3,X1))
      | ~ v1_relat_1(k7_relat_1(sK3,X1)) ) ),
    inference(resolution,[],[f255,f56])).

fof(f56,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k2_relat_1(X1),X0)
      | v1_funct_2(X1,k1_relat_1(X1),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f179,plain,(
    spl4_1 ),
    inference(avatar_contradiction_clause,[],[f178])).

fof(f178,plain,
    ( $false
    | spl4_1 ),
    inference(resolution,[],[f155,f90])).

fof(f90,plain,
    ( ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))
    | spl4_1 ),
    inference(avatar_component_clause,[],[f88])).

fof(f88,plain,
    ( spl4_1
  <=> v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f136,plain,
    ( ~ spl4_8
    | spl4_9 ),
    inference(avatar_split_clause,[],[f125,f133,f129])).

fof(f125,plain,
    ( sK0 = sK2
    | ~ r1_tarski(sK0,sK2) ),
    inference(resolution,[],[f61,f47])).

fof(f61,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f39])).

fof(f39,plain,(
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

fof(f108,plain,
    ( ~ spl4_4
    | spl4_5 ),
    inference(avatar_split_clause,[],[f48,f105,f101])).

fof(f48,plain,
    ( k1_xboole_0 = sK0
    | k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f37])).

fof(f99,plain,
    ( ~ spl4_1
    | ~ spl4_2
    | ~ spl4_3 ),
    inference(avatar_split_clause,[],[f49,f96,f92,f88])).

fof(f49,plain,
    ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1)
    | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) ),
    inference(cnf_transformation,[],[f37])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n024.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 14:18:36 EST 2020
% 0.14/0.35  % CPUTime    : 
% 1.39/0.54  % (11955)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 1.39/0.54  % (11964)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 1.39/0.55  % (11960)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 1.39/0.55  % (11956)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 1.39/0.56  % (11958)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 1.39/0.56  % (11971)lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_145 on theBenchmark
% 1.39/0.56  % (11977)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 1.60/0.57  % (11974)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 1.60/0.57  % (11954)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 1.60/0.57  % (11963)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
% 1.60/0.57  % (11976)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 1.60/0.58  % (11970)lrs+4_5:4_av=off:bd=off:er=filter:lma=on:lwlo=on:nwc=1:stl=30:sp=occurrence:updr=off_230 on theBenchmark
% 1.60/0.58  % (11959)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 1.60/0.58  % (11966)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 1.60/0.58  % (11961)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 1.60/0.58  % (11965)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 1.60/0.58  % (11968)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 1.60/0.58  % (11962)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 1.60/0.58  % (11978)dis+2_128_add=large:afp=100000:afq=1.4:amm=sco:anc=none:lma=on:nm=2:newcnf=on:nwc=1:nicw=on:sas=z3:sos=theory:sac=on:updr=off_288 on theBenchmark
% 1.60/0.59  % (11975)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 1.60/0.59  % (11969)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 1.60/0.59  % (11979)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_364 on theBenchmark
% 1.60/0.59  % (11967)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 1.60/0.59  % (11972)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 1.60/0.60  % (11964)Refutation found. Thanks to Tanya!
% 1.60/0.60  % SZS status Theorem for theBenchmark
% 1.60/0.60  % SZS output start Proof for theBenchmark
% 1.60/0.60  fof(f828,plain,(
% 1.60/0.60    $false),
% 1.60/0.60    inference(avatar_sat_refutation,[],[f99,f108,f136,f179,f594,f666,f744,f803,f827])).
% 1.60/0.60  fof(f827,plain,(
% 1.60/0.60    spl4_2 | ~spl4_4 | ~spl4_5 | ~spl4_9),
% 1.60/0.60    inference(avatar_contradiction_clause,[],[f826])).
% 1.60/0.60  fof(f826,plain,(
% 1.60/0.60    $false | (spl4_2 | ~spl4_4 | ~spl4_5 | ~spl4_9)),
% 1.60/0.60    inference(subsumption_resolution,[],[f825,f720])).
% 1.60/0.60  fof(f720,plain,(
% 1.60/0.60    v1_funct_2(sK3,k1_xboole_0,k1_xboole_0) | (~spl4_4 | ~spl4_5)),
% 1.60/0.60    inference(forward_demodulation,[],[f698,f107])).
% 1.60/0.60  fof(f107,plain,(
% 1.60/0.60    k1_xboole_0 = sK0 | ~spl4_5),
% 1.60/0.60    inference(avatar_component_clause,[],[f105])).
% 1.60/0.60  fof(f105,plain,(
% 1.60/0.60    spl4_5 <=> k1_xboole_0 = sK0),
% 1.60/0.60    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).
% 1.60/0.60  fof(f698,plain,(
% 1.60/0.60    v1_funct_2(sK3,sK0,k1_xboole_0) | ~spl4_4),
% 1.60/0.60    inference(superposition,[],[f45,f102])).
% 1.60/0.60  fof(f102,plain,(
% 1.60/0.60    k1_xboole_0 = sK1 | ~spl4_4),
% 1.60/0.60    inference(avatar_component_clause,[],[f101])).
% 1.60/0.60  fof(f101,plain,(
% 1.60/0.60    spl4_4 <=> k1_xboole_0 = sK1),
% 1.60/0.60    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 1.60/0.60  fof(f45,plain,(
% 1.60/0.60    v1_funct_2(sK3,sK0,sK1)),
% 1.60/0.60    inference(cnf_transformation,[],[f37])).
% 1.60/0.60  fof(f37,plain,(
% 1.60/0.60    (~m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1) | ~v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))) & (k1_xboole_0 = sK0 | k1_xboole_0 != sK1) & r1_tarski(sK2,sK0) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK3,sK0,sK1) & v1_funct_1(sK3)),
% 1.60/0.60    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f18,f36])).
% 1.60/0.60  fof(f36,plain,(
% 1.60/0.60    ? [X0,X1,X2,X3] : ((~m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1) | ~v1_funct_1(k2_partfun1(X0,X1,X3,X2))) & (k1_xboole_0 = X0 | k1_xboole_0 != X1) & r1_tarski(X2,X0) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ((~m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1) | ~v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))) & (k1_xboole_0 = sK0 | k1_xboole_0 != sK1) & r1_tarski(sK2,sK0) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK3,sK0,sK1) & v1_funct_1(sK3))),
% 1.60/0.60    introduced(choice_axiom,[])).
% 1.60/0.60  fof(f18,plain,(
% 1.60/0.60    ? [X0,X1,X2,X3] : ((~m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1) | ~v1_funct_1(k2_partfun1(X0,X1,X3,X2))) & (k1_xboole_0 = X0 | k1_xboole_0 != X1) & r1_tarski(X2,X0) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3))),
% 1.60/0.60    inference(flattening,[],[f17])).
% 1.60/0.60  fof(f17,plain,(
% 1.60/0.60    ? [X0,X1,X2,X3] : ((((~m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1) | ~v1_funct_1(k2_partfun1(X0,X1,X3,X2))) & (k1_xboole_0 = X0 | k1_xboole_0 != X1)) & r1_tarski(X2,X0)) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)))),
% 1.60/0.60    inference(ennf_transformation,[],[f16])).
% 1.60/0.60  fof(f16,negated_conjecture,(
% 1.60/0.60    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r1_tarski(X2,X0) => ((m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1) & v1_funct_1(k2_partfun1(X0,X1,X3,X2))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))))),
% 1.60/0.60    inference(negated_conjecture,[],[f15])).
% 1.60/0.60  fof(f15,conjecture,(
% 1.60/0.60    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r1_tarski(X2,X0) => ((m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1) & v1_funct_1(k2_partfun1(X0,X1,X3,X2))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))))),
% 1.60/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_funct_2)).
% 1.60/0.60  fof(f825,plain,(
% 1.60/0.60    ~v1_funct_2(sK3,k1_xboole_0,k1_xboole_0) | (spl4_2 | ~spl4_4 | ~spl4_5 | ~spl4_9)),
% 1.60/0.60    inference(forward_demodulation,[],[f823,f791])).
% 1.60/0.60  fof(f791,plain,(
% 1.60/0.60    sK3 = k7_relat_1(sK3,k1_xboole_0) | ~spl4_5),
% 1.60/0.60    inference(superposition,[],[f172,f107])).
% 1.60/0.60  fof(f172,plain,(
% 1.60/0.60    sK3 = k7_relat_1(sK3,sK0)),
% 1.60/0.60    inference(subsumption_resolution,[],[f171,f121])).
% 1.60/0.60  fof(f121,plain,(
% 1.60/0.60    v1_relat_1(sK3)),
% 1.60/0.60    inference(resolution,[],[f65,f46])).
% 1.60/0.60  fof(f46,plain,(
% 1.60/0.60    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 1.60/0.60    inference(cnf_transformation,[],[f37])).
% 1.60/0.60  fof(f65,plain,(
% 1.60/0.60    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)) )),
% 1.60/0.60    inference(cnf_transformation,[],[f27])).
% 1.60/0.60  fof(f27,plain,(
% 1.60/0.60    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.60/0.60    inference(ennf_transformation,[],[f8])).
% 1.60/0.60  fof(f8,axiom,(
% 1.60/0.60    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 1.60/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).
% 1.60/0.60  fof(f171,plain,(
% 1.60/0.60    sK3 = k7_relat_1(sK3,sK0) | ~v1_relat_1(sK3)),
% 1.60/0.60    inference(resolution,[],[f138,f58])).
% 1.60/0.60  fof(f58,plain,(
% 1.60/0.60    ( ! [X0,X1] : (~v4_relat_1(X1,X0) | k7_relat_1(X1,X0) = X1 | ~v1_relat_1(X1)) )),
% 1.60/0.60    inference(cnf_transformation,[],[f26])).
% 1.60/0.60  fof(f26,plain,(
% 1.60/0.60    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 1.60/0.60    inference(flattening,[],[f25])).
% 1.60/0.60  fof(f25,plain,(
% 1.60/0.60    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 1.60/0.60    inference(ennf_transformation,[],[f6])).
% 1.60/0.60  fof(f6,axiom,(
% 1.60/0.60    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => k7_relat_1(X1,X0) = X1)),
% 1.60/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t209_relat_1)).
% 1.60/0.60  fof(f138,plain,(
% 1.60/0.60    v4_relat_1(sK3,sK0)),
% 1.60/0.60    inference(resolution,[],[f67,f46])).
% 1.60/0.60  fof(f67,plain,(
% 1.60/0.60    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v4_relat_1(X2,X0)) )),
% 1.60/0.60    inference(cnf_transformation,[],[f29])).
% 1.60/0.60  fof(f29,plain,(
% 1.60/0.60    ! [X0,X1,X2] : ((v5_relat_1(X2,X1) & v4_relat_1(X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.60/0.60    inference(ennf_transformation,[],[f9])).
% 1.60/0.60  fof(f9,axiom,(
% 1.60/0.60    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 1.60/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).
% 1.60/0.60  fof(f823,plain,(
% 1.60/0.60    ~v1_funct_2(k7_relat_1(sK3,k1_xboole_0),k1_xboole_0,k1_xboole_0) | (spl4_2 | ~spl4_4 | ~spl4_5 | ~spl4_9)),
% 1.60/0.60    inference(superposition,[],[f769,f814])).
% 1.60/0.60  fof(f814,plain,(
% 1.60/0.60    k1_xboole_0 = sK2 | (~spl4_5 | ~spl4_9)),
% 1.60/0.60    inference(forward_demodulation,[],[f135,f107])).
% 1.60/0.60  fof(f135,plain,(
% 1.60/0.60    sK0 = sK2 | ~spl4_9),
% 1.60/0.60    inference(avatar_component_clause,[],[f133])).
% 1.60/0.60  fof(f133,plain,(
% 1.60/0.60    spl4_9 <=> sK0 = sK2),
% 1.60/0.60    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).
% 1.60/0.60  fof(f769,plain,(
% 1.60/0.60    ~v1_funct_2(k7_relat_1(sK3,sK2),sK2,k1_xboole_0) | (spl4_2 | ~spl4_4 | ~spl4_5)),
% 1.60/0.60    inference(forward_demodulation,[],[f768,f726])).
% 1.60/0.60  fof(f726,plain,(
% 1.60/0.60    ( ! [X0] : (k7_relat_1(sK3,X0) = k2_partfun1(k1_xboole_0,k1_xboole_0,sK3,X0)) ) | (~spl4_4 | ~spl4_5)),
% 1.60/0.60    inference(forward_demodulation,[],[f704,f107])).
% 1.60/0.60  fof(f704,plain,(
% 1.60/0.60    ( ! [X0] : (k7_relat_1(sK3,X0) = k2_partfun1(sK0,k1_xboole_0,sK3,X0)) ) | ~spl4_4),
% 1.60/0.60    inference(superposition,[],[f160,f102])).
% 1.60/0.60  fof(f160,plain,(
% 1.60/0.60    ( ! [X0] : (k7_relat_1(sK3,X0) = k2_partfun1(sK0,sK1,sK3,X0)) )),
% 1.60/0.60    inference(subsumption_resolution,[],[f157,f44])).
% 1.60/0.60  fof(f44,plain,(
% 1.60/0.60    v1_funct_1(sK3)),
% 1.60/0.60    inference(cnf_transformation,[],[f37])).
% 1.60/0.60  fof(f157,plain,(
% 1.60/0.60    ( ! [X0] : (k7_relat_1(sK3,X0) = k2_partfun1(sK0,sK1,sK3,X0) | ~v1_funct_1(sK3)) )),
% 1.60/0.60    inference(resolution,[],[f75,f46])).
% 1.60/0.60  fof(f75,plain,(
% 1.60/0.60    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3) | ~v1_funct_1(X2)) )),
% 1.60/0.60    inference(cnf_transformation,[],[f33])).
% 1.60/0.60  fof(f33,plain,(
% 1.60/0.60    ! [X0,X1,X2,X3] : (k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 1.60/0.60    inference(flattening,[],[f32])).
% 1.60/0.60  fof(f32,plain,(
% 1.60/0.60    ! [X0,X1,X2,X3] : (k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 1.60/0.60    inference(ennf_transformation,[],[f13])).
% 1.60/0.60  fof(f13,axiom,(
% 1.60/0.60    ! [X0,X1,X2,X3] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3))),
% 1.60/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_partfun1)).
% 1.60/0.60  fof(f768,plain,(
% 1.60/0.60    ~v1_funct_2(k2_partfun1(k1_xboole_0,k1_xboole_0,sK3,sK2),sK2,k1_xboole_0) | (spl4_2 | ~spl4_4 | ~spl4_5)),
% 1.60/0.60    inference(forward_demodulation,[],[f767,f107])).
% 1.60/0.60  fof(f767,plain,(
% 1.60/0.60    ~v1_funct_2(k2_partfun1(sK0,k1_xboole_0,sK3,sK2),sK2,k1_xboole_0) | (spl4_2 | ~spl4_4)),
% 1.60/0.60    inference(forward_demodulation,[],[f94,f102])).
% 1.60/0.60  fof(f94,plain,(
% 1.60/0.60    ~v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1) | spl4_2),
% 1.60/0.60    inference(avatar_component_clause,[],[f92])).
% 1.60/0.60  fof(f92,plain,(
% 1.60/0.60    spl4_2 <=> v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1)),
% 1.60/0.60    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 1.60/0.60  fof(f803,plain,(
% 1.60/0.60    ~spl4_5 | spl4_8),
% 1.60/0.60    inference(avatar_contradiction_clause,[],[f802])).
% 1.60/0.60  fof(f802,plain,(
% 1.60/0.60    $false | (~spl4_5 | spl4_8)),
% 1.60/0.60    inference(subsumption_resolution,[],[f785,f50])).
% 1.60/0.60  fof(f50,plain,(
% 1.60/0.60    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 1.60/0.60    inference(cnf_transformation,[],[f2])).
% 1.60/0.60  fof(f2,axiom,(
% 1.60/0.60    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 1.60/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).
% 1.60/0.60  fof(f785,plain,(
% 1.60/0.60    ~r1_tarski(k1_xboole_0,sK2) | (~spl4_5 | spl4_8)),
% 1.60/0.60    inference(superposition,[],[f131,f107])).
% 1.60/0.60  fof(f131,plain,(
% 1.60/0.60    ~r1_tarski(sK0,sK2) | spl4_8),
% 1.60/0.60    inference(avatar_component_clause,[],[f129])).
% 1.60/0.60  fof(f129,plain,(
% 1.60/0.60    spl4_8 <=> r1_tarski(sK0,sK2)),
% 1.60/0.60    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).
% 1.60/0.60  fof(f744,plain,(
% 1.60/0.60    spl4_3 | ~spl4_4),
% 1.60/0.60    inference(avatar_contradiction_clause,[],[f743])).
% 1.60/0.60  fof(f743,plain,(
% 1.60/0.60    $false | (spl4_3 | ~spl4_4)),
% 1.60/0.60    inference(subsumption_resolution,[],[f730,f739])).
% 1.60/0.60  fof(f739,plain,(
% 1.60/0.60    ( ! [X0] : (m1_subset_1(k7_relat_1(sK3,X0),k1_zfmisc_1(k1_xboole_0))) ) | ~spl4_4),
% 1.60/0.60    inference(forward_demodulation,[],[f715,f80])).
% 1.60/0.60  fof(f80,plain,(
% 1.60/0.60    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 1.60/0.60    inference(equality_resolution,[],[f64])).
% 1.60/0.60  fof(f64,plain,(
% 1.60/0.60    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X1) )),
% 1.60/0.60    inference(cnf_transformation,[],[f42])).
% 1.60/0.60  fof(f42,plain,(
% 1.60/0.60    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 1.60/0.60    inference(flattening,[],[f41])).
% 1.60/0.60  fof(f41,plain,(
% 1.60/0.60    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 1.60/0.60    inference(nnf_transformation,[],[f3])).
% 1.60/0.60  fof(f3,axiom,(
% 1.60/0.60    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 1.60/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 1.60/0.60  fof(f715,plain,(
% 1.60/0.60    ( ! [X0] : (m1_subset_1(k7_relat_1(sK3,X0),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k7_relat_1(sK3,X0)),k1_xboole_0)))) ) | ~spl4_4),
% 1.60/0.60    inference(superposition,[],[f317,f102])).
% 1.60/0.60  fof(f317,plain,(
% 1.60/0.60    ( ! [X0] : (m1_subset_1(k7_relat_1(sK3,X0),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k7_relat_1(sK3,X0)),sK1)))) )),
% 1.60/0.60    inference(subsumption_resolution,[],[f316,f137])).
% 1.60/0.60  fof(f137,plain,(
% 1.60/0.60    ( ! [X0] : (v1_relat_1(k7_relat_1(sK3,X0))) )),
% 1.60/0.60    inference(resolution,[],[f121,f51])).
% 1.60/0.60  fof(f51,plain,(
% 1.60/0.60    ( ! [X0,X1] : (~v1_relat_1(X0) | v1_relat_1(k7_relat_1(X0,X1))) )),
% 1.60/0.60    inference(cnf_transformation,[],[f19])).
% 1.60/0.60  fof(f19,plain,(
% 1.60/0.60    ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0))),
% 1.60/0.60    inference(ennf_transformation,[],[f5])).
% 1.60/0.60  fof(f5,axiom,(
% 1.60/0.60    ! [X0,X1] : (v1_relat_1(X0) => v1_relat_1(k7_relat_1(X0,X1)))),
% 1.60/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_relat_1)).
% 1.60/0.60  fof(f316,plain,(
% 1.60/0.60    ( ! [X0] : (m1_subset_1(k7_relat_1(sK3,X0),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k7_relat_1(sK3,X0)),sK1))) | ~v1_relat_1(k7_relat_1(sK3,X0))) )),
% 1.60/0.60    inference(subsumption_resolution,[],[f311,f198])).
% 1.60/0.60  fof(f198,plain,(
% 1.60/0.60    ( ! [X0] : (v1_funct_1(k7_relat_1(sK3,X0))) )),
% 1.60/0.60    inference(superposition,[],[f155,f160])).
% 1.60/0.60  fof(f155,plain,(
% 1.60/0.60    ( ! [X0] : (v1_funct_1(k2_partfun1(sK0,sK1,sK3,X0))) )),
% 1.60/0.60    inference(subsumption_resolution,[],[f152,f44])).
% 1.60/0.60  fof(f152,plain,(
% 1.60/0.60    ( ! [X0] : (v1_funct_1(k2_partfun1(sK0,sK1,sK3,X0)) | ~v1_funct_1(sK3)) )),
% 1.60/0.60    inference(resolution,[],[f76,f46])).
% 1.60/0.60  fof(f76,plain,(
% 1.60/0.60    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_funct_1(k2_partfun1(X0,X1,X2,X3)) | ~v1_funct_1(X2)) )),
% 1.60/0.60    inference(cnf_transformation,[],[f35])).
% 1.60/0.60  fof(f35,plain,(
% 1.60/0.60    ! [X0,X1,X2,X3] : ((m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(k2_partfun1(X0,X1,X2,X3))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 1.60/0.60    inference(flattening,[],[f34])).
% 1.60/0.60  fof(f34,plain,(
% 1.60/0.60    ! [X0,X1,X2,X3] : ((m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(k2_partfun1(X0,X1,X2,X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 1.60/0.60    inference(ennf_transformation,[],[f12])).
% 1.60/0.60  fof(f12,axiom,(
% 1.60/0.60    ! [X0,X1,X2,X3] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => (m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(k2_partfun1(X0,X1,X2,X3))))),
% 1.60/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_partfun1)).
% 1.60/0.60  fof(f311,plain,(
% 1.60/0.60    ( ! [X0] : (m1_subset_1(k7_relat_1(sK3,X0),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k7_relat_1(sK3,X0)),sK1))) | ~v1_funct_1(k7_relat_1(sK3,X0)) | ~v1_relat_1(k7_relat_1(sK3,X0))) )),
% 1.60/0.60    inference(resolution,[],[f255,f57])).
% 1.60/0.60  fof(f57,plain,(
% 1.60/0.60    ( ! [X0,X1] : (~r1_tarski(k2_relat_1(X1),X0) | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 1.60/0.60    inference(cnf_transformation,[],[f24])).
% 1.60/0.60  fof(f24,plain,(
% 1.60/0.60    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) & v1_funct_2(X1,k1_relat_1(X1),X0) & v1_funct_1(X1)) | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 1.60/0.60    inference(flattening,[],[f23])).
% 1.60/0.60  fof(f23,plain,(
% 1.60/0.60    ! [X0,X1] : (((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) & v1_funct_2(X1,k1_relat_1(X1),X0) & v1_funct_1(X1)) | ~r1_tarski(k2_relat_1(X1),X0)) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 1.60/0.60    inference(ennf_transformation,[],[f14])).
% 1.60/0.60  fof(f14,axiom,(
% 1.60/0.60    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (r1_tarski(k2_relat_1(X1),X0) => (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) & v1_funct_2(X1,k1_relat_1(X1),X0) & v1_funct_1(X1))))),
% 1.60/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_funct_2)).
% 1.60/0.60  fof(f255,plain,(
% 1.60/0.60    ( ! [X0] : (r1_tarski(k2_relat_1(k7_relat_1(sK3,X0)),sK1)) )),
% 1.60/0.60    inference(subsumption_resolution,[],[f253,f137])).
% 1.60/0.60  fof(f253,plain,(
% 1.60/0.60    ( ! [X0] : (r1_tarski(k2_relat_1(k7_relat_1(sK3,X0)),sK1) | ~v1_relat_1(k7_relat_1(sK3,X0))) )),
% 1.60/0.60    inference(resolution,[],[f186,f53])).
% 1.60/0.60  fof(f53,plain,(
% 1.60/0.60    ( ! [X0,X1] : (~v5_relat_1(X1,X0) | r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 1.60/0.60    inference(cnf_transformation,[],[f38])).
% 1.60/0.60  fof(f38,plain,(
% 1.60/0.60    ! [X0,X1] : (((v5_relat_1(X1,X0) | ~r1_tarski(k2_relat_1(X1),X0)) & (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 1.60/0.60    inference(nnf_transformation,[],[f22])).
% 1.60/0.60  fof(f22,plain,(
% 1.60/0.60    ! [X0,X1] : ((v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 1.60/0.60    inference(ennf_transformation,[],[f4])).
% 1.60/0.60  fof(f4,axiom,(
% 1.60/0.60    ! [X0,X1] : (v1_relat_1(X1) => (v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)))),
% 1.60/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).
% 1.60/0.60  fof(f186,plain,(
% 1.60/0.60    ( ! [X3] : (v5_relat_1(k7_relat_1(sK3,X3),sK1)) )),
% 1.60/0.60    inference(resolution,[],[f165,f68])).
% 1.60/0.60  fof(f68,plain,(
% 1.60/0.60    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v5_relat_1(X2,X1)) )),
% 1.60/0.60    inference(cnf_transformation,[],[f29])).
% 1.60/0.60  fof(f165,plain,(
% 1.60/0.60    ( ! [X0] : (m1_subset_1(k7_relat_1(sK3,X0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))) )),
% 1.60/0.60    inference(forward_demodulation,[],[f164,f160])).
% 1.60/0.60  fof(f164,plain,(
% 1.60/0.60    ( ! [X0] : (m1_subset_1(k2_partfun1(sK0,sK1,sK3,X0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))) )),
% 1.60/0.60    inference(subsumption_resolution,[],[f161,f44])).
% 1.60/0.60  fof(f161,plain,(
% 1.60/0.60    ( ! [X0] : (m1_subset_1(k2_partfun1(sK0,sK1,sK3,X0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(sK3)) )),
% 1.60/0.60    inference(resolution,[],[f77,f46])).
% 1.60/0.60  fof(f77,plain,(
% 1.60/0.60    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 1.60/0.60    inference(cnf_transformation,[],[f35])).
% 1.60/0.60  fof(f730,plain,(
% 1.60/0.60    ~m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k1_xboole_0)) | (spl4_3 | ~spl4_4)),
% 1.60/0.60    inference(forward_demodulation,[],[f709,f80])).
% 1.60/0.60  fof(f709,plain,(
% 1.60/0.60    ~m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,k1_xboole_0))) | (spl4_3 | ~spl4_4)),
% 1.60/0.60    inference(superposition,[],[f196,f102])).
% 1.60/0.60  fof(f196,plain,(
% 1.60/0.60    ~m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | spl4_3),
% 1.60/0.60    inference(superposition,[],[f98,f160])).
% 1.60/0.60  fof(f98,plain,(
% 1.60/0.60    ~m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | spl4_3),
% 1.60/0.60    inference(avatar_component_clause,[],[f96])).
% 1.60/0.60  fof(f96,plain,(
% 1.60/0.60    spl4_3 <=> m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))),
% 1.60/0.60    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 1.60/0.60  fof(f666,plain,(
% 1.60/0.60    spl4_3 | spl4_4),
% 1.60/0.60    inference(avatar_contradiction_clause,[],[f665])).
% 1.60/0.60  fof(f665,plain,(
% 1.60/0.60    $false | (spl4_3 | spl4_4)),
% 1.60/0.60    inference(subsumption_resolution,[],[f650,f196])).
% 1.60/0.60  fof(f650,plain,(
% 1.60/0.60    m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | spl4_4),
% 1.60/0.60    inference(superposition,[],[f317,f367])).
% 1.60/0.60  fof(f367,plain,(
% 1.60/0.60    sK2 = k1_relat_1(k7_relat_1(sK3,sK2)) | spl4_4),
% 1.60/0.60    inference(resolution,[],[f229,f47])).
% 1.60/0.60  fof(f47,plain,(
% 1.60/0.60    r1_tarski(sK2,sK0)),
% 1.60/0.60    inference(cnf_transformation,[],[f37])).
% 1.60/0.60  fof(f229,plain,(
% 1.60/0.60    ( ! [X0] : (~r1_tarski(X0,sK0) | k1_relat_1(k7_relat_1(sK3,X0)) = X0) ) | spl4_4),
% 1.60/0.60    inference(subsumption_resolution,[],[f228,f121])).
% 1.60/0.60  fof(f228,plain,(
% 1.60/0.60    ( ! [X0] : (~r1_tarski(X0,sK0) | k1_relat_1(k7_relat_1(sK3,X0)) = X0 | ~v1_relat_1(sK3)) ) | spl4_4),
% 1.60/0.60    inference(superposition,[],[f52,f180])).
% 1.60/0.60  fof(f180,plain,(
% 1.60/0.60    sK0 = k1_relat_1(sK3) | spl4_4),
% 1.60/0.60    inference(superposition,[],[f149,f170])).
% 1.60/0.60  fof(f170,plain,(
% 1.60/0.60    sK0 = k1_relset_1(sK0,sK1,sK3) | spl4_4),
% 1.60/0.60    inference(subsumption_resolution,[],[f169,f103])).
% 1.60/0.60  fof(f103,plain,(
% 1.60/0.60    k1_xboole_0 != sK1 | spl4_4),
% 1.60/0.60    inference(avatar_component_clause,[],[f101])).
% 1.60/0.60  fof(f169,plain,(
% 1.60/0.60    k1_xboole_0 = sK1 | sK0 = k1_relset_1(sK0,sK1,sK3)),
% 1.60/0.60    inference(subsumption_resolution,[],[f166,f45])).
% 1.60/0.60  fof(f166,plain,(
% 1.60/0.60    ~v1_funct_2(sK3,sK0,sK1) | k1_xboole_0 = sK1 | sK0 = k1_relset_1(sK0,sK1,sK3)),
% 1.60/0.60    inference(resolution,[],[f69,f46])).
% 1.60/0.60  fof(f69,plain,(
% 1.60/0.60    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | k1_relset_1(X0,X1,X2) = X0) )),
% 1.60/0.60    inference(cnf_transformation,[],[f43])).
% 1.60/0.60  fof(f43,plain,(
% 1.60/0.60    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.60/0.60    inference(nnf_transformation,[],[f31])).
% 1.60/0.60  fof(f31,plain,(
% 1.60/0.60    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.60/0.60    inference(flattening,[],[f30])).
% 1.60/0.60  fof(f30,plain,(
% 1.60/0.60    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.60/0.60    inference(ennf_transformation,[],[f11])).
% 1.60/0.60  fof(f11,axiom,(
% 1.60/0.60    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 1.60/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).
% 1.60/0.60  fof(f149,plain,(
% 1.60/0.60    k1_relset_1(sK0,sK1,sK3) = k1_relat_1(sK3)),
% 1.60/0.60    inference(resolution,[],[f66,f46])).
% 1.60/0.60  fof(f66,plain,(
% 1.60/0.60    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_relset_1(X0,X1,X2) = k1_relat_1(X2)) )),
% 1.60/0.60    inference(cnf_transformation,[],[f28])).
% 1.60/0.60  fof(f28,plain,(
% 1.60/0.60    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.60/0.60    inference(ennf_transformation,[],[f10])).
% 1.60/0.60  fof(f10,axiom,(
% 1.60/0.60    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 1.60/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 1.60/0.60  fof(f52,plain,(
% 1.60/0.60    ( ! [X0,X1] : (~r1_tarski(X0,k1_relat_1(X1)) | k1_relat_1(k7_relat_1(X1,X0)) = X0 | ~v1_relat_1(X1)) )),
% 1.60/0.60    inference(cnf_transformation,[],[f21])).
% 1.60/0.60  fof(f21,plain,(
% 1.60/0.60    ! [X0,X1] : (k1_relat_1(k7_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k1_relat_1(X1)) | ~v1_relat_1(X1))),
% 1.60/0.60    inference(flattening,[],[f20])).
% 1.60/0.60  fof(f20,plain,(
% 1.60/0.60    ! [X0,X1] : ((k1_relat_1(k7_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k1_relat_1(X1))) | ~v1_relat_1(X1))),
% 1.60/0.60    inference(ennf_transformation,[],[f7])).
% 1.60/0.60  fof(f7,axiom,(
% 1.60/0.60    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(X0,k1_relat_1(X1)) => k1_relat_1(k7_relat_1(X1,X0)) = X0))),
% 1.60/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_relat_1)).
% 1.60/0.60  fof(f594,plain,(
% 1.60/0.60    spl4_2 | spl4_4),
% 1.60/0.60    inference(avatar_contradiction_clause,[],[f593])).
% 1.60/0.60  fof(f593,plain,(
% 1.60/0.60    $false | (spl4_2 | spl4_4)),
% 1.60/0.60    inference(subsumption_resolution,[],[f591,f197])).
% 1.60/0.60  fof(f197,plain,(
% 1.60/0.60    ~v1_funct_2(k7_relat_1(sK3,sK2),sK2,sK1) | spl4_2),
% 1.60/0.60    inference(superposition,[],[f94,f160])).
% 1.60/0.60  fof(f591,plain,(
% 1.60/0.60    v1_funct_2(k7_relat_1(sK3,sK2),sK2,sK1) | spl4_4),
% 1.60/0.60    inference(superposition,[],[f319,f367])).
% 1.60/0.60  fof(f319,plain,(
% 1.60/0.60    ( ! [X1] : (v1_funct_2(k7_relat_1(sK3,X1),k1_relat_1(k7_relat_1(sK3,X1)),sK1)) )),
% 1.60/0.60    inference(subsumption_resolution,[],[f318,f137])).
% 1.60/0.60  fof(f318,plain,(
% 1.60/0.60    ( ! [X1] : (v1_funct_2(k7_relat_1(sK3,X1),k1_relat_1(k7_relat_1(sK3,X1)),sK1) | ~v1_relat_1(k7_relat_1(sK3,X1))) )),
% 1.60/0.60    inference(subsumption_resolution,[],[f312,f198])).
% 1.60/0.60  fof(f312,plain,(
% 1.60/0.60    ( ! [X1] : (v1_funct_2(k7_relat_1(sK3,X1),k1_relat_1(k7_relat_1(sK3,X1)),sK1) | ~v1_funct_1(k7_relat_1(sK3,X1)) | ~v1_relat_1(k7_relat_1(sK3,X1))) )),
% 1.60/0.60    inference(resolution,[],[f255,f56])).
% 1.60/0.60  fof(f56,plain,(
% 1.60/0.60    ( ! [X0,X1] : (~r1_tarski(k2_relat_1(X1),X0) | v1_funct_2(X1,k1_relat_1(X1),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 1.60/0.60    inference(cnf_transformation,[],[f24])).
% 1.60/0.60  fof(f179,plain,(
% 1.60/0.60    spl4_1),
% 1.60/0.60    inference(avatar_contradiction_clause,[],[f178])).
% 1.60/0.60  fof(f178,plain,(
% 1.60/0.60    $false | spl4_1),
% 1.60/0.60    inference(resolution,[],[f155,f90])).
% 1.60/0.60  fof(f90,plain,(
% 1.60/0.60    ~v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) | spl4_1),
% 1.60/0.60    inference(avatar_component_clause,[],[f88])).
% 1.60/0.60  fof(f88,plain,(
% 1.60/0.60    spl4_1 <=> v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))),
% 1.60/0.60    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 1.60/0.60  fof(f136,plain,(
% 1.60/0.60    ~spl4_8 | spl4_9),
% 1.60/0.60    inference(avatar_split_clause,[],[f125,f133,f129])).
% 1.60/0.60  fof(f125,plain,(
% 1.60/0.60    sK0 = sK2 | ~r1_tarski(sK0,sK2)),
% 1.60/0.60    inference(resolution,[],[f61,f47])).
% 1.60/0.60  fof(f61,plain,(
% 1.60/0.60    ( ! [X0,X1] : (~r1_tarski(X1,X0) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 1.60/0.60    inference(cnf_transformation,[],[f40])).
% 1.60/0.60  fof(f40,plain,(
% 1.60/0.60    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.60/0.60    inference(flattening,[],[f39])).
% 1.60/0.60  fof(f39,plain,(
% 1.60/0.60    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.60/0.60    inference(nnf_transformation,[],[f1])).
% 1.60/0.60  fof(f1,axiom,(
% 1.60/0.60    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.60/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 1.60/0.60  fof(f108,plain,(
% 1.60/0.60    ~spl4_4 | spl4_5),
% 1.60/0.60    inference(avatar_split_clause,[],[f48,f105,f101])).
% 1.60/0.60  fof(f48,plain,(
% 1.60/0.60    k1_xboole_0 = sK0 | k1_xboole_0 != sK1),
% 1.60/0.60    inference(cnf_transformation,[],[f37])).
% 1.60/0.60  fof(f99,plain,(
% 1.60/0.60    ~spl4_1 | ~spl4_2 | ~spl4_3),
% 1.60/0.60    inference(avatar_split_clause,[],[f49,f96,f92,f88])).
% 1.60/0.60  fof(f49,plain,(
% 1.60/0.60    ~m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1) | ~v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))),
% 1.60/0.60    inference(cnf_transformation,[],[f37])).
% 1.60/0.60  % SZS output end Proof for theBenchmark
% 1.60/0.60  % (11964)------------------------------
% 1.60/0.60  % (11964)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.60/0.60  % (11964)Termination reason: Refutation
% 1.60/0.60  
% 1.60/0.60  % (11964)Memory used [KB]: 11001
% 1.60/0.60  % (11964)Time elapsed: 0.149 s
% 1.60/0.60  % (11964)------------------------------
% 1.60/0.60  % (11964)------------------------------
% 1.60/0.60  % (11973)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 1.60/0.60  % (11953)Success in time 0.234 s
%------------------------------------------------------------------------------
