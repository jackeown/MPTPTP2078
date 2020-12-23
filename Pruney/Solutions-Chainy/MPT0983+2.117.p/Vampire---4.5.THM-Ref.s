%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:01:51 EST 2020

% Result     : Theorem 1.66s
% Output     : Refutation 1.66s
% Verified   : 
% Statistics : Number of formulae       :  178 ( 626 expanded)
%              Number of leaves         :   33 ( 197 expanded)
%              Depth                    :   22
%              Number of atoms          :  571 (4104 expanded)
%              Number of equality atoms :   87 ( 169 expanded)
%              Maximal formula depth    :   15 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1042,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f116,f133,f151,f164,f799,f812,f825,f858,f901,f1006,f1039])).

fof(f1039,plain,
    ( spl4_2
    | ~ spl4_49 ),
    inference(avatar_contradiction_clause,[],[f1038])).

fof(f1038,plain,
    ( $false
    | spl4_2
    | ~ spl4_49 ),
    inference(subsumption_resolution,[],[f1037,f157])).

fof(f157,plain,(
    v1_relat_1(sK3) ),
    inference(subsumption_resolution,[],[f153,f75])).

fof(f75,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f153,plain,
    ( v1_relat_1(sK3)
    | ~ v1_relat_1(k2_zfmisc_1(sK1,sK0)) ),
    inference(resolution,[],[f74,f59])).

fof(f59,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,
    ( ( ~ v2_funct_2(sK3,sK0)
      | ~ v2_funct_1(sK2) )
    & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0))
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    & v1_funct_2(sK3,sK1,sK0)
    & v1_funct_1(sK3)
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    & v1_funct_2(sK2,sK0,sK1)
    & v1_funct_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f25,f45,f44])).

fof(f44,plain,
    ( ? [X0,X1,X2] :
        ( ? [X3] :
            ( ( ~ v2_funct_2(X3,X0)
              | ~ v2_funct_1(X2) )
            & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
            & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
            & v1_funct_2(X3,X1,X0)
            & v1_funct_1(X3) )
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
   => ( ? [X3] :
          ( ( ~ v2_funct_2(X3,sK0)
            | ~ v2_funct_1(sK2) )
          & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,X3),k6_partfun1(sK0))
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
          & v1_funct_2(X3,sK1,sK0)
          & v1_funct_1(X3) )
      & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      & v1_funct_2(sK2,sK0,sK1)
      & v1_funct_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f45,plain,
    ( ? [X3] :
        ( ( ~ v2_funct_2(X3,sK0)
          | ~ v2_funct_1(sK2) )
        & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,X3),k6_partfun1(sK0))
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
        & v1_funct_2(X3,sK1,sK0)
        & v1_funct_1(X3) )
   => ( ( ~ v2_funct_2(sK3,sK0)
        | ~ v2_funct_1(sK2) )
      & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0))
      & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
      & v1_funct_2(sK3,sK1,sK0)
      & v1_funct_1(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( ( ~ v2_funct_2(X3,X0)
            | ~ v2_funct_1(X2) )
          & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
          & v1_funct_2(X3,X1,X0)
          & v1_funct_1(X3) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( ( ~ v2_funct_2(X3,X0)
            | ~ v2_funct_1(X2) )
          & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
          & v1_funct_2(X3,X1,X0)
          & v1_funct_1(X3) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f23,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) )
       => ! [X3] :
            ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
              & v1_funct_2(X3,X1,X0)
              & v1_funct_1(X3) )
           => ( r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
             => ( v2_funct_2(X3,X0)
                & v2_funct_1(X2) ) ) ) ) ),
    inference(negated_conjecture,[],[f22])).

fof(f22,conjecture,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ! [X3] :
          ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
            & v1_funct_2(X3,X1,X0)
            & v1_funct_1(X3) )
         => ( r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
           => ( v2_funct_2(X3,X0)
              & v2_funct_1(X2) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_funct_2)).

fof(f74,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

fof(f1037,plain,
    ( ~ v1_relat_1(sK3)
    | spl4_2
    | ~ spl4_49 ),
    inference(subsumption_resolution,[],[f1030,f115])).

fof(f115,plain,
    ( ~ v2_funct_2(sK3,sK0)
    | spl4_2 ),
    inference(avatar_component_clause,[],[f113])).

fof(f113,plain,
    ( spl4_2
  <=> v2_funct_2(sK3,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f1030,plain,
    ( v2_funct_2(sK3,sK0)
    | ~ v1_relat_1(sK3)
    | ~ spl4_49 ),
    inference(superposition,[],[f205,f824])).

fof(f824,plain,
    ( sK0 = k2_relat_1(sK3)
    | ~ spl4_49 ),
    inference(avatar_component_clause,[],[f822])).

fof(f822,plain,
    ( spl4_49
  <=> sK0 = k2_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_49])])).

fof(f205,plain,(
    ! [X1] :
      ( v2_funct_2(X1,k2_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(global_subsumption,[],[f100,f169])).

fof(f169,plain,(
    ! [X0] :
      ( v5_relat_1(X0,k2_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(resolution,[],[f78,f101])).

fof(f101,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f82])).

fof(f82,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f78,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k2_relat_1(X1),X0)
      | v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ( ( v5_relat_1(X1,X0)
          | ~ r1_tarski(k2_relat_1(X1),X0) )
        & ( r1_tarski(k2_relat_1(X1),X0)
          | ~ v5_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).

fof(f100,plain,(
    ! [X1] :
      ( v2_funct_2(X1,k2_relat_1(X1))
      | ~ v5_relat_1(X1,k2_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(equality_resolution,[],[f80])).

fof(f80,plain,(
    ! [X0,X1] :
      ( v2_funct_2(X1,X0)
      | k2_relat_1(X1) != X0
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ( ( v2_funct_2(X1,X0)
          | k2_relat_1(X1) != X0 )
        & ( k2_relat_1(X1) = X0
          | ~ v2_funct_2(X1,X0) ) )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( v2_funct_2(X1,X0)
      <=> k2_relat_1(X1) = X0 )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( v2_funct_2(X1,X0)
      <=> k2_relat_1(X1) = X0 )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ( v2_funct_2(X1,X0)
      <=> k2_relat_1(X1) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_funct_2)).

fof(f1006,plain,(
    spl4_48 ),
    inference(avatar_contradiction_clause,[],[f1005])).

fof(f1005,plain,
    ( $false
    | spl4_48 ),
    inference(subsumption_resolution,[],[f1004,f157])).

fof(f1004,plain,
    ( ~ v1_relat_1(sK3)
    | spl4_48 ),
    inference(subsumption_resolution,[],[f1003,f196])).

fof(f196,plain,(
    v5_relat_1(sK3,sK0) ),
    inference(resolution,[],[f88,f59])).

fof(f88,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v5_relat_1(X2,X1) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f1003,plain,
    ( ~ v5_relat_1(sK3,sK0)
    | ~ v1_relat_1(sK3)
    | spl4_48 ),
    inference(resolution,[],[f820,f77])).

fof(f77,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(X1),X0)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f820,plain,
    ( ~ r1_tarski(k2_relat_1(sK3),sK0)
    | spl4_48 ),
    inference(avatar_component_clause,[],[f818])).

fof(f818,plain,
    ( spl4_48
  <=> r1_tarski(k2_relat_1(sK3),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_48])])).

fof(f901,plain,
    ( spl4_1
    | ~ spl4_4
    | ~ spl4_8 ),
    inference(avatar_contradiction_clause,[],[f900])).

fof(f900,plain,
    ( $false
    | spl4_1
    | ~ spl4_4
    | ~ spl4_8 ),
    inference(subsumption_resolution,[],[f878,f182])).

fof(f182,plain,
    ( v2_funct_1(k1_xboole_0)
    | ~ spl4_8 ),
    inference(superposition,[],[f96,f174])).

fof(f174,plain,
    ( k1_xboole_0 = k6_partfun1(k1_xboole_0)
    | ~ spl4_8 ),
    inference(resolution,[],[f150,f71])).

fof(f71,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

fof(f150,plain,
    ( v1_xboole_0(k6_partfun1(k1_xboole_0))
    | ~ spl4_8 ),
    inference(avatar_component_clause,[],[f148])).

fof(f148,plain,
    ( spl4_8
  <=> v1_xboole_0(k6_partfun1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).

fof(f96,plain,(
    ! [X0] : v2_funct_1(k6_partfun1(X0)) ),
    inference(definition_unfolding,[],[f66,f64])).

fof(f64,plain,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

fof(f66,plain,(
    ! [X0] : v2_funct_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] :
      ( v2_funct_1(k6_relat_1(X0))
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc4_funct_1)).

fof(f878,plain,
    ( ~ v2_funct_1(k1_xboole_0)
    | spl4_1
    | ~ spl4_4 ),
    inference(backward_demodulation,[],[f111,f871])).

fof(f871,plain,
    ( k1_xboole_0 = sK2
    | ~ spl4_4 ),
    inference(resolution,[],[f132,f71])).

fof(f132,plain,
    ( v1_xboole_0(sK2)
    | ~ spl4_4 ),
    inference(avatar_component_clause,[],[f130])).

fof(f130,plain,
    ( spl4_4
  <=> v1_xboole_0(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f111,plain,
    ( ~ v2_funct_1(sK2)
    | spl4_1 ),
    inference(avatar_component_clause,[],[f109])).

fof(f109,plain,
    ( spl4_1
  <=> v2_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f858,plain,
    ( spl4_3
    | ~ spl4_7
    | ~ spl4_46 ),
    inference(avatar_contradiction_clause,[],[f857])).

fof(f857,plain,
    ( $false
    | spl4_3
    | ~ spl4_7
    | ~ spl4_46 ),
    inference(subsumption_resolution,[],[f856,f145])).

fof(f145,plain,
    ( v1_xboole_0(k1_xboole_0)
    | ~ spl4_7 ),
    inference(avatar_component_clause,[],[f144])).

fof(f144,plain,
    ( spl4_7
  <=> v1_xboole_0(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).

fof(f856,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | spl4_3
    | ~ spl4_46 ),
    inference(forward_demodulation,[],[f837,f104])).

fof(f104,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f85])).

fof(f85,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f837,plain,
    ( ~ v1_xboole_0(k2_zfmisc_1(k1_xboole_0,sK1))
    | spl4_3
    | ~ spl4_46 ),
    inference(backward_demodulation,[],[f128,f794])).

fof(f794,plain,
    ( k1_xboole_0 = sK0
    | ~ spl4_46 ),
    inference(avatar_component_clause,[],[f792])).

fof(f792,plain,
    ( spl4_46
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_46])])).

fof(f128,plain,
    ( ~ v1_xboole_0(k2_zfmisc_1(sK0,sK1))
    | spl4_3 ),
    inference(avatar_component_clause,[],[f126])).

fof(f126,plain,
    ( spl4_3
  <=> v1_xboole_0(k2_zfmisc_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f825,plain,
    ( ~ spl4_48
    | spl4_49 ),
    inference(avatar_split_clause,[],[f816,f822,f818])).

fof(f816,plain,
    ( sK0 = k2_relat_1(sK3)
    | ~ r1_tarski(k2_relat_1(sK3),sK0) ),
    inference(forward_demodulation,[],[f815,f98])).

fof(f98,plain,(
    ! [X0] : k2_relat_1(k6_partfun1(X0)) = X0 ),
    inference(definition_unfolding,[],[f70,f64])).

fof(f70,plain,(
    ! [X0] : k2_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

fof(f815,plain,
    ( ~ r1_tarski(k2_relat_1(sK3),sK0)
    | k2_relat_1(sK3) = k2_relat_1(k6_partfun1(sK0)) ),
    inference(forward_demodulation,[],[f814,f98])).

fof(f814,plain,
    ( ~ r1_tarski(k2_relat_1(sK3),k2_relat_1(k6_partfun1(sK0)))
    | k2_relat_1(sK3) = k2_relat_1(k6_partfun1(sK0)) ),
    inference(subsumption_resolution,[],[f813,f157])).

fof(f813,plain,
    ( ~ r1_tarski(k2_relat_1(sK3),k2_relat_1(k6_partfun1(sK0)))
    | k2_relat_1(sK3) = k2_relat_1(k6_partfun1(sK0))
    | ~ v1_relat_1(sK3) ),
    inference(subsumption_resolution,[],[f808,f156])).

fof(f156,plain,(
    v1_relat_1(sK2) ),
    inference(subsumption_resolution,[],[f152,f75])).

fof(f152,plain,
    ( v1_relat_1(sK2)
    | ~ v1_relat_1(k2_zfmisc_1(sK0,sK1)) ),
    inference(resolution,[],[f74,f56])).

fof(f56,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f46])).

fof(f808,plain,
    ( ~ r1_tarski(k2_relat_1(sK3),k2_relat_1(k6_partfun1(sK0)))
    | ~ v1_relat_1(sK2)
    | k2_relat_1(sK3) = k2_relat_1(k6_partfun1(sK0))
    | ~ v1_relat_1(sK3) ),
    inference(superposition,[],[f211,f802])).

fof(f802,plain,(
    k6_partfun1(sK0) = k5_relat_1(sK2,sK3) ),
    inference(global_subsumption,[],[f779,f801])).

fof(f801,plain,
    ( k6_partfun1(sK0) = k5_relat_1(sK2,sK3)
    | ~ m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(resolution,[],[f767,f255])).

fof(f255,plain,(
    ! [X2,X3] :
      ( ~ r2_relset_1(X2,X2,X3,k6_partfun1(X2))
      | k6_partfun1(X2) = X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X2))) ) ),
    inference(resolution,[],[f91,f68])).

fof(f68,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0] :
      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v1_partfun1(k6_partfun1(X0),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_partfun1)).

fof(f91,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r2_relset_1(X0,X1,X2,X3)
      | X2 = X3
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f53,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( r2_relset_1(X0,X1,X2,X3)
          | X2 != X3 )
        & ( X2 = X3
          | ~ r2_relset_1(X0,X1,X2,X3) ) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(nnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f38])).

fof(f38,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

fof(f767,plain,(
    r2_relset_1(sK0,sK0,k5_relat_1(sK2,sK3),k6_partfun1(sK0)) ),
    inference(backward_demodulation,[],[f60,f554])).

fof(f554,plain,(
    k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3) ),
    inference(subsumption_resolution,[],[f548,f54])).

fof(f54,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f46])).

fof(f548,plain,
    ( k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3)
    | ~ v1_funct_1(sK2) ),
    inference(resolution,[],[f284,f56])).

fof(f284,plain,(
    ! [X4,X5,X3] :
      ( ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))
      | k1_partfun1(X3,X4,sK1,sK0,X5,sK3) = k5_relat_1(X5,sK3)
      | ~ v1_funct_1(X5) ) ),
    inference(subsumption_resolution,[],[f279,f57])).

fof(f57,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f46])).

fof(f279,plain,(
    ! [X4,X5,X3] :
      ( k1_partfun1(X3,X4,sK1,sK0,X5,sK3) = k5_relat_1(X5,sK3)
      | ~ v1_funct_1(sK3)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))
      | ~ v1_funct_1(X5) ) ),
    inference(resolution,[],[f93,f59])).

fof(f93,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f40])).

fof(f40,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

fof(f60,plain,(
    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) ),
    inference(cnf_transformation,[],[f46])).

fof(f779,plain,(
    m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(subsumption_resolution,[],[f778,f54])).

fof(f778,plain,
    ( m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_1(sK2) ),
    inference(subsumption_resolution,[],[f777,f56])).

fof(f777,plain,
    ( m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK2) ),
    inference(subsumption_resolution,[],[f776,f57])).

fof(f776,plain,
    ( m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_1(sK3)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK2) ),
    inference(subsumption_resolution,[],[f769,f59])).

fof(f769,plain,
    ( m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_1(sK3)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK2) ),
    inference(superposition,[],[f95,f554])).

fof(f95,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f42])).

fof(f42,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_partfun1)).

fof(f211,plain,(
    ! [X2,X3] :
      ( ~ r1_tarski(k2_relat_1(X2),k2_relat_1(k5_relat_1(X3,X2)))
      | ~ v1_relat_1(X3)
      | k2_relat_1(X2) = k2_relat_1(k5_relat_1(X3,X2))
      | ~ v1_relat_1(X2) ) ),
    inference(resolution,[],[f73,f83])).

fof(f83,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f73,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t45_relat_1)).

fof(f812,plain,(
    spl4_47 ),
    inference(avatar_contradiction_clause,[],[f811])).

fof(f811,plain,
    ( $false
    | spl4_47 ),
    inference(subsumption_resolution,[],[f803,f96])).

fof(f803,plain,
    ( ~ v2_funct_1(k6_partfun1(sK0))
    | spl4_47 ),
    inference(backward_demodulation,[],[f798,f802])).

fof(f798,plain,
    ( ~ v2_funct_1(k5_relat_1(sK2,sK3))
    | spl4_47 ),
    inference(avatar_component_clause,[],[f796])).

fof(f796,plain,
    ( spl4_47
  <=> v2_funct_1(k5_relat_1(sK2,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_47])])).

fof(f799,plain,
    ( spl4_46
    | ~ spl4_47
    | spl4_1 ),
    inference(avatar_split_clause,[],[f790,f109,f796,f792])).

fof(f790,plain,
    ( ~ v2_funct_1(k5_relat_1(sK2,sK3))
    | k1_xboole_0 = sK0
    | spl4_1 ),
    inference(subsumption_resolution,[],[f789,f54])).

fof(f789,plain,
    ( ~ v2_funct_1(k5_relat_1(sK2,sK3))
    | k1_xboole_0 = sK0
    | ~ v1_funct_1(sK2)
    | spl4_1 ),
    inference(subsumption_resolution,[],[f788,f55])).

fof(f55,plain,(
    v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f46])).

fof(f788,plain,
    ( ~ v2_funct_1(k5_relat_1(sK2,sK3))
    | k1_xboole_0 = sK0
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ v1_funct_1(sK2)
    | spl4_1 ),
    inference(subsumption_resolution,[],[f787,f56])).

fof(f787,plain,
    ( ~ v2_funct_1(k5_relat_1(sK2,sK3))
    | k1_xboole_0 = sK0
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ v1_funct_1(sK2)
    | spl4_1 ),
    inference(subsumption_resolution,[],[f786,f57])).

fof(f786,plain,
    ( ~ v2_funct_1(k5_relat_1(sK2,sK3))
    | k1_xboole_0 = sK0
    | ~ v1_funct_1(sK3)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ v1_funct_1(sK2)
    | spl4_1 ),
    inference(subsumption_resolution,[],[f785,f58])).

fof(f58,plain,(
    v1_funct_2(sK3,sK1,sK0) ),
    inference(cnf_transformation,[],[f46])).

fof(f785,plain,
    ( ~ v2_funct_1(k5_relat_1(sK2,sK3))
    | k1_xboole_0 = sK0
    | ~ v1_funct_2(sK3,sK1,sK0)
    | ~ v1_funct_1(sK3)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ v1_funct_1(sK2)
    | spl4_1 ),
    inference(subsumption_resolution,[],[f784,f59])).

fof(f784,plain,
    ( ~ v2_funct_1(k5_relat_1(sK2,sK3))
    | k1_xboole_0 = sK0
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_2(sK3,sK1,sK0)
    | ~ v1_funct_1(sK3)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ v1_funct_1(sK2)
    | spl4_1 ),
    inference(subsumption_resolution,[],[f771,f111])).

fof(f771,plain,
    ( ~ v2_funct_1(k5_relat_1(sK2,sK3))
    | k1_xboole_0 = sK0
    | v2_funct_1(sK2)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_2(sK3,sK1,sK0)
    | ~ v1_funct_1(sK3)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ v1_funct_1(sK2) ),
    inference(superposition,[],[f89,f554])).

fof(f89,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4))
      | k1_xboole_0 = X2
      | v2_funct_1(X3)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ v1_funct_2(X4,X1,X2)
      | ~ v1_funct_1(X4)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1,X2,X3] :
      ( ! [X4] :
          ( v2_funct_1(X3)
          | ( k1_xboole_0 != X1
            & k1_xboole_0 = X2 )
          | ~ v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4))
          | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
          | ~ v1_funct_2(X4,X1,X2)
          | ~ v1_funct_1(X4) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(flattening,[],[f36])).

fof(f36,plain,(
    ! [X0,X1,X2,X3] :
      ( ! [X4] :
          ( v2_funct_1(X3)
          | ( k1_xboole_0 != X1
            & k1_xboole_0 = X2 )
          | ~ v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4))
          | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
          | ~ v1_funct_2(X4,X1,X2)
          | ~ v1_funct_1(X4) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
     => ! [X4] :
          ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
            & v1_funct_2(X4,X1,X2)
            & v1_funct_1(X4) )
         => ( v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4))
           => ( v2_funct_1(X3)
              | ( k1_xboole_0 != X1
                & k1_xboole_0 = X2 ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t26_funct_2)).

fof(f164,plain,(
    spl4_7 ),
    inference(avatar_contradiction_clause,[],[f163])).

fof(f163,plain,
    ( $false
    | spl4_7 ),
    inference(subsumption_resolution,[],[f160,f146])).

fof(f146,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | spl4_7 ),
    inference(avatar_component_clause,[],[f144])).

fof(f160,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(resolution,[],[f158,f101])).

fof(f158,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,k1_xboole_0)
      | v1_xboole_0(X0) ) ),
    inference(resolution,[],[f76,f62])).

fof(f62,plain,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).

fof(f76,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X1,X0)
      | ~ r1_tarski(X1,X0)
      | v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X1,X0)
      | ~ r1_tarski(X1,X0)
      | v1_xboole_0(X1) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X1,X0)
      | ~ r1_tarski(X1,X0)
      | v1_xboole_0(X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
     => ~ ( r1_xboole_0(X1,X0)
          & r1_tarski(X1,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_xboole_1)).

fof(f151,plain,
    ( ~ spl4_7
    | spl4_8 ),
    inference(avatar_split_clause,[],[f124,f148,f144])).

fof(f124,plain,
    ( v1_xboole_0(k6_partfun1(k1_xboole_0))
    | ~ v1_xboole_0(k1_xboole_0) ),
    inference(resolution,[],[f72,f119])).

fof(f119,plain,(
    m1_subset_1(k6_partfun1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) ),
    inference(superposition,[],[f68,f103])).

fof(f103,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f86])).

fof(f86,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f52])).

fof(f72,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | v1_xboole_0(X1)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_xboole_0(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_subset_1)).

fof(f133,plain,
    ( ~ spl4_3
    | spl4_4 ),
    inference(avatar_split_clause,[],[f121,f130,f126])).

fof(f121,plain,
    ( v1_xboole_0(sK2)
    | ~ v1_xboole_0(k2_zfmisc_1(sK0,sK1)) ),
    inference(resolution,[],[f72,f56])).

fof(f116,plain,
    ( ~ spl4_1
    | ~ spl4_2 ),
    inference(avatar_split_clause,[],[f61,f113,f109])).

fof(f61,plain,
    ( ~ v2_funct_2(sK3,sK0)
    | ~ v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f46])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n021.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 16:48:04 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.50  % (30417)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 0.21/0.51  % (30398)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.21/0.51  % (30400)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.21/0.52  % (30415)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 0.21/0.52  % (30425)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 0.21/0.52  % (30401)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.21/0.53  % (30407)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.21/0.53  % (30403)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.53  % (30408)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.21/0.53  % (30420)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.21/0.53  % (30399)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.21/0.54  % (30409)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.21/0.54  % (30412)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.21/0.54  % (30426)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 0.21/0.54  % (30414)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 0.21/0.54  % (30427)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.21/0.54  % (30418)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 0.21/0.54  % (30402)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.21/0.54  % (30413)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.21/0.54  % (30421)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.21/0.54  % (30408)Refutation not found, incomplete strategy% (30408)------------------------------
% 0.21/0.54  % (30408)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (30408)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (30408)Memory used [KB]: 10874
% 0.21/0.54  % (30408)Time elapsed: 0.121 s
% 0.21/0.54  % (30408)------------------------------
% 0.21/0.54  % (30408)------------------------------
% 0.21/0.55  % (30424)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 0.21/0.55  % (30416)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 0.21/0.55  % (30419)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 0.21/0.55  % (30405)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.21/0.55  % (30426)Refutation not found, incomplete strategy% (30426)------------------------------
% 0.21/0.55  % (30426)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (30411)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 1.49/0.55  % (30404)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.49/0.55  % (30426)Termination reason: Refutation not found, incomplete strategy
% 1.49/0.55  
% 1.49/0.55  % (30426)Memory used [KB]: 10874
% 1.49/0.55  % (30426)Time elapsed: 0.139 s
% 1.49/0.55  % (30426)------------------------------
% 1.49/0.55  % (30426)------------------------------
% 1.49/0.55  % (30423)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 1.49/0.55  % (30410)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 1.49/0.56  % (30406)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 1.49/0.56  % (30422)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 1.66/0.57  % (30414)Refutation not found, incomplete strategy% (30414)------------------------------
% 1.66/0.57  % (30414)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.66/0.57  % (30414)Termination reason: Refutation not found, incomplete strategy
% 1.66/0.57  
% 1.66/0.57  % (30414)Memory used [KB]: 10746
% 1.66/0.57  % (30414)Time elapsed: 0.166 s
% 1.66/0.57  % (30414)------------------------------
% 1.66/0.57  % (30414)------------------------------
% 1.66/0.58  % (30404)Refutation found. Thanks to Tanya!
% 1.66/0.58  % SZS status Theorem for theBenchmark
% 1.66/0.58  % SZS output start Proof for theBenchmark
% 1.66/0.58  fof(f1042,plain,(
% 1.66/0.58    $false),
% 1.66/0.58    inference(avatar_sat_refutation,[],[f116,f133,f151,f164,f799,f812,f825,f858,f901,f1006,f1039])).
% 1.66/0.58  fof(f1039,plain,(
% 1.66/0.58    spl4_2 | ~spl4_49),
% 1.66/0.58    inference(avatar_contradiction_clause,[],[f1038])).
% 1.66/0.58  fof(f1038,plain,(
% 1.66/0.58    $false | (spl4_2 | ~spl4_49)),
% 1.66/0.58    inference(subsumption_resolution,[],[f1037,f157])).
% 1.66/0.58  fof(f157,plain,(
% 1.66/0.58    v1_relat_1(sK3)),
% 1.66/0.58    inference(subsumption_resolution,[],[f153,f75])).
% 1.66/0.58  fof(f75,plain,(
% 1.66/0.58    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 1.66/0.58    inference(cnf_transformation,[],[f10])).
% 1.66/0.58  fof(f10,axiom,(
% 1.66/0.58    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 1.66/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).
% 1.66/0.58  fof(f153,plain,(
% 1.66/0.58    v1_relat_1(sK3) | ~v1_relat_1(k2_zfmisc_1(sK1,sK0))),
% 1.66/0.58    inference(resolution,[],[f74,f59])).
% 1.66/0.58  fof(f59,plain,(
% 1.66/0.58    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 1.66/0.58    inference(cnf_transformation,[],[f46])).
% 1.66/0.58  fof(f46,plain,(
% 1.66/0.58    ((~v2_funct_2(sK3,sK0) | ~v2_funct_1(sK2)) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_2(sK3,sK1,sK0) & v1_funct_1(sK3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2)),
% 1.66/0.58    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f25,f45,f44])).
% 1.66/0.58  fof(f44,plain,(
% 1.66/0.58    ? [X0,X1,X2] : (? [X3] : ((~v2_funct_2(X3,X0) | ~v2_funct_1(X2)) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (? [X3] : ((~v2_funct_2(X3,sK0) | ~v2_funct_1(sK2)) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,X3),k6_partfun1(sK0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_2(X3,sK1,sK0) & v1_funct_1(X3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2))),
% 1.66/0.58    introduced(choice_axiom,[])).
% 1.66/0.58  fof(f45,plain,(
% 1.66/0.58    ? [X3] : ((~v2_funct_2(X3,sK0) | ~v2_funct_1(sK2)) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,X3),k6_partfun1(sK0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_2(X3,sK1,sK0) & v1_funct_1(X3)) => ((~v2_funct_2(sK3,sK0) | ~v2_funct_1(sK2)) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_2(sK3,sK1,sK0) & v1_funct_1(sK3))),
% 1.66/0.58    introduced(choice_axiom,[])).
% 1.66/0.58  fof(f25,plain,(
% 1.66/0.58    ? [X0,X1,X2] : (? [X3] : ((~v2_funct_2(X3,X0) | ~v2_funct_1(X2)) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 1.66/0.58    inference(flattening,[],[f24])).
% 1.66/0.58  fof(f24,plain,(
% 1.66/0.58    ? [X0,X1,X2] : (? [X3] : (((~v2_funct_2(X3,X0) | ~v2_funct_1(X2)) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 1.66/0.58    inference(ennf_transformation,[],[f23])).
% 1.66/0.58  fof(f23,negated_conjecture,(
% 1.66/0.58    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => (r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) => (v2_funct_2(X3,X0) & v2_funct_1(X2)))))),
% 1.66/0.58    inference(negated_conjecture,[],[f22])).
% 1.66/0.58  fof(f22,conjecture,(
% 1.66/0.58    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => (r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) => (v2_funct_2(X3,X0) & v2_funct_1(X2)))))),
% 1.66/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_funct_2)).
% 1.66/0.58  fof(f74,plain,(
% 1.66/0.58    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 1.66/0.58    inference(cnf_transformation,[],[f29])).
% 1.66/0.58  fof(f29,plain,(
% 1.66/0.58    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 1.66/0.58    inference(ennf_transformation,[],[f8])).
% 1.66/0.58  fof(f8,axiom,(
% 1.66/0.58    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 1.66/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).
% 1.66/0.58  fof(f1037,plain,(
% 1.66/0.58    ~v1_relat_1(sK3) | (spl4_2 | ~spl4_49)),
% 1.66/0.58    inference(subsumption_resolution,[],[f1030,f115])).
% 1.66/0.58  fof(f115,plain,(
% 1.66/0.58    ~v2_funct_2(sK3,sK0) | spl4_2),
% 1.66/0.58    inference(avatar_component_clause,[],[f113])).
% 1.66/0.58  fof(f113,plain,(
% 1.66/0.58    spl4_2 <=> v2_funct_2(sK3,sK0)),
% 1.66/0.58    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 1.66/0.58  fof(f1030,plain,(
% 1.66/0.58    v2_funct_2(sK3,sK0) | ~v1_relat_1(sK3) | ~spl4_49),
% 1.66/0.58    inference(superposition,[],[f205,f824])).
% 1.66/0.58  fof(f824,plain,(
% 1.66/0.58    sK0 = k2_relat_1(sK3) | ~spl4_49),
% 1.66/0.58    inference(avatar_component_clause,[],[f822])).
% 1.66/0.59  fof(f822,plain,(
% 1.66/0.59    spl4_49 <=> sK0 = k2_relat_1(sK3)),
% 1.66/0.59    introduced(avatar_definition,[new_symbols(naming,[spl4_49])])).
% 1.66/0.61  fof(f205,plain,(
% 1.66/0.61    ( ! [X1] : (v2_funct_2(X1,k2_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 1.66/0.61    inference(global_subsumption,[],[f100,f169])).
% 1.66/0.61  fof(f169,plain,(
% 1.66/0.61    ( ! [X0] : (v5_relat_1(X0,k2_relat_1(X0)) | ~v1_relat_1(X0)) )),
% 1.66/0.61    inference(resolution,[],[f78,f101])).
% 1.66/0.61  fof(f101,plain,(
% 1.66/0.61    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 1.66/0.61    inference(equality_resolution,[],[f82])).
% 1.66/0.61  fof(f82,plain,(
% 1.66/0.61    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 1.66/0.61    inference(cnf_transformation,[],[f50])).
% 1.66/0.61  fof(f50,plain,(
% 1.66/0.61    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.66/0.61    inference(flattening,[],[f49])).
% 1.66/0.61  fof(f49,plain,(
% 1.66/0.61    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.66/0.61    inference(nnf_transformation,[],[f2])).
% 1.66/0.61  fof(f2,axiom,(
% 1.66/0.61    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.66/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 1.66/0.61  fof(f78,plain,(
% 1.66/0.61    ( ! [X0,X1] : (~r1_tarski(k2_relat_1(X1),X0) | v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 1.66/0.61    inference(cnf_transformation,[],[f47])).
% 1.66/0.61  fof(f47,plain,(
% 1.66/0.61    ! [X0,X1] : (((v5_relat_1(X1,X0) | ~r1_tarski(k2_relat_1(X1),X0)) & (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 1.66/0.61    inference(nnf_transformation,[],[f32])).
% 1.66/0.61  fof(f32,plain,(
% 1.66/0.61    ! [X0,X1] : ((v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 1.66/0.61    inference(ennf_transformation,[],[f9])).
% 1.66/0.61  fof(f9,axiom,(
% 1.66/0.61    ! [X0,X1] : (v1_relat_1(X1) => (v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)))),
% 1.66/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).
% 1.66/0.61  fof(f100,plain,(
% 1.66/0.61    ( ! [X1] : (v2_funct_2(X1,k2_relat_1(X1)) | ~v5_relat_1(X1,k2_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 1.66/0.61    inference(equality_resolution,[],[f80])).
% 1.66/0.61  fof(f80,plain,(
% 1.66/0.61    ( ! [X0,X1] : (v2_funct_2(X1,X0) | k2_relat_1(X1) != X0 | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 1.66/0.61    inference(cnf_transformation,[],[f48])).
% 1.66/0.61  fof(f48,plain,(
% 1.66/0.61    ! [X0,X1] : (((v2_funct_2(X1,X0) | k2_relat_1(X1) != X0) & (k2_relat_1(X1) = X0 | ~v2_funct_2(X1,X0))) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 1.66/0.61    inference(nnf_transformation,[],[f34])).
% 1.66/0.61  fof(f34,plain,(
% 1.66/0.61    ! [X0,X1] : ((v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 1.66/0.61    inference(flattening,[],[f33])).
% 1.66/0.61  fof(f33,plain,(
% 1.66/0.61    ! [X0,X1] : ((v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0) | (~v5_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 1.66/0.61    inference(ennf_transformation,[],[f16])).
% 1.66/0.61  fof(f16,axiom,(
% 1.66/0.61    ! [X0,X1] : ((v5_relat_1(X1,X0) & v1_relat_1(X1)) => (v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0))),
% 1.66/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_funct_2)).
% 1.66/0.61  fof(f1006,plain,(
% 1.66/0.61    spl4_48),
% 1.66/0.61    inference(avatar_contradiction_clause,[],[f1005])).
% 1.66/0.61  fof(f1005,plain,(
% 1.66/0.61    $false | spl4_48),
% 1.66/0.61    inference(subsumption_resolution,[],[f1004,f157])).
% 1.66/0.61  fof(f1004,plain,(
% 1.66/0.61    ~v1_relat_1(sK3) | spl4_48),
% 1.66/0.61    inference(subsumption_resolution,[],[f1003,f196])).
% 1.66/0.61  fof(f196,plain,(
% 1.66/0.61    v5_relat_1(sK3,sK0)),
% 1.66/0.61    inference(resolution,[],[f88,f59])).
% 1.66/0.61  fof(f88,plain,(
% 1.66/0.61    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v5_relat_1(X2,X1)) )),
% 1.66/0.61    inference(cnf_transformation,[],[f35])).
% 1.66/0.61  fof(f35,plain,(
% 1.66/0.61    ! [X0,X1,X2] : ((v5_relat_1(X2,X1) & v4_relat_1(X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.66/0.61    inference(ennf_transformation,[],[f14])).
% 1.66/0.61  fof(f14,axiom,(
% 1.66/0.61    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 1.66/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).
% 1.66/0.61  fof(f1003,plain,(
% 1.66/0.61    ~v5_relat_1(sK3,sK0) | ~v1_relat_1(sK3) | spl4_48),
% 1.66/0.61    inference(resolution,[],[f820,f77])).
% 1.66/0.61  fof(f77,plain,(
% 1.66/0.61    ( ! [X0,X1] : (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 1.66/0.61    inference(cnf_transformation,[],[f47])).
% 1.66/0.61  fof(f820,plain,(
% 1.66/0.61    ~r1_tarski(k2_relat_1(sK3),sK0) | spl4_48),
% 1.66/0.61    inference(avatar_component_clause,[],[f818])).
% 1.66/0.61  fof(f818,plain,(
% 1.66/0.61    spl4_48 <=> r1_tarski(k2_relat_1(sK3),sK0)),
% 1.66/0.61    introduced(avatar_definition,[new_symbols(naming,[spl4_48])])).
% 1.66/0.61  fof(f901,plain,(
% 1.66/0.61    spl4_1 | ~spl4_4 | ~spl4_8),
% 1.66/0.61    inference(avatar_contradiction_clause,[],[f900])).
% 1.66/0.61  fof(f900,plain,(
% 1.66/0.61    $false | (spl4_1 | ~spl4_4 | ~spl4_8)),
% 1.66/0.61    inference(subsumption_resolution,[],[f878,f182])).
% 1.66/0.61  fof(f182,plain,(
% 1.66/0.61    v2_funct_1(k1_xboole_0) | ~spl4_8),
% 1.66/0.61    inference(superposition,[],[f96,f174])).
% 1.66/0.61  fof(f174,plain,(
% 1.66/0.61    k1_xboole_0 = k6_partfun1(k1_xboole_0) | ~spl4_8),
% 1.66/0.61    inference(resolution,[],[f150,f71])).
% 1.66/0.61  fof(f71,plain,(
% 1.66/0.61    ( ! [X0] : (~v1_xboole_0(X0) | k1_xboole_0 = X0) )),
% 1.66/0.61    inference(cnf_transformation,[],[f26])).
% 1.66/0.61  fof(f26,plain,(
% 1.66/0.61    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 1.66/0.61    inference(ennf_transformation,[],[f1])).
% 1.66/0.61  fof(f1,axiom,(
% 1.66/0.61    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 1.66/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).
% 1.66/0.61  fof(f150,plain,(
% 1.66/0.61    v1_xboole_0(k6_partfun1(k1_xboole_0)) | ~spl4_8),
% 1.66/0.61    inference(avatar_component_clause,[],[f148])).
% 1.66/0.61  fof(f148,plain,(
% 1.66/0.61    spl4_8 <=> v1_xboole_0(k6_partfun1(k1_xboole_0))),
% 1.66/0.61    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).
% 1.66/0.61  fof(f96,plain,(
% 1.66/0.61    ( ! [X0] : (v2_funct_1(k6_partfun1(X0))) )),
% 1.66/0.61    inference(definition_unfolding,[],[f66,f64])).
% 1.66/0.61  fof(f64,plain,(
% 1.66/0.61    ( ! [X0] : (k6_relat_1(X0) = k6_partfun1(X0)) )),
% 1.66/0.61    inference(cnf_transformation,[],[f20])).
% 1.66/0.61  fof(f20,axiom,(
% 1.66/0.61    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0)),
% 1.66/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_partfun1)).
% 1.66/0.61  fof(f66,plain,(
% 1.66/0.61    ( ! [X0] : (v2_funct_1(k6_relat_1(X0))) )),
% 1.66/0.61    inference(cnf_transformation,[],[f13])).
% 1.66/0.61  fof(f13,axiom,(
% 1.66/0.61    ! [X0] : (v2_funct_1(k6_relat_1(X0)) & v1_relat_1(k6_relat_1(X0)))),
% 1.66/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc4_funct_1)).
% 1.66/0.61  fof(f878,plain,(
% 1.66/0.61    ~v2_funct_1(k1_xboole_0) | (spl4_1 | ~spl4_4)),
% 1.66/0.61    inference(backward_demodulation,[],[f111,f871])).
% 1.66/0.61  fof(f871,plain,(
% 1.66/0.61    k1_xboole_0 = sK2 | ~spl4_4),
% 1.66/0.61    inference(resolution,[],[f132,f71])).
% 1.66/0.61  fof(f132,plain,(
% 1.66/0.61    v1_xboole_0(sK2) | ~spl4_4),
% 1.66/0.61    inference(avatar_component_clause,[],[f130])).
% 1.66/0.61  fof(f130,plain,(
% 1.66/0.61    spl4_4 <=> v1_xboole_0(sK2)),
% 1.66/0.61    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 1.66/0.61  fof(f111,plain,(
% 1.66/0.61    ~v2_funct_1(sK2) | spl4_1),
% 1.66/0.61    inference(avatar_component_clause,[],[f109])).
% 1.66/0.61  fof(f109,plain,(
% 1.66/0.61    spl4_1 <=> v2_funct_1(sK2)),
% 1.66/0.61    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 1.66/0.61  fof(f858,plain,(
% 1.66/0.61    spl4_3 | ~spl4_7 | ~spl4_46),
% 1.66/0.61    inference(avatar_contradiction_clause,[],[f857])).
% 1.66/0.61  fof(f857,plain,(
% 1.66/0.61    $false | (spl4_3 | ~spl4_7 | ~spl4_46)),
% 1.66/0.61    inference(subsumption_resolution,[],[f856,f145])).
% 1.66/0.61  fof(f145,plain,(
% 1.66/0.61    v1_xboole_0(k1_xboole_0) | ~spl4_7),
% 1.66/0.61    inference(avatar_component_clause,[],[f144])).
% 1.66/0.61  fof(f144,plain,(
% 1.66/0.61    spl4_7 <=> v1_xboole_0(k1_xboole_0)),
% 1.66/0.61    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).
% 1.66/0.61  fof(f856,plain,(
% 1.66/0.61    ~v1_xboole_0(k1_xboole_0) | (spl4_3 | ~spl4_46)),
% 1.66/0.61    inference(forward_demodulation,[],[f837,f104])).
% 1.66/0.61  fof(f104,plain,(
% 1.66/0.61    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 1.66/0.61    inference(equality_resolution,[],[f85])).
% 1.66/0.61  fof(f85,plain,(
% 1.66/0.61    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X0) )),
% 1.66/0.61    inference(cnf_transformation,[],[f52])).
% 1.66/0.61  fof(f52,plain,(
% 1.66/0.61    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 1.66/0.61    inference(flattening,[],[f51])).
% 1.66/0.61  fof(f51,plain,(
% 1.66/0.61    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 1.66/0.61    inference(nnf_transformation,[],[f6])).
% 1.66/0.61  fof(f6,axiom,(
% 1.66/0.61    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 1.66/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 1.66/0.61  fof(f837,plain,(
% 1.66/0.61    ~v1_xboole_0(k2_zfmisc_1(k1_xboole_0,sK1)) | (spl4_3 | ~spl4_46)),
% 1.66/0.61    inference(backward_demodulation,[],[f128,f794])).
% 1.66/0.61  fof(f794,plain,(
% 1.66/0.61    k1_xboole_0 = sK0 | ~spl4_46),
% 1.66/0.61    inference(avatar_component_clause,[],[f792])).
% 1.66/0.61  fof(f792,plain,(
% 1.66/0.61    spl4_46 <=> k1_xboole_0 = sK0),
% 1.66/0.61    introduced(avatar_definition,[new_symbols(naming,[spl4_46])])).
% 1.66/0.61  fof(f128,plain,(
% 1.66/0.61    ~v1_xboole_0(k2_zfmisc_1(sK0,sK1)) | spl4_3),
% 1.66/0.61    inference(avatar_component_clause,[],[f126])).
% 1.66/0.61  fof(f126,plain,(
% 1.66/0.61    spl4_3 <=> v1_xboole_0(k2_zfmisc_1(sK0,sK1))),
% 1.66/0.61    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 1.66/0.61  fof(f825,plain,(
% 1.66/0.61    ~spl4_48 | spl4_49),
% 1.66/0.61    inference(avatar_split_clause,[],[f816,f822,f818])).
% 1.66/0.61  fof(f816,plain,(
% 1.66/0.61    sK0 = k2_relat_1(sK3) | ~r1_tarski(k2_relat_1(sK3),sK0)),
% 1.66/0.61    inference(forward_demodulation,[],[f815,f98])).
% 1.66/0.61  fof(f98,plain,(
% 1.66/0.61    ( ! [X0] : (k2_relat_1(k6_partfun1(X0)) = X0) )),
% 1.66/0.61    inference(definition_unfolding,[],[f70,f64])).
% 1.66/0.61  fof(f70,plain,(
% 1.66/0.61    ( ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0) )),
% 1.66/0.61    inference(cnf_transformation,[],[f12])).
% 1.66/0.61  fof(f12,axiom,(
% 1.66/0.61    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 1.66/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).
% 1.66/0.61  fof(f815,plain,(
% 1.66/0.61    ~r1_tarski(k2_relat_1(sK3),sK0) | k2_relat_1(sK3) = k2_relat_1(k6_partfun1(sK0))),
% 1.66/0.61    inference(forward_demodulation,[],[f814,f98])).
% 1.66/0.61  fof(f814,plain,(
% 1.66/0.61    ~r1_tarski(k2_relat_1(sK3),k2_relat_1(k6_partfun1(sK0))) | k2_relat_1(sK3) = k2_relat_1(k6_partfun1(sK0))),
% 1.66/0.61    inference(subsumption_resolution,[],[f813,f157])).
% 1.66/0.61  fof(f813,plain,(
% 1.66/0.61    ~r1_tarski(k2_relat_1(sK3),k2_relat_1(k6_partfun1(sK0))) | k2_relat_1(sK3) = k2_relat_1(k6_partfun1(sK0)) | ~v1_relat_1(sK3)),
% 1.66/0.61    inference(subsumption_resolution,[],[f808,f156])).
% 1.66/0.61  fof(f156,plain,(
% 1.66/0.61    v1_relat_1(sK2)),
% 1.66/0.61    inference(subsumption_resolution,[],[f152,f75])).
% 1.66/0.61  fof(f152,plain,(
% 1.66/0.61    v1_relat_1(sK2) | ~v1_relat_1(k2_zfmisc_1(sK0,sK1))),
% 1.66/0.61    inference(resolution,[],[f74,f56])).
% 1.66/0.61  fof(f56,plain,(
% 1.66/0.61    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 1.66/0.61    inference(cnf_transformation,[],[f46])).
% 1.66/0.61  fof(f808,plain,(
% 1.66/0.61    ~r1_tarski(k2_relat_1(sK3),k2_relat_1(k6_partfun1(sK0))) | ~v1_relat_1(sK2) | k2_relat_1(sK3) = k2_relat_1(k6_partfun1(sK0)) | ~v1_relat_1(sK3)),
% 1.66/0.61    inference(superposition,[],[f211,f802])).
% 1.66/0.61  fof(f802,plain,(
% 1.66/0.61    k6_partfun1(sK0) = k5_relat_1(sK2,sK3)),
% 1.66/0.61    inference(global_subsumption,[],[f779,f801])).
% 1.66/0.62  fof(f801,plain,(
% 1.66/0.62    k6_partfun1(sK0) = k5_relat_1(sK2,sK3) | ~m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 1.66/0.62    inference(resolution,[],[f767,f255])).
% 1.66/0.62  fof(f255,plain,(
% 1.66/0.62    ( ! [X2,X3] : (~r2_relset_1(X2,X2,X3,k6_partfun1(X2)) | k6_partfun1(X2) = X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X2)))) )),
% 1.66/0.62    inference(resolution,[],[f91,f68])).
% 1.66/0.62  fof(f68,plain,(
% 1.66/0.62    ( ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 1.66/0.62    inference(cnf_transformation,[],[f18])).
% 1.66/0.62  fof(f18,axiom,(
% 1.66/0.62    ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_partfun1(k6_partfun1(X0),X0))),
% 1.66/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_partfun1)).
% 1.66/0.62  fof(f91,plain,(
% 1.66/0.62    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r2_relset_1(X0,X1,X2,X3) | X2 = X3 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.66/0.62    inference(cnf_transformation,[],[f53])).
% 1.66/0.62  fof(f53,plain,(
% 1.66/0.62    ! [X0,X1,X2,X3] : (((r2_relset_1(X0,X1,X2,X3) | X2 != X3) & (X2 = X3 | ~r2_relset_1(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.66/0.62    inference(nnf_transformation,[],[f39])).
% 1.66/0.62  fof(f39,plain,(
% 1.66/0.62    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.66/0.62    inference(flattening,[],[f38])).
% 1.66/0.62  fof(f38,plain,(
% 1.66/0.62    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 1.66/0.62    inference(ennf_transformation,[],[f15])).
% 1.66/0.62  fof(f15,axiom,(
% 1.66/0.62    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => (r2_relset_1(X0,X1,X2,X3) <=> X2 = X3))),
% 1.66/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_relset_1)).
% 1.66/0.62  fof(f767,plain,(
% 1.66/0.62    r2_relset_1(sK0,sK0,k5_relat_1(sK2,sK3),k6_partfun1(sK0))),
% 1.66/0.62    inference(backward_demodulation,[],[f60,f554])).
% 1.66/0.62  fof(f554,plain,(
% 1.66/0.62    k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3)),
% 1.66/0.62    inference(subsumption_resolution,[],[f548,f54])).
% 1.66/0.62  fof(f54,plain,(
% 1.66/0.62    v1_funct_1(sK2)),
% 1.66/0.62    inference(cnf_transformation,[],[f46])).
% 1.66/0.62  fof(f548,plain,(
% 1.66/0.62    k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3) | ~v1_funct_1(sK2)),
% 1.66/0.62    inference(resolution,[],[f284,f56])).
% 1.66/0.62  fof(f284,plain,(
% 1.66/0.62    ( ! [X4,X5,X3] : (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) | k1_partfun1(X3,X4,sK1,sK0,X5,sK3) = k5_relat_1(X5,sK3) | ~v1_funct_1(X5)) )),
% 1.66/0.62    inference(subsumption_resolution,[],[f279,f57])).
% 1.66/0.62  fof(f57,plain,(
% 1.66/0.62    v1_funct_1(sK3)),
% 1.66/0.62    inference(cnf_transformation,[],[f46])).
% 1.66/0.62  fof(f279,plain,(
% 1.66/0.62    ( ! [X4,X5,X3] : (k1_partfun1(X3,X4,sK1,sK0,X5,sK3) = k5_relat_1(X5,sK3) | ~v1_funct_1(sK3) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) | ~v1_funct_1(X5)) )),
% 1.66/0.62    inference(resolution,[],[f93,f59])).
% 1.66/0.62  fof(f93,plain,(
% 1.66/0.62    ( ! [X4,X2,X0,X5,X3,X1] : (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 1.66/0.62    inference(cnf_transformation,[],[f41])).
% 1.66/0.62  fof(f41,plain,(
% 1.66/0.62    ! [X0,X1,X2,X3,X4,X5] : (k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 1.66/0.62    inference(flattening,[],[f40])).
% 1.66/0.62  fof(f40,plain,(
% 1.66/0.62    ! [X0,X1,X2,X3,X4,X5] : (k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 1.66/0.62    inference(ennf_transformation,[],[f19])).
% 1.66/0.62  fof(f19,axiom,(
% 1.66/0.62    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5))),
% 1.66/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_partfun1)).
% 1.66/0.62  fof(f60,plain,(
% 1.66/0.62    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0))),
% 1.66/0.62    inference(cnf_transformation,[],[f46])).
% 1.66/0.62  fof(f779,plain,(
% 1.66/0.62    m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 1.66/0.62    inference(subsumption_resolution,[],[f778,f54])).
% 1.66/0.62  fof(f778,plain,(
% 1.66/0.62    m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~v1_funct_1(sK2)),
% 1.66/0.62    inference(subsumption_resolution,[],[f777,f56])).
% 1.66/0.62  fof(f777,plain,(
% 1.66/0.62    m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(sK2)),
% 1.66/0.62    inference(subsumption_resolution,[],[f776,f57])).
% 1.66/0.62  fof(f776,plain,(
% 1.66/0.62    m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~v1_funct_1(sK3) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(sK2)),
% 1.66/0.62    inference(subsumption_resolution,[],[f769,f59])).
% 1.66/0.62  fof(f769,plain,(
% 1.66/0.62    m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_1(sK3) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(sK2)),
% 1.66/0.62    inference(superposition,[],[f95,f554])).
% 1.66/0.62  fof(f95,plain,(
% 1.66/0.62    ( ! [X4,X2,X0,X5,X3,X1] : (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 1.66/0.62    inference(cnf_transformation,[],[f43])).
% 1.66/0.62  fof(f43,plain,(
% 1.66/0.62    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 1.66/0.62    inference(flattening,[],[f42])).
% 1.66/0.62  fof(f42,plain,(
% 1.66/0.62    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 1.66/0.62    inference(ennf_transformation,[],[f17])).
% 1.66/0.62  fof(f17,axiom,(
% 1.66/0.62    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))))),
% 1.66/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_partfun1)).
% 1.66/0.62  fof(f211,plain,(
% 1.66/0.62    ( ! [X2,X3] : (~r1_tarski(k2_relat_1(X2),k2_relat_1(k5_relat_1(X3,X2))) | ~v1_relat_1(X3) | k2_relat_1(X2) = k2_relat_1(k5_relat_1(X3,X2)) | ~v1_relat_1(X2)) )),
% 1.66/0.62    inference(resolution,[],[f73,f83])).
% 1.66/0.62  fof(f83,plain,(
% 1.66/0.62    ( ! [X0,X1] : (~r1_tarski(X1,X0) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 1.66/0.62    inference(cnf_transformation,[],[f50])).
% 1.66/0.62  fof(f73,plain,(
% 1.66/0.62    ( ! [X0,X1] : (r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 1.66/0.62    inference(cnf_transformation,[],[f28])).
% 1.66/0.62  fof(f28,plain,(
% 1.66/0.62    ! [X0] : (! [X1] : (r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 1.66/0.62    inference(ennf_transformation,[],[f11])).
% 1.66/0.62  fof(f11,axiom,(
% 1.66/0.62    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1))))),
% 1.66/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t45_relat_1)).
% 1.66/0.62  fof(f812,plain,(
% 1.66/0.62    spl4_47),
% 1.66/0.62    inference(avatar_contradiction_clause,[],[f811])).
% 1.66/0.62  fof(f811,plain,(
% 1.66/0.62    $false | spl4_47),
% 1.66/0.62    inference(subsumption_resolution,[],[f803,f96])).
% 1.66/0.62  fof(f803,plain,(
% 1.66/0.62    ~v2_funct_1(k6_partfun1(sK0)) | spl4_47),
% 1.66/0.62    inference(backward_demodulation,[],[f798,f802])).
% 1.66/0.62  fof(f798,plain,(
% 1.66/0.62    ~v2_funct_1(k5_relat_1(sK2,sK3)) | spl4_47),
% 1.66/0.62    inference(avatar_component_clause,[],[f796])).
% 1.66/0.62  fof(f796,plain,(
% 1.66/0.62    spl4_47 <=> v2_funct_1(k5_relat_1(sK2,sK3))),
% 1.66/0.62    introduced(avatar_definition,[new_symbols(naming,[spl4_47])])).
% 1.66/0.62  fof(f799,plain,(
% 1.66/0.62    spl4_46 | ~spl4_47 | spl4_1),
% 1.66/0.62    inference(avatar_split_clause,[],[f790,f109,f796,f792])).
% 1.66/0.62  fof(f790,plain,(
% 1.66/0.62    ~v2_funct_1(k5_relat_1(sK2,sK3)) | k1_xboole_0 = sK0 | spl4_1),
% 1.66/0.62    inference(subsumption_resolution,[],[f789,f54])).
% 1.66/0.62  fof(f789,plain,(
% 1.66/0.62    ~v2_funct_1(k5_relat_1(sK2,sK3)) | k1_xboole_0 = sK0 | ~v1_funct_1(sK2) | spl4_1),
% 1.66/0.62    inference(subsumption_resolution,[],[f788,f55])).
% 1.66/0.62  fof(f55,plain,(
% 1.66/0.62    v1_funct_2(sK2,sK0,sK1)),
% 1.66/0.62    inference(cnf_transformation,[],[f46])).
% 1.66/0.62  fof(f788,plain,(
% 1.66/0.62    ~v2_funct_1(k5_relat_1(sK2,sK3)) | k1_xboole_0 = sK0 | ~v1_funct_2(sK2,sK0,sK1) | ~v1_funct_1(sK2) | spl4_1),
% 1.66/0.62    inference(subsumption_resolution,[],[f787,f56])).
% 1.66/0.62  fof(f787,plain,(
% 1.66/0.62    ~v2_funct_1(k5_relat_1(sK2,sK3)) | k1_xboole_0 = sK0 | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_2(sK2,sK0,sK1) | ~v1_funct_1(sK2) | spl4_1),
% 1.66/0.62    inference(subsumption_resolution,[],[f786,f57])).
% 1.66/0.62  fof(f786,plain,(
% 1.66/0.62    ~v2_funct_1(k5_relat_1(sK2,sK3)) | k1_xboole_0 = sK0 | ~v1_funct_1(sK3) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_2(sK2,sK0,sK1) | ~v1_funct_1(sK2) | spl4_1),
% 1.66/0.62    inference(subsumption_resolution,[],[f785,f58])).
% 1.66/0.62  fof(f58,plain,(
% 1.66/0.62    v1_funct_2(sK3,sK1,sK0)),
% 1.66/0.62    inference(cnf_transformation,[],[f46])).
% 1.66/0.62  fof(f785,plain,(
% 1.66/0.62    ~v2_funct_1(k5_relat_1(sK2,sK3)) | k1_xboole_0 = sK0 | ~v1_funct_2(sK3,sK1,sK0) | ~v1_funct_1(sK3) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_2(sK2,sK0,sK1) | ~v1_funct_1(sK2) | spl4_1),
% 1.66/0.62    inference(subsumption_resolution,[],[f784,f59])).
% 1.66/0.62  fof(f784,plain,(
% 1.66/0.62    ~v2_funct_1(k5_relat_1(sK2,sK3)) | k1_xboole_0 = sK0 | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_2(sK3,sK1,sK0) | ~v1_funct_1(sK3) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_2(sK2,sK0,sK1) | ~v1_funct_1(sK2) | spl4_1),
% 1.66/0.62    inference(subsumption_resolution,[],[f771,f111])).
% 1.66/0.62  fof(f771,plain,(
% 1.66/0.62    ~v2_funct_1(k5_relat_1(sK2,sK3)) | k1_xboole_0 = sK0 | v2_funct_1(sK2) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_2(sK3,sK1,sK0) | ~v1_funct_1(sK3) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_2(sK2,sK0,sK1) | ~v1_funct_1(sK2)),
% 1.66/0.62    inference(superposition,[],[f89,f554])).
% 1.66/0.62  fof(f89,plain,(
% 1.66/0.62    ( ! [X4,X2,X0,X3,X1] : (~v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)) | k1_xboole_0 = X2 | v2_funct_1(X3) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X4,X1,X2) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) )),
% 1.66/0.62    inference(cnf_transformation,[],[f37])).
% 1.66/0.62  fof(f37,plain,(
% 1.66/0.62    ! [X0,X1,X2,X3] : (! [X4] : (v2_funct_1(X3) | (k1_xboole_0 != X1 & k1_xboole_0 = X2) | ~v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X4,X1,X2) | ~v1_funct_1(X4)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3))),
% 1.66/0.62    inference(flattening,[],[f36])).
% 1.66/0.62  fof(f36,plain,(
% 1.66/0.62    ! [X0,X1,X2,X3] : (! [X4] : (((v2_funct_1(X3) | (k1_xboole_0 != X1 & k1_xboole_0 = X2)) | ~v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4))) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X4,X1,X2) | ~v1_funct_1(X4))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)))),
% 1.66/0.62    inference(ennf_transformation,[],[f21])).
% 1.66/0.62  fof(f21,axiom,(
% 1.66/0.62    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X4,X1,X2) & v1_funct_1(X4)) => (v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)) => (v2_funct_1(X3) | (k1_xboole_0 != X1 & k1_xboole_0 = X2)))))),
% 1.66/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t26_funct_2)).
% 1.66/0.62  fof(f164,plain,(
% 1.66/0.62    spl4_7),
% 1.66/0.62    inference(avatar_contradiction_clause,[],[f163])).
% 1.66/0.62  fof(f163,plain,(
% 1.66/0.62    $false | spl4_7),
% 1.66/0.62    inference(subsumption_resolution,[],[f160,f146])).
% 1.66/0.62  fof(f146,plain,(
% 1.66/0.62    ~v1_xboole_0(k1_xboole_0) | spl4_7),
% 1.66/0.62    inference(avatar_component_clause,[],[f144])).
% 1.66/0.62  fof(f160,plain,(
% 1.66/0.62    v1_xboole_0(k1_xboole_0)),
% 1.66/0.62    inference(resolution,[],[f158,f101])).
% 1.66/0.62  fof(f158,plain,(
% 1.66/0.62    ( ! [X0] : (~r1_tarski(X0,k1_xboole_0) | v1_xboole_0(X0)) )),
% 1.66/0.62    inference(resolution,[],[f76,f62])).
% 1.66/0.62  fof(f62,plain,(
% 1.66/0.62    ( ! [X0] : (r1_xboole_0(X0,k1_xboole_0)) )),
% 1.66/0.62    inference(cnf_transformation,[],[f4])).
% 1.66/0.62  fof(f4,axiom,(
% 1.66/0.62    ! [X0] : r1_xboole_0(X0,k1_xboole_0)),
% 1.66/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).
% 1.66/0.62  fof(f76,plain,(
% 1.66/0.62    ( ! [X0,X1] : (~r1_xboole_0(X1,X0) | ~r1_tarski(X1,X0) | v1_xboole_0(X1)) )),
% 1.66/0.62    inference(cnf_transformation,[],[f31])).
% 1.66/0.62  fof(f31,plain,(
% 1.66/0.62    ! [X0,X1] : (~r1_xboole_0(X1,X0) | ~r1_tarski(X1,X0) | v1_xboole_0(X1))),
% 1.66/0.62    inference(flattening,[],[f30])).
% 1.66/0.62  fof(f30,plain,(
% 1.66/0.62    ! [X0,X1] : ((~r1_xboole_0(X1,X0) | ~r1_tarski(X1,X0)) | v1_xboole_0(X1))),
% 1.66/0.62    inference(ennf_transformation,[],[f5])).
% 1.66/0.62  fof(f5,axiom,(
% 1.66/0.62    ! [X0,X1] : (~v1_xboole_0(X1) => ~(r1_xboole_0(X1,X0) & r1_tarski(X1,X0)))),
% 1.66/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_xboole_1)).
% 1.66/0.62  fof(f151,plain,(
% 1.66/0.62    ~spl4_7 | spl4_8),
% 1.66/0.62    inference(avatar_split_clause,[],[f124,f148,f144])).
% 1.66/0.62  fof(f124,plain,(
% 1.66/0.62    v1_xboole_0(k6_partfun1(k1_xboole_0)) | ~v1_xboole_0(k1_xboole_0)),
% 1.66/0.62    inference(resolution,[],[f72,f119])).
% 1.66/0.62  fof(f119,plain,(
% 1.66/0.62    m1_subset_1(k6_partfun1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0))),
% 1.66/0.62    inference(superposition,[],[f68,f103])).
% 1.66/0.62  fof(f103,plain,(
% 1.66/0.62    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 1.66/0.62    inference(equality_resolution,[],[f86])).
% 1.66/0.62  fof(f86,plain,(
% 1.66/0.62    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X1) )),
% 1.66/0.62    inference(cnf_transformation,[],[f52])).
% 1.66/0.62  fof(f72,plain,(
% 1.66/0.62    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | v1_xboole_0(X1) | ~v1_xboole_0(X0)) )),
% 1.66/0.62    inference(cnf_transformation,[],[f27])).
% 1.66/0.62  fof(f27,plain,(
% 1.66/0.62    ! [X0] : (! [X1] : (v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_xboole_0(X0))),
% 1.66/0.62    inference(ennf_transformation,[],[f7])).
% 1.66/0.62  fof(f7,axiom,(
% 1.66/0.62    ! [X0] : (v1_xboole_0(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_xboole_0(X1)))),
% 1.66/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_subset_1)).
% 1.66/0.62  fof(f133,plain,(
% 1.66/0.62    ~spl4_3 | spl4_4),
% 1.66/0.62    inference(avatar_split_clause,[],[f121,f130,f126])).
% 1.66/0.62  fof(f121,plain,(
% 1.66/0.62    v1_xboole_0(sK2) | ~v1_xboole_0(k2_zfmisc_1(sK0,sK1))),
% 1.66/0.62    inference(resolution,[],[f72,f56])).
% 1.66/0.62  fof(f116,plain,(
% 1.66/0.62    ~spl4_1 | ~spl4_2),
% 1.66/0.62    inference(avatar_split_clause,[],[f61,f113,f109])).
% 1.66/0.62  fof(f61,plain,(
% 1.66/0.62    ~v2_funct_2(sK3,sK0) | ~v2_funct_1(sK2)),
% 1.66/0.62    inference(cnf_transformation,[],[f46])).
% 1.66/0.62  % SZS output end Proof for theBenchmark
% 1.66/0.62  % (30404)------------------------------
% 1.66/0.62  % (30404)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.66/0.62  % (30404)Termination reason: Refutation
% 1.66/0.62  
% 1.66/0.62  % (30404)Memory used [KB]: 11385
% 1.66/0.62  % (30404)Time elapsed: 0.151 s
% 1.66/0.62  % (30404)------------------------------
% 1.66/0.62  % (30404)------------------------------
% 1.66/0.62  % (30397)Success in time 0.265 s
%------------------------------------------------------------------------------
