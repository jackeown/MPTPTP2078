%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:20:00 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   89 ( 143 expanded)
%              Number of leaves         :   26 (  59 expanded)
%              Depth                    :   10
%              Number of atoms          :  267 ( 512 expanded)
%              Number of equality atoms :   85 ( 139 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f139,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f58,f62,f66,f70,f74,f79,f90,f100,f108,f122,f124,f136,f137,f138])).

fof(f138,plain,
    ( k1_xboole_0 != sK0
    | v1_xboole_0(sK0)
    | ~ v1_xboole_0(k1_xboole_0) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f137,plain,
    ( k1_xboole_0 != sK0
    | r1_tarski(k1_xboole_0,sK1)
    | ~ r1_tarski(sK0,sK1) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f136,plain,
    ( spl3_14
    | ~ spl3_15
    | ~ spl3_7 ),
    inference(avatar_split_clause,[],[f129,f85,f134,f131])).

fof(f131,plain,
    ( spl3_14
  <=> v1_xboole_0(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).

fof(f134,plain,
    ( spl3_15
  <=> r1_tarski(k1_xboole_0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_15])])).

fof(f85,plain,
    ( spl3_7
  <=> r1_xboole_0(k1_xboole_0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f129,plain,
    ( ~ r1_tarski(k1_xboole_0,sK1)
    | v1_xboole_0(k1_xboole_0)
    | ~ spl3_7 ),
    inference(resolution,[],[f86,f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X1,X0)
      | ~ r1_tarski(X1,X0)
      | v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X1,X0)
      | ~ r1_tarski(X1,X0)
      | v1_xboole_0(X1) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X1,X0)
      | ~ r1_tarski(X1,X0)
      | v1_xboole_0(X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
     => ~ ( r1_xboole_0(X1,X0)
          & r1_tarski(X1,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_xboole_1)).

fof(f86,plain,
    ( r1_xboole_0(k1_xboole_0,sK1)
    | ~ spl3_7 ),
    inference(avatar_component_clause,[],[f85])).

fof(f124,plain,
    ( ~ spl3_10
    | ~ spl3_12 ),
    inference(avatar_contradiction_clause,[],[f123])).

fof(f123,plain,
    ( $false
    | ~ spl3_10
    | ~ spl3_12 ),
    inference(subsumption_resolution,[],[f106,f119])).

fof(f119,plain,
    ( ! [X0] : k1_tarski(X0) != sK1
    | ~ spl3_12 ),
    inference(avatar_component_clause,[],[f118])).

fof(f118,plain,
    ( spl3_12
  <=> ! [X0] : k1_tarski(X0) != sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).

fof(f106,plain,
    ( sK1 = k1_tarski(sK2(sK1))
    | ~ spl3_10 ),
    inference(avatar_component_clause,[],[f105])).

fof(f105,plain,
    ( spl3_10
  <=> sK1 = k1_tarski(sK2(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).

fof(f122,plain,
    ( spl3_12
    | spl3_1
    | spl3_8
    | ~ spl3_2 ),
    inference(avatar_split_clause,[],[f116,f60,f88,f56,f118])).

fof(f56,plain,
    ( spl3_1
  <=> sK0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f88,plain,
    ( spl3_8
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).

fof(f60,plain,
    ( spl3_2
  <=> r1_tarski(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f116,plain,
    ( ! [X0] :
        ( k1_xboole_0 = sK0
        | sK0 = sK1
        | k1_tarski(X0) != sK1 )
    | ~ spl3_2 ),
    inference(inner_rewriting,[],[f115])).

fof(f115,plain,
    ( ! [X0] :
        ( k1_xboole_0 = sK0
        | k1_tarski(X0) = sK0
        | k1_tarski(X0) != sK1 )
    | ~ spl3_2 ),
    inference(resolution,[],[f112,f61])).

fof(f61,plain,
    ( r1_tarski(sK0,sK1)
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f60])).

fof(f112,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k1_xboole_0 = X0
      | k1_tarski(X2) = X0
      | k1_tarski(X2) != X1 ) ),
    inference(superposition,[],[f51,f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
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

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( k1_tarski(X0) != k2_xboole_0(X1,X2)
      | k1_xboole_0 = X1
      | k1_tarski(X0) = X1 ) ),
    inference(duplicate_literal_removal,[],[f43])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( k1_tarski(X0) = X1
      | k1_xboole_0 = X1
      | k1_tarski(X0) = X1
      | k1_tarski(X0) != k2_xboole_0(X1,X2) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( ( k1_xboole_0 = X2
        & k1_tarski(X0) = X1 )
      | ( k1_tarski(X0) = X2
        & k1_xboole_0 = X1 )
      | ( k1_tarski(X0) = X2
        & k1_tarski(X0) = X1 )
      | k1_tarski(X0) != k2_xboole_0(X1,X2) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ~ ( ~ ( k1_xboole_0 = X2
            & k1_tarski(X0) = X1 )
        & ~ ( k1_tarski(X0) = X2
            & k1_xboole_0 = X1 )
        & ~ ( k1_tarski(X0) = X2
            & k1_tarski(X0) = X1 )
        & k1_tarski(X0) = k2_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_zfmisc_1)).

fof(f108,plain,
    ( spl3_4
    | ~ spl3_3
    | spl3_10
    | ~ spl3_9 ),
    inference(avatar_split_clause,[],[f102,f97,f105,f64,f68])).

fof(f68,plain,
    ( spl3_4
  <=> v1_xboole_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f64,plain,
    ( spl3_3
  <=> v1_zfmisc_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f97,plain,
    ( spl3_9
  <=> k6_domain_1(sK1,sK2(sK1)) = k1_tarski(sK2(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).

fof(f102,plain,
    ( sK1 = k1_tarski(sK2(sK1))
    | ~ v1_zfmisc_1(sK1)
    | v1_xboole_0(sK1)
    | ~ spl3_9 ),
    inference(superposition,[],[f35,f98])).

fof(f98,plain,
    ( k6_domain_1(sK1,sK2(sK1)) = k1_tarski(sK2(sK1))
    | ~ spl3_9 ),
    inference(avatar_component_clause,[],[f97])).

fof(f35,plain,(
    ! [X0] :
      ( k6_domain_1(X0,sK2(X0)) = X0
      | ~ v1_zfmisc_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ( ( v1_zfmisc_1(X0)
          | ! [X1] :
              ( k6_domain_1(X0,X1) != X0
              | ~ m1_subset_1(X1,X0) ) )
        & ( ( k6_domain_1(X0,sK2(X0)) = X0
            & m1_subset_1(sK2(X0),X0) )
          | ~ v1_zfmisc_1(X0) ) )
      | v1_xboole_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f25,f26])).

fof(f26,plain,(
    ! [X0] :
      ( ? [X2] :
          ( k6_domain_1(X0,X2) = X0
          & m1_subset_1(X2,X0) )
     => ( k6_domain_1(X0,sK2(X0)) = X0
        & m1_subset_1(sK2(X0),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,(
    ! [X0] :
      ( ( ( v1_zfmisc_1(X0)
          | ! [X1] :
              ( k6_domain_1(X0,X1) != X0
              | ~ m1_subset_1(X1,X0) ) )
        & ( ? [X2] :
              ( k6_domain_1(X0,X2) = X0
              & m1_subset_1(X2,X0) )
          | ~ v1_zfmisc_1(X0) ) )
      | v1_xboole_0(X0) ) ),
    inference(rectify,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ( ( v1_zfmisc_1(X0)
          | ! [X1] :
              ( k6_domain_1(X0,X1) != X0
              | ~ m1_subset_1(X1,X0) ) )
        & ( ? [X1] :
              ( k6_domain_1(X0,X1) = X0
              & m1_subset_1(X1,X0) )
          | ~ v1_zfmisc_1(X0) ) )
      | v1_xboole_0(X0) ) ),
    inference(nnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( ( v1_zfmisc_1(X0)
      <=> ? [X1] :
            ( k6_domain_1(X0,X1) = X0
            & m1_subset_1(X1,X0) ) )
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ( v1_zfmisc_1(X0)
      <=> ? [X1] :
            ( k6_domain_1(X0,X1) = X0
            & m1_subset_1(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tex_2)).

fof(f100,plain,
    ( spl3_9
    | spl3_4
    | ~ spl3_3 ),
    inference(avatar_split_clause,[],[f93,f64,f68,f97])).

fof(f93,plain,
    ( v1_xboole_0(sK1)
    | k6_domain_1(sK1,sK2(sK1)) = k1_tarski(sK2(sK1))
    | ~ spl3_3 ),
    inference(resolution,[],[f92,f65])).

fof(f65,plain,
    ( v1_zfmisc_1(sK1)
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f64])).

fof(f92,plain,(
    ! [X0] :
      ( ~ v1_zfmisc_1(X0)
      | v1_xboole_0(X0)
      | k6_domain_1(X0,sK2(X0)) = k1_tarski(sK2(X0)) ) ),
    inference(duplicate_literal_removal,[],[f91])).

fof(f91,plain,(
    ! [X0] :
      ( k6_domain_1(X0,sK2(X0)) = k1_tarski(sK2(X0))
      | v1_xboole_0(X0)
      | ~ v1_zfmisc_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(resolution,[],[f39,f34])).

fof(f34,plain,(
    ! [X0] :
      ( m1_subset_1(sK2(X0),X0)
      | ~ v1_zfmisc_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,X0)
      | k6_domain_1(X0,X1) = k1_tarski(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( k6_domain_1(X0,X1) = k1_tarski(X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( k6_domain_1(X0,X1) = k1_tarski(X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,X0)
        & ~ v1_xboole_0(X0) )
     => k6_domain_1(X0,X1) = k1_tarski(X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

fof(f90,plain,
    ( spl3_7
    | ~ spl3_8
    | ~ spl3_6 ),
    inference(avatar_split_clause,[],[f83,f77,f88,f85])).

fof(f77,plain,
    ( spl3_6
  <=> k1_xboole_0 = k4_xboole_0(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f83,plain,
    ( k1_xboole_0 != sK0
    | r1_xboole_0(k1_xboole_0,sK1)
    | ~ spl3_6 ),
    inference(inner_rewriting,[],[f81])).

fof(f81,plain,
    ( k1_xboole_0 != sK0
    | r1_xboole_0(sK0,sK1)
    | ~ spl3_6 ),
    inference(superposition,[],[f40,f78])).

fof(f78,plain,
    ( k1_xboole_0 = k4_xboole_0(sK0,sK1)
    | ~ spl3_6 ),
    inference(avatar_component_clause,[],[f77])).

fof(f40,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) != X0
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | k4_xboole_0(X0,X1) != X0 ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = X0
     => r1_xboole_0(X0,X1) ) ),
    inference(unused_predicate_definition_removal,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k4_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).

fof(f79,plain,
    ( spl3_6
    | ~ spl3_2 ),
    inference(avatar_split_clause,[],[f75,f60,f77])).

fof(f75,plain,
    ( k1_xboole_0 = k4_xboole_0(sK0,sK1)
    | ~ spl3_2 ),
    inference(resolution,[],[f42,f61])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k4_xboole_0(X0,X1) = k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( k4_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | k4_xboole_0(X0,X1) != k1_xboole_0 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

fof(f74,plain,(
    ~ spl3_5 ),
    inference(avatar_split_clause,[],[f29,f72])).

fof(f72,plain,
    ( spl3_5
  <=> v1_xboole_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f29,plain,(
    ~ v1_xboole_0(sK0) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,
    ( sK0 != sK1
    & r1_tarski(sK0,sK1)
    & v1_zfmisc_1(sK1)
    & ~ v1_xboole_0(sK1)
    & ~ v1_xboole_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f12,f22,f21])).

fof(f21,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( X0 != X1
            & r1_tarski(X0,X1)
            & v1_zfmisc_1(X1)
            & ~ v1_xboole_0(X1) )
        & ~ v1_xboole_0(X0) )
   => ( ? [X1] :
          ( sK0 != X1
          & r1_tarski(sK0,X1)
          & v1_zfmisc_1(X1)
          & ~ v1_xboole_0(X1) )
      & ~ v1_xboole_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,
    ( ? [X1] :
        ( sK0 != X1
        & r1_tarski(sK0,X1)
        & v1_zfmisc_1(X1)
        & ~ v1_xboole_0(X1) )
   => ( sK0 != sK1
      & r1_tarski(sK0,sK1)
      & v1_zfmisc_1(sK1)
      & ~ v1_xboole_0(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f12,plain,(
    ? [X0] :
      ( ? [X1] :
          ( X0 != X1
          & r1_tarski(X0,X1)
          & v1_zfmisc_1(X1)
          & ~ v1_xboole_0(X1) )
      & ~ v1_xboole_0(X0) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ? [X0] :
      ( ? [X1] :
          ( X0 != X1
          & r1_tarski(X0,X1)
          & v1_zfmisc_1(X1)
          & ~ v1_xboole_0(X1) )
      & ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,negated_conjecture,(
    ~ ! [X0] :
        ( ~ v1_xboole_0(X0)
       => ! [X1] :
            ( ( v1_zfmisc_1(X1)
              & ~ v1_xboole_0(X1) )
           => ( r1_tarski(X0,X1)
             => X0 = X1 ) ) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f8,conjecture,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( ( v1_zfmisc_1(X1)
            & ~ v1_xboole_0(X1) )
         => ( r1_tarski(X0,X1)
           => X0 = X1 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_tex_2)).

fof(f70,plain,(
    ~ spl3_4 ),
    inference(avatar_split_clause,[],[f30,f68])).

fof(f30,plain,(
    ~ v1_xboole_0(sK1) ),
    inference(cnf_transformation,[],[f23])).

fof(f66,plain,(
    spl3_3 ),
    inference(avatar_split_clause,[],[f31,f64])).

fof(f31,plain,(
    v1_zfmisc_1(sK1) ),
    inference(cnf_transformation,[],[f23])).

fof(f62,plain,(
    spl3_2 ),
    inference(avatar_split_clause,[],[f32,f60])).

fof(f32,plain,(
    r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f23])).

fof(f58,plain,(
    ~ spl3_1 ),
    inference(avatar_split_clause,[],[f33,f56])).

fof(f33,plain,(
    sK0 != sK1 ),
    inference(cnf_transformation,[],[f23])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 14:13:44 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.44  % (27583)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
% 0.20/0.45  % (27583)Refutation not found, incomplete strategy% (27583)------------------------------
% 0.20/0.45  % (27583)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.45  % (27583)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.45  
% 0.20/0.45  % (27583)Memory used [KB]: 6140
% 0.20/0.45  % (27583)Time elapsed: 0.047 s
% 0.20/0.45  % (27583)------------------------------
% 0.20/0.45  % (27583)------------------------------
% 0.20/0.46  % (27578)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.20/0.47  % (27587)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.20/0.47  % (27573)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.47  % (27573)Refutation not found, incomplete strategy% (27573)------------------------------
% 0.20/0.47  % (27573)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.47  % (27573)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.47  
% 0.20/0.47  % (27573)Memory used [KB]: 10490
% 0.20/0.47  % (27573)Time elapsed: 0.060 s
% 0.20/0.47  % (27573)------------------------------
% 0.20/0.47  % (27573)------------------------------
% 0.20/0.47  % (27586)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.20/0.48  % (27578)Refutation found. Thanks to Tanya!
% 0.20/0.48  % SZS status Theorem for theBenchmark
% 0.20/0.48  % SZS output start Proof for theBenchmark
% 0.20/0.48  fof(f139,plain,(
% 0.20/0.48    $false),
% 0.20/0.48    inference(avatar_sat_refutation,[],[f58,f62,f66,f70,f74,f79,f90,f100,f108,f122,f124,f136,f137,f138])).
% 0.20/0.48  fof(f138,plain,(
% 0.20/0.48    k1_xboole_0 != sK0 | v1_xboole_0(sK0) | ~v1_xboole_0(k1_xboole_0)),
% 0.20/0.48    introduced(theory_tautology_sat_conflict,[])).
% 0.20/0.48  fof(f137,plain,(
% 0.20/0.48    k1_xboole_0 != sK0 | r1_tarski(k1_xboole_0,sK1) | ~r1_tarski(sK0,sK1)),
% 0.20/0.48    introduced(theory_tautology_sat_conflict,[])).
% 0.20/0.48  fof(f136,plain,(
% 0.20/0.48    spl3_14 | ~spl3_15 | ~spl3_7),
% 0.20/0.48    inference(avatar_split_clause,[],[f129,f85,f134,f131])).
% 0.20/0.48  fof(f131,plain,(
% 0.20/0.48    spl3_14 <=> v1_xboole_0(k1_xboole_0)),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).
% 0.20/0.48  fof(f134,plain,(
% 0.20/0.48    spl3_15 <=> r1_tarski(k1_xboole_0,sK1)),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_15])])).
% 0.20/0.48  fof(f85,plain,(
% 0.20/0.48    spl3_7 <=> r1_xboole_0(k1_xboole_0,sK1)),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).
% 0.20/0.48  fof(f129,plain,(
% 0.20/0.48    ~r1_tarski(k1_xboole_0,sK1) | v1_xboole_0(k1_xboole_0) | ~spl3_7),
% 0.20/0.48    inference(resolution,[],[f86,f37])).
% 0.20/0.48  fof(f37,plain,(
% 0.20/0.48    ( ! [X0,X1] : (~r1_xboole_0(X1,X0) | ~r1_tarski(X1,X0) | v1_xboole_0(X1)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f15])).
% 0.20/0.48  fof(f15,plain,(
% 0.20/0.48    ! [X0,X1] : (~r1_xboole_0(X1,X0) | ~r1_tarski(X1,X0) | v1_xboole_0(X1))),
% 0.20/0.48    inference(flattening,[],[f14])).
% 0.20/0.48  fof(f14,plain,(
% 0.20/0.48    ! [X0,X1] : ((~r1_xboole_0(X1,X0) | ~r1_tarski(X1,X0)) | v1_xboole_0(X1))),
% 0.20/0.48    inference(ennf_transformation,[],[f3])).
% 0.20/0.48  fof(f3,axiom,(
% 0.20/0.48    ! [X0,X1] : (~v1_xboole_0(X1) => ~(r1_xboole_0(X1,X0) & r1_tarski(X1,X0)))),
% 0.20/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_xboole_1)).
% 0.20/0.48  fof(f86,plain,(
% 0.20/0.48    r1_xboole_0(k1_xboole_0,sK1) | ~spl3_7),
% 0.20/0.48    inference(avatar_component_clause,[],[f85])).
% 0.20/0.48  fof(f124,plain,(
% 0.20/0.48    ~spl3_10 | ~spl3_12),
% 0.20/0.48    inference(avatar_contradiction_clause,[],[f123])).
% 0.20/0.48  fof(f123,plain,(
% 0.20/0.48    $false | (~spl3_10 | ~spl3_12)),
% 0.20/0.48    inference(subsumption_resolution,[],[f106,f119])).
% 0.20/0.48  fof(f119,plain,(
% 0.20/0.48    ( ! [X0] : (k1_tarski(X0) != sK1) ) | ~spl3_12),
% 0.20/0.48    inference(avatar_component_clause,[],[f118])).
% 0.20/0.48  fof(f118,plain,(
% 0.20/0.48    spl3_12 <=> ! [X0] : k1_tarski(X0) != sK1),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).
% 0.20/0.48  fof(f106,plain,(
% 0.20/0.48    sK1 = k1_tarski(sK2(sK1)) | ~spl3_10),
% 0.20/0.48    inference(avatar_component_clause,[],[f105])).
% 0.20/0.48  fof(f105,plain,(
% 0.20/0.48    spl3_10 <=> sK1 = k1_tarski(sK2(sK1))),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).
% 0.20/0.48  fof(f122,plain,(
% 0.20/0.48    spl3_12 | spl3_1 | spl3_8 | ~spl3_2),
% 0.20/0.48    inference(avatar_split_clause,[],[f116,f60,f88,f56,f118])).
% 0.20/0.48  fof(f56,plain,(
% 0.20/0.48    spl3_1 <=> sK0 = sK1),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.20/0.48  fof(f88,plain,(
% 0.20/0.48    spl3_8 <=> k1_xboole_0 = sK0),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).
% 0.20/0.48  fof(f60,plain,(
% 0.20/0.48    spl3_2 <=> r1_tarski(sK0,sK1)),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.20/0.48  fof(f116,plain,(
% 0.20/0.48    ( ! [X0] : (k1_xboole_0 = sK0 | sK0 = sK1 | k1_tarski(X0) != sK1) ) | ~spl3_2),
% 0.20/0.48    inference(inner_rewriting,[],[f115])).
% 0.20/0.48  fof(f115,plain,(
% 0.20/0.48    ( ! [X0] : (k1_xboole_0 = sK0 | k1_tarski(X0) = sK0 | k1_tarski(X0) != sK1) ) | ~spl3_2),
% 0.20/0.48    inference(resolution,[],[f112,f61])).
% 0.20/0.48  fof(f61,plain,(
% 0.20/0.48    r1_tarski(sK0,sK1) | ~spl3_2),
% 0.20/0.48    inference(avatar_component_clause,[],[f60])).
% 0.20/0.48  fof(f112,plain,(
% 0.20/0.48    ( ! [X2,X0,X1] : (~r1_tarski(X0,X1) | k1_xboole_0 = X0 | k1_tarski(X2) = X0 | k1_tarski(X2) != X1) )),
% 0.20/0.48    inference(superposition,[],[f51,f38])).
% 0.20/0.48  fof(f38,plain,(
% 0.20/0.48    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f16])).
% 0.20/0.48  fof(f16,plain,(
% 0.20/0.48    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 0.20/0.48    inference(ennf_transformation,[],[f2])).
% 0.20/0.48  fof(f2,axiom,(
% 0.20/0.48    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 0.20/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).
% 0.20/0.48  fof(f51,plain,(
% 0.20/0.48    ( ! [X2,X0,X1] : (k1_tarski(X0) != k2_xboole_0(X1,X2) | k1_xboole_0 = X1 | k1_tarski(X0) = X1) )),
% 0.20/0.48    inference(duplicate_literal_removal,[],[f43])).
% 0.20/0.48  fof(f43,plain,(
% 0.20/0.48    ( ! [X2,X0,X1] : (k1_tarski(X0) = X1 | k1_xboole_0 = X1 | k1_tarski(X0) = X1 | k1_tarski(X0) != k2_xboole_0(X1,X2)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f20])).
% 0.20/0.48  fof(f20,plain,(
% 0.20/0.48    ! [X0,X1,X2] : ((k1_xboole_0 = X2 & k1_tarski(X0) = X1) | (k1_tarski(X0) = X2 & k1_xboole_0 = X1) | (k1_tarski(X0) = X2 & k1_tarski(X0) = X1) | k1_tarski(X0) != k2_xboole_0(X1,X2))),
% 0.20/0.48    inference(ennf_transformation,[],[f5])).
% 0.20/0.48  fof(f5,axiom,(
% 0.20/0.48    ! [X0,X1,X2] : ~(~(k1_xboole_0 = X2 & k1_tarski(X0) = X1) & ~(k1_tarski(X0) = X2 & k1_xboole_0 = X1) & ~(k1_tarski(X0) = X2 & k1_tarski(X0) = X1) & k1_tarski(X0) = k2_xboole_0(X1,X2))),
% 0.20/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_zfmisc_1)).
% 0.20/0.48  fof(f108,plain,(
% 0.20/0.48    spl3_4 | ~spl3_3 | spl3_10 | ~spl3_9),
% 0.20/0.48    inference(avatar_split_clause,[],[f102,f97,f105,f64,f68])).
% 0.20/0.48  fof(f68,plain,(
% 0.20/0.48    spl3_4 <=> v1_xboole_0(sK1)),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.20/0.48  fof(f64,plain,(
% 0.20/0.48    spl3_3 <=> v1_zfmisc_1(sK1)),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.20/0.48  fof(f97,plain,(
% 0.20/0.48    spl3_9 <=> k6_domain_1(sK1,sK2(sK1)) = k1_tarski(sK2(sK1))),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).
% 0.20/0.48  fof(f102,plain,(
% 0.20/0.48    sK1 = k1_tarski(sK2(sK1)) | ~v1_zfmisc_1(sK1) | v1_xboole_0(sK1) | ~spl3_9),
% 0.20/0.48    inference(superposition,[],[f35,f98])).
% 0.20/0.48  fof(f98,plain,(
% 0.20/0.48    k6_domain_1(sK1,sK2(sK1)) = k1_tarski(sK2(sK1)) | ~spl3_9),
% 0.20/0.48    inference(avatar_component_clause,[],[f97])).
% 0.20/0.48  fof(f35,plain,(
% 0.20/0.48    ( ! [X0] : (k6_domain_1(X0,sK2(X0)) = X0 | ~v1_zfmisc_1(X0) | v1_xboole_0(X0)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f27])).
% 0.20/0.48  fof(f27,plain,(
% 0.20/0.48    ! [X0] : (((v1_zfmisc_1(X0) | ! [X1] : (k6_domain_1(X0,X1) != X0 | ~m1_subset_1(X1,X0))) & ((k6_domain_1(X0,sK2(X0)) = X0 & m1_subset_1(sK2(X0),X0)) | ~v1_zfmisc_1(X0))) | v1_xboole_0(X0))),
% 0.20/0.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f25,f26])).
% 0.20/0.48  fof(f26,plain,(
% 0.20/0.48    ! [X0] : (? [X2] : (k6_domain_1(X0,X2) = X0 & m1_subset_1(X2,X0)) => (k6_domain_1(X0,sK2(X0)) = X0 & m1_subset_1(sK2(X0),X0)))),
% 0.20/0.48    introduced(choice_axiom,[])).
% 0.20/0.48  fof(f25,plain,(
% 0.20/0.48    ! [X0] : (((v1_zfmisc_1(X0) | ! [X1] : (k6_domain_1(X0,X1) != X0 | ~m1_subset_1(X1,X0))) & (? [X2] : (k6_domain_1(X0,X2) = X0 & m1_subset_1(X2,X0)) | ~v1_zfmisc_1(X0))) | v1_xboole_0(X0))),
% 0.20/0.48    inference(rectify,[],[f24])).
% 0.20/0.48  fof(f24,plain,(
% 0.20/0.48    ! [X0] : (((v1_zfmisc_1(X0) | ! [X1] : (k6_domain_1(X0,X1) != X0 | ~m1_subset_1(X1,X0))) & (? [X1] : (k6_domain_1(X0,X1) = X0 & m1_subset_1(X1,X0)) | ~v1_zfmisc_1(X0))) | v1_xboole_0(X0))),
% 0.20/0.48    inference(nnf_transformation,[],[f13])).
% 0.20/0.48  fof(f13,plain,(
% 0.20/0.48    ! [X0] : ((v1_zfmisc_1(X0) <=> ? [X1] : (k6_domain_1(X0,X1) = X0 & m1_subset_1(X1,X0))) | v1_xboole_0(X0))),
% 0.20/0.48    inference(ennf_transformation,[],[f7])).
% 0.20/0.48  fof(f7,axiom,(
% 0.20/0.48    ! [X0] : (~v1_xboole_0(X0) => (v1_zfmisc_1(X0) <=> ? [X1] : (k6_domain_1(X0,X1) = X0 & m1_subset_1(X1,X0))))),
% 0.20/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tex_2)).
% 0.20/0.48  fof(f100,plain,(
% 0.20/0.48    spl3_9 | spl3_4 | ~spl3_3),
% 0.20/0.48    inference(avatar_split_clause,[],[f93,f64,f68,f97])).
% 0.20/0.48  fof(f93,plain,(
% 0.20/0.48    v1_xboole_0(sK1) | k6_domain_1(sK1,sK2(sK1)) = k1_tarski(sK2(sK1)) | ~spl3_3),
% 0.20/0.48    inference(resolution,[],[f92,f65])).
% 0.20/0.48  fof(f65,plain,(
% 0.20/0.48    v1_zfmisc_1(sK1) | ~spl3_3),
% 0.20/0.48    inference(avatar_component_clause,[],[f64])).
% 0.20/0.48  fof(f92,plain,(
% 0.20/0.48    ( ! [X0] : (~v1_zfmisc_1(X0) | v1_xboole_0(X0) | k6_domain_1(X0,sK2(X0)) = k1_tarski(sK2(X0))) )),
% 0.20/0.48    inference(duplicate_literal_removal,[],[f91])).
% 0.20/0.48  fof(f91,plain,(
% 0.20/0.48    ( ! [X0] : (k6_domain_1(X0,sK2(X0)) = k1_tarski(sK2(X0)) | v1_xboole_0(X0) | ~v1_zfmisc_1(X0) | v1_xboole_0(X0)) )),
% 0.20/0.48    inference(resolution,[],[f39,f34])).
% 0.20/0.48  fof(f34,plain,(
% 0.20/0.48    ( ! [X0] : (m1_subset_1(sK2(X0),X0) | ~v1_zfmisc_1(X0) | v1_xboole_0(X0)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f27])).
% 0.20/0.48  fof(f39,plain,(
% 0.20/0.48    ( ! [X0,X1] : (~m1_subset_1(X1,X0) | k6_domain_1(X0,X1) = k1_tarski(X1) | v1_xboole_0(X0)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f18])).
% 0.20/0.48  fof(f18,plain,(
% 0.20/0.48    ! [X0,X1] : (k6_domain_1(X0,X1) = k1_tarski(X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0))),
% 0.20/0.48    inference(flattening,[],[f17])).
% 0.20/0.48  fof(f17,plain,(
% 0.20/0.48    ! [X0,X1] : (k6_domain_1(X0,X1) = k1_tarski(X1) | (~m1_subset_1(X1,X0) | v1_xboole_0(X0)))),
% 0.20/0.48    inference(ennf_transformation,[],[f6])).
% 0.20/0.48  fof(f6,axiom,(
% 0.20/0.48    ! [X0,X1] : ((m1_subset_1(X1,X0) & ~v1_xboole_0(X0)) => k6_domain_1(X0,X1) = k1_tarski(X1))),
% 0.20/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_domain_1)).
% 0.20/0.48  fof(f90,plain,(
% 0.20/0.48    spl3_7 | ~spl3_8 | ~spl3_6),
% 0.20/0.48    inference(avatar_split_clause,[],[f83,f77,f88,f85])).
% 0.20/0.48  fof(f77,plain,(
% 0.20/0.48    spl3_6 <=> k1_xboole_0 = k4_xboole_0(sK0,sK1)),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 0.20/0.48  fof(f83,plain,(
% 0.20/0.48    k1_xboole_0 != sK0 | r1_xboole_0(k1_xboole_0,sK1) | ~spl3_6),
% 0.20/0.48    inference(inner_rewriting,[],[f81])).
% 0.20/0.48  fof(f81,plain,(
% 0.20/0.48    k1_xboole_0 != sK0 | r1_xboole_0(sK0,sK1) | ~spl3_6),
% 0.20/0.48    inference(superposition,[],[f40,f78])).
% 0.20/0.48  fof(f78,plain,(
% 0.20/0.48    k1_xboole_0 = k4_xboole_0(sK0,sK1) | ~spl3_6),
% 0.20/0.48    inference(avatar_component_clause,[],[f77])).
% 0.20/0.48  fof(f40,plain,(
% 0.20/0.48    ( ! [X0,X1] : (k4_xboole_0(X0,X1) != X0 | r1_xboole_0(X0,X1)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f19])).
% 0.20/0.48  fof(f19,plain,(
% 0.20/0.48    ! [X0,X1] : (r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) != X0)),
% 0.20/0.48    inference(ennf_transformation,[],[f10])).
% 0.20/0.48  fof(f10,plain,(
% 0.20/0.48    ! [X0,X1] : (k4_xboole_0(X0,X1) = X0 => r1_xboole_0(X0,X1))),
% 0.20/0.48    inference(unused_predicate_definition_removal,[],[f4])).
% 0.20/0.48  fof(f4,axiom,(
% 0.20/0.48    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k4_xboole_0(X0,X1) = X0)),
% 0.20/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).
% 0.20/0.48  fof(f79,plain,(
% 0.20/0.48    spl3_6 | ~spl3_2),
% 0.20/0.48    inference(avatar_split_clause,[],[f75,f60,f77])).
% 0.20/0.48  fof(f75,plain,(
% 0.20/0.48    k1_xboole_0 = k4_xboole_0(sK0,sK1) | ~spl3_2),
% 0.20/0.48    inference(resolution,[],[f42,f61])).
% 0.20/0.48  fof(f42,plain,(
% 0.20/0.48    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k4_xboole_0(X0,X1) = k1_xboole_0) )),
% 0.20/0.48    inference(cnf_transformation,[],[f28])).
% 0.20/0.48  fof(f28,plain,(
% 0.20/0.48    ! [X0,X1] : ((k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0))),
% 0.20/0.48    inference(nnf_transformation,[],[f1])).
% 0.20/0.48  fof(f1,axiom,(
% 0.20/0.48    ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 <=> r1_tarski(X0,X1))),
% 0.20/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).
% 0.20/0.48  fof(f74,plain,(
% 0.20/0.48    ~spl3_5),
% 0.20/0.48    inference(avatar_split_clause,[],[f29,f72])).
% 0.20/0.48  fof(f72,plain,(
% 0.20/0.48    spl3_5 <=> v1_xboole_0(sK0)),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 0.20/0.48  fof(f29,plain,(
% 0.20/0.48    ~v1_xboole_0(sK0)),
% 0.20/0.48    inference(cnf_transformation,[],[f23])).
% 0.20/0.48  fof(f23,plain,(
% 0.20/0.48    (sK0 != sK1 & r1_tarski(sK0,sK1) & v1_zfmisc_1(sK1) & ~v1_xboole_0(sK1)) & ~v1_xboole_0(sK0)),
% 0.20/0.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f12,f22,f21])).
% 0.20/0.48  fof(f21,plain,(
% 0.20/0.48    ? [X0] : (? [X1] : (X0 != X1 & r1_tarski(X0,X1) & v1_zfmisc_1(X1) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0)) => (? [X1] : (sK0 != X1 & r1_tarski(sK0,X1) & v1_zfmisc_1(X1) & ~v1_xboole_0(X1)) & ~v1_xboole_0(sK0))),
% 0.20/0.48    introduced(choice_axiom,[])).
% 0.20/0.48  fof(f22,plain,(
% 0.20/0.48    ? [X1] : (sK0 != X1 & r1_tarski(sK0,X1) & v1_zfmisc_1(X1) & ~v1_xboole_0(X1)) => (sK0 != sK1 & r1_tarski(sK0,sK1) & v1_zfmisc_1(sK1) & ~v1_xboole_0(sK1))),
% 0.20/0.48    introduced(choice_axiom,[])).
% 0.20/0.48  fof(f12,plain,(
% 0.20/0.48    ? [X0] : (? [X1] : (X0 != X1 & r1_tarski(X0,X1) & v1_zfmisc_1(X1) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0))),
% 0.20/0.48    inference(flattening,[],[f11])).
% 0.20/0.48  fof(f11,plain,(
% 0.20/0.48    ? [X0] : (? [X1] : ((X0 != X1 & r1_tarski(X0,X1)) & (v1_zfmisc_1(X1) & ~v1_xboole_0(X1))) & ~v1_xboole_0(X0))),
% 0.20/0.48    inference(ennf_transformation,[],[f9])).
% 0.20/0.48  fof(f9,negated_conjecture,(
% 0.20/0.48    ~! [X0] : (~v1_xboole_0(X0) => ! [X1] : ((v1_zfmisc_1(X1) & ~v1_xboole_0(X1)) => (r1_tarski(X0,X1) => X0 = X1)))),
% 0.20/0.48    inference(negated_conjecture,[],[f8])).
% 0.20/0.48  fof(f8,conjecture,(
% 0.20/0.48    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : ((v1_zfmisc_1(X1) & ~v1_xboole_0(X1)) => (r1_tarski(X0,X1) => X0 = X1)))),
% 0.20/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_tex_2)).
% 0.20/0.48  fof(f70,plain,(
% 0.20/0.48    ~spl3_4),
% 0.20/0.48    inference(avatar_split_clause,[],[f30,f68])).
% 0.20/0.48  fof(f30,plain,(
% 0.20/0.48    ~v1_xboole_0(sK1)),
% 0.20/0.48    inference(cnf_transformation,[],[f23])).
% 0.20/0.48  fof(f66,plain,(
% 0.20/0.48    spl3_3),
% 0.20/0.48    inference(avatar_split_clause,[],[f31,f64])).
% 0.20/0.48  fof(f31,plain,(
% 0.20/0.48    v1_zfmisc_1(sK1)),
% 0.20/0.48    inference(cnf_transformation,[],[f23])).
% 0.20/0.48  fof(f62,plain,(
% 0.20/0.48    spl3_2),
% 0.20/0.48    inference(avatar_split_clause,[],[f32,f60])).
% 0.20/0.48  fof(f32,plain,(
% 0.20/0.48    r1_tarski(sK0,sK1)),
% 0.20/0.48    inference(cnf_transformation,[],[f23])).
% 0.20/0.48  fof(f58,plain,(
% 0.20/0.48    ~spl3_1),
% 0.20/0.48    inference(avatar_split_clause,[],[f33,f56])).
% 0.20/0.48  fof(f33,plain,(
% 0.20/0.48    sK0 != sK1),
% 0.20/0.48    inference(cnf_transformation,[],[f23])).
% 0.20/0.48  % SZS output end Proof for theBenchmark
% 0.20/0.48  % (27578)------------------------------
% 0.20/0.48  % (27578)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.48  % (27578)Termination reason: Refutation
% 0.20/0.48  
% 0.20/0.48  % (27578)Memory used [KB]: 10618
% 0.20/0.48  % (27578)Time elapsed: 0.032 s
% 0.20/0.48  % (27578)------------------------------
% 0.20/0.48  % (27578)------------------------------
% 0.20/0.48  % (27571)Success in time 0.124 s
%------------------------------------------------------------------------------
