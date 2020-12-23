%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1841+1.003 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n026.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:50:43 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   71 ( 120 expanded)
%              Number of leaves         :   18 (  51 expanded)
%              Depth                    :    8
%              Number of atoms          :  228 ( 398 expanded)
%              Number of equality atoms :   10 (  17 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f128,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f33,f38,f43,f48,f52,f60,f64,f68,f75,f81,f95,f127])).

fof(f127,plain,
    ( ~ spl2_1
    | spl2_4
    | ~ spl2_5
    | ~ spl2_7
    | ~ spl2_11
    | ~ spl2_13 ),
    inference(avatar_contradiction_clause,[],[f126])).

fof(f126,plain,
    ( $false
    | ~ spl2_1
    | spl2_4
    | ~ spl2_5
    | ~ spl2_7
    | ~ spl2_11
    | ~ spl2_13 ),
    inference(subsumption_resolution,[],[f125,f47])).

fof(f47,plain,
    ( ~ v1_xboole_0(sK0)
    | spl2_4 ),
    inference(avatar_component_clause,[],[f45])).

fof(f45,plain,
    ( spl2_4
  <=> v1_xboole_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).

fof(f125,plain,
    ( v1_xboole_0(sK0)
    | ~ spl2_1
    | ~ spl2_5
    | ~ spl2_7
    | ~ spl2_11
    | ~ spl2_13 ),
    inference(subsumption_resolution,[],[f124,f32])).

fof(f32,plain,
    ( v1_zfmisc_1(sK0)
    | ~ spl2_1 ),
    inference(avatar_component_clause,[],[f30])).

fof(f30,plain,
    ( spl2_1
  <=> v1_zfmisc_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f124,plain,
    ( ~ v1_zfmisc_1(sK0)
    | v1_xboole_0(sK0)
    | ~ spl2_5
    | ~ spl2_7
    | ~ spl2_11
    | ~ spl2_13 ),
    inference(subsumption_resolution,[],[f123,f51])).

fof(f51,plain,
    ( ! [X0] : ~ v1_xboole_0(k1_tarski(X0))
    | ~ spl2_5 ),
    inference(avatar_component_clause,[],[f50])).

fof(f50,plain,
    ( spl2_5
  <=> ! [X0] : ~ v1_xboole_0(k1_tarski(X0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).

fof(f123,plain,
    ( v1_xboole_0(k1_tarski(sK1))
    | ~ v1_zfmisc_1(sK0)
    | v1_xboole_0(sK0)
    | ~ spl2_7
    | ~ spl2_11
    | ~ spl2_13 ),
    inference(subsumption_resolution,[],[f117,f80])).

fof(f80,plain,
    ( v1_subset_1(k1_tarski(sK1),sK0)
    | ~ spl2_11 ),
    inference(avatar_component_clause,[],[f78])).

fof(f78,plain,
    ( spl2_11
  <=> v1_subset_1(k1_tarski(sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_11])])).

fof(f117,plain,
    ( ~ v1_subset_1(k1_tarski(sK1),sK0)
    | v1_xboole_0(k1_tarski(sK1))
    | ~ v1_zfmisc_1(sK0)
    | v1_xboole_0(sK0)
    | ~ spl2_7
    | ~ spl2_13 ),
    inference(resolution,[],[f59,f94])).

fof(f94,plain,
    ( m1_subset_1(k1_tarski(sK1),k1_zfmisc_1(sK0))
    | ~ spl2_13 ),
    inference(avatar_component_clause,[],[f92])).

fof(f92,plain,
    ( spl2_13
  <=> m1_subset_1(k1_tarski(sK1),k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_13])])).

fof(f59,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
        | ~ v1_subset_1(X1,X0)
        | v1_xboole_0(X1)
        | ~ v1_zfmisc_1(X0)
        | v1_xboole_0(X0) )
    | ~ spl2_7 ),
    inference(avatar_component_clause,[],[f58])).

fof(f58,plain,
    ( spl2_7
  <=> ! [X1,X0] :
        ( v1_xboole_0(X1)
        | ~ v1_subset_1(X1,X0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
        | ~ v1_zfmisc_1(X0)
        | v1_xboole_0(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).

fof(f95,plain,
    ( spl2_13
    | ~ spl2_3
    | spl2_4
    | ~ spl2_9
    | ~ spl2_10 ),
    inference(avatar_split_clause,[],[f90,f72,f66,f45,f40,f92])).

fof(f40,plain,
    ( spl2_3
  <=> m1_subset_1(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).

fof(f66,plain,
    ( spl2_9
  <=> ! [X1,X0] :
        ( m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0))
        | ~ m1_subset_1(X1,X0)
        | v1_xboole_0(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_9])])).

fof(f72,plain,
    ( spl2_10
  <=> k6_domain_1(sK0,sK1) = k1_tarski(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_10])])).

fof(f90,plain,
    ( m1_subset_1(k1_tarski(sK1),k1_zfmisc_1(sK0))
    | ~ spl2_3
    | spl2_4
    | ~ spl2_9
    | ~ spl2_10 ),
    inference(subsumption_resolution,[],[f89,f47])).

fof(f89,plain,
    ( m1_subset_1(k1_tarski(sK1),k1_zfmisc_1(sK0))
    | v1_xboole_0(sK0)
    | ~ spl2_3
    | ~ spl2_9
    | ~ spl2_10 ),
    inference(subsumption_resolution,[],[f84,f42])).

fof(f42,plain,
    ( m1_subset_1(sK1,sK0)
    | ~ spl2_3 ),
    inference(avatar_component_clause,[],[f40])).

fof(f84,plain,
    ( m1_subset_1(k1_tarski(sK1),k1_zfmisc_1(sK0))
    | ~ m1_subset_1(sK1,sK0)
    | v1_xboole_0(sK0)
    | ~ spl2_9
    | ~ spl2_10 ),
    inference(superposition,[],[f67,f74])).

fof(f74,plain,
    ( k6_domain_1(sK0,sK1) = k1_tarski(sK1)
    | ~ spl2_10 ),
    inference(avatar_component_clause,[],[f72])).

fof(f67,plain,
    ( ! [X0,X1] :
        ( m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0))
        | ~ m1_subset_1(X1,X0)
        | v1_xboole_0(X0) )
    | ~ spl2_9 ),
    inference(avatar_component_clause,[],[f66])).

fof(f81,plain,
    ( spl2_11
    | ~ spl2_2
    | ~ spl2_10 ),
    inference(avatar_split_clause,[],[f76,f72,f35,f78])).

fof(f35,plain,
    ( spl2_2
  <=> v1_subset_1(k6_domain_1(sK0,sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f76,plain,
    ( v1_subset_1(k1_tarski(sK1),sK0)
    | ~ spl2_2
    | ~ spl2_10 ),
    inference(backward_demodulation,[],[f37,f74])).

fof(f37,plain,
    ( v1_subset_1(k6_domain_1(sK0,sK1),sK0)
    | ~ spl2_2 ),
    inference(avatar_component_clause,[],[f35])).

fof(f75,plain,
    ( spl2_10
    | ~ spl2_3
    | spl2_4
    | ~ spl2_8 ),
    inference(avatar_split_clause,[],[f70,f62,f45,f40,f72])).

fof(f62,plain,
    ( spl2_8
  <=> ! [X1,X0] :
        ( k6_domain_1(X0,X1) = k1_tarski(X1)
        | ~ m1_subset_1(X1,X0)
        | v1_xboole_0(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_8])])).

fof(f70,plain,
    ( k6_domain_1(sK0,sK1) = k1_tarski(sK1)
    | ~ spl2_3
    | spl2_4
    | ~ spl2_8 ),
    inference(subsumption_resolution,[],[f69,f47])).

fof(f69,plain,
    ( k6_domain_1(sK0,sK1) = k1_tarski(sK1)
    | v1_xboole_0(sK0)
    | ~ spl2_3
    | ~ spl2_8 ),
    inference(resolution,[],[f63,f42])).

fof(f63,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X1,X0)
        | k6_domain_1(X0,X1) = k1_tarski(X1)
        | v1_xboole_0(X0) )
    | ~ spl2_8 ),
    inference(avatar_component_clause,[],[f62])).

fof(f68,plain,(
    spl2_9 ),
    inference(avatar_split_clause,[],[f28,f66])).

fof(f28,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,X0)
        & ~ v1_xboole_0(X0) )
     => m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_domain_1)).

fof(f64,plain,(
    spl2_8 ),
    inference(avatar_split_clause,[],[f27,f62])).

fof(f27,plain,(
    ! [X0,X1] :
      ( k6_domain_1(X0,X1) = k1_tarski(X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( k6_domain_1(X0,X1) = k1_tarski(X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( k6_domain_1(X0,X1) = k1_tarski(X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,X0)
        & ~ v1_xboole_0(X0) )
     => k6_domain_1(X0,X1) = k1_tarski(X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

fof(f60,plain,(
    spl2_7 ),
    inference(avatar_split_clause,[],[f26,f58])).

fof(f26,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(X1)
      | ~ v1_subset_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_zfmisc_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_xboole_0(X1)
          | ~ v1_subset_1(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_zfmisc_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_xboole_0(X1)
          | ~ v1_subset_1(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_zfmisc_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( ( v1_zfmisc_1(X0)
        & ~ v1_xboole_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => ( v1_subset_1(X1,X0)
           => v1_xboole_0(X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_tex_2)).

fof(f52,plain,(
    spl2_5 ),
    inference(avatar_split_clause,[],[f24,f50])).

fof(f24,plain,(
    ! [X0] : ~ v1_xboole_0(k1_tarski(X0)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : ~ v1_xboole_0(k1_tarski(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_xboole_0)).

fof(f48,plain,(
    ~ spl2_4 ),
    inference(avatar_split_clause,[],[f20,f45])).

fof(f20,plain,(
    ~ v1_xboole_0(sK0) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,
    ( v1_zfmisc_1(sK0)
    & v1_subset_1(k6_domain_1(sK0,sK1),sK0)
    & m1_subset_1(sK1,sK0)
    & ~ v1_xboole_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f9,f18,f17])).

fof(f17,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( v1_zfmisc_1(X0)
            & v1_subset_1(k6_domain_1(X0,X1),X0)
            & m1_subset_1(X1,X0) )
        & ~ v1_xboole_0(X0) )
   => ( ? [X1] :
          ( v1_zfmisc_1(sK0)
          & v1_subset_1(k6_domain_1(sK0,X1),sK0)
          & m1_subset_1(X1,sK0) )
      & ~ v1_xboole_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,
    ( ? [X1] :
        ( v1_zfmisc_1(sK0)
        & v1_subset_1(k6_domain_1(sK0,X1),sK0)
        & m1_subset_1(X1,sK0) )
   => ( v1_zfmisc_1(sK0)
      & v1_subset_1(k6_domain_1(sK0,sK1),sK0)
      & m1_subset_1(sK1,sK0) ) ),
    introduced(choice_axiom,[])).

fof(f9,plain,(
    ? [X0] :
      ( ? [X1] :
          ( v1_zfmisc_1(X0)
          & v1_subset_1(k6_domain_1(X0,X1),X0)
          & m1_subset_1(X1,X0) )
      & ~ v1_xboole_0(X0) ) ),
    inference(flattening,[],[f8])).

fof(f8,plain,(
    ? [X0] :
      ( ? [X1] :
          ( v1_zfmisc_1(X0)
          & v1_subset_1(k6_domain_1(X0,X1),X0)
          & m1_subset_1(X1,X0) )
      & ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,negated_conjecture,(
    ~ ! [X0] :
        ( ~ v1_xboole_0(X0)
       => ! [X1] :
            ( m1_subset_1(X1,X0)
           => ~ ( v1_zfmisc_1(X0)
                & v1_subset_1(k6_domain_1(X0,X1),X0) ) ) ) ),
    inference(negated_conjecture,[],[f6])).

fof(f6,conjecture,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( m1_subset_1(X1,X0)
         => ~ ( v1_zfmisc_1(X0)
              & v1_subset_1(k6_domain_1(X0,X1),X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_tex_2)).

fof(f43,plain,(
    spl2_3 ),
    inference(avatar_split_clause,[],[f21,f40])).

fof(f21,plain,(
    m1_subset_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f19])).

fof(f38,plain,(
    spl2_2 ),
    inference(avatar_split_clause,[],[f22,f35])).

fof(f22,plain,(
    v1_subset_1(k6_domain_1(sK0,sK1),sK0) ),
    inference(cnf_transformation,[],[f19])).

fof(f33,plain,(
    spl2_1 ),
    inference(avatar_split_clause,[],[f23,f30])).

fof(f23,plain,(
    v1_zfmisc_1(sK0) ),
    inference(cnf_transformation,[],[f19])).

%------------------------------------------------------------------------------
