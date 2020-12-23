%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:07:04 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  138 ( 404 expanded)
%              Number of leaves         :   26 ( 116 expanded)
%              Depth                    :   17
%              Number of atoms          :  374 (1124 expanded)
%              Number of equality atoms :  114 ( 332 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f940,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f98,f257,f448,f658,f772,f779,f780,f815,f938])).

fof(f938,plain,
    ( spl4_9
    | ~ spl4_10 ),
    inference(avatar_contradiction_clause,[],[f937])).

fof(f937,plain,
    ( $false
    | spl4_9
    | ~ spl4_10 ),
    inference(subsumption_resolution,[],[f936,f192])).

fof(f192,plain,
    ( k1_xboole_0 != sK0
    | spl4_9 ),
    inference(avatar_component_clause,[],[f191])).

fof(f191,plain,
    ( spl4_9
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).

fof(f936,plain,
    ( k1_xboole_0 = sK0
    | ~ spl4_10 ),
    inference(subsumption_resolution,[],[f932,f100])).

fof(f100,plain,(
    ! [X0] : ~ r2_hidden(X0,k1_xboole_0) ),
    inference(resolution,[],[f54,f47])).

fof(f47,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f54,plain,(
    ! [X2,X0] :
      ( ~ v1_xboole_0(X0)
      | ~ r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | r2_hidden(sK3(X0),X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f36,f37])).

fof(f37,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK3(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(rectify,[],[f35])).

fof(f35,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X1] : ~ r2_hidden(X1,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

fof(f932,plain,
    ( r2_hidden(k1_xboole_0,k1_xboole_0)
    | k1_xboole_0 = sK0
    | ~ spl4_10 ),
    inference(superposition,[],[f909,f347])).

fof(f347,plain,(
    ! [X4] :
      ( k1_xboole_0 = k5_partfun1(X4,k1_xboole_0,k3_partfun1(k1_xboole_0,X4,k1_xboole_0))
      | k1_xboole_0 = X4 ) ),
    inference(resolution,[],[f344,f53])).

fof(f53,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

fof(f344,plain,(
    ! [X0] :
      ( v1_xboole_0(k5_partfun1(X0,k1_xboole_0,k3_partfun1(k1_xboole_0,X0,k1_xboole_0)))
      | k1_xboole_0 = X0 ) ),
    inference(global_subsumption,[],[f53,f126])).

fof(f126,plain,(
    ! [X0] :
      ( v1_xboole_0(k5_partfun1(X0,k1_xboole_0,k3_partfun1(k1_xboole_0,X0,k1_xboole_0)))
      | v1_xboole_0(X0) ) ),
    inference(resolution,[],[f79,f47])).

fof(f79,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | v1_xboole_0(k5_partfun1(X0,X1,k3_partfun1(k1_xboole_0,X0,X1)))
      | v1_xboole_0(X0) ) ),
    inference(definition_unfolding,[],[f60,f58])).

fof(f58,plain,(
    ! [X0,X1] : k1_funct_2(X0,X1) = k5_partfun1(X0,X1,k3_partfun1(k1_xboole_0,X0,X1)) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1] : k1_funct_2(X0,X1) = k5_partfun1(X0,X1,k3_partfun1(k1_xboole_0,X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t160_funct_2)).

fof(f60,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(k1_funct_2(X0,X1))
      | ~ v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(k1_funct_2(X0,X1))
      | ~ v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(k1_funct_2(X0,X1))
      | ~ v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( ( v1_xboole_0(X1)
        & ~ v1_xboole_0(X0) )
     => v1_xboole_0(k1_funct_2(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc3_funct_2)).

fof(f909,plain,
    ( r2_hidden(k1_xboole_0,k5_partfun1(sK0,k1_xboole_0,k3_partfun1(k1_xboole_0,sK0,k1_xboole_0)))
    | ~ spl4_10 ),
    inference(forward_demodulation,[],[f908,f280])).

fof(f280,plain,
    ( k1_xboole_0 = sK2
    | ~ spl4_10 ),
    inference(superposition,[],[f267,f106])).

fof(f106,plain,(
    ! [X1] : k2_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(superposition,[],[f105,f57])).

fof(f57,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(f105,plain,(
    ! [X0] : k2_xboole_0(k1_xboole_0,X0) = X0 ),
    inference(resolution,[],[f59,f50])).

fof(f50,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f59,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k2_xboole_0(X0,X1) = X1 ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

fof(f267,plain,
    ( k1_xboole_0 = k2_xboole_0(sK2,k1_xboole_0)
    | ~ spl4_10 ),
    inference(resolution,[],[f264,f59])).

fof(f264,plain,
    ( r1_tarski(sK2,k1_xboole_0)
    | ~ spl4_10 ),
    inference(forward_demodulation,[],[f263,f83])).

fof(f83,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f65])).

fof(f65,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f263,plain,
    ( r1_tarski(sK2,k2_zfmisc_1(sK0,k1_xboole_0))
    | ~ spl4_10 ),
    inference(forward_demodulation,[],[f158,f197])).

fof(f197,plain,
    ( k1_xboole_0 = sK1
    | ~ spl4_10 ),
    inference(avatar_component_clause,[],[f195])).

fof(f195,plain,
    ( spl4_10
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).

fof(f158,plain,(
    r1_tarski(sK2,k2_zfmisc_1(sK0,sK1)) ),
    inference(resolution,[],[f149,f78])).

fof(f78,plain,(
    r2_hidden(sK2,k5_partfun1(sK0,sK1,k3_partfun1(k1_xboole_0,sK0,sK1))) ),
    inference(definition_unfolding,[],[f45,f58])).

fof(f45,plain,(
    r2_hidden(sK2,k1_funct_2(sK0,sK1)) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,
    ( ( ~ r1_tarski(k2_relat_1(sK2),sK1)
      | sK0 != k1_relat_1(sK2) )
    & r2_hidden(sK2,k1_funct_2(sK0,sK1))
    & v1_funct_1(sK2)
    & v1_relat_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f21,f33])).

fof(f33,plain,
    ( ? [X0,X1,X2] :
        ( ( ~ r1_tarski(k2_relat_1(X2),X1)
          | k1_relat_1(X2) != X0 )
        & r2_hidden(X2,k1_funct_2(X0,X1))
        & v1_funct_1(X2)
        & v1_relat_1(X2) )
   => ( ( ~ r1_tarski(k2_relat_1(sK2),sK1)
        | sK0 != k1_relat_1(sK2) )
      & r2_hidden(sK2,k1_funct_2(sK0,sK1))
      & v1_funct_1(sK2)
      & v1_relat_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,(
    ? [X0,X1,X2] :
      ( ( ~ r1_tarski(k2_relat_1(X2),X1)
        | k1_relat_1(X2) != X0 )
      & r2_hidden(X2,k1_funct_2(X0,X1))
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ? [X0,X1,X2] :
      ( ( ~ r1_tarski(k2_relat_1(X2),X1)
        | k1_relat_1(X2) != X0 )
      & r2_hidden(X2,k1_funct_2(X0,X1))
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( v1_funct_1(X2)
          & v1_relat_1(X2) )
       => ( r2_hidden(X2,k1_funct_2(X0,X1))
         => ( r1_tarski(k2_relat_1(X2),X1)
            & k1_relat_1(X2) = X0 ) ) ) ),
    inference(negated_conjecture,[],[f18])).

fof(f18,conjecture,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( r2_hidden(X2,k1_funct_2(X0,X1))
       => ( r1_tarski(k2_relat_1(X2),X1)
          & k1_relat_1(X2) = X0 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t169_funct_2)).

fof(f149,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k5_partfun1(X1,X2,k3_partfun1(k1_xboole_0,X1,X2)))
      | r1_tarski(X0,k2_zfmisc_1(X1,X2)) ) ),
    inference(resolution,[],[f80,f61])).

fof(f61,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(f80,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r2_hidden(X2,k5_partfun1(X0,X1,k3_partfun1(k1_xboole_0,X0,X1))) ) ),
    inference(definition_unfolding,[],[f70,f58])).

fof(f70,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r2_hidden(X2,k1_funct_2(X0,X1)) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
      | ~ r2_hidden(X2,k1_funct_2(X0,X1)) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1,X2] :
      ( r2_hidden(X2,k1_funct_2(X0,X1))
     => ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t121_funct_2)).

fof(f908,plain,
    ( r2_hidden(sK2,k5_partfun1(sK0,k1_xboole_0,k3_partfun1(k1_xboole_0,sK0,k1_xboole_0)))
    | ~ spl4_10 ),
    inference(forward_demodulation,[],[f78,f197])).

fof(f815,plain,
    ( spl4_2
    | ~ spl4_10 ),
    inference(avatar_contradiction_clause,[],[f814])).

fof(f814,plain,
    ( $false
    | spl4_2
    | ~ spl4_10 ),
    inference(subsumption_resolution,[],[f813,f50])).

fof(f813,plain,
    ( ~ r1_tarski(k1_xboole_0,k1_xboole_0)
    | spl4_2
    | ~ spl4_10 ),
    inference(forward_demodulation,[],[f812,f49])).

fof(f49,plain,(
    k1_xboole_0 = k2_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    & k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

fof(f812,plain,
    ( ~ r1_tarski(k2_relat_1(k1_xboole_0),k1_xboole_0)
    | spl4_2
    | ~ spl4_10 ),
    inference(forward_demodulation,[],[f811,f280])).

fof(f811,plain,
    ( ~ r1_tarski(k2_relat_1(sK2),k1_xboole_0)
    | spl4_2
    | ~ spl4_10 ),
    inference(forward_demodulation,[],[f97,f197])).

fof(f97,plain,
    ( ~ r1_tarski(k2_relat_1(sK2),sK1)
    | spl4_2 ),
    inference(avatar_component_clause,[],[f95])).

fof(f95,plain,
    ( spl4_2
  <=> r1_tarski(k2_relat_1(sK2),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f780,plain,
    ( ~ spl4_14
    | spl4_15
    | spl4_10 ),
    inference(avatar_split_clause,[],[f560,f195,f442,f438])).

fof(f438,plain,
    ( spl4_14
  <=> v1_funct_2(sK2,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_14])])).

fof(f442,plain,
    ( spl4_15
  <=> sK0 = k1_relset_1(sK0,sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_15])])).

fof(f560,plain,
    ( k1_xboole_0 = sK1
    | sK0 = k1_relset_1(sK0,sK1,sK2)
    | ~ v1_funct_2(sK2,sK0,sK1) ),
    inference(resolution,[],[f158,f428])).

fof(f428,plain,(
    ! [X4,X5,X3] :
      ( ~ r1_tarski(X3,k2_zfmisc_1(X4,X5))
      | k1_xboole_0 = X5
      | k1_relset_1(X4,X5,X3) = X4
      | ~ v1_funct_2(X3,X4,X5) ) ),
    inference(resolution,[],[f72,f62])).

fof(f62,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f72,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | k1_relset_1(X0,X1,X2) = X0 ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
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
    inference(nnf_transformation,[],[f32])).

fof(f32,plain,(
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
    inference(flattening,[],[f31])).

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
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
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

fof(f779,plain,
    ( spl4_9
    | spl4_10
    | spl4_2 ),
    inference(avatar_split_clause,[],[f640,f95,f195,f191])).

fof(f640,plain,
    ( r1_tarski(k2_relat_1(sK2),sK1)
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0 ),
    inference(superposition,[],[f165,f67])).

fof(f67,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k2_zfmisc_1(X0,X1)) = X1
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( k2_relat_1(k2_zfmisc_1(X0,X1)) = X1
        & k1_relat_1(k2_zfmisc_1(X0,X1)) = X0 )
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ~ ( ~ ( k2_relat_1(k2_zfmisc_1(X0,X1)) = X1
            & k1_relat_1(k2_zfmisc_1(X0,X1)) = X0 )
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t195_relat_1)).

fof(f165,plain,(
    r1_tarski(k2_relat_1(sK2),k2_relat_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(subsumption_resolution,[],[f164,f43])).

fof(f43,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f34])).

fof(f164,plain,
    ( r1_tarski(k2_relat_1(sK2),k2_relat_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_relat_1(sK2) ),
    inference(subsumption_resolution,[],[f161,f56])).

fof(f56,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f161,plain,
    ( r1_tarski(k2_relat_1(sK2),k2_relat_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_relat_1(k2_zfmisc_1(sK0,sK1))
    | ~ v1_relat_1(sK2) ),
    inference(resolution,[],[f158,f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
            & r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) )
          | ~ r1_tarski(X0,X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
            & r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) )
          | ~ r1_tarski(X0,X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ( r1_tarski(X0,X1)
           => ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
              & r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t25_relat_1)).

fof(f772,plain,
    ( spl4_2
    | ~ spl4_9 ),
    inference(avatar_contradiction_clause,[],[f771])).

fof(f771,plain,
    ( $false
    | spl4_2
    | ~ spl4_9 ),
    inference(subsumption_resolution,[],[f770,f50])).

fof(f770,plain,
    ( ~ r1_tarski(k1_xboole_0,sK1)
    | spl4_2
    | ~ spl4_9 ),
    inference(forward_demodulation,[],[f769,f49])).

fof(f769,plain,
    ( ~ r1_tarski(k2_relat_1(k1_xboole_0),sK1)
    | spl4_2
    | ~ spl4_9 ),
    inference(forward_demodulation,[],[f97,f239])).

fof(f239,plain,
    ( k1_xboole_0 = sK2
    | ~ spl4_9 ),
    inference(superposition,[],[f208,f106])).

fof(f208,plain,
    ( k1_xboole_0 = k2_xboole_0(sK2,k1_xboole_0)
    | ~ spl4_9 ),
    inference(resolution,[],[f205,f59])).

fof(f205,plain,
    ( r1_tarski(sK2,k1_xboole_0)
    | ~ spl4_9 ),
    inference(forward_demodulation,[],[f200,f84])).

fof(f84,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f64])).

fof(f64,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f41])).

fof(f200,plain,
    ( r1_tarski(sK2,k2_zfmisc_1(k1_xboole_0,sK1))
    | ~ spl4_9 ),
    inference(backward_demodulation,[],[f158,f193])).

fof(f193,plain,
    ( k1_xboole_0 = sK0
    | ~ spl4_9 ),
    inference(avatar_component_clause,[],[f191])).

fof(f658,plain,
    ( spl4_1
    | ~ spl4_15 ),
    inference(avatar_contradiction_clause,[],[f657])).

fof(f657,plain,
    ( $false
    | spl4_1
    | ~ spl4_15 ),
    inference(subsumption_resolution,[],[f654,f158])).

fof(f654,plain,
    ( ~ r1_tarski(sK2,k2_zfmisc_1(sK0,sK1))
    | spl4_1
    | ~ spl4_15 ),
    inference(resolution,[],[f647,f62])).

fof(f647,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | spl4_1
    | ~ spl4_15 ),
    inference(subsumption_resolution,[],[f645,f93])).

fof(f93,plain,
    ( sK0 != k1_relat_1(sK2)
    | spl4_1 ),
    inference(avatar_component_clause,[],[f91])).

fof(f91,plain,
    ( spl4_1
  <=> sK0 = k1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f645,plain,
    ( sK0 = k1_relat_1(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl4_15 ),
    inference(superposition,[],[f444,f71])).

fof(f71,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f444,plain,
    ( sK0 = k1_relset_1(sK0,sK1,sK2)
    | ~ spl4_15 ),
    inference(avatar_component_clause,[],[f442])).

fof(f448,plain,(
    spl4_14 ),
    inference(avatar_contradiction_clause,[],[f447])).

fof(f447,plain,
    ( $false
    | spl4_14 ),
    inference(subsumption_resolution,[],[f446,f78])).

fof(f446,plain,
    ( ~ r2_hidden(sK2,k5_partfun1(sK0,sK1,k3_partfun1(k1_xboole_0,sK0,sK1)))
    | spl4_14 ),
    inference(resolution,[],[f440,f81])).

fof(f81,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(X2,X0,X1)
      | ~ r2_hidden(X2,k5_partfun1(X0,X1,k3_partfun1(k1_xboole_0,X0,X1))) ) ),
    inference(definition_unfolding,[],[f69,f58])).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(X2,X0,X1)
      | ~ r2_hidden(X2,k1_funct_2(X0,X1)) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f440,plain,
    ( ~ v1_funct_2(sK2,sK0,sK1)
    | spl4_14 ),
    inference(avatar_component_clause,[],[f438])).

fof(f257,plain,
    ( spl4_1
    | ~ spl4_9 ),
    inference(avatar_contradiction_clause,[],[f256])).

fof(f256,plain,
    ( $false
    | spl4_1
    | ~ spl4_9 ),
    inference(subsumption_resolution,[],[f247,f48])).

fof(f48,plain,(
    k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f12])).

fof(f247,plain,
    ( k1_xboole_0 != k1_relat_1(k1_xboole_0)
    | spl4_1
    | ~ spl4_9 ),
    inference(backward_demodulation,[],[f202,f239])).

fof(f202,plain,
    ( k1_xboole_0 != k1_relat_1(sK2)
    | spl4_1
    | ~ spl4_9 ),
    inference(backward_demodulation,[],[f93,f193])).

fof(f98,plain,
    ( ~ spl4_1
    | ~ spl4_2 ),
    inference(avatar_split_clause,[],[f46,f95,f91])).

fof(f46,plain,
    ( ~ r1_tarski(k2_relat_1(sK2),sK1)
    | sK0 != k1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f34])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n012.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 17:18:52 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.51  % (24926)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.21/0.52  % (24933)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.21/0.52  % (24926)Refutation not found, incomplete strategy% (24926)------------------------------
% 0.21/0.52  % (24926)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (24924)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.21/0.52  % (24918)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.52  % (24926)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (24926)Memory used [KB]: 10618
% 0.21/0.52  % (24926)Time elapsed: 0.092 s
% 0.21/0.52  % (24926)------------------------------
% 0.21/0.52  % (24926)------------------------------
% 0.21/0.52  % (24921)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.21/0.53  % (24918)Refutation not found, incomplete strategy% (24918)------------------------------
% 0.21/0.53  % (24918)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (24918)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (24918)Memory used [KB]: 10746
% 0.21/0.53  % (24918)Time elapsed: 0.103 s
% 0.21/0.53  % (24918)------------------------------
% 0.21/0.53  % (24918)------------------------------
% 0.21/0.53  % (24919)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.21/0.53  % (24930)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.21/0.53  % (24920)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.54  % (24938)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.21/0.54  % (24927)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.21/0.54  % (24917)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.21/0.54  % (24916)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.21/0.54  % (24942)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.21/0.54  % (24944)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.21/0.54  % (24924)Refutation not found, incomplete strategy% (24924)------------------------------
% 0.21/0.54  % (24924)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (24924)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (24924)Memory used [KB]: 10746
% 0.21/0.54  % (24924)Time elapsed: 0.124 s
% 0.21/0.54  % (24924)------------------------------
% 0.21/0.54  % (24924)------------------------------
% 0.21/0.54  % (24932)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.21/0.55  % (24929)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.21/0.55  % (24934)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.21/0.55  % (24935)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.21/0.55  % (24922)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.21/0.55  % (24945)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.21/0.55  % (24939)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.21/0.55  % (24928)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.55  % (24940)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.21/0.55  % (24943)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.21/0.55  % (24931)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.21/0.55  % (24941)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.21/0.55  % (24937)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.21/0.55  % (24923)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.21/0.56  % (24937)Refutation not found, incomplete strategy% (24937)------------------------------
% 0.21/0.56  % (24937)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.56  % (24938)Refutation not found, incomplete strategy% (24938)------------------------------
% 0.21/0.56  % (24938)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.56  % (24925)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.21/0.56  % (24936)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.21/0.56  % (24919)Refutation found. Thanks to Tanya!
% 0.21/0.56  % SZS status Theorem for theBenchmark
% 0.21/0.56  % (24938)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.56  
% 0.21/0.56  % (24938)Memory used [KB]: 10874
% 0.21/0.56  % (24938)Time elapsed: 0.094 s
% 0.21/0.56  % (24938)------------------------------
% 0.21/0.56  % (24938)------------------------------
% 0.21/0.56  % (24937)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.56  
% 0.21/0.56  % (24937)Memory used [KB]: 1791
% 0.21/0.56  % (24937)Time elapsed: 0.140 s
% 0.21/0.56  % (24937)------------------------------
% 0.21/0.56  % (24937)------------------------------
% 0.21/0.57  % SZS output start Proof for theBenchmark
% 0.21/0.57  fof(f940,plain,(
% 0.21/0.57    $false),
% 0.21/0.57    inference(avatar_sat_refutation,[],[f98,f257,f448,f658,f772,f779,f780,f815,f938])).
% 0.21/0.57  fof(f938,plain,(
% 0.21/0.57    spl4_9 | ~spl4_10),
% 0.21/0.57    inference(avatar_contradiction_clause,[],[f937])).
% 0.21/0.57  fof(f937,plain,(
% 0.21/0.57    $false | (spl4_9 | ~spl4_10)),
% 0.21/0.57    inference(subsumption_resolution,[],[f936,f192])).
% 0.21/0.57  fof(f192,plain,(
% 0.21/0.57    k1_xboole_0 != sK0 | spl4_9),
% 0.21/0.57    inference(avatar_component_clause,[],[f191])).
% 0.21/0.57  fof(f191,plain,(
% 0.21/0.57    spl4_9 <=> k1_xboole_0 = sK0),
% 0.21/0.57    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).
% 0.21/0.57  fof(f936,plain,(
% 0.21/0.57    k1_xboole_0 = sK0 | ~spl4_10),
% 0.21/0.57    inference(subsumption_resolution,[],[f932,f100])).
% 0.21/0.57  fof(f100,plain,(
% 0.21/0.57    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0)) )),
% 0.21/0.57    inference(resolution,[],[f54,f47])).
% 0.21/0.57  fof(f47,plain,(
% 0.21/0.57    v1_xboole_0(k1_xboole_0)),
% 0.21/0.57    inference(cnf_transformation,[],[f3])).
% 0.21/0.57  fof(f3,axiom,(
% 0.21/0.57    v1_xboole_0(k1_xboole_0)),
% 0.21/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).
% 0.21/0.57  fof(f54,plain,(
% 0.21/0.57    ( ! [X2,X0] : (~v1_xboole_0(X0) | ~r2_hidden(X2,X0)) )),
% 0.21/0.57    inference(cnf_transformation,[],[f38])).
% 0.21/0.57  fof(f38,plain,(
% 0.21/0.57    ! [X0] : ((v1_xboole_0(X0) | r2_hidden(sK3(X0),X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 0.21/0.57    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f36,f37])).
% 0.21/0.57  fof(f37,plain,(
% 0.21/0.57    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK3(X0),X0))),
% 0.21/0.57    introduced(choice_axiom,[])).
% 0.21/0.57  fof(f36,plain,(
% 0.21/0.57    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 0.21/0.57    inference(rectify,[],[f35])).
% 0.21/0.57  fof(f35,plain,(
% 0.21/0.57    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0)))),
% 0.21/0.57    inference(nnf_transformation,[],[f2])).
% 0.21/0.57  fof(f2,axiom,(
% 0.21/0.57    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 0.21/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).
% 0.21/0.57  fof(f932,plain,(
% 0.21/0.57    r2_hidden(k1_xboole_0,k1_xboole_0) | k1_xboole_0 = sK0 | ~spl4_10),
% 0.21/0.57    inference(superposition,[],[f909,f347])).
% 0.21/0.57  fof(f347,plain,(
% 0.21/0.57    ( ! [X4] : (k1_xboole_0 = k5_partfun1(X4,k1_xboole_0,k3_partfun1(k1_xboole_0,X4,k1_xboole_0)) | k1_xboole_0 = X4) )),
% 0.21/0.57    inference(resolution,[],[f344,f53])).
% 0.21/0.57  fof(f53,plain,(
% 0.21/0.57    ( ! [X0] : (~v1_xboole_0(X0) | k1_xboole_0 = X0) )),
% 0.21/0.57    inference(cnf_transformation,[],[f24])).
% 0.21/0.57  fof(f24,plain,(
% 0.21/0.57    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 0.21/0.57    inference(ennf_transformation,[],[f4])).
% 0.21/0.57  fof(f4,axiom,(
% 0.21/0.57    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 0.21/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).
% 0.21/0.57  fof(f344,plain,(
% 0.21/0.57    ( ! [X0] : (v1_xboole_0(k5_partfun1(X0,k1_xboole_0,k3_partfun1(k1_xboole_0,X0,k1_xboole_0))) | k1_xboole_0 = X0) )),
% 0.21/0.57    inference(global_subsumption,[],[f53,f126])).
% 0.21/0.57  fof(f126,plain,(
% 0.21/0.57    ( ! [X0] : (v1_xboole_0(k5_partfun1(X0,k1_xboole_0,k3_partfun1(k1_xboole_0,X0,k1_xboole_0))) | v1_xboole_0(X0)) )),
% 0.21/0.57    inference(resolution,[],[f79,f47])).
% 0.21/0.57  fof(f79,plain,(
% 0.21/0.57    ( ! [X0,X1] : (~v1_xboole_0(X1) | v1_xboole_0(k5_partfun1(X0,X1,k3_partfun1(k1_xboole_0,X0,X1))) | v1_xboole_0(X0)) )),
% 0.21/0.57    inference(definition_unfolding,[],[f60,f58])).
% 0.21/0.57  fof(f58,plain,(
% 0.21/0.57    ( ! [X0,X1] : (k1_funct_2(X0,X1) = k5_partfun1(X0,X1,k3_partfun1(k1_xboole_0,X0,X1))) )),
% 0.21/0.57    inference(cnf_transformation,[],[f17])).
% 0.21/0.57  fof(f17,axiom,(
% 0.21/0.57    ! [X0,X1] : k1_funct_2(X0,X1) = k5_partfun1(X0,X1,k3_partfun1(k1_xboole_0,X0,X1))),
% 0.21/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t160_funct_2)).
% 0.21/0.57  fof(f60,plain,(
% 0.21/0.57    ( ! [X0,X1] : (v1_xboole_0(k1_funct_2(X0,X1)) | ~v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 0.21/0.57    inference(cnf_transformation,[],[f27])).
% 0.21/0.57  fof(f27,plain,(
% 0.21/0.57    ! [X0,X1] : (v1_xboole_0(k1_funct_2(X0,X1)) | ~v1_xboole_0(X1) | v1_xboole_0(X0))),
% 0.21/0.57    inference(flattening,[],[f26])).
% 0.21/0.57  fof(f26,plain,(
% 0.21/0.57    ! [X0,X1] : (v1_xboole_0(k1_funct_2(X0,X1)) | (~v1_xboole_0(X1) | v1_xboole_0(X0)))),
% 0.21/0.57    inference(ennf_transformation,[],[f15])).
% 0.21/0.57  fof(f15,axiom,(
% 0.21/0.57    ! [X0,X1] : ((v1_xboole_0(X1) & ~v1_xboole_0(X0)) => v1_xboole_0(k1_funct_2(X0,X1)))),
% 0.21/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc3_funct_2)).
% 0.21/0.57  fof(f909,plain,(
% 0.21/0.57    r2_hidden(k1_xboole_0,k5_partfun1(sK0,k1_xboole_0,k3_partfun1(k1_xboole_0,sK0,k1_xboole_0))) | ~spl4_10),
% 0.21/0.57    inference(forward_demodulation,[],[f908,f280])).
% 0.21/0.57  fof(f280,plain,(
% 0.21/0.57    k1_xboole_0 = sK2 | ~spl4_10),
% 0.21/0.57    inference(superposition,[],[f267,f106])).
% 0.21/0.57  fof(f106,plain,(
% 0.21/0.57    ( ! [X1] : (k2_xboole_0(X1,k1_xboole_0) = X1) )),
% 0.21/0.57    inference(superposition,[],[f105,f57])).
% 0.21/0.57  fof(f57,plain,(
% 0.21/0.57    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 0.21/0.57    inference(cnf_transformation,[],[f1])).
% 0.21/0.57  fof(f1,axiom,(
% 0.21/0.57    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 0.21/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).
% 0.21/0.57  fof(f105,plain,(
% 0.21/0.57    ( ! [X0] : (k2_xboole_0(k1_xboole_0,X0) = X0) )),
% 0.21/0.57    inference(resolution,[],[f59,f50])).
% 0.21/0.57  fof(f50,plain,(
% 0.21/0.57    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 0.21/0.57    inference(cnf_transformation,[],[f6])).
% 0.21/0.57  fof(f6,axiom,(
% 0.21/0.57    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 0.21/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).
% 0.21/0.57  fof(f59,plain,(
% 0.21/0.57    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k2_xboole_0(X0,X1) = X1) )),
% 0.21/0.57    inference(cnf_transformation,[],[f25])).
% 0.21/0.57  fof(f25,plain,(
% 0.21/0.57    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 0.21/0.57    inference(ennf_transformation,[],[f5])).
% 0.21/0.57  fof(f5,axiom,(
% 0.21/0.57    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 0.21/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).
% 0.21/0.57  fof(f267,plain,(
% 0.21/0.57    k1_xboole_0 = k2_xboole_0(sK2,k1_xboole_0) | ~spl4_10),
% 0.21/0.57    inference(resolution,[],[f264,f59])).
% 0.21/0.57  fof(f264,plain,(
% 0.21/0.57    r1_tarski(sK2,k1_xboole_0) | ~spl4_10),
% 0.21/0.57    inference(forward_demodulation,[],[f263,f83])).
% 0.21/0.57  fof(f83,plain,(
% 0.21/0.57    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 0.21/0.57    inference(equality_resolution,[],[f65])).
% 0.21/0.57  fof(f65,plain,(
% 0.21/0.57    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X1) )),
% 0.21/0.57    inference(cnf_transformation,[],[f41])).
% 0.21/0.57  fof(f41,plain,(
% 0.21/0.57    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 0.21/0.57    inference(flattening,[],[f40])).
% 0.21/0.57  fof(f40,plain,(
% 0.21/0.57    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 0.21/0.57    inference(nnf_transformation,[],[f7])).
% 0.21/0.57  fof(f7,axiom,(
% 0.21/0.57    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 0.21/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 0.21/0.57  fof(f263,plain,(
% 0.21/0.57    r1_tarski(sK2,k2_zfmisc_1(sK0,k1_xboole_0)) | ~spl4_10),
% 0.21/0.57    inference(forward_demodulation,[],[f158,f197])).
% 0.21/0.57  fof(f197,plain,(
% 0.21/0.57    k1_xboole_0 = sK1 | ~spl4_10),
% 0.21/0.57    inference(avatar_component_clause,[],[f195])).
% 0.21/0.57  fof(f195,plain,(
% 0.21/0.57    spl4_10 <=> k1_xboole_0 = sK1),
% 0.21/0.57    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).
% 0.21/0.57  fof(f158,plain,(
% 0.21/0.57    r1_tarski(sK2,k2_zfmisc_1(sK0,sK1))),
% 0.21/0.57    inference(resolution,[],[f149,f78])).
% 0.21/0.57  fof(f78,plain,(
% 0.21/0.57    r2_hidden(sK2,k5_partfun1(sK0,sK1,k3_partfun1(k1_xboole_0,sK0,sK1)))),
% 0.21/0.57    inference(definition_unfolding,[],[f45,f58])).
% 0.21/0.57  fof(f45,plain,(
% 0.21/0.57    r2_hidden(sK2,k1_funct_2(sK0,sK1))),
% 0.21/0.57    inference(cnf_transformation,[],[f34])).
% 0.21/0.57  fof(f34,plain,(
% 0.21/0.57    (~r1_tarski(k2_relat_1(sK2),sK1) | sK0 != k1_relat_1(sK2)) & r2_hidden(sK2,k1_funct_2(sK0,sK1)) & v1_funct_1(sK2) & v1_relat_1(sK2)),
% 0.21/0.57    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f21,f33])).
% 0.21/0.57  fof(f33,plain,(
% 0.21/0.57    ? [X0,X1,X2] : ((~r1_tarski(k2_relat_1(X2),X1) | k1_relat_1(X2) != X0) & r2_hidden(X2,k1_funct_2(X0,X1)) & v1_funct_1(X2) & v1_relat_1(X2)) => ((~r1_tarski(k2_relat_1(sK2),sK1) | sK0 != k1_relat_1(sK2)) & r2_hidden(sK2,k1_funct_2(sK0,sK1)) & v1_funct_1(sK2) & v1_relat_1(sK2))),
% 0.21/0.57    introduced(choice_axiom,[])).
% 0.21/0.57  fof(f21,plain,(
% 0.21/0.57    ? [X0,X1,X2] : ((~r1_tarski(k2_relat_1(X2),X1) | k1_relat_1(X2) != X0) & r2_hidden(X2,k1_funct_2(X0,X1)) & v1_funct_1(X2) & v1_relat_1(X2))),
% 0.21/0.57    inference(flattening,[],[f20])).
% 0.21/0.57  fof(f20,plain,(
% 0.21/0.57    ? [X0,X1,X2] : (((~r1_tarski(k2_relat_1(X2),X1) | k1_relat_1(X2) != X0) & r2_hidden(X2,k1_funct_2(X0,X1))) & (v1_funct_1(X2) & v1_relat_1(X2)))),
% 0.21/0.57    inference(ennf_transformation,[],[f19])).
% 0.21/0.57  fof(f19,negated_conjecture,(
% 0.21/0.57    ~! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (r2_hidden(X2,k1_funct_2(X0,X1)) => (r1_tarski(k2_relat_1(X2),X1) & k1_relat_1(X2) = X0)))),
% 0.21/0.57    inference(negated_conjecture,[],[f18])).
% 0.21/0.57  fof(f18,conjecture,(
% 0.21/0.57    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (r2_hidden(X2,k1_funct_2(X0,X1)) => (r1_tarski(k2_relat_1(X2),X1) & k1_relat_1(X2) = X0)))),
% 0.21/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t169_funct_2)).
% 0.21/0.57  fof(f149,plain,(
% 0.21/0.57    ( ! [X2,X0,X1] : (~r2_hidden(X0,k5_partfun1(X1,X2,k3_partfun1(k1_xboole_0,X1,X2))) | r1_tarski(X0,k2_zfmisc_1(X1,X2))) )),
% 0.21/0.57    inference(resolution,[],[f80,f61])).
% 0.21/0.57  fof(f61,plain,(
% 0.21/0.57    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 0.21/0.57    inference(cnf_transformation,[],[f39])).
% 0.21/0.57  fof(f39,plain,(
% 0.21/0.57    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 0.21/0.57    inference(nnf_transformation,[],[f8])).
% 0.21/0.57  fof(f8,axiom,(
% 0.21/0.57    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.21/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).
% 0.21/0.57  fof(f80,plain,(
% 0.21/0.57    ( ! [X2,X0,X1] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r2_hidden(X2,k5_partfun1(X0,X1,k3_partfun1(k1_xboole_0,X0,X1)))) )),
% 0.21/0.57    inference(definition_unfolding,[],[f70,f58])).
% 0.21/0.57  fof(f70,plain,(
% 0.21/0.57    ( ! [X2,X0,X1] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r2_hidden(X2,k1_funct_2(X0,X1))) )),
% 0.21/0.57    inference(cnf_transformation,[],[f29])).
% 0.21/0.57  fof(f29,plain,(
% 0.21/0.57    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) | ~r2_hidden(X2,k1_funct_2(X0,X1)))),
% 0.21/0.57    inference(ennf_transformation,[],[f16])).
% 0.21/0.57  fof(f16,axiom,(
% 0.21/0.57    ! [X0,X1,X2] : (r2_hidden(X2,k1_funct_2(X0,X1)) => (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 0.21/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t121_funct_2)).
% 0.21/0.57  fof(f908,plain,(
% 0.21/0.57    r2_hidden(sK2,k5_partfun1(sK0,k1_xboole_0,k3_partfun1(k1_xboole_0,sK0,k1_xboole_0))) | ~spl4_10),
% 0.21/0.57    inference(forward_demodulation,[],[f78,f197])).
% 0.21/0.57  fof(f815,plain,(
% 0.21/0.57    spl4_2 | ~spl4_10),
% 0.21/0.57    inference(avatar_contradiction_clause,[],[f814])).
% 0.21/0.57  fof(f814,plain,(
% 0.21/0.57    $false | (spl4_2 | ~spl4_10)),
% 0.21/0.57    inference(subsumption_resolution,[],[f813,f50])).
% 0.21/0.57  fof(f813,plain,(
% 0.21/0.57    ~r1_tarski(k1_xboole_0,k1_xboole_0) | (spl4_2 | ~spl4_10)),
% 0.21/0.57    inference(forward_demodulation,[],[f812,f49])).
% 0.21/0.57  fof(f49,plain,(
% 0.21/0.57    k1_xboole_0 = k2_relat_1(k1_xboole_0)),
% 0.21/0.57    inference(cnf_transformation,[],[f12])).
% 0.21/0.57  fof(f12,axiom,(
% 0.21/0.57    k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.21/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).
% 0.21/0.57  fof(f812,plain,(
% 0.21/0.57    ~r1_tarski(k2_relat_1(k1_xboole_0),k1_xboole_0) | (spl4_2 | ~spl4_10)),
% 0.21/0.57    inference(forward_demodulation,[],[f811,f280])).
% 0.21/0.57  fof(f811,plain,(
% 0.21/0.57    ~r1_tarski(k2_relat_1(sK2),k1_xboole_0) | (spl4_2 | ~spl4_10)),
% 0.21/0.57    inference(forward_demodulation,[],[f97,f197])).
% 0.21/0.57  fof(f97,plain,(
% 0.21/0.57    ~r1_tarski(k2_relat_1(sK2),sK1) | spl4_2),
% 0.21/0.57    inference(avatar_component_clause,[],[f95])).
% 0.21/0.57  fof(f95,plain,(
% 0.21/0.57    spl4_2 <=> r1_tarski(k2_relat_1(sK2),sK1)),
% 0.21/0.57    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 0.21/0.57  fof(f780,plain,(
% 0.21/0.57    ~spl4_14 | spl4_15 | spl4_10),
% 0.21/0.57    inference(avatar_split_clause,[],[f560,f195,f442,f438])).
% 0.21/0.57  fof(f438,plain,(
% 0.21/0.57    spl4_14 <=> v1_funct_2(sK2,sK0,sK1)),
% 0.21/0.57    introduced(avatar_definition,[new_symbols(naming,[spl4_14])])).
% 0.21/0.57  fof(f442,plain,(
% 0.21/0.57    spl4_15 <=> sK0 = k1_relset_1(sK0,sK1,sK2)),
% 0.21/0.57    introduced(avatar_definition,[new_symbols(naming,[spl4_15])])).
% 0.21/0.57  fof(f560,plain,(
% 0.21/0.57    k1_xboole_0 = sK1 | sK0 = k1_relset_1(sK0,sK1,sK2) | ~v1_funct_2(sK2,sK0,sK1)),
% 0.21/0.57    inference(resolution,[],[f158,f428])).
% 0.21/0.57  fof(f428,plain,(
% 0.21/0.57    ( ! [X4,X5,X3] : (~r1_tarski(X3,k2_zfmisc_1(X4,X5)) | k1_xboole_0 = X5 | k1_relset_1(X4,X5,X3) = X4 | ~v1_funct_2(X3,X4,X5)) )),
% 0.21/0.57    inference(resolution,[],[f72,f62])).
% 0.21/0.57  fof(f62,plain,(
% 0.21/0.57    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 0.21/0.57    inference(cnf_transformation,[],[f39])).
% 0.21/0.57  fof(f72,plain,(
% 0.21/0.57    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | k1_relset_1(X0,X1,X2) = X0) )),
% 0.21/0.57    inference(cnf_transformation,[],[f42])).
% 0.21/0.57  fof(f42,plain,(
% 0.21/0.57    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.57    inference(nnf_transformation,[],[f32])).
% 0.21/0.57  fof(f32,plain,(
% 0.21/0.57    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.57    inference(flattening,[],[f31])).
% 0.21/0.57  fof(f31,plain,(
% 0.21/0.57    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.57    inference(ennf_transformation,[],[f14])).
% 0.21/0.57  fof(f14,axiom,(
% 0.21/0.57    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 0.21/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).
% 0.21/0.57  fof(f779,plain,(
% 0.21/0.57    spl4_9 | spl4_10 | spl4_2),
% 0.21/0.57    inference(avatar_split_clause,[],[f640,f95,f195,f191])).
% 0.21/0.57  fof(f640,plain,(
% 0.21/0.57    r1_tarski(k2_relat_1(sK2),sK1) | k1_xboole_0 = sK1 | k1_xboole_0 = sK0),
% 0.21/0.57    inference(superposition,[],[f165,f67])).
% 0.21/0.57  fof(f67,plain,(
% 0.21/0.57    ( ! [X0,X1] : (k2_relat_1(k2_zfmisc_1(X0,X1)) = X1 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 0.21/0.57    inference(cnf_transformation,[],[f28])).
% 0.21/0.57  fof(f28,plain,(
% 0.21/0.57    ! [X0,X1] : ((k2_relat_1(k2_zfmisc_1(X0,X1)) = X1 & k1_relat_1(k2_zfmisc_1(X0,X1)) = X0) | k1_xboole_0 = X1 | k1_xboole_0 = X0)),
% 0.21/0.57    inference(ennf_transformation,[],[f10])).
% 0.21/0.58  fof(f10,axiom,(
% 0.21/0.58    ! [X0,X1] : ~(~(k2_relat_1(k2_zfmisc_1(X0,X1)) = X1 & k1_relat_1(k2_zfmisc_1(X0,X1)) = X0) & k1_xboole_0 != X1 & k1_xboole_0 != X0)),
% 0.21/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t195_relat_1)).
% 0.21/0.58  fof(f165,plain,(
% 0.21/0.58    r1_tarski(k2_relat_1(sK2),k2_relat_1(k2_zfmisc_1(sK0,sK1)))),
% 0.21/0.58    inference(subsumption_resolution,[],[f164,f43])).
% 0.21/0.58  fof(f43,plain,(
% 0.21/0.58    v1_relat_1(sK2)),
% 0.21/0.58    inference(cnf_transformation,[],[f34])).
% 0.21/0.58  fof(f164,plain,(
% 0.21/0.58    r1_tarski(k2_relat_1(sK2),k2_relat_1(k2_zfmisc_1(sK0,sK1))) | ~v1_relat_1(sK2)),
% 0.21/0.58    inference(subsumption_resolution,[],[f161,f56])).
% 0.21/0.58  fof(f56,plain,(
% 0.21/0.58    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 0.21/0.58    inference(cnf_transformation,[],[f9])).
% 0.21/0.58  fof(f9,axiom,(
% 0.21/0.58    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 0.21/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).
% 0.21/0.58  fof(f161,plain,(
% 0.21/0.58    r1_tarski(k2_relat_1(sK2),k2_relat_1(k2_zfmisc_1(sK0,sK1))) | ~v1_relat_1(k2_zfmisc_1(sK0,sK1)) | ~v1_relat_1(sK2)),
% 0.21/0.58    inference(resolution,[],[f158,f52])).
% 0.21/0.58  fof(f52,plain,(
% 0.21/0.58    ( ! [X0,X1] : (~r1_tarski(X0,X1) | r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 0.21/0.58    inference(cnf_transformation,[],[f23])).
% 0.21/0.58  fof(f23,plain,(
% 0.21/0.58    ! [X0] : (! [X1] : ((r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) & r1_tarski(k1_relat_1(X0),k1_relat_1(X1))) | ~r1_tarski(X0,X1) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.21/0.58    inference(flattening,[],[f22])).
% 0.21/0.58  fof(f22,plain,(
% 0.21/0.58    ! [X0] : (! [X1] : (((r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) & r1_tarski(k1_relat_1(X0),k1_relat_1(X1))) | ~r1_tarski(X0,X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.21/0.58    inference(ennf_transformation,[],[f11])).
% 0.21/0.58  fof(f11,axiom,(
% 0.21/0.58    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => (r1_tarski(X0,X1) => (r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) & r1_tarski(k1_relat_1(X0),k1_relat_1(X1))))))),
% 0.21/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t25_relat_1)).
% 0.21/0.58  fof(f772,plain,(
% 0.21/0.58    spl4_2 | ~spl4_9),
% 0.21/0.58    inference(avatar_contradiction_clause,[],[f771])).
% 0.21/0.58  fof(f771,plain,(
% 0.21/0.58    $false | (spl4_2 | ~spl4_9)),
% 0.21/0.58    inference(subsumption_resolution,[],[f770,f50])).
% 0.21/0.58  fof(f770,plain,(
% 0.21/0.58    ~r1_tarski(k1_xboole_0,sK1) | (spl4_2 | ~spl4_9)),
% 0.21/0.58    inference(forward_demodulation,[],[f769,f49])).
% 0.21/0.58  fof(f769,plain,(
% 0.21/0.58    ~r1_tarski(k2_relat_1(k1_xboole_0),sK1) | (spl4_2 | ~spl4_9)),
% 0.21/0.58    inference(forward_demodulation,[],[f97,f239])).
% 0.21/0.58  fof(f239,plain,(
% 0.21/0.58    k1_xboole_0 = sK2 | ~spl4_9),
% 0.21/0.58    inference(superposition,[],[f208,f106])).
% 0.21/0.58  fof(f208,plain,(
% 0.21/0.58    k1_xboole_0 = k2_xboole_0(sK2,k1_xboole_0) | ~spl4_9),
% 0.21/0.58    inference(resolution,[],[f205,f59])).
% 0.21/0.58  fof(f205,plain,(
% 0.21/0.58    r1_tarski(sK2,k1_xboole_0) | ~spl4_9),
% 0.21/0.58    inference(forward_demodulation,[],[f200,f84])).
% 0.21/0.58  fof(f84,plain,(
% 0.21/0.58    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 0.21/0.58    inference(equality_resolution,[],[f64])).
% 0.21/0.58  fof(f64,plain,(
% 0.21/0.58    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X0) )),
% 0.21/0.58    inference(cnf_transformation,[],[f41])).
% 0.21/0.58  fof(f200,plain,(
% 0.21/0.58    r1_tarski(sK2,k2_zfmisc_1(k1_xboole_0,sK1)) | ~spl4_9),
% 0.21/0.58    inference(backward_demodulation,[],[f158,f193])).
% 0.21/0.58  fof(f193,plain,(
% 0.21/0.58    k1_xboole_0 = sK0 | ~spl4_9),
% 0.21/0.58    inference(avatar_component_clause,[],[f191])).
% 0.21/0.58  fof(f658,plain,(
% 0.21/0.58    spl4_1 | ~spl4_15),
% 0.21/0.58    inference(avatar_contradiction_clause,[],[f657])).
% 0.21/0.58  fof(f657,plain,(
% 0.21/0.58    $false | (spl4_1 | ~spl4_15)),
% 0.21/0.58    inference(subsumption_resolution,[],[f654,f158])).
% 0.21/0.58  fof(f654,plain,(
% 0.21/0.58    ~r1_tarski(sK2,k2_zfmisc_1(sK0,sK1)) | (spl4_1 | ~spl4_15)),
% 0.21/0.58    inference(resolution,[],[f647,f62])).
% 0.21/0.58  fof(f647,plain,(
% 0.21/0.58    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | (spl4_1 | ~spl4_15)),
% 0.21/0.58    inference(subsumption_resolution,[],[f645,f93])).
% 0.21/0.58  fof(f93,plain,(
% 0.21/0.58    sK0 != k1_relat_1(sK2) | spl4_1),
% 0.21/0.58    inference(avatar_component_clause,[],[f91])).
% 0.21/0.58  fof(f91,plain,(
% 0.21/0.58    spl4_1 <=> sK0 = k1_relat_1(sK2)),
% 0.21/0.58    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 0.21/0.58  fof(f645,plain,(
% 0.21/0.58    sK0 = k1_relat_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~spl4_15),
% 0.21/0.58    inference(superposition,[],[f444,f71])).
% 0.21/0.58  fof(f71,plain,(
% 0.21/0.58    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.21/0.58    inference(cnf_transformation,[],[f30])).
% 0.21/0.58  fof(f30,plain,(
% 0.21/0.58    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.58    inference(ennf_transformation,[],[f13])).
% 0.21/0.58  fof(f13,axiom,(
% 0.21/0.58    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 0.21/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 0.21/0.58  fof(f444,plain,(
% 0.21/0.58    sK0 = k1_relset_1(sK0,sK1,sK2) | ~spl4_15),
% 0.21/0.58    inference(avatar_component_clause,[],[f442])).
% 0.21/0.58  fof(f448,plain,(
% 0.21/0.58    spl4_14),
% 0.21/0.58    inference(avatar_contradiction_clause,[],[f447])).
% 0.21/0.58  fof(f447,plain,(
% 0.21/0.58    $false | spl4_14),
% 0.21/0.58    inference(subsumption_resolution,[],[f446,f78])).
% 0.21/0.58  fof(f446,plain,(
% 0.21/0.58    ~r2_hidden(sK2,k5_partfun1(sK0,sK1,k3_partfun1(k1_xboole_0,sK0,sK1))) | spl4_14),
% 0.21/0.58    inference(resolution,[],[f440,f81])).
% 0.21/0.58  fof(f81,plain,(
% 0.21/0.58    ( ! [X2,X0,X1] : (v1_funct_2(X2,X0,X1) | ~r2_hidden(X2,k5_partfun1(X0,X1,k3_partfun1(k1_xboole_0,X0,X1)))) )),
% 0.21/0.58    inference(definition_unfolding,[],[f69,f58])).
% 0.21/0.58  fof(f69,plain,(
% 0.21/0.58    ( ! [X2,X0,X1] : (v1_funct_2(X2,X0,X1) | ~r2_hidden(X2,k1_funct_2(X0,X1))) )),
% 0.21/0.58    inference(cnf_transformation,[],[f29])).
% 0.21/0.58  fof(f440,plain,(
% 0.21/0.58    ~v1_funct_2(sK2,sK0,sK1) | spl4_14),
% 0.21/0.58    inference(avatar_component_clause,[],[f438])).
% 0.21/0.58  fof(f257,plain,(
% 0.21/0.58    spl4_1 | ~spl4_9),
% 0.21/0.58    inference(avatar_contradiction_clause,[],[f256])).
% 0.21/0.58  fof(f256,plain,(
% 0.21/0.58    $false | (spl4_1 | ~spl4_9)),
% 0.21/0.58    inference(subsumption_resolution,[],[f247,f48])).
% 0.21/0.58  fof(f48,plain,(
% 0.21/0.58    k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.21/0.58    inference(cnf_transformation,[],[f12])).
% 0.21/0.58  fof(f247,plain,(
% 0.21/0.58    k1_xboole_0 != k1_relat_1(k1_xboole_0) | (spl4_1 | ~spl4_9)),
% 0.21/0.58    inference(backward_demodulation,[],[f202,f239])).
% 0.21/0.58  fof(f202,plain,(
% 0.21/0.58    k1_xboole_0 != k1_relat_1(sK2) | (spl4_1 | ~spl4_9)),
% 0.21/0.58    inference(backward_demodulation,[],[f93,f193])).
% 0.21/0.58  fof(f98,plain,(
% 0.21/0.58    ~spl4_1 | ~spl4_2),
% 0.21/0.58    inference(avatar_split_clause,[],[f46,f95,f91])).
% 0.21/0.58  fof(f46,plain,(
% 0.21/0.58    ~r1_tarski(k2_relat_1(sK2),sK1) | sK0 != k1_relat_1(sK2)),
% 0.21/0.58    inference(cnf_transformation,[],[f34])).
% 0.21/0.58  % SZS output end Proof for theBenchmark
% 0.21/0.58  % (24919)------------------------------
% 0.21/0.58  % (24919)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.58  % (24919)Termination reason: Refutation
% 0.21/0.58  
% 0.21/0.58  % (24919)Memory used [KB]: 11001
% 0.21/0.58  % (24919)Time elapsed: 0.145 s
% 0.21/0.58  % (24919)------------------------------
% 0.21/0.58  % (24919)------------------------------
% 0.21/0.58  % (24915)Success in time 0.214 s
%------------------------------------------------------------------------------
