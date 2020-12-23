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
% DateTime   : Thu Dec  3 13:01:50 EST 2020

% Result     : Theorem 1.38s
% Output     : Refutation 1.38s
% Verified   : 
% Statistics : Number of formulae       :  216 ( 470 expanded)
%              Number of leaves         :   47 ( 164 expanded)
%              Depth                    :   18
%              Number of atoms          :  666 (2171 expanded)
%              Number of equality atoms :   61 ( 109 expanded)
%              Maximal formula depth    :   15 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1024,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f124,f386,f388,f468,f503,f510,f512,f514,f563,f570,f574,f586,f612,f731,f757,f765,f767,f780,f818,f833,f1023])).

fof(f1023,plain,
    ( spl6_1
    | ~ spl6_52 ),
    inference(avatar_contradiction_clause,[],[f1021])).

fof(f1021,plain,
    ( $false
    | spl6_1
    | ~ spl6_52 ),
    inference(resolution,[],[f924,f244])).

fof(f244,plain,(
    v2_funct_1(k1_xboole_0) ),
    inference(superposition,[],[f106,f180])).

fof(f180,plain,(
    k1_xboole_0 = k6_partfun1(k1_xboole_0) ),
    inference(resolution,[],[f171,f152])).

fof(f152,plain,(
    ! [X0] : r1_tarski(k6_partfun1(k1_xboole_0),X0) ),
    inference(resolution,[],[f150,f94])).

fof(f94,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK5(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f60])).

fof(f60,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK5(X0,X1),X1)
          & r2_hidden(sK5(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f58,f59])).

fof(f59,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK5(X0,X1),X1)
        & r2_hidden(sK5(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f58,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f57])).

fof(f57,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(f150,plain,(
    ! [X2] : ~ r2_hidden(X2,k6_partfun1(k1_xboole_0)) ),
    inference(resolution,[],[f147,f81])).

fof(f81,plain,(
    ! [X2,X0] :
      ( ~ v1_xboole_0(X0)
      | ~ r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f52,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | r2_hidden(sK4(X0),X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f50,f51])).

fof(f51,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK4(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f50,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(rectify,[],[f49])).

fof(f49,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X1] : ~ r2_hidden(X1,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

fof(f147,plain,(
    v1_xboole_0(k6_partfun1(k1_xboole_0)) ),
    inference(resolution,[],[f133,f105])).

fof(f105,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(definition_unfolding,[],[f73,f72])).

fof(f72,plain,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

fof(f73,plain,(
    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_relset_1)).

fof(f133,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
      | v1_xboole_0(X0) ) ),
    inference(resolution,[],[f129,f78])).

fof(f78,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_xboole_0(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_subset_1)).

fof(f129,plain,(
    ! [X1] : v1_xboole_0(k2_zfmisc_1(k1_xboole_0,X1)) ),
    inference(resolution,[],[f126,f85])).

fof(f85,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X0)
      | v1_xboole_0(k2_zfmisc_1(X0,X1)) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(k2_zfmisc_1(X0,X1))
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( v1_xboole_0(X0)
     => v1_xboole_0(k2_zfmisc_1(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc4_zfmisc_1)).

fof(f126,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(resolution,[],[f125,f71])).

fof(f71,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f125,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,k1_xboole_0)
      | v1_xboole_0(X0) ) ),
    inference(resolution,[],[f84,f70])).

fof(f70,plain,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).

fof(f84,plain,(
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
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
     => ~ ( r1_xboole_0(X1,X0)
          & r1_tarski(X1,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_xboole_1)).

fof(f171,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,k1_xboole_0)
      | k1_xboole_0 = X0 ) ),
    inference(resolution,[],[f92,f71])).

fof(f92,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f56])).

fof(f56,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f55])).

fof(f55,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f106,plain,(
    ! [X0] : v2_funct_1(k6_partfun1(X0)) ),
    inference(definition_unfolding,[],[f75,f72])).

fof(f75,plain,(
    ! [X0] : v2_funct_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] :
      ( v2_funct_1(k6_relat_1(X0))
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc4_funct_1)).

fof(f924,plain,
    ( ~ v2_funct_1(k1_xboole_0)
    | spl6_1
    | ~ spl6_52 ),
    inference(backward_demodulation,[],[f119,f919])).

fof(f919,plain,
    ( k1_xboole_0 = sK2
    | ~ spl6_52 ),
    inference(resolution,[],[f914,f171])).

fof(f914,plain,
    ( ! [X0] : r1_tarski(sK2,X0)
    | ~ spl6_52 ),
    inference(resolution,[],[f912,f94])).

fof(f912,plain,
    ( ! [X2] : ~ r2_hidden(X2,sK2)
    | ~ spl6_52 ),
    inference(resolution,[],[f893,f81])).

fof(f893,plain,
    ( v1_xboole_0(sK2)
    | ~ spl6_52 ),
    inference(resolution,[],[f860,f128])).

fof(f128,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0))
      | v1_xboole_0(X0) ) ),
    inference(resolution,[],[f126,f78])).

fof(f860,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0))
    | ~ spl6_52 ),
    inference(forward_demodulation,[],[f835,f181])).

fof(f181,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X0) ),
    inference(resolution,[],[f171,f137])).

fof(f137,plain,(
    ! [X2,X1] : r1_tarski(k2_zfmisc_1(k1_xboole_0,X1),X2) ),
    inference(resolution,[],[f135,f94])).

fof(f135,plain,(
    ! [X4,X5] : ~ r2_hidden(X4,k2_zfmisc_1(k1_xboole_0,X5)) ),
    inference(resolution,[],[f129,f81])).

fof(f835,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1)))
    | ~ spl6_52 ),
    inference(backward_demodulation,[],[f64,f813])).

fof(f813,plain,
    ( k1_xboole_0 = sK0
    | ~ spl6_52 ),
    inference(avatar_component_clause,[],[f811])).

fof(f811,plain,
    ( spl6_52
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_52])])).

fof(f64,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f48])).

fof(f48,plain,
    ( ( ~ v2_funct_2(sK3,sK0)
      | ~ v2_funct_1(sK2) )
    & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0))
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    & v1_funct_2(sK3,sK1,sK0)
    & v1_funct_1(sK3)
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    & v1_funct_2(sK2,sK0,sK1)
    & v1_funct_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f26,f47,f46])).

fof(f46,plain,
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

fof(f47,plain,
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

fof(f26,plain,(
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
    inference(flattening,[],[f25])).

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
    inference(ennf_transformation,[],[f24])).

fof(f24,negated_conjecture,(
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
    inference(negated_conjecture,[],[f23])).

fof(f23,conjecture,(
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

fof(f119,plain,
    ( ~ v2_funct_1(sK2)
    | spl6_1 ),
    inference(avatar_component_clause,[],[f117])).

fof(f117,plain,
    ( spl6_1
  <=> v2_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).

fof(f833,plain,(
    spl6_53 ),
    inference(avatar_contradiction_clause,[],[f831])).

fof(f831,plain,
    ( $false
    | spl6_53 ),
    inference(resolution,[],[f817,f106])).

fof(f817,plain,
    ( ~ v2_funct_1(k6_partfun1(sK0))
    | spl6_53 ),
    inference(avatar_component_clause,[],[f815])).

fof(f815,plain,
    ( spl6_53
  <=> v2_funct_1(k6_partfun1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_53])])).

fof(f818,plain,
    ( spl6_52
    | ~ spl6_23
    | ~ spl6_24
    | ~ spl6_53
    | ~ spl6_14
    | ~ spl6_49 ),
    inference(avatar_split_clause,[],[f809,f778,f383,f815,f500,f496,f811])).

fof(f496,plain,
    ( spl6_23
  <=> v1_funct_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_23])])).

fof(f500,plain,
    ( spl6_24
  <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_24])])).

fof(f383,plain,
    ( spl6_14
  <=> k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_14])])).

fof(f778,plain,
    ( spl6_49
  <=> ! [X1,X0] :
        ( k1_xboole_0 = X0
        | ~ v2_funct_1(k1_partfun1(sK0,sK1,sK1,X0,sK2,X1))
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK1,X0)))
        | ~ v1_funct_1(X1)
        | ~ v1_funct_2(X1,sK1,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_49])])).

fof(f809,plain,
    ( ~ v2_funct_1(k6_partfun1(sK0))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_1(sK3)
    | k1_xboole_0 = sK0
    | ~ spl6_14
    | ~ spl6_49 ),
    inference(forward_demodulation,[],[f808,f385])).

fof(f385,plain,
    ( k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
    | ~ spl6_14 ),
    inference(avatar_component_clause,[],[f383])).

fof(f808,plain,
    ( ~ v2_funct_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_1(sK3)
    | k1_xboole_0 = sK0
    | ~ spl6_49 ),
    inference(resolution,[],[f779,f66])).

fof(f66,plain,(
    v1_funct_2(sK3,sK1,sK0) ),
    inference(cnf_transformation,[],[f48])).

fof(f779,plain,
    ( ! [X0,X1] :
        ( ~ v1_funct_2(X1,sK1,X0)
        | ~ v2_funct_1(k1_partfun1(sK0,sK1,sK1,X0,sK2,X1))
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK1,X0)))
        | ~ v1_funct_1(X1)
        | k1_xboole_0 = X0 )
    | ~ spl6_49 ),
    inference(avatar_component_clause,[],[f778])).

fof(f780,plain,
    ( ~ spl6_22
    | spl6_49
    | ~ spl6_32 ),
    inference(avatar_split_clause,[],[f776,f568,f778,f492])).

fof(f492,plain,
    ( spl6_22
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_22])])).

fof(f568,plain,
    ( spl6_32
  <=> ! [X1,X3,X0,X2] :
        ( k1_xboole_0 = X0
        | ~ v1_funct_2(sK2,X1,X2)
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        | ~ v1_funct_1(X3)
        | ~ v1_funct_2(X3,X2,X0)
        | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
        | ~ v2_funct_1(k1_partfun1(X1,X2,X2,X0,sK2,X3)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_32])])).

fof(f776,plain,
    ( ! [X0,X1] :
        ( k1_xboole_0 = X0
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
        | ~ v1_funct_1(X1)
        | ~ v1_funct_2(X1,sK1,X0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK1,X0)))
        | ~ v2_funct_1(k1_partfun1(sK0,sK1,sK1,X0,sK2,X1)) )
    | ~ spl6_32 ),
    inference(resolution,[],[f569,f63])).

fof(f63,plain,(
    v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f48])).

fof(f569,plain,
    ( ! [X2,X0,X3,X1] :
        ( ~ v1_funct_2(sK2,X1,X2)
        | k1_xboole_0 = X0
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        | ~ v1_funct_1(X3)
        | ~ v1_funct_2(X3,X2,X0)
        | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
        | ~ v2_funct_1(k1_partfun1(X1,X2,X2,X0,sK2,X3)) )
    | ~ spl6_32 ),
    inference(avatar_component_clause,[],[f568])).

fof(f767,plain,(
    spl6_48 ),
    inference(avatar_contradiction_clause,[],[f766])).

fof(f766,plain,
    ( $false
    | spl6_48 ),
    inference(resolution,[],[f764,f111])).

fof(f111,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f91])).

fof(f91,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f56])).

fof(f764,plain,
    ( ~ r1_tarski(sK0,sK0)
    | spl6_48 ),
    inference(avatar_component_clause,[],[f762])).

fof(f762,plain,
    ( spl6_48
  <=> r1_tarski(sK0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_48])])).

fof(f765,plain,
    ( ~ spl6_30
    | ~ spl6_48
    | ~ spl6_34
    | spl6_47 ),
    inference(avatar_split_clause,[],[f760,f754,f609,f762,f556])).

fof(f556,plain,
    ( spl6_30
  <=> v1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_30])])).

fof(f609,plain,
    ( spl6_34
  <=> sK0 = k2_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_34])])).

fof(f754,plain,
    ( spl6_47
  <=> v5_relat_1(sK3,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_47])])).

fof(f760,plain,
    ( ~ r1_tarski(sK0,sK0)
    | ~ v1_relat_1(sK3)
    | ~ spl6_34
    | spl6_47 ),
    inference(forward_demodulation,[],[f759,f611])).

fof(f611,plain,
    ( sK0 = k2_relat_1(sK3)
    | ~ spl6_34 ),
    inference(avatar_component_clause,[],[f609])).

fof(f759,plain,
    ( ~ r1_tarski(k2_relat_1(sK3),sK0)
    | ~ v1_relat_1(sK3)
    | spl6_47 ),
    inference(resolution,[],[f756,f87])).

fof(f87,plain,(
    ! [X0,X1] :
      ( v5_relat_1(X1,X0)
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f53,plain,(
    ! [X0,X1] :
      ( ( ( v5_relat_1(X1,X0)
          | ~ r1_tarski(k2_relat_1(X1),X0) )
        & ( r1_tarski(k2_relat_1(X1),X0)
          | ~ v5_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).

fof(f756,plain,
    ( ~ v5_relat_1(sK3,sK0)
    | spl6_47 ),
    inference(avatar_component_clause,[],[f754])).

fof(f757,plain,
    ( ~ spl6_30
    | ~ spl6_47
    | spl6_2
    | ~ spl6_34 ),
    inference(avatar_split_clause,[],[f748,f609,f121,f754,f556])).

fof(f121,plain,
    ( spl6_2
  <=> v2_funct_2(sK3,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).

fof(f748,plain,
    ( v2_funct_2(sK3,sK0)
    | ~ v5_relat_1(sK3,sK0)
    | ~ v1_relat_1(sK3)
    | ~ spl6_34 ),
    inference(superposition,[],[f110,f611])).

fof(f110,plain,(
    ! [X1] :
      ( v2_funct_2(X1,k2_relat_1(X1))
      | ~ v5_relat_1(X1,k2_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(equality_resolution,[],[f89])).

fof(f89,plain,(
    ! [X0,X1] :
      ( v2_funct_2(X1,X0)
      | k2_relat_1(X1) != X0
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f54,plain,(
    ! [X0,X1] :
      ( ( ( v2_funct_2(X1,X0)
          | k2_relat_1(X1) != X0 )
        & ( k2_relat_1(X1) = X0
          | ~ v2_funct_2(X1,X0) ) )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( v2_funct_2(X1,X0)
      <=> k2_relat_1(X1) = X0 )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( v2_funct_2(X1,X0)
      <=> k2_relat_1(X1) = X0 )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ( v2_funct_2(X1,X0)
      <=> k2_relat_1(X1) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_funct_2)).

fof(f731,plain,
    ( ~ spl6_30
    | spl6_33 ),
    inference(avatar_contradiction_clause,[],[f728])).

fof(f728,plain,
    ( $false
    | ~ spl6_30
    | spl6_33 ),
    inference(resolution,[],[f726,f607])).

fof(f607,plain,
    ( ~ r1_tarski(k2_relat_1(sK3),sK0)
    | spl6_33 ),
    inference(avatar_component_clause,[],[f605])).

fof(f605,plain,
    ( spl6_33
  <=> r1_tarski(k2_relat_1(sK3),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_33])])).

fof(f726,plain,
    ( r1_tarski(k2_relat_1(sK3),sK0)
    | ~ spl6_30 ),
    inference(resolution,[],[f588,f67])).

fof(f67,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f48])).

fof(f588,plain,
    ( ! [X2,X1] :
        ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
        | r1_tarski(k2_relat_1(sK3),X1) )
    | ~ spl6_30 ),
    inference(resolution,[],[f557,f252])).

fof(f252,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X0)
      | r1_tarski(k2_relat_1(X0),X2)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ) ),
    inference(resolution,[],[f97,f86])).

fof(f86,plain,(
    ! [X0,X1] :
      ( ~ v5_relat_1(X1,X0)
      | r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f97,plain,(
    ! [X2,X0,X1] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f557,plain,
    ( v1_relat_1(sK3)
    | ~ spl6_30 ),
    inference(avatar_component_clause,[],[f556])).

fof(f612,plain,
    ( ~ spl6_33
    | spl6_34
    | ~ spl6_31 ),
    inference(avatar_split_clause,[],[f603,f560,f609,f605])).

fof(f560,plain,
    ( spl6_31
  <=> r1_tarski(sK0,k2_relat_1(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_31])])).

fof(f603,plain,
    ( sK0 = k2_relat_1(sK3)
    | ~ r1_tarski(k2_relat_1(sK3),sK0)
    | ~ spl6_31 ),
    inference(resolution,[],[f562,f92])).

fof(f562,plain,
    ( r1_tarski(sK0,k2_relat_1(sK3))
    | ~ spl6_31 ),
    inference(avatar_component_clause,[],[f560])).

fof(f586,plain,(
    spl6_30 ),
    inference(avatar_contradiction_clause,[],[f584])).

fof(f584,plain,
    ( $false
    | spl6_30 ),
    inference(resolution,[],[f583,f83])).

fof(f83,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f583,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(sK1,sK0))
    | spl6_30 ),
    inference(resolution,[],[f565,f67])).

fof(f565,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK3,k1_zfmisc_1(X0))
        | ~ v1_relat_1(X0) )
    | spl6_30 ),
    inference(resolution,[],[f558,f80])).

fof(f80,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

fof(f558,plain,
    ( ~ v1_relat_1(sK3)
    | spl6_30 ),
    inference(avatar_component_clause,[],[f556])).

fof(f574,plain,(
    spl6_29 ),
    inference(avatar_contradiction_clause,[],[f572])).

fof(f572,plain,
    ( $false
    | spl6_29 ),
    inference(resolution,[],[f571,f83])).

fof(f571,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(sK0,sK1))
    | spl6_29 ),
    inference(resolution,[],[f564,f64])).

fof(f564,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK2,k1_zfmisc_1(X0))
        | ~ v1_relat_1(X0) )
    | spl6_29 ),
    inference(resolution,[],[f554,f80])).

fof(f554,plain,
    ( ~ v1_relat_1(sK2)
    | spl6_29 ),
    inference(avatar_component_clause,[],[f552])).

fof(f552,plain,
    ( spl6_29
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_29])])).

fof(f570,plain,
    ( ~ spl6_17
    | spl6_32
    | spl6_1 ),
    inference(avatar_split_clause,[],[f566,f117,f568,f457])).

fof(f457,plain,
    ( spl6_17
  <=> v1_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_17])])).

fof(f566,plain,
    ( ! [X2,X0,X3,X1] :
        ( k1_xboole_0 = X0
        | ~ v2_funct_1(k1_partfun1(X1,X2,X2,X0,sK2,X3))
        | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
        | ~ v1_funct_2(X3,X2,X0)
        | ~ v1_funct_1(X3)
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        | ~ v1_funct_2(sK2,X1,X2)
        | ~ v1_funct_1(sK2) )
    | spl6_1 ),
    inference(resolution,[],[f98,f119])).

fof(f98,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( v2_funct_1(X3)
      | k1_xboole_0 = X2
      | ~ v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ v1_funct_2(X4,X1,X2)
      | ~ v1_funct_1(X4)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
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
    inference(flattening,[],[f38])).

fof(f38,plain,(
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
    inference(ennf_transformation,[],[f22])).

fof(f22,axiom,(
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

fof(f563,plain,
    ( ~ spl6_29
    | ~ spl6_30
    | spl6_31
    | ~ spl6_14 ),
    inference(avatar_split_clause,[],[f550,f383,f560,f556,f552])).

fof(f550,plain,
    ( r1_tarski(sK0,k2_relat_1(sK3))
    | ~ v1_relat_1(sK3)
    | ~ v1_relat_1(sK2)
    | ~ spl6_14 ),
    inference(forward_demodulation,[],[f549,f108])).

fof(f108,plain,(
    ! [X0] : k2_relat_1(k6_partfun1(X0)) = X0 ),
    inference(definition_unfolding,[],[f77,f72])).

fof(f77,plain,(
    ! [X0] : k2_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

fof(f549,plain,
    ( r1_tarski(k2_relat_1(k6_partfun1(sK0)),k2_relat_1(sK3))
    | ~ v1_relat_1(sK3)
    | ~ v1_relat_1(sK2)
    | ~ spl6_14 ),
    inference(superposition,[],[f79,f538])).

fof(f538,plain,
    ( k6_partfun1(sK0) = k5_relat_1(sK2,sK3)
    | ~ spl6_14 ),
    inference(forward_demodulation,[],[f536,f385])).

fof(f536,plain,(
    k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3) ),
    inference(resolution,[],[f485,f64])).

fof(f485,plain,(
    ! [X14,X13] :
      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X13,X14)))
      | k1_partfun1(X13,X14,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3) ) ),
    inference(resolution,[],[f473,f62])).

fof(f62,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f48])).

fof(f473,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_partfun1(X0,X1,sK1,sK0,X2,sK3) = k5_relat_1(X2,sK3) ) ),
    inference(resolution,[],[f452,f67])).

fof(f452,plain,(
    ! [X6,X8,X7,X5,X9] :
      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X5,X6)))
      | k1_partfun1(X7,X8,X5,X6,X9,sK3) = k5_relat_1(X9,sK3)
      | ~ m1_subset_1(X9,k1_zfmisc_1(k2_zfmisc_1(X7,X8)))
      | ~ v1_funct_1(X9) ) ),
    inference(resolution,[],[f102,f65])).

fof(f65,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f48])).

fof(f102,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ v1_funct_1(X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f42])).

fof(f42,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

fof(f79,plain,(
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
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t45_relat_1)).

fof(f514,plain,(
    spl6_24 ),
    inference(avatar_contradiction_clause,[],[f513])).

fof(f513,plain,
    ( $false
    | spl6_24 ),
    inference(resolution,[],[f502,f67])).

fof(f502,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | spl6_24 ),
    inference(avatar_component_clause,[],[f500])).

fof(f512,plain,(
    spl6_22 ),
    inference(avatar_contradiction_clause,[],[f511])).

fof(f511,plain,
    ( $false
    | spl6_22 ),
    inference(resolution,[],[f494,f64])).

fof(f494,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | spl6_22 ),
    inference(avatar_component_clause,[],[f492])).

fof(f510,plain,(
    spl6_23 ),
    inference(avatar_contradiction_clause,[],[f509])).

fof(f509,plain,
    ( $false
    | spl6_23 ),
    inference(resolution,[],[f498,f65])).

fof(f498,plain,
    ( ~ v1_funct_1(sK3)
    | spl6_23 ),
    inference(avatar_component_clause,[],[f496])).

fof(f503,plain,
    ( ~ spl6_17
    | ~ spl6_22
    | ~ spl6_23
    | ~ spl6_24
    | spl6_12 ),
    inference(avatar_split_clause,[],[f487,f375,f500,f496,f492,f457])).

fof(f375,plain,
    ( spl6_12
  <=> m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_12])])).

fof(f487,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_1(sK3)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK2)
    | spl6_12 ),
    inference(resolution,[],[f104,f377])).

fof(f377,plain,
    ( ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | spl6_12 ),
    inference(avatar_component_clause,[],[f375])).

fof(f104,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f44])).

fof(f44,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
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
     => ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_partfun1)).

fof(f468,plain,(
    spl6_17 ),
    inference(avatar_contradiction_clause,[],[f467])).

fof(f467,plain,
    ( $false
    | spl6_17 ),
    inference(resolution,[],[f459,f62])).

fof(f459,plain,
    ( ~ v1_funct_1(sK2)
    | spl6_17 ),
    inference(avatar_component_clause,[],[f457])).

fof(f388,plain,(
    spl6_13 ),
    inference(avatar_contradiction_clause,[],[f387])).

fof(f387,plain,
    ( $false
    | spl6_13 ),
    inference(resolution,[],[f381,f105])).

fof(f381,plain,
    ( ~ m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | spl6_13 ),
    inference(avatar_component_clause,[],[f379])).

fof(f379,plain,
    ( spl6_13
  <=> m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_13])])).

fof(f386,plain,
    ( ~ spl6_12
    | ~ spl6_13
    | spl6_14 ),
    inference(avatar_split_clause,[],[f371,f383,f379,f375])).

fof(f371,plain,
    ( k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
    | ~ m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(resolution,[],[f100,f68])).

fof(f68,plain,(
    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) ),
    inference(cnf_transformation,[],[f48])).

fof(f100,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_relset_1(X0,X1,X2,X3)
      | X2 = X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f61])).

fof(f61,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( r2_relset_1(X0,X1,X2,X3)
          | X2 != X3 )
        & ( X2 = X3
          | ~ r2_relset_1(X0,X1,X2,X3) ) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(nnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f40])).

fof(f40,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

fof(f124,plain,
    ( ~ spl6_1
    | ~ spl6_2 ),
    inference(avatar_split_clause,[],[f69,f121,f117])).

fof(f69,plain,
    ( ~ v2_funct_2(sK3,sK0)
    | ~ v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f48])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 20:28:30 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.50  % (4868)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.50  % (4891)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.21/0.51  % (4874)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.21/0.51  % (4873)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.21/0.51  % (4877)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.21/0.51  % (4870)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 1.22/0.52  % (4882)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 1.22/0.52  % (4886)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 1.22/0.52  % (4867)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 1.22/0.52  % (4885)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 1.22/0.53  % (4878)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.22/0.53  % (4888)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 1.22/0.53  % (4880)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 1.22/0.53  % (4895)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 1.38/0.54  % (4871)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 1.38/0.54  % (4875)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 1.38/0.54  % (4894)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 1.38/0.54  % (4872)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 1.38/0.54  % (4892)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 1.38/0.54  % (4869)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 1.38/0.54  % (4866)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 1.38/0.54  % (4887)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 1.38/0.55  % (4888)Refutation not found, incomplete strategy% (4888)------------------------------
% 1.38/0.55  % (4888)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.38/0.55  % (4888)Termination reason: Refutation not found, incomplete strategy
% 1.38/0.55  
% 1.38/0.55  % (4888)Memory used [KB]: 10874
% 1.38/0.55  % (4888)Time elapsed: 0.094 s
% 1.38/0.55  % (4888)------------------------------
% 1.38/0.55  % (4888)------------------------------
% 1.38/0.55  % (4879)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 1.38/0.55  % (4889)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 1.38/0.55  % (4876)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 1.38/0.56  % (4884)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 1.38/0.56  % (4881)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 1.38/0.56  % (4883)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 1.38/0.56  % (4893)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 1.38/0.57  % (4890)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 1.38/0.57  % (4883)Refutation not found, incomplete strategy% (4883)------------------------------
% 1.38/0.57  % (4883)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.38/0.57  % (4883)Termination reason: Refutation not found, incomplete strategy
% 1.38/0.57  
% 1.38/0.57  % (4883)Memory used [KB]: 10746
% 1.38/0.57  % (4883)Time elapsed: 0.169 s
% 1.38/0.57  % (4883)------------------------------
% 1.38/0.57  % (4883)------------------------------
% 1.38/0.58  % (4878)Refutation found. Thanks to Tanya!
% 1.38/0.58  % SZS status Theorem for theBenchmark
% 1.38/0.60  % SZS output start Proof for theBenchmark
% 1.38/0.60  fof(f1024,plain,(
% 1.38/0.60    $false),
% 1.38/0.60    inference(avatar_sat_refutation,[],[f124,f386,f388,f468,f503,f510,f512,f514,f563,f570,f574,f586,f612,f731,f757,f765,f767,f780,f818,f833,f1023])).
% 1.38/0.60  fof(f1023,plain,(
% 1.38/0.60    spl6_1 | ~spl6_52),
% 1.38/0.60    inference(avatar_contradiction_clause,[],[f1021])).
% 1.38/0.60  fof(f1021,plain,(
% 1.38/0.60    $false | (spl6_1 | ~spl6_52)),
% 1.38/0.60    inference(resolution,[],[f924,f244])).
% 1.38/0.60  fof(f244,plain,(
% 1.38/0.60    v2_funct_1(k1_xboole_0)),
% 1.38/0.60    inference(superposition,[],[f106,f180])).
% 1.38/0.60  fof(f180,plain,(
% 1.38/0.60    k1_xboole_0 = k6_partfun1(k1_xboole_0)),
% 1.38/0.60    inference(resolution,[],[f171,f152])).
% 1.38/0.60  fof(f152,plain,(
% 1.38/0.60    ( ! [X0] : (r1_tarski(k6_partfun1(k1_xboole_0),X0)) )),
% 1.38/0.60    inference(resolution,[],[f150,f94])).
% 1.38/0.60  fof(f94,plain,(
% 1.38/0.60    ( ! [X0,X1] : (r2_hidden(sK5(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 1.38/0.60    inference(cnf_transformation,[],[f60])).
% 1.38/0.60  fof(f60,plain,(
% 1.38/0.60    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK5(X0,X1),X1) & r2_hidden(sK5(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 1.38/0.60    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f58,f59])).
% 1.38/0.60  fof(f59,plain,(
% 1.38/0.60    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK5(X0,X1),X1) & r2_hidden(sK5(X0,X1),X0)))),
% 1.38/0.60    introduced(choice_axiom,[])).
% 1.38/0.60  fof(f58,plain,(
% 1.38/0.60    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 1.38/0.60    inference(rectify,[],[f57])).
% 1.38/0.60  fof(f57,plain,(
% 1.38/0.60    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 1.38/0.60    inference(nnf_transformation,[],[f36])).
% 1.38/0.60  fof(f36,plain,(
% 1.38/0.60    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 1.38/0.60    inference(ennf_transformation,[],[f2])).
% 1.38/0.60  fof(f2,axiom,(
% 1.38/0.60    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 1.38/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).
% 1.38/0.60  fof(f150,plain,(
% 1.38/0.60    ( ! [X2] : (~r2_hidden(X2,k6_partfun1(k1_xboole_0))) )),
% 1.38/0.60    inference(resolution,[],[f147,f81])).
% 1.38/0.60  fof(f81,plain,(
% 1.38/0.60    ( ! [X2,X0] : (~v1_xboole_0(X0) | ~r2_hidden(X2,X0)) )),
% 1.38/0.60    inference(cnf_transformation,[],[f52])).
% 1.38/0.60  fof(f52,plain,(
% 1.38/0.60    ! [X0] : ((v1_xboole_0(X0) | r2_hidden(sK4(X0),X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 1.38/0.60    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f50,f51])).
% 1.38/0.60  fof(f51,plain,(
% 1.38/0.60    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK4(X0),X0))),
% 1.38/0.60    introduced(choice_axiom,[])).
% 1.38/0.60  fof(f50,plain,(
% 1.38/0.60    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 1.38/0.60    inference(rectify,[],[f49])).
% 1.38/0.60  fof(f49,plain,(
% 1.38/0.60    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0)))),
% 1.38/0.60    inference(nnf_transformation,[],[f1])).
% 1.38/0.60  fof(f1,axiom,(
% 1.38/0.60    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 1.38/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).
% 1.38/0.60  fof(f147,plain,(
% 1.38/0.60    v1_xboole_0(k6_partfun1(k1_xboole_0))),
% 1.38/0.60    inference(resolution,[],[f133,f105])).
% 1.38/0.60  fof(f105,plain,(
% 1.38/0.60    ( ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 1.38/0.60    inference(definition_unfolding,[],[f73,f72])).
% 1.38/0.60  fof(f72,plain,(
% 1.38/0.60    ( ! [X0] : (k6_relat_1(X0) = k6_partfun1(X0)) )),
% 1.38/0.60    inference(cnf_transformation,[],[f21])).
% 1.38/0.60  fof(f21,axiom,(
% 1.38/0.60    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0)),
% 1.38/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_partfun1)).
% 1.38/0.60  fof(f73,plain,(
% 1.38/0.60    ( ! [X0] : (m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 1.38/0.60    inference(cnf_transformation,[],[f17])).
% 1.38/0.60  fof(f17,axiom,(
% 1.38/0.60    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))),
% 1.38/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_relset_1)).
% 1.38/0.60  fof(f133,plain,(
% 1.38/0.60    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) | v1_xboole_0(X0)) )),
% 1.38/0.60    inference(resolution,[],[f129,f78])).
% 1.38/0.60  fof(f78,plain,(
% 1.38/0.60    ( ! [X0,X1] : (~v1_xboole_0(X0) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | v1_xboole_0(X1)) )),
% 1.38/0.60    inference(cnf_transformation,[],[f27])).
% 1.38/0.60  fof(f27,plain,(
% 1.38/0.60    ! [X0] : (! [X1] : (v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_xboole_0(X0))),
% 1.38/0.60    inference(ennf_transformation,[],[f8])).
% 1.38/0.60  fof(f8,axiom,(
% 1.38/0.60    ! [X0] : (v1_xboole_0(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_xboole_0(X1)))),
% 1.38/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_subset_1)).
% 1.38/0.60  fof(f129,plain,(
% 1.38/0.60    ( ! [X1] : (v1_xboole_0(k2_zfmisc_1(k1_xboole_0,X1))) )),
% 1.38/0.60    inference(resolution,[],[f126,f85])).
% 1.38/0.60  fof(f85,plain,(
% 1.38/0.60    ( ! [X0,X1] : (~v1_xboole_0(X0) | v1_xboole_0(k2_zfmisc_1(X0,X1))) )),
% 1.38/0.60    inference(cnf_transformation,[],[f32])).
% 1.38/0.60  fof(f32,plain,(
% 1.38/0.60    ! [X0,X1] : (v1_xboole_0(k2_zfmisc_1(X0,X1)) | ~v1_xboole_0(X0))),
% 1.38/0.60    inference(ennf_transformation,[],[f7])).
% 1.38/0.60  fof(f7,axiom,(
% 1.38/0.60    ! [X0,X1] : (v1_xboole_0(X0) => v1_xboole_0(k2_zfmisc_1(X0,X1)))),
% 1.38/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc4_zfmisc_1)).
% 1.38/0.60  fof(f126,plain,(
% 1.38/0.60    v1_xboole_0(k1_xboole_0)),
% 1.38/0.60    inference(resolution,[],[f125,f71])).
% 1.38/0.60  fof(f71,plain,(
% 1.38/0.60    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 1.38/0.60    inference(cnf_transformation,[],[f4])).
% 1.38/0.60  fof(f4,axiom,(
% 1.38/0.60    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 1.38/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).
% 1.38/0.60  fof(f125,plain,(
% 1.38/0.60    ( ! [X0] : (~r1_tarski(X0,k1_xboole_0) | v1_xboole_0(X0)) )),
% 1.38/0.60    inference(resolution,[],[f84,f70])).
% 1.38/0.60  fof(f70,plain,(
% 1.38/0.60    ( ! [X0] : (r1_xboole_0(X0,k1_xboole_0)) )),
% 1.38/0.60    inference(cnf_transformation,[],[f5])).
% 1.38/0.60  fof(f5,axiom,(
% 1.38/0.60    ! [X0] : r1_xboole_0(X0,k1_xboole_0)),
% 1.38/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).
% 1.38/0.60  fof(f84,plain,(
% 1.38/0.60    ( ! [X0,X1] : (~r1_xboole_0(X1,X0) | ~r1_tarski(X1,X0) | v1_xboole_0(X1)) )),
% 1.38/0.60    inference(cnf_transformation,[],[f31])).
% 1.38/0.60  fof(f31,plain,(
% 1.38/0.60    ! [X0,X1] : (~r1_xboole_0(X1,X0) | ~r1_tarski(X1,X0) | v1_xboole_0(X1))),
% 1.38/0.60    inference(flattening,[],[f30])).
% 1.38/0.60  fof(f30,plain,(
% 1.38/0.60    ! [X0,X1] : ((~r1_xboole_0(X1,X0) | ~r1_tarski(X1,X0)) | v1_xboole_0(X1))),
% 1.38/0.60    inference(ennf_transformation,[],[f6])).
% 1.38/0.60  fof(f6,axiom,(
% 1.38/0.60    ! [X0,X1] : (~v1_xboole_0(X1) => ~(r1_xboole_0(X1,X0) & r1_tarski(X1,X0)))),
% 1.38/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_xboole_1)).
% 1.38/0.60  fof(f171,plain,(
% 1.38/0.60    ( ! [X0] : (~r1_tarski(X0,k1_xboole_0) | k1_xboole_0 = X0) )),
% 1.38/0.60    inference(resolution,[],[f92,f71])).
% 1.38/0.60  fof(f92,plain,(
% 1.38/0.60    ( ! [X0,X1] : (~r1_tarski(X1,X0) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 1.38/0.60    inference(cnf_transformation,[],[f56])).
% 1.38/0.60  fof(f56,plain,(
% 1.38/0.60    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.38/0.60    inference(flattening,[],[f55])).
% 1.38/0.60  fof(f55,plain,(
% 1.38/0.60    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.38/0.60    inference(nnf_transformation,[],[f3])).
% 1.38/0.60  fof(f3,axiom,(
% 1.38/0.60    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.38/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 1.38/0.60  fof(f106,plain,(
% 1.38/0.60    ( ! [X0] : (v2_funct_1(k6_partfun1(X0))) )),
% 1.38/0.60    inference(definition_unfolding,[],[f75,f72])).
% 1.38/0.60  fof(f75,plain,(
% 1.38/0.60    ( ! [X0] : (v2_funct_1(k6_relat_1(X0))) )),
% 1.38/0.60    inference(cnf_transformation,[],[f14])).
% 1.38/0.60  fof(f14,axiom,(
% 1.38/0.60    ! [X0] : (v2_funct_1(k6_relat_1(X0)) & v1_relat_1(k6_relat_1(X0)))),
% 1.38/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc4_funct_1)).
% 1.38/0.60  fof(f924,plain,(
% 1.38/0.60    ~v2_funct_1(k1_xboole_0) | (spl6_1 | ~spl6_52)),
% 1.38/0.60    inference(backward_demodulation,[],[f119,f919])).
% 1.38/0.60  fof(f919,plain,(
% 1.38/0.60    k1_xboole_0 = sK2 | ~spl6_52),
% 1.38/0.60    inference(resolution,[],[f914,f171])).
% 1.38/0.60  fof(f914,plain,(
% 1.38/0.60    ( ! [X0] : (r1_tarski(sK2,X0)) ) | ~spl6_52),
% 1.38/0.60    inference(resolution,[],[f912,f94])).
% 1.38/0.60  fof(f912,plain,(
% 1.38/0.60    ( ! [X2] : (~r2_hidden(X2,sK2)) ) | ~spl6_52),
% 1.38/0.60    inference(resolution,[],[f893,f81])).
% 1.38/0.60  fof(f893,plain,(
% 1.38/0.60    v1_xboole_0(sK2) | ~spl6_52),
% 1.38/0.60    inference(resolution,[],[f860,f128])).
% 1.38/0.60  fof(f128,plain,(
% 1.38/0.60    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) | v1_xboole_0(X0)) )),
% 1.38/0.60    inference(resolution,[],[f126,f78])).
% 1.38/0.60  fof(f860,plain,(
% 1.38/0.60    m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0)) | ~spl6_52),
% 1.38/0.60    inference(forward_demodulation,[],[f835,f181])).
% 1.38/0.60  fof(f181,plain,(
% 1.38/0.60    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X0)) )),
% 1.38/0.60    inference(resolution,[],[f171,f137])).
% 1.38/0.60  fof(f137,plain,(
% 1.38/0.60    ( ! [X2,X1] : (r1_tarski(k2_zfmisc_1(k1_xboole_0,X1),X2)) )),
% 1.38/0.60    inference(resolution,[],[f135,f94])).
% 1.38/0.60  fof(f135,plain,(
% 1.38/0.60    ( ! [X4,X5] : (~r2_hidden(X4,k2_zfmisc_1(k1_xboole_0,X5))) )),
% 1.38/0.60    inference(resolution,[],[f129,f81])).
% 1.38/0.60  fof(f835,plain,(
% 1.38/0.60    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1))) | ~spl6_52),
% 1.38/0.60    inference(backward_demodulation,[],[f64,f813])).
% 1.38/0.60  fof(f813,plain,(
% 1.38/0.60    k1_xboole_0 = sK0 | ~spl6_52),
% 1.38/0.60    inference(avatar_component_clause,[],[f811])).
% 1.38/0.60  fof(f811,plain,(
% 1.38/0.60    spl6_52 <=> k1_xboole_0 = sK0),
% 1.38/0.60    introduced(avatar_definition,[new_symbols(naming,[spl6_52])])).
% 1.38/0.60  fof(f64,plain,(
% 1.38/0.60    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 1.38/0.60    inference(cnf_transformation,[],[f48])).
% 1.38/0.60  fof(f48,plain,(
% 1.38/0.60    ((~v2_funct_2(sK3,sK0) | ~v2_funct_1(sK2)) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_2(sK3,sK1,sK0) & v1_funct_1(sK3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2)),
% 1.38/0.60    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f26,f47,f46])).
% 1.38/0.60  fof(f46,plain,(
% 1.38/0.60    ? [X0,X1,X2] : (? [X3] : ((~v2_funct_2(X3,X0) | ~v2_funct_1(X2)) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (? [X3] : ((~v2_funct_2(X3,sK0) | ~v2_funct_1(sK2)) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,X3),k6_partfun1(sK0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_2(X3,sK1,sK0) & v1_funct_1(X3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2))),
% 1.38/0.60    introduced(choice_axiom,[])).
% 1.38/0.60  fof(f47,plain,(
% 1.38/0.60    ? [X3] : ((~v2_funct_2(X3,sK0) | ~v2_funct_1(sK2)) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,X3),k6_partfun1(sK0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_2(X3,sK1,sK0) & v1_funct_1(X3)) => ((~v2_funct_2(sK3,sK0) | ~v2_funct_1(sK2)) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_2(sK3,sK1,sK0) & v1_funct_1(sK3))),
% 1.38/0.60    introduced(choice_axiom,[])).
% 1.38/0.60  fof(f26,plain,(
% 1.38/0.60    ? [X0,X1,X2] : (? [X3] : ((~v2_funct_2(X3,X0) | ~v2_funct_1(X2)) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 1.38/0.60    inference(flattening,[],[f25])).
% 1.38/0.60  fof(f25,plain,(
% 1.38/0.60    ? [X0,X1,X2] : (? [X3] : (((~v2_funct_2(X3,X0) | ~v2_funct_1(X2)) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 1.38/0.60    inference(ennf_transformation,[],[f24])).
% 1.38/0.60  fof(f24,negated_conjecture,(
% 1.38/0.60    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => (r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) => (v2_funct_2(X3,X0) & v2_funct_1(X2)))))),
% 1.38/0.60    inference(negated_conjecture,[],[f23])).
% 1.38/0.60  fof(f23,conjecture,(
% 1.38/0.60    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => (r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) => (v2_funct_2(X3,X0) & v2_funct_1(X2)))))),
% 1.38/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_funct_2)).
% 1.38/0.60  fof(f119,plain,(
% 1.38/0.60    ~v2_funct_1(sK2) | spl6_1),
% 1.38/0.60    inference(avatar_component_clause,[],[f117])).
% 1.38/0.60  fof(f117,plain,(
% 1.38/0.60    spl6_1 <=> v2_funct_1(sK2)),
% 1.38/0.60    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).
% 1.38/0.60  fof(f833,plain,(
% 1.38/0.60    spl6_53),
% 1.38/0.60    inference(avatar_contradiction_clause,[],[f831])).
% 1.38/0.60  fof(f831,plain,(
% 1.38/0.60    $false | spl6_53),
% 1.38/0.60    inference(resolution,[],[f817,f106])).
% 1.38/0.60  fof(f817,plain,(
% 1.38/0.60    ~v2_funct_1(k6_partfun1(sK0)) | spl6_53),
% 1.38/0.60    inference(avatar_component_clause,[],[f815])).
% 1.38/0.60  fof(f815,plain,(
% 1.38/0.60    spl6_53 <=> v2_funct_1(k6_partfun1(sK0))),
% 1.38/0.60    introduced(avatar_definition,[new_symbols(naming,[spl6_53])])).
% 1.38/0.60  fof(f818,plain,(
% 1.38/0.60    spl6_52 | ~spl6_23 | ~spl6_24 | ~spl6_53 | ~spl6_14 | ~spl6_49),
% 1.38/0.60    inference(avatar_split_clause,[],[f809,f778,f383,f815,f500,f496,f811])).
% 1.38/0.60  fof(f496,plain,(
% 1.38/0.60    spl6_23 <=> v1_funct_1(sK3)),
% 1.38/0.60    introduced(avatar_definition,[new_symbols(naming,[spl6_23])])).
% 1.38/0.60  fof(f500,plain,(
% 1.38/0.60    spl6_24 <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 1.38/0.60    introduced(avatar_definition,[new_symbols(naming,[spl6_24])])).
% 1.38/0.60  fof(f383,plain,(
% 1.38/0.60    spl6_14 <=> k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)),
% 1.38/0.60    introduced(avatar_definition,[new_symbols(naming,[spl6_14])])).
% 1.38/0.60  fof(f778,plain,(
% 1.38/0.60    spl6_49 <=> ! [X1,X0] : (k1_xboole_0 = X0 | ~v2_funct_1(k1_partfun1(sK0,sK1,sK1,X0,sK2,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK1,X0))) | ~v1_funct_1(X1) | ~v1_funct_2(X1,sK1,X0))),
% 1.38/0.60    introduced(avatar_definition,[new_symbols(naming,[spl6_49])])).
% 1.38/0.60  fof(f809,plain,(
% 1.38/0.60    ~v2_funct_1(k6_partfun1(sK0)) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_1(sK3) | k1_xboole_0 = sK0 | (~spl6_14 | ~spl6_49)),
% 1.38/0.60    inference(forward_demodulation,[],[f808,f385])).
% 1.38/0.60  fof(f385,plain,(
% 1.38/0.60    k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) | ~spl6_14),
% 1.38/0.60    inference(avatar_component_clause,[],[f383])).
% 1.38/0.60  fof(f808,plain,(
% 1.38/0.60    ~v2_funct_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_1(sK3) | k1_xboole_0 = sK0 | ~spl6_49),
% 1.38/0.60    inference(resolution,[],[f779,f66])).
% 1.38/0.60  fof(f66,plain,(
% 1.38/0.60    v1_funct_2(sK3,sK1,sK0)),
% 1.38/0.60    inference(cnf_transformation,[],[f48])).
% 1.38/0.60  fof(f779,plain,(
% 1.38/0.60    ( ! [X0,X1] : (~v1_funct_2(X1,sK1,X0) | ~v2_funct_1(k1_partfun1(sK0,sK1,sK1,X0,sK2,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK1,X0))) | ~v1_funct_1(X1) | k1_xboole_0 = X0) ) | ~spl6_49),
% 1.38/0.60    inference(avatar_component_clause,[],[f778])).
% 1.38/0.61  fof(f780,plain,(
% 1.38/0.61    ~spl6_22 | spl6_49 | ~spl6_32),
% 1.38/0.61    inference(avatar_split_clause,[],[f776,f568,f778,f492])).
% 1.38/0.61  fof(f492,plain,(
% 1.38/0.61    spl6_22 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 1.38/0.61    introduced(avatar_definition,[new_symbols(naming,[spl6_22])])).
% 1.38/0.61  fof(f568,plain,(
% 1.38/0.61    spl6_32 <=> ! [X1,X3,X0,X2] : (k1_xboole_0 = X0 | ~v1_funct_2(sK2,X1,X2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_1(X3) | ~v1_funct_2(X3,X2,X0) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) | ~v2_funct_1(k1_partfun1(X1,X2,X2,X0,sK2,X3)))),
% 1.38/0.61    introduced(avatar_definition,[new_symbols(naming,[spl6_32])])).
% 1.38/0.61  fof(f776,plain,(
% 1.38/0.61    ( ! [X0,X1] : (k1_xboole_0 = X0 | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(X1) | ~v1_funct_2(X1,sK1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK1,X0))) | ~v2_funct_1(k1_partfun1(sK0,sK1,sK1,X0,sK2,X1))) ) | ~spl6_32),
% 1.38/0.61    inference(resolution,[],[f569,f63])).
% 1.38/0.61  fof(f63,plain,(
% 1.38/0.61    v1_funct_2(sK2,sK0,sK1)),
% 1.38/0.61    inference(cnf_transformation,[],[f48])).
% 1.38/0.61  fof(f569,plain,(
% 1.38/0.61    ( ! [X2,X0,X3,X1] : (~v1_funct_2(sK2,X1,X2) | k1_xboole_0 = X0 | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_1(X3) | ~v1_funct_2(X3,X2,X0) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) | ~v2_funct_1(k1_partfun1(X1,X2,X2,X0,sK2,X3))) ) | ~spl6_32),
% 1.38/0.61    inference(avatar_component_clause,[],[f568])).
% 1.38/0.61  fof(f767,plain,(
% 1.38/0.61    spl6_48),
% 1.38/0.61    inference(avatar_contradiction_clause,[],[f766])).
% 1.38/0.61  fof(f766,plain,(
% 1.38/0.61    $false | spl6_48),
% 1.38/0.61    inference(resolution,[],[f764,f111])).
% 1.38/0.61  fof(f111,plain,(
% 1.38/0.61    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 1.38/0.61    inference(equality_resolution,[],[f91])).
% 1.38/0.61  fof(f91,plain,(
% 1.38/0.61    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 1.38/0.61    inference(cnf_transformation,[],[f56])).
% 1.38/0.61  fof(f764,plain,(
% 1.38/0.61    ~r1_tarski(sK0,sK0) | spl6_48),
% 1.38/0.61    inference(avatar_component_clause,[],[f762])).
% 1.38/0.61  fof(f762,plain,(
% 1.38/0.61    spl6_48 <=> r1_tarski(sK0,sK0)),
% 1.38/0.61    introduced(avatar_definition,[new_symbols(naming,[spl6_48])])).
% 1.38/0.61  fof(f765,plain,(
% 1.38/0.61    ~spl6_30 | ~spl6_48 | ~spl6_34 | spl6_47),
% 1.38/0.61    inference(avatar_split_clause,[],[f760,f754,f609,f762,f556])).
% 1.38/0.61  fof(f556,plain,(
% 1.38/0.61    spl6_30 <=> v1_relat_1(sK3)),
% 1.38/0.61    introduced(avatar_definition,[new_symbols(naming,[spl6_30])])).
% 1.38/0.61  fof(f609,plain,(
% 1.38/0.61    spl6_34 <=> sK0 = k2_relat_1(sK3)),
% 1.38/0.61    introduced(avatar_definition,[new_symbols(naming,[spl6_34])])).
% 1.38/0.61  fof(f754,plain,(
% 1.38/0.61    spl6_47 <=> v5_relat_1(sK3,sK0)),
% 1.38/0.61    introduced(avatar_definition,[new_symbols(naming,[spl6_47])])).
% 1.38/0.61  fof(f760,plain,(
% 1.38/0.61    ~r1_tarski(sK0,sK0) | ~v1_relat_1(sK3) | (~spl6_34 | spl6_47)),
% 1.38/0.61    inference(forward_demodulation,[],[f759,f611])).
% 1.38/0.61  fof(f611,plain,(
% 1.38/0.61    sK0 = k2_relat_1(sK3) | ~spl6_34),
% 1.38/0.61    inference(avatar_component_clause,[],[f609])).
% 1.38/0.61  fof(f759,plain,(
% 1.38/0.61    ~r1_tarski(k2_relat_1(sK3),sK0) | ~v1_relat_1(sK3) | spl6_47),
% 1.38/0.61    inference(resolution,[],[f756,f87])).
% 1.38/0.61  fof(f87,plain,(
% 1.38/0.61    ( ! [X0,X1] : (v5_relat_1(X1,X0) | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 1.38/0.61    inference(cnf_transformation,[],[f53])).
% 1.38/0.61  fof(f53,plain,(
% 1.38/0.61    ! [X0,X1] : (((v5_relat_1(X1,X0) | ~r1_tarski(k2_relat_1(X1),X0)) & (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 1.38/0.61    inference(nnf_transformation,[],[f33])).
% 1.38/0.61  fof(f33,plain,(
% 1.38/0.61    ! [X0,X1] : ((v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 1.38/0.61    inference(ennf_transformation,[],[f10])).
% 1.38/0.61  fof(f10,axiom,(
% 1.38/0.61    ! [X0,X1] : (v1_relat_1(X1) => (v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)))),
% 1.38/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).
% 1.38/0.61  fof(f756,plain,(
% 1.38/0.61    ~v5_relat_1(sK3,sK0) | spl6_47),
% 1.38/0.61    inference(avatar_component_clause,[],[f754])).
% 1.38/0.61  fof(f757,plain,(
% 1.38/0.61    ~spl6_30 | ~spl6_47 | spl6_2 | ~spl6_34),
% 1.38/0.61    inference(avatar_split_clause,[],[f748,f609,f121,f754,f556])).
% 1.38/0.61  fof(f121,plain,(
% 1.38/0.61    spl6_2 <=> v2_funct_2(sK3,sK0)),
% 1.38/0.61    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).
% 1.38/0.61  fof(f748,plain,(
% 1.38/0.61    v2_funct_2(sK3,sK0) | ~v5_relat_1(sK3,sK0) | ~v1_relat_1(sK3) | ~spl6_34),
% 1.38/0.61    inference(superposition,[],[f110,f611])).
% 1.38/0.61  fof(f110,plain,(
% 1.38/0.61    ( ! [X1] : (v2_funct_2(X1,k2_relat_1(X1)) | ~v5_relat_1(X1,k2_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 1.38/0.61    inference(equality_resolution,[],[f89])).
% 1.38/0.61  fof(f89,plain,(
% 1.38/0.61    ( ! [X0,X1] : (v2_funct_2(X1,X0) | k2_relat_1(X1) != X0 | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 1.38/0.61    inference(cnf_transformation,[],[f54])).
% 1.38/0.61  fof(f54,plain,(
% 1.38/0.61    ! [X0,X1] : (((v2_funct_2(X1,X0) | k2_relat_1(X1) != X0) & (k2_relat_1(X1) = X0 | ~v2_funct_2(X1,X0))) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 1.38/0.61    inference(nnf_transformation,[],[f35])).
% 1.38/0.61  fof(f35,plain,(
% 1.38/0.61    ! [X0,X1] : ((v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 1.38/0.61    inference(flattening,[],[f34])).
% 1.38/0.61  fof(f34,plain,(
% 1.38/0.61    ! [X0,X1] : ((v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0) | (~v5_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 1.38/0.61    inference(ennf_transformation,[],[f18])).
% 1.38/0.61  fof(f18,axiom,(
% 1.38/0.61    ! [X0,X1] : ((v5_relat_1(X1,X0) & v1_relat_1(X1)) => (v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0))),
% 1.38/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_funct_2)).
% 1.38/0.61  fof(f731,plain,(
% 1.38/0.61    ~spl6_30 | spl6_33),
% 1.38/0.61    inference(avatar_contradiction_clause,[],[f728])).
% 1.38/0.61  fof(f728,plain,(
% 1.38/0.61    $false | (~spl6_30 | spl6_33)),
% 1.38/0.61    inference(resolution,[],[f726,f607])).
% 1.38/0.61  fof(f607,plain,(
% 1.38/0.61    ~r1_tarski(k2_relat_1(sK3),sK0) | spl6_33),
% 1.38/0.61    inference(avatar_component_clause,[],[f605])).
% 1.38/0.61  fof(f605,plain,(
% 1.38/0.61    spl6_33 <=> r1_tarski(k2_relat_1(sK3),sK0)),
% 1.38/0.61    introduced(avatar_definition,[new_symbols(naming,[spl6_33])])).
% 1.38/0.61  fof(f726,plain,(
% 1.38/0.61    r1_tarski(k2_relat_1(sK3),sK0) | ~spl6_30),
% 1.38/0.61    inference(resolution,[],[f588,f67])).
% 1.38/0.61  fof(f67,plain,(
% 1.38/0.61    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 1.38/0.61    inference(cnf_transformation,[],[f48])).
% 1.38/0.61  fof(f588,plain,(
% 1.38/0.61    ( ! [X2,X1] : (~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | r1_tarski(k2_relat_1(sK3),X1)) ) | ~spl6_30),
% 1.38/0.61    inference(resolution,[],[f557,f252])).
% 1.38/0.61  fof(f252,plain,(
% 1.38/0.61    ( ! [X2,X0,X1] : (~v1_relat_1(X0) | r1_tarski(k2_relat_1(X0),X2) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))) )),
% 1.38/0.61    inference(resolution,[],[f97,f86])).
% 1.38/0.61  fof(f86,plain,(
% 1.38/0.61    ( ! [X0,X1] : (~v5_relat_1(X1,X0) | r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 1.38/0.61    inference(cnf_transformation,[],[f53])).
% 1.38/0.61  fof(f97,plain,(
% 1.38/0.61    ( ! [X2,X0,X1] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.38/0.61    inference(cnf_transformation,[],[f37])).
% 1.38/0.61  fof(f37,plain,(
% 1.38/0.61    ! [X0,X1,X2] : ((v5_relat_1(X2,X1) & v4_relat_1(X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.38/0.61    inference(ennf_transformation,[],[f15])).
% 1.38/0.61  fof(f15,axiom,(
% 1.38/0.61    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 1.38/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).
% 1.38/0.61  fof(f557,plain,(
% 1.38/0.61    v1_relat_1(sK3) | ~spl6_30),
% 1.38/0.61    inference(avatar_component_clause,[],[f556])).
% 1.38/0.61  fof(f612,plain,(
% 1.38/0.61    ~spl6_33 | spl6_34 | ~spl6_31),
% 1.38/0.61    inference(avatar_split_clause,[],[f603,f560,f609,f605])).
% 1.38/0.61  fof(f560,plain,(
% 1.38/0.61    spl6_31 <=> r1_tarski(sK0,k2_relat_1(sK3))),
% 1.38/0.61    introduced(avatar_definition,[new_symbols(naming,[spl6_31])])).
% 1.38/0.61  fof(f603,plain,(
% 1.38/0.61    sK0 = k2_relat_1(sK3) | ~r1_tarski(k2_relat_1(sK3),sK0) | ~spl6_31),
% 1.38/0.61    inference(resolution,[],[f562,f92])).
% 1.38/0.61  fof(f562,plain,(
% 1.38/0.61    r1_tarski(sK0,k2_relat_1(sK3)) | ~spl6_31),
% 1.38/0.61    inference(avatar_component_clause,[],[f560])).
% 1.38/0.61  fof(f586,plain,(
% 1.38/0.61    spl6_30),
% 1.38/0.61    inference(avatar_contradiction_clause,[],[f584])).
% 1.38/0.61  fof(f584,plain,(
% 1.38/0.61    $false | spl6_30),
% 1.38/0.61    inference(resolution,[],[f583,f83])).
% 1.38/0.61  fof(f83,plain,(
% 1.38/0.61    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 1.38/0.61    inference(cnf_transformation,[],[f11])).
% 1.38/0.61  fof(f11,axiom,(
% 1.38/0.61    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 1.38/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).
% 1.38/0.61  fof(f583,plain,(
% 1.38/0.61    ~v1_relat_1(k2_zfmisc_1(sK1,sK0)) | spl6_30),
% 1.38/0.61    inference(resolution,[],[f565,f67])).
% 1.38/0.61  fof(f565,plain,(
% 1.38/0.61    ( ! [X0] : (~m1_subset_1(sK3,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) ) | spl6_30),
% 1.38/0.61    inference(resolution,[],[f558,f80])).
% 1.38/0.61  fof(f80,plain,(
% 1.38/0.61    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 1.38/0.61    inference(cnf_transformation,[],[f29])).
% 1.38/0.61  fof(f29,plain,(
% 1.38/0.61    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 1.38/0.61    inference(ennf_transformation,[],[f9])).
% 1.38/0.61  fof(f9,axiom,(
% 1.38/0.61    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 1.38/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).
% 1.38/0.61  fof(f558,plain,(
% 1.38/0.61    ~v1_relat_1(sK3) | spl6_30),
% 1.38/0.61    inference(avatar_component_clause,[],[f556])).
% 1.38/0.61  fof(f574,plain,(
% 1.38/0.61    spl6_29),
% 1.38/0.61    inference(avatar_contradiction_clause,[],[f572])).
% 1.38/0.61  fof(f572,plain,(
% 1.38/0.61    $false | spl6_29),
% 1.38/0.61    inference(resolution,[],[f571,f83])).
% 1.38/0.61  fof(f571,plain,(
% 1.38/0.61    ~v1_relat_1(k2_zfmisc_1(sK0,sK1)) | spl6_29),
% 1.38/0.61    inference(resolution,[],[f564,f64])).
% 1.38/0.61  fof(f564,plain,(
% 1.38/0.61    ( ! [X0] : (~m1_subset_1(sK2,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) ) | spl6_29),
% 1.38/0.61    inference(resolution,[],[f554,f80])).
% 1.38/0.61  fof(f554,plain,(
% 1.38/0.61    ~v1_relat_1(sK2) | spl6_29),
% 1.38/0.61    inference(avatar_component_clause,[],[f552])).
% 1.38/0.61  fof(f552,plain,(
% 1.38/0.61    spl6_29 <=> v1_relat_1(sK2)),
% 1.38/0.61    introduced(avatar_definition,[new_symbols(naming,[spl6_29])])).
% 1.38/0.61  fof(f570,plain,(
% 1.38/0.61    ~spl6_17 | spl6_32 | spl6_1),
% 1.38/0.61    inference(avatar_split_clause,[],[f566,f117,f568,f457])).
% 1.38/0.61  fof(f457,plain,(
% 1.38/0.61    spl6_17 <=> v1_funct_1(sK2)),
% 1.38/0.61    introduced(avatar_definition,[new_symbols(naming,[spl6_17])])).
% 1.38/0.61  fof(f566,plain,(
% 1.38/0.61    ( ! [X2,X0,X3,X1] : (k1_xboole_0 = X0 | ~v2_funct_1(k1_partfun1(X1,X2,X2,X0,sK2,X3)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) | ~v1_funct_2(X3,X2,X0) | ~v1_funct_1(X3) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(sK2,X1,X2) | ~v1_funct_1(sK2)) ) | spl6_1),
% 1.38/0.61    inference(resolution,[],[f98,f119])).
% 1.38/0.61  fof(f98,plain,(
% 1.38/0.61    ( ! [X4,X2,X0,X3,X1] : (v2_funct_1(X3) | k1_xboole_0 = X2 | ~v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X4,X1,X2) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) )),
% 1.38/0.61    inference(cnf_transformation,[],[f39])).
% 1.38/0.61  fof(f39,plain,(
% 1.38/0.61    ! [X0,X1,X2,X3] : (! [X4] : (v2_funct_1(X3) | (k1_xboole_0 != X1 & k1_xboole_0 = X2) | ~v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X4,X1,X2) | ~v1_funct_1(X4)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3))),
% 1.38/0.61    inference(flattening,[],[f38])).
% 1.38/0.61  fof(f38,plain,(
% 1.38/0.61    ! [X0,X1,X2,X3] : (! [X4] : (((v2_funct_1(X3) | (k1_xboole_0 != X1 & k1_xboole_0 = X2)) | ~v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4))) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X4,X1,X2) | ~v1_funct_1(X4))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)))),
% 1.38/0.61    inference(ennf_transformation,[],[f22])).
% 1.38/0.61  fof(f22,axiom,(
% 1.38/0.61    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X4,X1,X2) & v1_funct_1(X4)) => (v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)) => (v2_funct_1(X3) | (k1_xboole_0 != X1 & k1_xboole_0 = X2)))))),
% 1.38/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t26_funct_2)).
% 1.38/0.61  fof(f563,plain,(
% 1.38/0.61    ~spl6_29 | ~spl6_30 | spl6_31 | ~spl6_14),
% 1.38/0.61    inference(avatar_split_clause,[],[f550,f383,f560,f556,f552])).
% 1.38/0.61  fof(f550,plain,(
% 1.38/0.61    r1_tarski(sK0,k2_relat_1(sK3)) | ~v1_relat_1(sK3) | ~v1_relat_1(sK2) | ~spl6_14),
% 1.38/0.61    inference(forward_demodulation,[],[f549,f108])).
% 1.38/0.61  fof(f108,plain,(
% 1.38/0.61    ( ! [X0] : (k2_relat_1(k6_partfun1(X0)) = X0) )),
% 1.38/0.61    inference(definition_unfolding,[],[f77,f72])).
% 1.38/0.61  fof(f77,plain,(
% 1.38/0.61    ( ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0) )),
% 1.38/0.61    inference(cnf_transformation,[],[f13])).
% 1.38/0.61  fof(f13,axiom,(
% 1.38/0.61    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 1.38/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).
% 1.38/0.61  fof(f549,plain,(
% 1.38/0.61    r1_tarski(k2_relat_1(k6_partfun1(sK0)),k2_relat_1(sK3)) | ~v1_relat_1(sK3) | ~v1_relat_1(sK2) | ~spl6_14),
% 1.38/0.61    inference(superposition,[],[f79,f538])).
% 1.38/0.61  fof(f538,plain,(
% 1.38/0.61    k6_partfun1(sK0) = k5_relat_1(sK2,sK3) | ~spl6_14),
% 1.38/0.61    inference(forward_demodulation,[],[f536,f385])).
% 1.38/0.61  fof(f536,plain,(
% 1.38/0.61    k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3)),
% 1.38/0.61    inference(resolution,[],[f485,f64])).
% 1.38/0.61  fof(f485,plain,(
% 1.38/0.61    ( ! [X14,X13] : (~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X13,X14))) | k1_partfun1(X13,X14,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3)) )),
% 1.38/0.61    inference(resolution,[],[f473,f62])).
% 1.38/0.61  fof(f62,plain,(
% 1.38/0.61    v1_funct_1(sK2)),
% 1.38/0.61    inference(cnf_transformation,[],[f48])).
% 1.38/0.61  fof(f473,plain,(
% 1.38/0.61    ( ! [X2,X0,X1] : (~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_partfun1(X0,X1,sK1,sK0,X2,sK3) = k5_relat_1(X2,sK3)) )),
% 1.38/0.61    inference(resolution,[],[f452,f67])).
% 1.38/0.61  fof(f452,plain,(
% 1.38/0.61    ( ! [X6,X8,X7,X5,X9] : (~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X5,X6))) | k1_partfun1(X7,X8,X5,X6,X9,sK3) = k5_relat_1(X9,sK3) | ~m1_subset_1(X9,k1_zfmisc_1(k2_zfmisc_1(X7,X8))) | ~v1_funct_1(X9)) )),
% 1.38/0.61    inference(resolution,[],[f102,f65])).
% 1.38/0.61  fof(f65,plain,(
% 1.38/0.61    v1_funct_1(sK3)),
% 1.38/0.61    inference(cnf_transformation,[],[f48])).
% 1.38/0.61  fof(f102,plain,(
% 1.38/0.61    ( ! [X4,X2,X0,X5,X3,X1] : (~v1_funct_1(X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 1.38/0.61    inference(cnf_transformation,[],[f43])).
% 1.38/0.61  fof(f43,plain,(
% 1.38/0.61    ! [X0,X1,X2,X3,X4,X5] : (k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 1.38/0.61    inference(flattening,[],[f42])).
% 1.38/0.61  fof(f42,plain,(
% 1.38/0.61    ! [X0,X1,X2,X3,X4,X5] : (k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 1.38/0.61    inference(ennf_transformation,[],[f20])).
% 1.38/0.61  fof(f20,axiom,(
% 1.38/0.61    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5))),
% 1.38/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_partfun1)).
% 1.38/0.61  fof(f79,plain,(
% 1.38/0.61    ( ! [X0,X1] : (r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 1.38/0.61    inference(cnf_transformation,[],[f28])).
% 1.38/0.61  fof(f28,plain,(
% 1.38/0.61    ! [X0] : (! [X1] : (r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 1.38/0.61    inference(ennf_transformation,[],[f12])).
% 1.38/0.61  fof(f12,axiom,(
% 1.38/0.61    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1))))),
% 1.38/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t45_relat_1)).
% 1.38/0.61  fof(f514,plain,(
% 1.38/0.61    spl6_24),
% 1.38/0.61    inference(avatar_contradiction_clause,[],[f513])).
% 1.38/0.61  fof(f513,plain,(
% 1.38/0.61    $false | spl6_24),
% 1.38/0.61    inference(resolution,[],[f502,f67])).
% 1.38/0.61  fof(f502,plain,(
% 1.38/0.61    ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | spl6_24),
% 1.38/0.61    inference(avatar_component_clause,[],[f500])).
% 1.38/0.61  fof(f512,plain,(
% 1.38/0.61    spl6_22),
% 1.38/0.61    inference(avatar_contradiction_clause,[],[f511])).
% 1.38/0.61  fof(f511,plain,(
% 1.38/0.61    $false | spl6_22),
% 1.38/0.61    inference(resolution,[],[f494,f64])).
% 1.38/0.61  fof(f494,plain,(
% 1.38/0.61    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | spl6_22),
% 1.38/0.61    inference(avatar_component_clause,[],[f492])).
% 1.38/0.61  fof(f510,plain,(
% 1.38/0.61    spl6_23),
% 1.38/0.61    inference(avatar_contradiction_clause,[],[f509])).
% 1.38/0.61  fof(f509,plain,(
% 1.38/0.61    $false | spl6_23),
% 1.38/0.61    inference(resolution,[],[f498,f65])).
% 1.38/0.61  fof(f498,plain,(
% 1.38/0.61    ~v1_funct_1(sK3) | spl6_23),
% 1.38/0.61    inference(avatar_component_clause,[],[f496])).
% 1.38/0.61  fof(f503,plain,(
% 1.38/0.61    ~spl6_17 | ~spl6_22 | ~spl6_23 | ~spl6_24 | spl6_12),
% 1.38/0.61    inference(avatar_split_clause,[],[f487,f375,f500,f496,f492,f457])).
% 1.38/0.61  fof(f375,plain,(
% 1.38/0.61    spl6_12 <=> m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 1.38/0.61    introduced(avatar_definition,[new_symbols(naming,[spl6_12])])).
% 1.38/0.61  fof(f487,plain,(
% 1.38/0.61    ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_1(sK3) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(sK2) | spl6_12),
% 1.38/0.61    inference(resolution,[],[f104,f377])).
% 1.38/0.61  fof(f377,plain,(
% 1.38/0.61    ~m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | spl6_12),
% 1.38/0.61    inference(avatar_component_clause,[],[f375])).
% 1.38/0.61  fof(f104,plain,(
% 1.38/0.61    ( ! [X4,X2,X0,X5,X3,X1] : (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 1.38/0.61    inference(cnf_transformation,[],[f45])).
% 1.38/0.61  fof(f45,plain,(
% 1.38/0.61    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 1.38/0.61    inference(flattening,[],[f44])).
% 1.38/0.61  fof(f44,plain,(
% 1.38/0.61    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 1.38/0.61    inference(ennf_transformation,[],[f19])).
% 1.38/0.61  fof(f19,axiom,(
% 1.38/0.61    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))))),
% 1.38/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_partfun1)).
% 1.38/0.61  fof(f468,plain,(
% 1.38/0.61    spl6_17),
% 1.38/0.61    inference(avatar_contradiction_clause,[],[f467])).
% 1.38/0.61  fof(f467,plain,(
% 1.38/0.61    $false | spl6_17),
% 1.38/0.61    inference(resolution,[],[f459,f62])).
% 1.38/0.61  fof(f459,plain,(
% 1.38/0.61    ~v1_funct_1(sK2) | spl6_17),
% 1.38/0.61    inference(avatar_component_clause,[],[f457])).
% 1.38/0.61  fof(f388,plain,(
% 1.38/0.61    spl6_13),
% 1.38/0.61    inference(avatar_contradiction_clause,[],[f387])).
% 1.38/0.61  fof(f387,plain,(
% 1.38/0.61    $false | spl6_13),
% 1.38/0.61    inference(resolution,[],[f381,f105])).
% 1.38/0.61  fof(f381,plain,(
% 1.38/0.61    ~m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | spl6_13),
% 1.38/0.61    inference(avatar_component_clause,[],[f379])).
% 1.38/0.61  fof(f379,plain,(
% 1.38/0.61    spl6_13 <=> m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 1.38/0.61    introduced(avatar_definition,[new_symbols(naming,[spl6_13])])).
% 1.38/0.61  fof(f386,plain,(
% 1.38/0.61    ~spl6_12 | ~spl6_13 | spl6_14),
% 1.38/0.61    inference(avatar_split_clause,[],[f371,f383,f379,f375])).
% 1.38/0.61  fof(f371,plain,(
% 1.38/0.61    k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) | ~m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 1.38/0.61    inference(resolution,[],[f100,f68])).
% 1.38/0.61  fof(f68,plain,(
% 1.38/0.61    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0))),
% 1.38/0.61    inference(cnf_transformation,[],[f48])).
% 1.38/0.61  fof(f100,plain,(
% 1.38/0.61    ( ! [X2,X0,X3,X1] : (~r2_relset_1(X0,X1,X2,X3) | X2 = X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.38/0.61    inference(cnf_transformation,[],[f61])).
% 1.38/0.61  fof(f61,plain,(
% 1.38/0.61    ! [X0,X1,X2,X3] : (((r2_relset_1(X0,X1,X2,X3) | X2 != X3) & (X2 = X3 | ~r2_relset_1(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.38/0.61    inference(nnf_transformation,[],[f41])).
% 1.38/0.61  fof(f41,plain,(
% 1.38/0.61    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.38/0.61    inference(flattening,[],[f40])).
% 1.38/0.61  fof(f40,plain,(
% 1.38/0.61    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 1.38/0.61    inference(ennf_transformation,[],[f16])).
% 1.38/0.61  fof(f16,axiom,(
% 1.38/0.61    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => (r2_relset_1(X0,X1,X2,X3) <=> X2 = X3))),
% 1.38/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_relset_1)).
% 1.38/0.61  fof(f124,plain,(
% 1.38/0.61    ~spl6_1 | ~spl6_2),
% 1.38/0.61    inference(avatar_split_clause,[],[f69,f121,f117])).
% 1.38/0.61  fof(f69,plain,(
% 1.38/0.61    ~v2_funct_2(sK3,sK0) | ~v2_funct_1(sK2)),
% 1.38/0.61    inference(cnf_transformation,[],[f48])).
% 1.38/0.61  % SZS output end Proof for theBenchmark
% 1.38/0.61  % (4878)------------------------------
% 1.38/0.61  % (4878)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.38/0.61  % (4878)Termination reason: Refutation
% 1.38/0.61  
% 1.38/0.61  % (4878)Memory used [KB]: 6780
% 1.38/0.61  % (4878)Time elapsed: 0.173 s
% 1.38/0.61  % (4878)------------------------------
% 1.38/0.61  % (4878)------------------------------
% 1.38/0.61  % (4865)Success in time 0.25 s
%------------------------------------------------------------------------------
