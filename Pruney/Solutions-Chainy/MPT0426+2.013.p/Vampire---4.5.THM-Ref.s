%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:46:32 EST 2020

% Result     : Theorem 2.06s
% Output     : Refutation 2.06s
% Verified   : 
% Statistics : Number of formulae       :  130 ( 378 expanded)
%              Number of leaves         :   27 ( 114 expanded)
%              Depth                    :   13
%              Number of atoms          :  427 (1322 expanded)
%              Number of equality atoms :   47 ( 100 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f772,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f106,f111,f115,f176,f316,f333,f337,f770])).

fof(f770,plain,
    ( ~ spl9_3
    | ~ spl9_5 ),
    inference(avatar_contradiction_clause,[],[f769])).

fof(f769,plain,
    ( $false
    | ~ spl9_3
    | ~ spl9_5 ),
    inference(subsumption_resolution,[],[f723,f674])).

fof(f674,plain,
    ( ! [X0] : ~ r2_hidden(X0,sK3)
    | ~ spl9_3
    | ~ spl9_5 ),
    inference(forward_demodulation,[],[f673,f589])).

fof(f589,plain,
    ( sK3 = k3_xboole_0(sK3,sK3)
    | ~ spl9_3
    | ~ spl9_5 ),
    inference(subsumption_resolution,[],[f587,f357])).

fof(f357,plain,
    ( ! [X0] : m1_subset_1(sK3,X0)
    | ~ spl9_3
    | ~ spl9_5 ),
    inference(unit_resulting_resolution,[],[f69,f340,f95])).

fof(f95,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f40])).

fof(f40,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).

fof(f340,plain,
    ( r2_hidden(sK3,k1_xboole_0)
    | ~ spl9_3
    | ~ spl9_5 ),
    inference(backward_demodulation,[],[f110,f144])).

fof(f144,plain,
    ( k1_xboole_0 = sK2
    | ~ spl9_5 ),
    inference(avatar_component_clause,[],[f142])).

fof(f142,plain,
    ( spl9_5
  <=> k1_xboole_0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_5])])).

fof(f110,plain,
    ( r2_hidden(sK3,sK2)
    | ~ spl9_3 ),
    inference(avatar_component_clause,[],[f108])).

fof(f108,plain,
    ( spl9_3
  <=> r2_hidden(sK3,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_3])])).

fof(f69,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

fof(f587,plain,
    ( ! [X2] :
        ( sK3 = k3_xboole_0(sK3,sK3)
        | ~ m1_subset_1(sK3,k1_zfmisc_1(X2)) )
    | ~ spl9_3
    | ~ spl9_5 ),
    inference(superposition,[],[f388,f94])).

fof(f94,plain,(
    ! [X2,X0,X1] :
      ( k8_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1,X2] :
      ( k8_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k8_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k8_subset_1)).

fof(f388,plain,
    ( ! [X0] : sK3 = k8_subset_1(X0,sK3,sK3)
    | ~ spl9_3
    | ~ spl9_5 ),
    inference(unit_resulting_resolution,[],[f357,f93])).

fof(f93,plain,(
    ! [X0,X1] :
      ( k8_subset_1(X0,X1,X1) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( k8_subset_1(X0,X1,X1) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k8_subset_1(X0,X1,X1) = X1 ) ),
    inference(rectify,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k8_subset_1(X0,X1,X1) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k8_subset_1)).

fof(f673,plain,
    ( ! [X0] : ~ r2_hidden(X0,k3_xboole_0(sK3,sK3))
    | ~ spl9_3
    | ~ spl9_5 ),
    inference(unit_resulting_resolution,[],[f483,f72])).

fof(f72,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,k3_xboole_0(X0,X1)) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( r2_hidden(sK5(X0,X1),k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f26,f50])).

fof(f50,plain,(
    ! [X1,X0] :
      ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
     => r2_hidden(sK5(X0,X1),k3_xboole_0(X0,X1)) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X3] : ~ r2_hidden(X3,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).

fof(f483,plain,
    ( r1_xboole_0(sK3,sK3)
    | ~ spl9_3
    | ~ spl9_5 ),
    inference(unit_resulting_resolution,[],[f357,f357,f387,f79])).

fof(f79,plain,(
    ! [X2,X0,X1] :
      ( r1_xboole_0(X1,X2)
      | ~ r1_tarski(X1,k3_subset_1(X0,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f55,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( ( r1_xboole_0(X1,X2)
              | ~ r1_tarski(X1,k3_subset_1(X0,X2)) )
            & ( r1_tarski(X1,k3_subset_1(X0,X2))
              | ~ r1_xboole_0(X1,X2) ) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(nnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( r1_xboole_0(X1,X2)
          <=> r1_tarski(X1,k3_subset_1(X0,X2)) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X0))
         => ( r1_xboole_0(X1,X2)
          <=> r1_tarski(X1,k3_subset_1(X0,X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_subset_1)).

fof(f387,plain,
    ( ! [X0] : r1_tarski(sK3,X0)
    | ~ spl9_3
    | ~ spl9_5 ),
    inference(unit_resulting_resolution,[],[f357,f90])).

fof(f90,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f63])).

fof(f63,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(f723,plain,
    ( r2_hidden(sK6(sK0,sK3),sK3)
    | ~ spl9_3
    | ~ spl9_5 ),
    inference(unit_resulting_resolution,[],[f323,f674,f365])).

fof(f365,plain,
    ( ! [X0,X1] :
        ( r2_hidden(sK3,X0)
        | r2_hidden(sK6(X1,X0),X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) )
    | ~ spl9_3
    | ~ spl9_5 ),
    inference(superposition,[],[f340,f77])).

fof(f77,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK6(X0,X1),X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f54,plain,(
    ! [X0,X1] :
      ( ( r2_hidden(sK6(X0,X1),X1)
        & m1_subset_1(sK6(X0,X1),X0) )
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f30,f53])).

fof(f53,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( r2_hidden(X2,X1)
          & m1_subset_1(X2,X0) )
     => ( r2_hidden(sK6(X0,X1),X1)
        & m1_subset_1(sK6(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( r2_hidden(X2,X1)
          & m1_subset_1(X2,X0) )
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( r2_hidden(X2,X1)
          & m1_subset_1(X2,X0) )
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ~ ( ! [X2] :
              ( m1_subset_1(X2,X0)
             => ~ r2_hidden(X2,X1) )
          & k1_xboole_0 != X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_subset_1)).

fof(f323,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(sK0))
    | ~ spl9_3 ),
    inference(unit_resulting_resolution,[],[f64,f110,f95])).

fof(f64,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0))) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,
    ( ( ( ~ r2_hidden(sK1,sK3)
        & r2_hidden(sK3,sK2) )
      | ~ r2_hidden(sK1,k8_setfam_1(sK0,sK2)) )
    & ( ! [X4] :
          ( r2_hidden(sK1,X4)
          | ~ r2_hidden(X4,sK2) )
      | r2_hidden(sK1,k8_setfam_1(sK0,sK2)) )
    & r2_hidden(sK1,sK0)
    & m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0))) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f44,f46,f45])).

fof(f45,plain,
    ( ? [X0,X1,X2] :
        ( ( ? [X3] :
              ( ~ r2_hidden(X1,X3)
              & r2_hidden(X3,X2) )
          | ~ r2_hidden(X1,k8_setfam_1(X0,X2)) )
        & ( ! [X4] :
              ( r2_hidden(X1,X4)
              | ~ r2_hidden(X4,X2) )
          | r2_hidden(X1,k8_setfam_1(X0,X2)) )
        & r2_hidden(X1,X0)
        & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) )
   => ( ( ? [X3] :
            ( ~ r2_hidden(sK1,X3)
            & r2_hidden(X3,sK2) )
        | ~ r2_hidden(sK1,k8_setfam_1(sK0,sK2)) )
      & ( ! [X4] :
            ( r2_hidden(sK1,X4)
            | ~ r2_hidden(X4,sK2) )
        | r2_hidden(sK1,k8_setfam_1(sK0,sK2)) )
      & r2_hidden(sK1,sK0)
      & m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f46,plain,
    ( ? [X3] :
        ( ~ r2_hidden(sK1,X3)
        & r2_hidden(X3,sK2) )
   => ( ~ r2_hidden(sK1,sK3)
      & r2_hidden(sK3,sK2) ) ),
    introduced(choice_axiom,[])).

fof(f44,plain,(
    ? [X0,X1,X2] :
      ( ( ? [X3] :
            ( ~ r2_hidden(X1,X3)
            & r2_hidden(X3,X2) )
        | ~ r2_hidden(X1,k8_setfam_1(X0,X2)) )
      & ( ! [X4] :
            ( r2_hidden(X1,X4)
            | ~ r2_hidden(X4,X2) )
        | r2_hidden(X1,k8_setfam_1(X0,X2)) )
      & r2_hidden(X1,X0)
      & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(rectify,[],[f43])).

fof(f43,plain,(
    ? [X0,X1,X2] :
      ( ( ? [X3] :
            ( ~ r2_hidden(X1,X3)
            & r2_hidden(X3,X2) )
        | ~ r2_hidden(X1,k8_setfam_1(X0,X2)) )
      & ( ! [X3] :
            ( r2_hidden(X1,X3)
            | ~ r2_hidden(X3,X2) )
        | r2_hidden(X1,k8_setfam_1(X0,X2)) )
      & r2_hidden(X1,X0)
      & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(flattening,[],[f42])).

fof(f42,plain,(
    ? [X0,X1,X2] :
      ( ( ? [X3] :
            ( ~ r2_hidden(X1,X3)
            & r2_hidden(X3,X2) )
        | ~ r2_hidden(X1,k8_setfam_1(X0,X2)) )
      & ( ! [X3] :
            ( r2_hidden(X1,X3)
            | ~ r2_hidden(X3,X2) )
        | r2_hidden(X1,k8_setfam_1(X0,X2)) )
      & r2_hidden(X1,X0)
      & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(nnf_transformation,[],[f24])).

fof(f24,plain,(
    ? [X0,X1,X2] :
      ( ( r2_hidden(X1,k8_setfam_1(X0,X2))
      <~> ! [X3] :
            ( r2_hidden(X1,X3)
            | ~ r2_hidden(X3,X2) ) )
      & r2_hidden(X1,X0)
      & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ? [X0,X1,X2] :
      ( ( r2_hidden(X1,k8_setfam_1(X0,X2))
      <~> ! [X3] :
            ( r2_hidden(X1,X3)
            | ~ r2_hidden(X3,X2) ) )
      & r2_hidden(X1,X0)
      & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))
       => ( r2_hidden(X1,X0)
         => ( r2_hidden(X1,k8_setfam_1(X0,X2))
          <=> ! [X3] :
                ( r2_hidden(X3,X2)
               => r2_hidden(X1,X3) ) ) ) ) ),
    inference(negated_conjecture,[],[f18])).

fof(f18,conjecture,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => ( r2_hidden(X1,X0)
       => ( r2_hidden(X1,k8_setfam_1(X0,X2))
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
             => r2_hidden(X1,X3) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t58_setfam_1)).

fof(f337,plain,
    ( spl9_5
    | spl9_6 ),
    inference(avatar_split_clause,[],[f336,f146,f142])).

fof(f146,plain,
    ( spl9_6
  <=> k8_setfam_1(sK0,sK2) = k1_setfam_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_6])])).

fof(f336,plain,
    ( k8_setfam_1(sK0,sK2) = k1_setfam_1(sK2)
    | k1_xboole_0 = sK2 ),
    inference(subsumption_resolution,[],[f209,f64])).

fof(f209,plain,
    ( k8_setfam_1(sK0,sK2) = k1_setfam_1(sK2)
    | k1_xboole_0 = sK2
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0))) ),
    inference(superposition,[],[f120,f81])).

fof(f81,plain,(
    ! [X0,X1] :
      ( k8_setfam_1(X0,X1) = k6_setfam_1(X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( ( k8_setfam_1(X0,X1) = X0
          | k1_xboole_0 != X1 )
        & ( k8_setfam_1(X0,X1) = k6_setfam_1(X0,X1)
          | k1_xboole_0 = X1 ) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => ( ( k1_xboole_0 = X1
         => k8_setfam_1(X0,X1) = X0 )
        & ( k1_xboole_0 != X1
         => k8_setfam_1(X0,X1) = k6_setfam_1(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_setfam_1)).

fof(f120,plain,(
    k6_setfam_1(sK0,sK2) = k1_setfam_1(sK2) ),
    inference(unit_resulting_resolution,[],[f64,f80])).

fof(f80,plain,(
    ! [X0,X1] :
      ( k6_setfam_1(X0,X1) = k1_setfam_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( k6_setfam_1(X0,X1) = k1_setfam_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => k6_setfam_1(X0,X1) = k1_setfam_1(X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_setfam_1)).

fof(f333,plain,
    ( ~ spl9_1
    | spl9_2
    | ~ spl9_3
    | ~ spl9_6 ),
    inference(avatar_contradiction_clause,[],[f332])).

fof(f332,plain,
    ( $false
    | ~ spl9_1
    | spl9_2
    | ~ spl9_3
    | ~ spl9_6 ),
    inference(subsumption_resolution,[],[f330,f327])).

fof(f327,plain,
    ( r1_tarski(k1_setfam_1(sK2),sK3)
    | ~ spl9_3 ),
    inference(unit_resulting_resolution,[],[f110,f73])).

fof(f73,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_setfam_1(X1),X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_setfam_1(X1),X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => r1_tarski(k1_setfam_1(X1),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_setfam_1)).

fof(f330,plain,
    ( ~ r1_tarski(k1_setfam_1(sK2),sK3)
    | ~ spl9_1
    | spl9_2
    | ~ spl9_6 ),
    inference(unit_resulting_resolution,[],[f105,f317,f85])).

fof(f85,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f61])).

fof(f61,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK8(X0,X1),X1)
          & r2_hidden(sK8(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8])],[f59,f60])).

fof(f60,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK8(X0,X1),X1)
        & r2_hidden(sK8(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f59,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f58])).

fof(f58,plain,(
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

fof(f317,plain,
    ( r2_hidden(sK1,k1_setfam_1(sK2))
    | ~ spl9_1
    | ~ spl9_6 ),
    inference(forward_demodulation,[],[f100,f148])).

fof(f148,plain,
    ( k8_setfam_1(sK0,sK2) = k1_setfam_1(sK2)
    | ~ spl9_6 ),
    inference(avatar_component_clause,[],[f146])).

fof(f100,plain,
    ( r2_hidden(sK1,k8_setfam_1(sK0,sK2))
    | ~ spl9_1 ),
    inference(avatar_component_clause,[],[f99])).

fof(f99,plain,
    ( spl9_1
  <=> r2_hidden(sK1,k8_setfam_1(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_1])])).

fof(f105,plain,
    ( ~ r2_hidden(sK1,sK3)
    | spl9_2 ),
    inference(avatar_component_clause,[],[f103])).

fof(f103,plain,
    ( spl9_2
  <=> r2_hidden(sK1,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_2])])).

fof(f316,plain,
    ( spl9_1
    | ~ spl9_4
    | spl9_5
    | ~ spl9_6 ),
    inference(avatar_contradiction_clause,[],[f315])).

fof(f315,plain,
    ( $false
    | spl9_1
    | ~ spl9_4
    | spl9_5
    | ~ spl9_6 ),
    inference(subsumption_resolution,[],[f311,f299])).

fof(f299,plain,
    ( r2_hidden(sK1,sK7(sK2,k1_tarski(sK1)))
    | spl9_1
    | ~ spl9_4
    | spl9_5
    | ~ spl9_6 ),
    inference(unit_resulting_resolution,[],[f204,f114])).

fof(f114,plain,
    ( ! [X4] :
        ( ~ r2_hidden(X4,sK2)
        | r2_hidden(sK1,X4) )
    | ~ spl9_4 ),
    inference(avatar_component_clause,[],[f113])).

fof(f113,plain,
    ( spl9_4
  <=> ! [X4] :
        ( r2_hidden(sK1,X4)
        | ~ r2_hidden(X4,sK2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_4])])).

fof(f204,plain,
    ( r2_hidden(sK7(sK2,k1_tarski(sK1)),sK2)
    | spl9_1
    | spl9_5
    | ~ spl9_6 ),
    inference(unit_resulting_resolution,[],[f143,f178,f83])).

fof(f83,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,k1_setfam_1(X0))
      | k1_xboole_0 = X0
      | r2_hidden(sK7(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f57,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,k1_setfam_1(X0))
      | k1_xboole_0 = X0
      | ( ~ r1_tarski(X1,sK7(X0,X1))
        & r2_hidden(sK7(X0,X1),X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f35,f56])).

fof(f56,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r1_tarski(X1,X2)
          & r2_hidden(X2,X0) )
     => ( ~ r1_tarski(X1,sK7(X0,X1))
        & r2_hidden(sK7(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,k1_setfam_1(X0))
      | k1_xboole_0 = X0
      | ? [X2] :
          ( ~ r1_tarski(X1,X2)
          & r2_hidden(X2,X0) ) ) ),
    inference(flattening,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,k1_setfam_1(X0))
      | k1_xboole_0 = X0
      | ? [X2] :
          ( ~ r1_tarski(X1,X2)
          & r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
         => r1_tarski(X1,X2) )
     => ( r1_tarski(X1,k1_setfam_1(X0))
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_setfam_1)).

fof(f178,plain,
    ( ~ r1_tarski(k1_tarski(sK1),k1_setfam_1(sK2))
    | spl9_1
    | ~ spl9_6 ),
    inference(backward_demodulation,[],[f124,f148])).

fof(f124,plain,
    ( ~ r1_tarski(k1_tarski(sK1),k8_setfam_1(sK0,sK2))
    | spl9_1 ),
    inference(unit_resulting_resolution,[],[f101,f88])).

fof(f88,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | ~ r1_tarski(k1_tarski(X0),X1) ) ),
    inference(cnf_transformation,[],[f62])).

fof(f62,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(k1_tarski(X0),X1)
        | ~ r2_hidden(X0,X1) )
      & ( r2_hidden(X0,X1)
        | ~ r1_tarski(k1_tarski(X0),X1) ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
    <=> r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l1_zfmisc_1)).

fof(f101,plain,
    ( ~ r2_hidden(sK1,k8_setfam_1(sK0,sK2))
    | spl9_1 ),
    inference(avatar_component_clause,[],[f99])).

fof(f143,plain,
    ( k1_xboole_0 != sK2
    | spl9_5 ),
    inference(avatar_component_clause,[],[f142])).

fof(f311,plain,
    ( ~ r2_hidden(sK1,sK7(sK2,k1_tarski(sK1)))
    | spl9_1
    | spl9_5
    | ~ spl9_6 ),
    inference(unit_resulting_resolution,[],[f205,f89])).

fof(f89,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f62])).

fof(f205,plain,
    ( ~ r1_tarski(k1_tarski(sK1),sK7(sK2,k1_tarski(sK1)))
    | spl9_1
    | spl9_5
    | ~ spl9_6 ),
    inference(unit_resulting_resolution,[],[f143,f178,f84])).

fof(f84,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,k1_setfam_1(X0))
      | k1_xboole_0 = X0
      | ~ r1_tarski(X1,sK7(X0,X1)) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f176,plain,
    ( spl9_1
    | ~ spl9_5 ),
    inference(avatar_contradiction_clause,[],[f175])).

fof(f175,plain,
    ( $false
    | spl9_1
    | ~ spl9_5 ),
    inference(subsumption_resolution,[],[f174,f69])).

fof(f174,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(sK0)))
    | spl9_1
    | ~ spl9_5 ),
    inference(subsumption_resolution,[],[f173,f65])).

fof(f65,plain,(
    r2_hidden(sK1,sK0) ),
    inference(cnf_transformation,[],[f47])).

fof(f173,plain,
    ( ~ r2_hidden(sK1,sK0)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(sK0)))
    | spl9_1
    | ~ spl9_5 ),
    inference(superposition,[],[f153,f97])).

fof(f97,plain,(
    ! [X0] :
      ( k8_setfam_1(X0,k1_xboole_0) = X0
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(equality_resolution,[],[f82])).

fof(f82,plain,(
    ! [X0,X1] :
      ( k8_setfam_1(X0,X1) = X0
      | k1_xboole_0 != X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f153,plain,
    ( ~ r2_hidden(sK1,k8_setfam_1(sK0,k1_xboole_0))
    | spl9_1
    | ~ spl9_5 ),
    inference(backward_demodulation,[],[f101,f144])).

fof(f115,plain,
    ( spl9_1
    | spl9_4 ),
    inference(avatar_split_clause,[],[f66,f113,f99])).

fof(f66,plain,(
    ! [X4] :
      ( r2_hidden(sK1,X4)
      | ~ r2_hidden(X4,sK2)
      | r2_hidden(sK1,k8_setfam_1(sK0,sK2)) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f111,plain,
    ( ~ spl9_1
    | spl9_3 ),
    inference(avatar_split_clause,[],[f67,f108,f99])).

fof(f67,plain,
    ( r2_hidden(sK3,sK2)
    | ~ r2_hidden(sK1,k8_setfam_1(sK0,sK2)) ),
    inference(cnf_transformation,[],[f47])).

fof(f106,plain,
    ( ~ spl9_1
    | ~ spl9_2 ),
    inference(avatar_split_clause,[],[f68,f103,f99])).

fof(f68,plain,
    ( ~ r2_hidden(sK1,sK3)
    | ~ r2_hidden(sK1,k8_setfam_1(sK0,sK2)) ),
    inference(cnf_transformation,[],[f47])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_vampire %s %d
% 0.13/0.33  % Computer   : n016.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 14:36:49 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.49  % (27381)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.21/0.50  % (27406)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.21/0.50  % (27397)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.21/0.52  % (27385)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.52  % (27386)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.21/0.52  % (27387)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.21/0.52  % (27390)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.21/0.52  % (27400)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.21/0.52  % (27382)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.21/0.53  % (27396)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.21/0.53  % (27410)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.21/0.53  % (27389)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.21/0.53  % (27409)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.21/0.53  % (27383)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.53  % (27402)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.21/0.53  % (27403)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.21/0.53  % (27395)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.21/0.54  % (27401)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.21/0.54  % (27405)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.21/0.54  % (27384)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.21/0.54  % (27407)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.21/0.54  % (27408)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.21/0.54  % (27394)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.21/0.54  % (27391)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.21/0.54  % (27392)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.21/0.54  % (27391)Refutation not found, incomplete strategy% (27391)------------------------------
% 0.21/0.54  % (27391)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (27391)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (27391)Memory used [KB]: 10618
% 0.21/0.54  % (27391)Time elapsed: 0.138 s
% 0.21/0.54  % (27391)------------------------------
% 0.21/0.54  % (27391)------------------------------
% 0.21/0.54  % (27398)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.21/0.54  % (27393)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.54  % (27403)Refutation not found, incomplete strategy% (27403)------------------------------
% 0.21/0.54  % (27403)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (27403)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (27403)Memory used [KB]: 10746
% 0.21/0.54  % (27403)Time elapsed: 0.070 s
% 0.21/0.54  % (27403)------------------------------
% 0.21/0.54  % (27403)------------------------------
% 0.21/0.54  % (27398)Refutation not found, incomplete strategy% (27398)------------------------------
% 0.21/0.54  % (27398)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (27398)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (27398)Memory used [KB]: 10618
% 0.21/0.54  % (27398)Time elapsed: 0.139 s
% 0.21/0.54  % (27398)------------------------------
% 0.21/0.54  % (27398)------------------------------
% 0.21/0.54  % (27388)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.21/0.55  % (27404)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.21/0.58  % (27399)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 2.06/0.62  % (27407)Refutation found. Thanks to Tanya!
% 2.06/0.62  % SZS status Theorem for theBenchmark
% 2.06/0.62  % SZS output start Proof for theBenchmark
% 2.06/0.62  fof(f772,plain,(
% 2.06/0.62    $false),
% 2.06/0.62    inference(avatar_sat_refutation,[],[f106,f111,f115,f176,f316,f333,f337,f770])).
% 2.06/0.62  fof(f770,plain,(
% 2.06/0.62    ~spl9_3 | ~spl9_5),
% 2.06/0.62    inference(avatar_contradiction_clause,[],[f769])).
% 2.06/0.62  fof(f769,plain,(
% 2.06/0.62    $false | (~spl9_3 | ~spl9_5)),
% 2.06/0.62    inference(subsumption_resolution,[],[f723,f674])).
% 2.06/0.62  fof(f674,plain,(
% 2.06/0.62    ( ! [X0] : (~r2_hidden(X0,sK3)) ) | (~spl9_3 | ~spl9_5)),
% 2.06/0.62    inference(forward_demodulation,[],[f673,f589])).
% 2.06/0.62  fof(f589,plain,(
% 2.06/0.62    sK3 = k3_xboole_0(sK3,sK3) | (~spl9_3 | ~spl9_5)),
% 2.06/0.62    inference(subsumption_resolution,[],[f587,f357])).
% 2.06/0.62  fof(f357,plain,(
% 2.06/0.62    ( ! [X0] : (m1_subset_1(sK3,X0)) ) | (~spl9_3 | ~spl9_5)),
% 2.06/0.62    inference(unit_resulting_resolution,[],[f69,f340,f95])).
% 2.06/0.62  fof(f95,plain,(
% 2.06/0.62    ( ! [X2,X0,X1] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) )),
% 2.06/0.62    inference(cnf_transformation,[],[f41])).
% 2.06/0.62  fof(f41,plain,(
% 2.06/0.62    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 2.06/0.62    inference(flattening,[],[f40])).
% 2.06/0.62  fof(f40,plain,(
% 2.06/0.62    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)))),
% 2.06/0.62    inference(ennf_transformation,[],[f16])).
% 2.06/0.62  fof(f16,axiom,(
% 2.06/0.62    ! [X0,X1,X2] : ((m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1)) => m1_subset_1(X0,X2))),
% 2.06/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).
% 2.06/0.62  fof(f340,plain,(
% 2.06/0.62    r2_hidden(sK3,k1_xboole_0) | (~spl9_3 | ~spl9_5)),
% 2.06/0.62    inference(backward_demodulation,[],[f110,f144])).
% 2.06/0.62  fof(f144,plain,(
% 2.06/0.62    k1_xboole_0 = sK2 | ~spl9_5),
% 2.06/0.62    inference(avatar_component_clause,[],[f142])).
% 2.06/0.62  fof(f142,plain,(
% 2.06/0.62    spl9_5 <=> k1_xboole_0 = sK2),
% 2.06/0.62    introduced(avatar_definition,[new_symbols(naming,[spl9_5])])).
% 2.06/0.62  fof(f110,plain,(
% 2.06/0.62    r2_hidden(sK3,sK2) | ~spl9_3),
% 2.06/0.62    inference(avatar_component_clause,[],[f108])).
% 2.06/0.62  fof(f108,plain,(
% 2.06/0.62    spl9_3 <=> r2_hidden(sK3,sK2)),
% 2.06/0.62    introduced(avatar_definition,[new_symbols(naming,[spl9_3])])).
% 2.06/0.62  fof(f69,plain,(
% 2.06/0.62    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 2.06/0.62    inference(cnf_transformation,[],[f11])).
% 2.06/0.62  fof(f11,axiom,(
% 2.06/0.62    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 2.06/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).
% 2.06/0.62  fof(f587,plain,(
% 2.06/0.62    ( ! [X2] : (sK3 = k3_xboole_0(sK3,sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(X2))) ) | (~spl9_3 | ~spl9_5)),
% 2.06/0.62    inference(superposition,[],[f388,f94])).
% 2.06/0.62  fof(f94,plain,(
% 2.06/0.62    ( ! [X2,X0,X1] : (k8_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 2.06/0.62    inference(cnf_transformation,[],[f39])).
% 2.06/0.62  fof(f39,plain,(
% 2.06/0.62    ! [X0,X1,X2] : (k8_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.06/0.62    inference(ennf_transformation,[],[f7])).
% 2.06/0.62  fof(f7,axiom,(
% 2.06/0.62    ! [X0,X1,X2] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k8_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2))),
% 2.06/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k8_subset_1)).
% 2.06/0.62  fof(f388,plain,(
% 2.06/0.62    ( ! [X0] : (sK3 = k8_subset_1(X0,sK3,sK3)) ) | (~spl9_3 | ~spl9_5)),
% 2.06/0.62    inference(unit_resulting_resolution,[],[f357,f93])).
% 2.06/0.62  fof(f93,plain,(
% 2.06/0.62    ( ! [X0,X1] : (k8_subset_1(X0,X1,X1) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 2.06/0.62    inference(cnf_transformation,[],[f38])).
% 2.06/0.62  fof(f38,plain,(
% 2.06/0.62    ! [X0,X1] : (k8_subset_1(X0,X1,X1) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.06/0.62    inference(ennf_transformation,[],[f21])).
% 2.06/0.62  fof(f21,plain,(
% 2.06/0.62    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k8_subset_1(X0,X1,X1) = X1)),
% 2.06/0.62    inference(rectify,[],[f6])).
% 2.06/0.62  fof(f6,axiom,(
% 2.06/0.62    ! [X0,X1,X2] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k8_subset_1(X0,X1,X1) = X1)),
% 2.06/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k8_subset_1)).
% 2.06/0.62  fof(f673,plain,(
% 2.06/0.62    ( ! [X0] : (~r2_hidden(X0,k3_xboole_0(sK3,sK3))) ) | (~spl9_3 | ~spl9_5)),
% 2.06/0.62    inference(unit_resulting_resolution,[],[f483,f72])).
% 2.06/0.63  fof(f72,plain,(
% 2.06/0.63    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,k3_xboole_0(X0,X1))) )),
% 2.06/0.63    inference(cnf_transformation,[],[f51])).
% 2.06/0.63  fof(f51,plain,(
% 2.06/0.63    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (r2_hidden(sK5(X0,X1),k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 2.06/0.63    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f26,f50])).
% 2.06/0.63  fof(f50,plain,(
% 2.06/0.63    ! [X1,X0] : (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) => r2_hidden(sK5(X0,X1),k3_xboole_0(X0,X1)))),
% 2.06/0.63    introduced(choice_axiom,[])).
% 2.06/0.63  fof(f26,plain,(
% 2.06/0.63    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 2.06/0.63    inference(ennf_transformation,[],[f20])).
% 2.06/0.63  fof(f20,plain,(
% 2.06/0.63    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X3] : ~r2_hidden(X3,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 2.06/0.63    inference(rectify,[],[f3])).
% 2.06/0.63  fof(f3,axiom,(
% 2.06/0.63    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 2.06/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).
% 2.06/0.63  fof(f483,plain,(
% 2.06/0.63    r1_xboole_0(sK3,sK3) | (~spl9_3 | ~spl9_5)),
% 2.06/0.63    inference(unit_resulting_resolution,[],[f357,f357,f387,f79])).
% 2.06/0.63  fof(f79,plain,(
% 2.06/0.63    ( ! [X2,X0,X1] : (r1_xboole_0(X1,X2) | ~r1_tarski(X1,k3_subset_1(X0,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 2.06/0.63    inference(cnf_transformation,[],[f55])).
% 2.06/0.63  fof(f55,plain,(
% 2.06/0.63    ! [X0,X1] : (! [X2] : (((r1_xboole_0(X1,X2) | ~r1_tarski(X1,k3_subset_1(X0,X2))) & (r1_tarski(X1,k3_subset_1(X0,X2)) | ~r1_xboole_0(X1,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.06/0.63    inference(nnf_transformation,[],[f31])).
% 2.06/0.63  fof(f31,plain,(
% 2.06/0.63    ! [X0,X1] : (! [X2] : ((r1_xboole_0(X1,X2) <=> r1_tarski(X1,k3_subset_1(X0,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.06/0.63    inference(ennf_transformation,[],[f10])).
% 2.06/0.63  fof(f10,axiom,(
% 2.06/0.63    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => (r1_xboole_0(X1,X2) <=> r1_tarski(X1,k3_subset_1(X0,X2)))))),
% 2.06/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_subset_1)).
% 2.06/0.63  fof(f387,plain,(
% 2.06/0.63    ( ! [X0] : (r1_tarski(sK3,X0)) ) | (~spl9_3 | ~spl9_5)),
% 2.06/0.63    inference(unit_resulting_resolution,[],[f357,f90])).
% 2.06/0.63  fof(f90,plain,(
% 2.06/0.63    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 2.06/0.63    inference(cnf_transformation,[],[f63])).
% 2.06/0.63  fof(f63,plain,(
% 2.06/0.63    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 2.06/0.63    inference(nnf_transformation,[],[f14])).
% 2.06/0.63  fof(f14,axiom,(
% 2.06/0.63    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 2.06/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).
% 2.06/0.63  fof(f723,plain,(
% 2.06/0.63    r2_hidden(sK6(sK0,sK3),sK3) | (~spl9_3 | ~spl9_5)),
% 2.06/0.63    inference(unit_resulting_resolution,[],[f323,f674,f365])).
% 2.06/0.63  fof(f365,plain,(
% 2.06/0.63    ( ! [X0,X1] : (r2_hidden(sK3,X0) | r2_hidden(sK6(X1,X0),X0) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) ) | (~spl9_3 | ~spl9_5)),
% 2.06/0.63    inference(superposition,[],[f340,f77])).
% 2.06/0.63  fof(f77,plain,(
% 2.06/0.63    ( ! [X0,X1] : (r2_hidden(sK6(X0,X1),X1) | k1_xboole_0 = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 2.06/0.63    inference(cnf_transformation,[],[f54])).
% 2.06/0.63  fof(f54,plain,(
% 2.06/0.63    ! [X0,X1] : ((r2_hidden(sK6(X0,X1),X1) & m1_subset_1(sK6(X0,X1),X0)) | k1_xboole_0 = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.06/0.63    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f30,f53])).
% 2.06/0.63  fof(f53,plain,(
% 2.06/0.63    ! [X1,X0] : (? [X2] : (r2_hidden(X2,X1) & m1_subset_1(X2,X0)) => (r2_hidden(sK6(X0,X1),X1) & m1_subset_1(sK6(X0,X1),X0)))),
% 2.06/0.63    introduced(choice_axiom,[])).
% 2.06/0.63  fof(f30,plain,(
% 2.06/0.63    ! [X0,X1] : (? [X2] : (r2_hidden(X2,X1) & m1_subset_1(X2,X0)) | k1_xboole_0 = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.06/0.63    inference(flattening,[],[f29])).
% 2.06/0.63  fof(f29,plain,(
% 2.06/0.63    ! [X0,X1] : ((? [X2] : (r2_hidden(X2,X1) & m1_subset_1(X2,X0)) | k1_xboole_0 = X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.06/0.63    inference(ennf_transformation,[],[f8])).
% 2.06/0.63  fof(f8,axiom,(
% 2.06/0.63    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ~(! [X2] : (m1_subset_1(X2,X0) => ~r2_hidden(X2,X1)) & k1_xboole_0 != X1))),
% 2.06/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_subset_1)).
% 2.06/0.63  fof(f323,plain,(
% 2.06/0.63    m1_subset_1(sK3,k1_zfmisc_1(sK0)) | ~spl9_3),
% 2.06/0.63    inference(unit_resulting_resolution,[],[f64,f110,f95])).
% 2.06/0.63  fof(f64,plain,(
% 2.06/0.63    m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0)))),
% 2.06/0.63    inference(cnf_transformation,[],[f47])).
% 2.06/0.63  fof(f47,plain,(
% 2.06/0.63    ((~r2_hidden(sK1,sK3) & r2_hidden(sK3,sK2)) | ~r2_hidden(sK1,k8_setfam_1(sK0,sK2))) & (! [X4] : (r2_hidden(sK1,X4) | ~r2_hidden(X4,sK2)) | r2_hidden(sK1,k8_setfam_1(sK0,sK2))) & r2_hidden(sK1,sK0) & m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0)))),
% 2.06/0.63    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f44,f46,f45])).
% 2.06/0.63  fof(f45,plain,(
% 2.06/0.63    ? [X0,X1,X2] : ((? [X3] : (~r2_hidden(X1,X3) & r2_hidden(X3,X2)) | ~r2_hidden(X1,k8_setfam_1(X0,X2))) & (! [X4] : (r2_hidden(X1,X4) | ~r2_hidden(X4,X2)) | r2_hidden(X1,k8_setfam_1(X0,X2))) & r2_hidden(X1,X0) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))) => ((? [X3] : (~r2_hidden(sK1,X3) & r2_hidden(X3,sK2)) | ~r2_hidden(sK1,k8_setfam_1(sK0,sK2))) & (! [X4] : (r2_hidden(sK1,X4) | ~r2_hidden(X4,sK2)) | r2_hidden(sK1,k8_setfam_1(sK0,sK2))) & r2_hidden(sK1,sK0) & m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0))))),
% 2.06/0.63    introduced(choice_axiom,[])).
% 2.06/0.63  fof(f46,plain,(
% 2.06/0.63    ? [X3] : (~r2_hidden(sK1,X3) & r2_hidden(X3,sK2)) => (~r2_hidden(sK1,sK3) & r2_hidden(sK3,sK2))),
% 2.06/0.63    introduced(choice_axiom,[])).
% 2.06/0.63  fof(f44,plain,(
% 2.06/0.63    ? [X0,X1,X2] : ((? [X3] : (~r2_hidden(X1,X3) & r2_hidden(X3,X2)) | ~r2_hidden(X1,k8_setfam_1(X0,X2))) & (! [X4] : (r2_hidden(X1,X4) | ~r2_hidden(X4,X2)) | r2_hidden(X1,k8_setfam_1(X0,X2))) & r2_hidden(X1,X0) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 2.06/0.63    inference(rectify,[],[f43])).
% 2.06/0.63  fof(f43,plain,(
% 2.06/0.63    ? [X0,X1,X2] : ((? [X3] : (~r2_hidden(X1,X3) & r2_hidden(X3,X2)) | ~r2_hidden(X1,k8_setfam_1(X0,X2))) & (! [X3] : (r2_hidden(X1,X3) | ~r2_hidden(X3,X2)) | r2_hidden(X1,k8_setfam_1(X0,X2))) & r2_hidden(X1,X0) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 2.06/0.63    inference(flattening,[],[f42])).
% 2.06/0.63  fof(f42,plain,(
% 2.06/0.63    ? [X0,X1,X2] : (((? [X3] : (~r2_hidden(X1,X3) & r2_hidden(X3,X2)) | ~r2_hidden(X1,k8_setfam_1(X0,X2))) & (! [X3] : (r2_hidden(X1,X3) | ~r2_hidden(X3,X2)) | r2_hidden(X1,k8_setfam_1(X0,X2)))) & r2_hidden(X1,X0) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 2.06/0.63    inference(nnf_transformation,[],[f24])).
% 2.06/0.63  fof(f24,plain,(
% 2.06/0.63    ? [X0,X1,X2] : ((r2_hidden(X1,k8_setfam_1(X0,X2)) <~> ! [X3] : (r2_hidden(X1,X3) | ~r2_hidden(X3,X2))) & r2_hidden(X1,X0) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 2.06/0.63    inference(flattening,[],[f23])).
% 2.06/0.63  fof(f23,plain,(
% 2.06/0.63    ? [X0,X1,X2] : (((r2_hidden(X1,k8_setfam_1(X0,X2)) <~> ! [X3] : (r2_hidden(X1,X3) | ~r2_hidden(X3,X2))) & r2_hidden(X1,X0)) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 2.06/0.63    inference(ennf_transformation,[],[f19])).
% 2.06/0.63  fof(f19,negated_conjecture,(
% 2.06/0.63    ~! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) => (r2_hidden(X1,X0) => (r2_hidden(X1,k8_setfam_1(X0,X2)) <=> ! [X3] : (r2_hidden(X3,X2) => r2_hidden(X1,X3)))))),
% 2.06/0.63    inference(negated_conjecture,[],[f18])).
% 2.06/0.63  fof(f18,conjecture,(
% 2.06/0.63    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) => (r2_hidden(X1,X0) => (r2_hidden(X1,k8_setfam_1(X0,X2)) <=> ! [X3] : (r2_hidden(X3,X2) => r2_hidden(X1,X3)))))),
% 2.06/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t58_setfam_1)).
% 2.06/0.63  fof(f337,plain,(
% 2.06/0.63    spl9_5 | spl9_6),
% 2.06/0.63    inference(avatar_split_clause,[],[f336,f146,f142])).
% 2.06/0.63  fof(f146,plain,(
% 2.06/0.63    spl9_6 <=> k8_setfam_1(sK0,sK2) = k1_setfam_1(sK2)),
% 2.06/0.63    introduced(avatar_definition,[new_symbols(naming,[spl9_6])])).
% 2.06/0.63  fof(f336,plain,(
% 2.06/0.63    k8_setfam_1(sK0,sK2) = k1_setfam_1(sK2) | k1_xboole_0 = sK2),
% 2.06/0.63    inference(subsumption_resolution,[],[f209,f64])).
% 2.06/0.63  fof(f209,plain,(
% 2.06/0.63    k8_setfam_1(sK0,sK2) = k1_setfam_1(sK2) | k1_xboole_0 = sK2 | ~m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0)))),
% 2.06/0.63    inference(superposition,[],[f120,f81])).
% 2.06/0.63  fof(f81,plain,(
% 2.06/0.63    ( ! [X0,X1] : (k8_setfam_1(X0,X1) = k6_setfam_1(X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 2.06/0.63    inference(cnf_transformation,[],[f33])).
% 2.06/0.63  fof(f33,plain,(
% 2.06/0.63    ! [X0,X1] : (((k8_setfam_1(X0,X1) = X0 | k1_xboole_0 != X1) & (k8_setfam_1(X0,X1) = k6_setfam_1(X0,X1) | k1_xboole_0 = X1)) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 2.06/0.63    inference(ennf_transformation,[],[f12])).
% 2.06/0.63  fof(f12,axiom,(
% 2.06/0.63    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => ((k1_xboole_0 = X1 => k8_setfam_1(X0,X1) = X0) & (k1_xboole_0 != X1 => k8_setfam_1(X0,X1) = k6_setfam_1(X0,X1))))),
% 2.06/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_setfam_1)).
% 2.06/0.63  fof(f120,plain,(
% 2.06/0.63    k6_setfam_1(sK0,sK2) = k1_setfam_1(sK2)),
% 2.06/0.63    inference(unit_resulting_resolution,[],[f64,f80])).
% 2.06/0.63  fof(f80,plain,(
% 2.06/0.63    ( ! [X0,X1] : (k6_setfam_1(X0,X1) = k1_setfam_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 2.06/0.63    inference(cnf_transformation,[],[f32])).
% 2.06/0.63  fof(f32,plain,(
% 2.06/0.63    ! [X0,X1] : (k6_setfam_1(X0,X1) = k1_setfam_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 2.06/0.63    inference(ennf_transformation,[],[f13])).
% 2.06/0.63  fof(f13,axiom,(
% 2.06/0.63    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => k6_setfam_1(X0,X1) = k1_setfam_1(X1))),
% 2.06/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_setfam_1)).
% 2.06/0.63  fof(f333,plain,(
% 2.06/0.63    ~spl9_1 | spl9_2 | ~spl9_3 | ~spl9_6),
% 2.06/0.63    inference(avatar_contradiction_clause,[],[f332])).
% 2.06/0.63  fof(f332,plain,(
% 2.06/0.63    $false | (~spl9_1 | spl9_2 | ~spl9_3 | ~spl9_6)),
% 2.06/0.63    inference(subsumption_resolution,[],[f330,f327])).
% 2.06/0.63  fof(f327,plain,(
% 2.06/0.63    r1_tarski(k1_setfam_1(sK2),sK3) | ~spl9_3),
% 2.06/0.63    inference(unit_resulting_resolution,[],[f110,f73])).
% 2.06/0.63  fof(f73,plain,(
% 2.06/0.63    ( ! [X0,X1] : (r1_tarski(k1_setfam_1(X1),X0) | ~r2_hidden(X0,X1)) )),
% 2.06/0.63    inference(cnf_transformation,[],[f27])).
% 2.06/0.63  fof(f27,plain,(
% 2.06/0.63    ! [X0,X1] : (r1_tarski(k1_setfam_1(X1),X0) | ~r2_hidden(X0,X1))),
% 2.06/0.63    inference(ennf_transformation,[],[f15])).
% 2.06/0.63  fof(f15,axiom,(
% 2.06/0.63    ! [X0,X1] : (r2_hidden(X0,X1) => r1_tarski(k1_setfam_1(X1),X0))),
% 2.06/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_setfam_1)).
% 2.06/0.63  fof(f330,plain,(
% 2.06/0.63    ~r1_tarski(k1_setfam_1(sK2),sK3) | (~spl9_1 | spl9_2 | ~spl9_6)),
% 2.06/0.63    inference(unit_resulting_resolution,[],[f105,f317,f85])).
% 2.06/0.63  fof(f85,plain,(
% 2.06/0.63    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r1_tarski(X0,X1)) )),
% 2.06/0.63    inference(cnf_transformation,[],[f61])).
% 2.06/0.63  fof(f61,plain,(
% 2.06/0.63    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK8(X0,X1),X1) & r2_hidden(sK8(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 2.06/0.63    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8])],[f59,f60])).
% 2.06/0.63  fof(f60,plain,(
% 2.06/0.63    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK8(X0,X1),X1) & r2_hidden(sK8(X0,X1),X0)))),
% 2.06/0.63    introduced(choice_axiom,[])).
% 2.06/0.63  fof(f59,plain,(
% 2.06/0.63    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 2.06/0.63    inference(rectify,[],[f58])).
% 2.06/0.63  fof(f58,plain,(
% 2.06/0.63    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 2.06/0.63    inference(nnf_transformation,[],[f36])).
% 2.06/0.63  fof(f36,plain,(
% 2.06/0.63    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 2.06/0.63    inference(ennf_transformation,[],[f2])).
% 2.06/0.63  fof(f2,axiom,(
% 2.06/0.63    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 2.06/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).
% 2.06/0.63  fof(f317,plain,(
% 2.06/0.63    r2_hidden(sK1,k1_setfam_1(sK2)) | (~spl9_1 | ~spl9_6)),
% 2.06/0.63    inference(forward_demodulation,[],[f100,f148])).
% 2.06/0.63  fof(f148,plain,(
% 2.06/0.63    k8_setfam_1(sK0,sK2) = k1_setfam_1(sK2) | ~spl9_6),
% 2.06/0.63    inference(avatar_component_clause,[],[f146])).
% 2.06/0.63  fof(f100,plain,(
% 2.06/0.63    r2_hidden(sK1,k8_setfam_1(sK0,sK2)) | ~spl9_1),
% 2.06/0.63    inference(avatar_component_clause,[],[f99])).
% 2.06/0.63  fof(f99,plain,(
% 2.06/0.63    spl9_1 <=> r2_hidden(sK1,k8_setfam_1(sK0,sK2))),
% 2.06/0.63    introduced(avatar_definition,[new_symbols(naming,[spl9_1])])).
% 2.06/0.63  fof(f105,plain,(
% 2.06/0.63    ~r2_hidden(sK1,sK3) | spl9_2),
% 2.06/0.63    inference(avatar_component_clause,[],[f103])).
% 2.06/0.63  fof(f103,plain,(
% 2.06/0.63    spl9_2 <=> r2_hidden(sK1,sK3)),
% 2.06/0.63    introduced(avatar_definition,[new_symbols(naming,[spl9_2])])).
% 2.06/0.63  fof(f316,plain,(
% 2.06/0.63    spl9_1 | ~spl9_4 | spl9_5 | ~spl9_6),
% 2.06/0.63    inference(avatar_contradiction_clause,[],[f315])).
% 2.06/0.63  fof(f315,plain,(
% 2.06/0.63    $false | (spl9_1 | ~spl9_4 | spl9_5 | ~spl9_6)),
% 2.06/0.63    inference(subsumption_resolution,[],[f311,f299])).
% 2.06/0.63  fof(f299,plain,(
% 2.06/0.63    r2_hidden(sK1,sK7(sK2,k1_tarski(sK1))) | (spl9_1 | ~spl9_4 | spl9_5 | ~spl9_6)),
% 2.06/0.63    inference(unit_resulting_resolution,[],[f204,f114])).
% 2.06/0.63  fof(f114,plain,(
% 2.06/0.63    ( ! [X4] : (~r2_hidden(X4,sK2) | r2_hidden(sK1,X4)) ) | ~spl9_4),
% 2.06/0.63    inference(avatar_component_clause,[],[f113])).
% 2.06/0.63  fof(f113,plain,(
% 2.06/0.63    spl9_4 <=> ! [X4] : (r2_hidden(sK1,X4) | ~r2_hidden(X4,sK2))),
% 2.06/0.63    introduced(avatar_definition,[new_symbols(naming,[spl9_4])])).
% 2.06/0.63  fof(f204,plain,(
% 2.06/0.63    r2_hidden(sK7(sK2,k1_tarski(sK1)),sK2) | (spl9_1 | spl9_5 | ~spl9_6)),
% 2.06/0.63    inference(unit_resulting_resolution,[],[f143,f178,f83])).
% 2.06/0.63  fof(f83,plain,(
% 2.06/0.63    ( ! [X0,X1] : (r1_tarski(X1,k1_setfam_1(X0)) | k1_xboole_0 = X0 | r2_hidden(sK7(X0,X1),X0)) )),
% 2.06/0.63    inference(cnf_transformation,[],[f57])).
% 2.06/0.63  fof(f57,plain,(
% 2.06/0.63    ! [X0,X1] : (r1_tarski(X1,k1_setfam_1(X0)) | k1_xboole_0 = X0 | (~r1_tarski(X1,sK7(X0,X1)) & r2_hidden(sK7(X0,X1),X0)))),
% 2.06/0.63    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f35,f56])).
% 2.06/0.63  fof(f56,plain,(
% 2.06/0.63    ! [X1,X0] : (? [X2] : (~r1_tarski(X1,X2) & r2_hidden(X2,X0)) => (~r1_tarski(X1,sK7(X0,X1)) & r2_hidden(sK7(X0,X1),X0)))),
% 2.06/0.63    introduced(choice_axiom,[])).
% 2.06/0.63  fof(f35,plain,(
% 2.06/0.63    ! [X0,X1] : (r1_tarski(X1,k1_setfam_1(X0)) | k1_xboole_0 = X0 | ? [X2] : (~r1_tarski(X1,X2) & r2_hidden(X2,X0)))),
% 2.06/0.63    inference(flattening,[],[f34])).
% 2.06/0.63  fof(f34,plain,(
% 2.06/0.63    ! [X0,X1] : ((r1_tarski(X1,k1_setfam_1(X0)) | k1_xboole_0 = X0) | ? [X2] : (~r1_tarski(X1,X2) & r2_hidden(X2,X0)))),
% 2.06/0.63    inference(ennf_transformation,[],[f17])).
% 2.06/0.63  fof(f17,axiom,(
% 2.06/0.63    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) => r1_tarski(X1,X2)) => (r1_tarski(X1,k1_setfam_1(X0)) | k1_xboole_0 = X0))),
% 2.06/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_setfam_1)).
% 2.06/0.63  fof(f178,plain,(
% 2.06/0.63    ~r1_tarski(k1_tarski(sK1),k1_setfam_1(sK2)) | (spl9_1 | ~spl9_6)),
% 2.06/0.63    inference(backward_demodulation,[],[f124,f148])).
% 2.06/0.63  fof(f124,plain,(
% 2.06/0.63    ~r1_tarski(k1_tarski(sK1),k8_setfam_1(sK0,sK2)) | spl9_1),
% 2.06/0.63    inference(unit_resulting_resolution,[],[f101,f88])).
% 2.06/0.63  fof(f88,plain,(
% 2.06/0.63    ( ! [X0,X1] : (r2_hidden(X0,X1) | ~r1_tarski(k1_tarski(X0),X1)) )),
% 2.06/0.63    inference(cnf_transformation,[],[f62])).
% 2.06/0.63  fof(f62,plain,(
% 2.06/0.63    ! [X0,X1] : ((r1_tarski(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) & (r2_hidden(X0,X1) | ~r1_tarski(k1_tarski(X0),X1)))),
% 2.06/0.63    inference(nnf_transformation,[],[f5])).
% 2.06/0.63  fof(f5,axiom,(
% 2.06/0.63    ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) <=> r2_hidden(X0,X1))),
% 2.06/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l1_zfmisc_1)).
% 2.06/0.63  fof(f101,plain,(
% 2.06/0.63    ~r2_hidden(sK1,k8_setfam_1(sK0,sK2)) | spl9_1),
% 2.06/0.63    inference(avatar_component_clause,[],[f99])).
% 2.06/0.63  fof(f143,plain,(
% 2.06/0.63    k1_xboole_0 != sK2 | spl9_5),
% 2.06/0.63    inference(avatar_component_clause,[],[f142])).
% 2.06/0.63  fof(f311,plain,(
% 2.06/0.63    ~r2_hidden(sK1,sK7(sK2,k1_tarski(sK1))) | (spl9_1 | spl9_5 | ~spl9_6)),
% 2.06/0.63    inference(unit_resulting_resolution,[],[f205,f89])).
% 2.06/0.63  fof(f89,plain,(
% 2.06/0.63    ( ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) )),
% 2.06/0.63    inference(cnf_transformation,[],[f62])).
% 2.06/0.63  fof(f205,plain,(
% 2.06/0.63    ~r1_tarski(k1_tarski(sK1),sK7(sK2,k1_tarski(sK1))) | (spl9_1 | spl9_5 | ~spl9_6)),
% 2.06/0.63    inference(unit_resulting_resolution,[],[f143,f178,f84])).
% 2.06/0.63  fof(f84,plain,(
% 2.06/0.63    ( ! [X0,X1] : (r1_tarski(X1,k1_setfam_1(X0)) | k1_xboole_0 = X0 | ~r1_tarski(X1,sK7(X0,X1))) )),
% 2.06/0.63    inference(cnf_transformation,[],[f57])).
% 2.06/0.63  fof(f176,plain,(
% 2.06/0.63    spl9_1 | ~spl9_5),
% 2.06/0.63    inference(avatar_contradiction_clause,[],[f175])).
% 2.06/0.63  fof(f175,plain,(
% 2.06/0.63    $false | (spl9_1 | ~spl9_5)),
% 2.06/0.63    inference(subsumption_resolution,[],[f174,f69])).
% 2.06/0.63  fof(f174,plain,(
% 2.06/0.63    ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(sK0))) | (spl9_1 | ~spl9_5)),
% 2.06/0.63    inference(subsumption_resolution,[],[f173,f65])).
% 2.06/0.63  fof(f65,plain,(
% 2.06/0.63    r2_hidden(sK1,sK0)),
% 2.06/0.63    inference(cnf_transformation,[],[f47])).
% 2.06/0.63  fof(f173,plain,(
% 2.06/0.63    ~r2_hidden(sK1,sK0) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(sK0))) | (spl9_1 | ~spl9_5)),
% 2.06/0.63    inference(superposition,[],[f153,f97])).
% 2.06/0.63  fof(f97,plain,(
% 2.06/0.63    ( ! [X0] : (k8_setfam_1(X0,k1_xboole_0) = X0 | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 2.06/0.63    inference(equality_resolution,[],[f82])).
% 2.06/0.63  fof(f82,plain,(
% 2.06/0.63    ( ! [X0,X1] : (k8_setfam_1(X0,X1) = X0 | k1_xboole_0 != X1 | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 2.06/0.63    inference(cnf_transformation,[],[f33])).
% 2.06/0.63  fof(f153,plain,(
% 2.06/0.63    ~r2_hidden(sK1,k8_setfam_1(sK0,k1_xboole_0)) | (spl9_1 | ~spl9_5)),
% 2.06/0.63    inference(backward_demodulation,[],[f101,f144])).
% 2.06/0.63  fof(f115,plain,(
% 2.06/0.63    spl9_1 | spl9_4),
% 2.06/0.63    inference(avatar_split_clause,[],[f66,f113,f99])).
% 2.06/0.63  fof(f66,plain,(
% 2.06/0.63    ( ! [X4] : (r2_hidden(sK1,X4) | ~r2_hidden(X4,sK2) | r2_hidden(sK1,k8_setfam_1(sK0,sK2))) )),
% 2.06/0.63    inference(cnf_transformation,[],[f47])).
% 2.06/0.63  fof(f111,plain,(
% 2.06/0.63    ~spl9_1 | spl9_3),
% 2.06/0.63    inference(avatar_split_clause,[],[f67,f108,f99])).
% 2.06/0.63  fof(f67,plain,(
% 2.06/0.63    r2_hidden(sK3,sK2) | ~r2_hidden(sK1,k8_setfam_1(sK0,sK2))),
% 2.06/0.63    inference(cnf_transformation,[],[f47])).
% 2.06/0.63  fof(f106,plain,(
% 2.06/0.63    ~spl9_1 | ~spl9_2),
% 2.06/0.63    inference(avatar_split_clause,[],[f68,f103,f99])).
% 2.06/0.63  fof(f68,plain,(
% 2.06/0.63    ~r2_hidden(sK1,sK3) | ~r2_hidden(sK1,k8_setfam_1(sK0,sK2))),
% 2.06/0.63    inference(cnf_transformation,[],[f47])).
% 2.06/0.63  % SZS output end Proof for theBenchmark
% 2.06/0.63  % (27407)------------------------------
% 2.06/0.63  % (27407)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.06/0.63  % (27407)Termination reason: Refutation
% 2.06/0.63  
% 2.06/0.63  % (27407)Memory used [KB]: 11129
% 2.06/0.63  % (27407)Time elapsed: 0.211 s
% 2.06/0.63  % (27407)------------------------------
% 2.06/0.63  % (27407)------------------------------
% 2.06/0.63  % (27380)Success in time 0.279 s
%------------------------------------------------------------------------------
