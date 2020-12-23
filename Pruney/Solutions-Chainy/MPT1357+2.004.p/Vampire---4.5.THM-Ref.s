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
% DateTime   : Thu Dec  3 13:14:43 EST 2020

% Result     : Theorem 1.15s
% Output     : Refutation 1.30s
% Verified   : 
% Statistics : Number of formulae       :  112 (1488 expanded)
%              Number of leaves         :   18 ( 575 expanded)
%              Depth                    :   28
%              Number of atoms          :  370 (7269 expanded)
%              Number of equality atoms :   47 (1381 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f422,plain,(
    $false ),
    inference(subsumption_resolution,[],[f421,f366])).

fof(f366,plain,(
    ~ sP3(k1_pre_topc(sK5,sK6),sK6) ),
    inference(subsumption_resolution,[],[f365,f83])).

fof(f83,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f76])).

fof(f76,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f48])).

fof(f48,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f365,plain,
    ( ~ sP3(k1_pre_topc(sK5,sK6),sK6)
    | ~ r1_tarski(sK6,sK6) ),
    inference(resolution,[],[f364,f80])).

fof(f80,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f364,plain,
    ( ~ m1_subset_1(sK6,k1_zfmisc_1(sK6))
    | ~ sP3(k1_pre_topc(sK5,sK6),sK6) ),
    inference(forward_demodulation,[],[f363,f101])).

fof(f101,plain,(
    sK6 = u1_struct_0(k1_pre_topc(sK5,sK6)) ),
    inference(subsumption_resolution,[],[f94,f57])).

fof(f57,plain,(
    l1_pre_topc(sK5) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,
    ( ( ( sP1(sK6,sK5)
        & k1_xboole_0 != sK6 )
      | sP2(sK5,sK6) )
    & m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK5)))
    & l1_pre_topc(sK5) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6])],[f29,f39,f38])).

fof(f38,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ( ( sP1(X1,X0)
                & k1_xboole_0 != X1 )
              | sP2(X0,X1) )
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_pre_topc(X0) )
   => ( ? [X1] :
          ( ( ( sP1(X1,sK5)
              & k1_xboole_0 != X1 )
            | sP2(sK5,X1) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK5))) )
      & l1_pre_topc(sK5) ) ),
    introduced(choice_axiom,[])).

fof(f39,plain,
    ( ? [X1] :
        ( ( ( sP1(X1,sK5)
            & k1_xboole_0 != X1 )
          | sP2(sK5,X1) )
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK5))) )
   => ( ( ( sP1(sK6,sK5)
          & k1_xboole_0 != sK6 )
        | sP2(sK5,sK6) )
      & m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK5))) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ( sP1(X1,X0)
              & k1_xboole_0 != X1 )
            | sP2(X0,X1) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(definition_folding,[],[f15,f28,f27,f26])).

fof(f26,plain,(
    ! [X1,X0] :
      ( ( v2_compts_1(X1,X0)
      <~> v1_compts_1(k1_pre_topc(X0,X1)) )
      | ~ sP0(X1,X0) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f27,plain,(
    ! [X1,X0] :
      ( ( v2_compts_1(X1,X0)
      <~> v1_compts_1(k1_pre_topc(X0,X1)) )
      | ~ sP1(X1,X0) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( sP0(X1,X0)
        & k1_xboole_0 = X1 )
      | ~ sP2(X0,X1) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).

fof(f15,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ( ( v2_compts_1(X1,X0)
              <~> v1_compts_1(k1_pre_topc(X0,X1)) )
              & k1_xboole_0 != X1 )
            | ( ( v2_compts_1(X1,X0)
              <~> v1_compts_1(k1_pre_topc(X0,X1)) )
              & k1_xboole_0 = X1 ) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,plain,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( ( ( v2_compts_1(X1,X0)
                <=> v1_compts_1(k1_pre_topc(X0,X1)) )
                | k1_xboole_0 = X1 )
              & ( k1_xboole_0 = X1
               => ( v2_compts_1(X1,X0)
                <=> v1_compts_1(k1_pre_topc(X0,X1)) ) ) ) ) ) ),
    inference(pure_predicate_removal,[],[f12])).

fof(f12,negated_conjecture,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( ( v2_pre_topc(X0)
               => ( ( v2_compts_1(X1,X0)
                  <=> v1_compts_1(k1_pre_topc(X0,X1)) )
                  | k1_xboole_0 = X1 ) )
              & ( k1_xboole_0 = X1
               => ( v2_compts_1(X1,X0)
                <=> v1_compts_1(k1_pre_topc(X0,X1)) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f11])).

fof(f11,conjecture,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( ( v2_pre_topc(X0)
             => ( ( v2_compts_1(X1,X0)
                <=> v1_compts_1(k1_pre_topc(X0,X1)) )
                | k1_xboole_0 = X1 ) )
            & ( k1_xboole_0 = X1
             => ( v2_compts_1(X1,X0)
              <=> v1_compts_1(k1_pre_topc(X0,X1)) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_compts_1)).

fof(f94,plain,
    ( sK6 = u1_struct_0(k1_pre_topc(sK5,sK6))
    | ~ l1_pre_topc(sK5) ),
    inference(resolution,[],[f58,f74])).

fof(f74,plain,(
    ! [X0,X1] :
      ( u1_struct_0(k1_pre_topc(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( u1_struct_0(k1_pre_topc(X0,X1)) = X1
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => u1_struct_0(k1_pre_topc(X0,X1)) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_pre_topc)).

fof(f58,plain,(
    m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK5))) ),
    inference(cnf_transformation,[],[f40])).

fof(f363,plain,
    ( ~ sP3(k1_pre_topc(sK5,sK6),sK6)
    | ~ m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(k1_pre_topc(sK5,sK6)))) ),
    inference(duplicate_literal_removal,[],[f359])).

fof(f359,plain,
    ( ~ sP3(k1_pre_topc(sK5,sK6),sK6)
    | ~ m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(k1_pre_topc(sK5,sK6))))
    | ~ sP3(k1_pre_topc(sK5,sK6),sK6) ),
    inference(resolution,[],[f296,f81])).

fof(f81,plain,(
    ! [X0,X3] :
      ( v2_compts_1(X3,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ sP3(X0,X3) ) ),
    inference(equality_resolution,[],[f69])).

fof(f69,plain,(
    ! [X0,X3,X1] :
      ( v2_compts_1(X3,X0)
      | X1 != X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ sP3(X0,X1) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ( sP3(X0,X1)
        | ( ~ v2_compts_1(sK7(X0,X1),X0)
          & sK7(X0,X1) = X1
          & m1_subset_1(sK7(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) )
      & ( ! [X3] :
            ( v2_compts_1(X3,X0)
            | X1 != X3
            | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
        | ~ sP3(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f45,f46])).

fof(f46,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ v2_compts_1(X2,X0)
          & X1 = X2
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ~ v2_compts_1(sK7(X0,X1),X0)
        & sK7(X0,X1) = X1
        & m1_subset_1(sK7(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ( sP3(X0,X1)
        | ? [X2] :
            ( ~ v2_compts_1(X2,X0)
            & X1 = X2
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
      & ( ! [X3] :
            ( v2_compts_1(X3,X0)
            | X1 != X3
            | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
        | ~ sP3(X0,X1) ) ) ),
    inference(rectify,[],[f44])).

fof(f44,plain,(
    ! [X1,X2] :
      ( ( sP3(X1,X2)
        | ? [X3] :
            ( ~ v2_compts_1(X3,X1)
            & X2 = X3
            & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) ) )
      & ( ! [X3] :
            ( v2_compts_1(X3,X1)
            | X2 != X3
            | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
        | ~ sP3(X1,X2) ) ) ),
    inference(nnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X1,X2] :
      ( sP3(X1,X2)
    <=> ! [X3] :
          ( v2_compts_1(X3,X1)
          | X2 != X3
          | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP3])])).

fof(f296,plain,
    ( ~ v2_compts_1(sK6,k1_pre_topc(sK5,sK6))
    | ~ sP3(k1_pre_topc(sK5,sK6),sK6) ),
    inference(resolution,[],[f248,f178])).

fof(f178,plain,
    ( v1_compts_1(k1_pre_topc(sK5,sK6))
    | ~ v2_compts_1(sK6,k1_pre_topc(sK5,sK6)) ),
    inference(subsumption_resolution,[],[f176,f117])).

fof(f117,plain,(
    l1_pre_topc(k1_pre_topc(sK5,sK6)) ),
    inference(resolution,[],[f100,f88])).

fof(f88,plain,(
    ! [X0] :
      ( ~ m1_pre_topc(X0,sK5)
      | l1_pre_topc(X0) ) ),
    inference(resolution,[],[f57,f65])).

fof(f65,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).

fof(f100,plain,(
    m1_pre_topc(k1_pre_topc(sK5,sK6),sK5) ),
    inference(subsumption_resolution,[],[f93,f57])).

fof(f93,plain,
    ( m1_pre_topc(k1_pre_topc(sK5,sK6),sK5)
    | ~ l1_pre_topc(sK5) ),
    inference(resolution,[],[f58,f75])).

fof(f75,plain,(
    ! [X0,X1] :
      ( m1_pre_topc(k1_pre_topc(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( m1_pre_topc(k1_pre_topc(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( m1_pre_topc(k1_pre_topc(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_pre_topc(k1_pre_topc(X0,X1),X0) ) ),
    inference(pure_predicate_removal,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => ( m1_pre_topc(k1_pre_topc(X0,X1),X0)
        & v1_pre_topc(k1_pre_topc(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_pre_topc)).

fof(f176,plain,
    ( ~ v2_compts_1(sK6,k1_pre_topc(sK5,sK6))
    | v1_compts_1(k1_pre_topc(sK5,sK6))
    | ~ l1_pre_topc(k1_pre_topc(sK5,sK6)) ),
    inference(superposition,[],[f64,f162])).

fof(f162,plain,(
    sK6 = k2_struct_0(k1_pre_topc(sK5,sK6)) ),
    inference(subsumption_resolution,[],[f153,f124])).

fof(f124,plain,(
    l1_struct_0(k1_pre_topc(sK5,sK6)) ),
    inference(resolution,[],[f117,f62])).

fof(f62,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(f153,plain,
    ( sK6 = k2_struct_0(k1_pre_topc(sK5,sK6))
    | ~ l1_struct_0(k1_pre_topc(sK5,sK6)) ),
    inference(superposition,[],[f101,f61])).

fof(f61,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k2_struct_0(X0) = u1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).

fof(f64,plain,(
    ! [X0] :
      ( v1_compts_1(X0)
      | ~ v2_compts_1(k2_struct_0(X0),X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0] :
      ( ( ( v1_compts_1(X0)
          | ~ v2_compts_1(k2_struct_0(X0),X0) )
        & ( v2_compts_1(k2_struct_0(X0),X0)
          | ~ v1_compts_1(X0) ) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ( v1_compts_1(X0)
      <=> v2_compts_1(k2_struct_0(X0),X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ( v1_compts_1(X0)
      <=> v2_compts_1(k2_struct_0(X0),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_compts_1)).

fof(f248,plain,
    ( ~ v1_compts_1(k1_pre_topc(sK5,sK6))
    | ~ sP3(k1_pre_topc(sK5,sK6),sK6) ),
    inference(resolution,[],[f244,f173])).

fof(f173,plain,
    ( ~ v2_compts_1(sK6,sK5)
    | ~ v1_compts_1(k1_pre_topc(sK5,sK6)) ),
    inference(subsumption_resolution,[],[f171,f56])).

fof(f56,plain,(
    ! [X0,X1] :
      ( ~ v1_compts_1(k1_pre_topc(X1,X0))
      | ~ v2_compts_1(X0,X1)
      | ~ sP0(X0,X1) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( ( ~ v1_compts_1(k1_pre_topc(X1,X0))
          | ~ v2_compts_1(X0,X1) )
        & ( v1_compts_1(k1_pre_topc(X1,X0))
          | v2_compts_1(X0,X1) ) )
      | ~ sP0(X0,X1) ) ),
    inference(rectify,[],[f36])).

fof(f36,plain,(
    ! [X1,X0] :
      ( ( ( ~ v1_compts_1(k1_pre_topc(X0,X1))
          | ~ v2_compts_1(X1,X0) )
        & ( v1_compts_1(k1_pre_topc(X0,X1))
          | v2_compts_1(X1,X0) ) )
      | ~ sP0(X1,X0) ) ),
    inference(nnf_transformation,[],[f26])).

fof(f171,plain,
    ( sP0(sK6,sK5)
    | ~ v1_compts_1(k1_pre_topc(sK5,sK6))
    | ~ v2_compts_1(sK6,sK5) ),
    inference(resolution,[],[f116,f54])).

fof(f54,plain,(
    ! [X0,X1] :
      ( ~ v1_compts_1(k1_pre_topc(X1,X0))
      | ~ v2_compts_1(X0,X1)
      | ~ sP1(X0,X1) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( ( ~ v1_compts_1(k1_pre_topc(X1,X0))
          | ~ v2_compts_1(X0,X1) )
        & ( v1_compts_1(k1_pre_topc(X1,X0))
          | v2_compts_1(X0,X1) ) )
      | ~ sP1(X0,X1) ) ),
    inference(rectify,[],[f34])).

fof(f34,plain,(
    ! [X1,X0] :
      ( ( ( ~ v1_compts_1(k1_pre_topc(X0,X1))
          | ~ v2_compts_1(X1,X0) )
        & ( v1_compts_1(k1_pre_topc(X0,X1))
          | v2_compts_1(X1,X0) ) )
      | ~ sP1(X1,X0) ) ),
    inference(nnf_transformation,[],[f27])).

fof(f116,plain,
    ( sP1(sK6,sK5)
    | sP0(sK6,sK5) ),
    inference(resolution,[],[f60,f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( sP0(X1,X0)
      | ~ sP2(X0,X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( sP0(X1,X0)
        & k1_xboole_0 = X1 )
      | ~ sP2(X0,X1) ) ),
    inference(nnf_transformation,[],[f28])).

fof(f60,plain,
    ( sP2(sK5,sK6)
    | sP1(sK6,sK5) ),
    inference(cnf_transformation,[],[f40])).

fof(f244,plain,
    ( v2_compts_1(sK6,sK5)
    | ~ sP3(k1_pre_topc(sK5,sK6),sK6) ),
    inference(resolution,[],[f240,f68])).

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( v2_compts_1(X0,X2)
      | ~ sP3(X1,X0)
      | ~ sP4(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0,X1,X2] :
      ( ( ( v2_compts_1(X0,X2)
          | ~ sP3(X1,X0) )
        & ( sP3(X1,X0)
          | ~ v2_compts_1(X0,X2) ) )
      | ~ sP4(X0,X1,X2) ) ),
    inference(rectify,[],[f42])).

fof(f42,plain,(
    ! [X2,X1,X0] :
      ( ( ( v2_compts_1(X2,X0)
          | ~ sP3(X1,X2) )
        & ( sP3(X1,X2)
          | ~ v2_compts_1(X2,X0) ) )
      | ~ sP4(X2,X1,X0) ) ),
    inference(nnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X2,X1,X0] :
      ( ( v2_compts_1(X2,X0)
      <=> sP3(X1,X2) )
      | ~ sP4(X2,X1,X0) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP4])])).

fof(f240,plain,(
    sP4(sK6,k1_pre_topc(sK5,sK6),sK5) ),
    inference(subsumption_resolution,[],[f239,f83])).

fof(f239,plain,
    ( ~ r1_tarski(sK6,sK6)
    | sP4(sK6,k1_pre_topc(sK5,sK6),sK5) ),
    inference(forward_demodulation,[],[f236,f162])).

fof(f236,plain,
    ( ~ r1_tarski(sK6,k2_struct_0(k1_pre_topc(sK5,sK6)))
    | sP4(sK6,k1_pre_topc(sK5,sK6),sK5) ),
    inference(resolution,[],[f102,f100])).

fof(f102,plain,(
    ! [X0] :
      ( ~ m1_pre_topc(X0,sK5)
      | ~ r1_tarski(sK6,k2_struct_0(X0))
      | sP4(sK6,X0,sK5) ) ),
    inference(subsumption_resolution,[],[f95,f57])).

fof(f95,plain,(
    ! [X0] :
      ( sP4(sK6,X0,sK5)
      | ~ r1_tarski(sK6,k2_struct_0(X0))
      | ~ m1_pre_topc(X0,sK5)
      | ~ l1_pre_topc(sK5) ) ),
    inference(resolution,[],[f58,f73])).

fof(f73,plain,(
    ! [X2,X0,X1] :
      ( sP4(X2,X1,X0)
      | ~ r1_tarski(X2,k2_struct_0(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( sP4(X2,X1,X0)
              | ~ r1_tarski(X2,k2_struct_0(X1))
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(definition_folding,[],[f22,f31,f30])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( v2_compts_1(X2,X0)
              <=> ! [X3] :
                    ( v2_compts_1(X3,X1)
                    | X2 != X3
                    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) ) )
              | ~ r1_tarski(X2,k2_struct_0(X1))
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( v2_compts_1(X2,X0)
              <=> ! [X3] :
                    ( v2_compts_1(X3,X1)
                    | X2 != X3
                    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) ) )
              | ~ r1_tarski(X2,k2_struct_0(X1))
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( r1_tarski(X2,k2_struct_0(X1))
               => ( v2_compts_1(X2,X0)
                <=> ! [X3] :
                      ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
                     => ( X2 = X3
                       => v2_compts_1(X3,X1) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_compts_1)).

fof(f421,plain,(
    sP3(k1_pre_topc(sK5,sK6),sK6) ),
    inference(subsumption_resolution,[],[f418,f401])).

fof(f401,plain,(
    v2_compts_1(sK6,k1_pre_topc(sK5,sK6)) ),
    inference(forward_demodulation,[],[f400,f162])).

fof(f400,plain,(
    v2_compts_1(k2_struct_0(k1_pre_topc(sK5,sK6)),k1_pre_topc(sK5,sK6)) ),
    inference(subsumption_resolution,[],[f399,f117])).

fof(f399,plain,
    ( v2_compts_1(k2_struct_0(k1_pre_topc(sK5,sK6)),k1_pre_topc(sK5,sK6))
    | ~ l1_pre_topc(k1_pre_topc(sK5,sK6)) ),
    inference(resolution,[],[f378,f63])).

fof(f63,plain,(
    ! [X0] :
      ( v2_compts_1(k2_struct_0(X0),X0)
      | ~ v1_compts_1(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f378,plain,(
    v1_compts_1(k1_pre_topc(sK5,sK6)) ),
    inference(resolution,[],[f368,f172])).

fof(f172,plain,
    ( v2_compts_1(sK6,sK5)
    | v1_compts_1(k1_pre_topc(sK5,sK6)) ),
    inference(subsumption_resolution,[],[f170,f55])).

fof(f55,plain,(
    ! [X0,X1] :
      ( v1_compts_1(k1_pre_topc(X1,X0))
      | v2_compts_1(X0,X1)
      | ~ sP0(X0,X1) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f170,plain,
    ( sP0(sK6,sK5)
    | v1_compts_1(k1_pre_topc(sK5,sK6))
    | v2_compts_1(sK6,sK5) ),
    inference(resolution,[],[f116,f53])).

fof(f53,plain,(
    ! [X0,X1] :
      ( v1_compts_1(k1_pre_topc(X1,X0))
      | v2_compts_1(X0,X1)
      | ~ sP1(X0,X1) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f368,plain,(
    ~ v2_compts_1(sK6,sK5) ),
    inference(resolution,[],[f366,f243])).

fof(f243,plain,
    ( sP3(k1_pre_topc(sK5,sK6),sK6)
    | ~ v2_compts_1(sK6,sK5) ),
    inference(resolution,[],[f240,f67])).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( sP3(X1,X0)
      | ~ v2_compts_1(X0,X2)
      | ~ sP4(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f418,plain,
    ( ~ v2_compts_1(sK6,k1_pre_topc(sK5,sK6))
    | sP3(k1_pre_topc(sK5,sK6),sK6) ),
    inference(superposition,[],[f72,f372])).

fof(f372,plain,(
    sK6 = sK7(k1_pre_topc(sK5,sK6),sK6) ),
    inference(resolution,[],[f366,f71])).

fof(f71,plain,(
    ! [X0,X1] :
      ( sP3(X0,X1)
      | sK7(X0,X1) = X1 ) ),
    inference(cnf_transformation,[],[f47])).

fof(f72,plain,(
    ! [X0,X1] :
      ( sP3(X0,X1)
      | ~ v2_compts_1(sK7(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f47])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n023.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 14:20:06 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.50  % (31727)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 0.22/0.51  % (31724)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 1.15/0.51  % (31735)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 1.15/0.51  % (31732)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 1.15/0.51  % (31725)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 1.15/0.52  % (31730)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 1.15/0.52  % (31733)lrs+4_5:4_av=off:bd=off:er=filter:lma=on:lwlo=on:nwc=1:stl=30:sp=occurrence:updr=off_230 on theBenchmark
% 1.15/0.52  % (31731)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 1.15/0.52  % (31721)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 1.15/0.52  % (31725)Refutation found. Thanks to Tanya!
% 1.15/0.52  % SZS status Theorem for theBenchmark
% 1.15/0.53  % (31738)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 1.15/0.53  % (31719)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 1.15/0.53  % (31741)dis+2_128_add=large:afp=100000:afq=1.4:amm=sco:anc=none:lma=on:nm=2:newcnf=on:nwc=1:nicw=on:sas=z3:sos=theory:sac=on:updr=off_288 on theBenchmark
% 1.15/0.53  % (31723)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 1.15/0.53  % (31723)Refutation not found, incomplete strategy% (31723)------------------------------
% 1.15/0.53  % (31723)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.15/0.53  % (31723)Termination reason: Refutation not found, incomplete strategy
% 1.15/0.53  
% 1.15/0.53  % (31723)Memory used [KB]: 10618
% 1.15/0.53  % (31726)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
% 1.15/0.53  % (31723)Time elapsed: 0.108 s
% 1.15/0.53  % (31723)------------------------------
% 1.15/0.53  % (31723)------------------------------
% 1.15/0.53  % (31740)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 1.30/0.53  % (31742)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_364 on theBenchmark
% 1.30/0.53  % (31739)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 1.30/0.54  % (31718)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 1.30/0.54  % (31728)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 1.30/0.54  % (31734)lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_145 on theBenchmark
% 1.30/0.54  % (31717)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 1.30/0.54  % SZS output start Proof for theBenchmark
% 1.30/0.54  fof(f422,plain,(
% 1.30/0.54    $false),
% 1.30/0.54    inference(subsumption_resolution,[],[f421,f366])).
% 1.30/0.54  fof(f366,plain,(
% 1.30/0.54    ~sP3(k1_pre_topc(sK5,sK6),sK6)),
% 1.30/0.54    inference(subsumption_resolution,[],[f365,f83])).
% 1.30/0.54  fof(f83,plain,(
% 1.30/0.54    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 1.30/0.54    inference(equality_resolution,[],[f76])).
% 1.30/0.54  fof(f76,plain,(
% 1.30/0.54    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 1.30/0.54    inference(cnf_transformation,[],[f49])).
% 1.30/0.54  fof(f49,plain,(
% 1.30/0.54    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.30/0.54    inference(flattening,[],[f48])).
% 1.30/0.54  fof(f48,plain,(
% 1.30/0.54    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.30/0.54    inference(nnf_transformation,[],[f1])).
% 1.30/0.54  fof(f1,axiom,(
% 1.30/0.54    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.30/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 1.30/0.54  fof(f365,plain,(
% 1.30/0.54    ~sP3(k1_pre_topc(sK5,sK6),sK6) | ~r1_tarski(sK6,sK6)),
% 1.30/0.54    inference(resolution,[],[f364,f80])).
% 1.30/0.54  fof(f80,plain,(
% 1.30/0.54    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 1.30/0.54    inference(cnf_transformation,[],[f50])).
% 1.30/0.54  fof(f50,plain,(
% 1.30/0.54    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 1.30/0.54    inference(nnf_transformation,[],[f2])).
% 1.30/0.54  fof(f2,axiom,(
% 1.30/0.54    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 1.30/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).
% 1.30/0.54  fof(f364,plain,(
% 1.30/0.54    ~m1_subset_1(sK6,k1_zfmisc_1(sK6)) | ~sP3(k1_pre_topc(sK5,sK6),sK6)),
% 1.30/0.54    inference(forward_demodulation,[],[f363,f101])).
% 1.30/0.54  fof(f101,plain,(
% 1.30/0.54    sK6 = u1_struct_0(k1_pre_topc(sK5,sK6))),
% 1.30/0.54    inference(subsumption_resolution,[],[f94,f57])).
% 1.30/0.54  fof(f57,plain,(
% 1.30/0.54    l1_pre_topc(sK5)),
% 1.30/0.54    inference(cnf_transformation,[],[f40])).
% 1.30/0.54  fof(f40,plain,(
% 1.30/0.54    (((sP1(sK6,sK5) & k1_xboole_0 != sK6) | sP2(sK5,sK6)) & m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK5)))) & l1_pre_topc(sK5)),
% 1.30/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6])],[f29,f39,f38])).
% 1.30/0.54  fof(f38,plain,(
% 1.30/0.54    ? [X0] : (? [X1] : (((sP1(X1,X0) & k1_xboole_0 != X1) | sP2(X0,X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0)) => (? [X1] : (((sP1(X1,sK5) & k1_xboole_0 != X1) | sP2(sK5,X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK5)))) & l1_pre_topc(sK5))),
% 1.30/0.54    introduced(choice_axiom,[])).
% 1.30/0.54  fof(f39,plain,(
% 1.30/0.54    ? [X1] : (((sP1(X1,sK5) & k1_xboole_0 != X1) | sP2(sK5,X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK5)))) => (((sP1(sK6,sK5) & k1_xboole_0 != sK6) | sP2(sK5,sK6)) & m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK5))))),
% 1.30/0.54    introduced(choice_axiom,[])).
% 1.30/0.54  fof(f29,plain,(
% 1.30/0.54    ? [X0] : (? [X1] : (((sP1(X1,X0) & k1_xboole_0 != X1) | sP2(X0,X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 1.30/0.54    inference(definition_folding,[],[f15,f28,f27,f26])).
% 1.30/0.54  fof(f26,plain,(
% 1.30/0.54    ! [X1,X0] : ((v2_compts_1(X1,X0) <~> v1_compts_1(k1_pre_topc(X0,X1))) | ~sP0(X1,X0))),
% 1.30/0.54    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 1.30/0.54  fof(f27,plain,(
% 1.30/0.54    ! [X1,X0] : ((v2_compts_1(X1,X0) <~> v1_compts_1(k1_pre_topc(X0,X1))) | ~sP1(X1,X0))),
% 1.30/0.54    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 1.30/0.54  fof(f28,plain,(
% 1.30/0.54    ! [X0,X1] : ((sP0(X1,X0) & k1_xboole_0 = X1) | ~sP2(X0,X1))),
% 1.30/0.54    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).
% 1.30/0.54  fof(f15,plain,(
% 1.30/0.54    ? [X0] : (? [X1] : ((((v2_compts_1(X1,X0) <~> v1_compts_1(k1_pre_topc(X0,X1))) & k1_xboole_0 != X1) | ((v2_compts_1(X1,X0) <~> v1_compts_1(k1_pre_topc(X0,X1))) & k1_xboole_0 = X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 1.30/0.54    inference(ennf_transformation,[],[f13])).
% 1.30/0.54  fof(f13,plain,(
% 1.30/0.54    ~! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (((v2_compts_1(X1,X0) <=> v1_compts_1(k1_pre_topc(X0,X1))) | k1_xboole_0 = X1) & (k1_xboole_0 = X1 => (v2_compts_1(X1,X0) <=> v1_compts_1(k1_pre_topc(X0,X1)))))))),
% 1.30/0.54    inference(pure_predicate_removal,[],[f12])).
% 1.30/0.54  fof(f12,negated_conjecture,(
% 1.30/0.54    ~! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ((v2_pre_topc(X0) => ((v2_compts_1(X1,X0) <=> v1_compts_1(k1_pre_topc(X0,X1))) | k1_xboole_0 = X1)) & (k1_xboole_0 = X1 => (v2_compts_1(X1,X0) <=> v1_compts_1(k1_pre_topc(X0,X1)))))))),
% 1.30/0.54    inference(negated_conjecture,[],[f11])).
% 1.30/0.54  fof(f11,conjecture,(
% 1.30/0.54    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ((v2_pre_topc(X0) => ((v2_compts_1(X1,X0) <=> v1_compts_1(k1_pre_topc(X0,X1))) | k1_xboole_0 = X1)) & (k1_xboole_0 = X1 => (v2_compts_1(X1,X0) <=> v1_compts_1(k1_pre_topc(X0,X1)))))))),
% 1.30/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_compts_1)).
% 1.30/0.54  fof(f94,plain,(
% 1.30/0.54    sK6 = u1_struct_0(k1_pre_topc(sK5,sK6)) | ~l1_pre_topc(sK5)),
% 1.30/0.54    inference(resolution,[],[f58,f74])).
% 1.30/0.54  fof(f74,plain,(
% 1.30/0.54    ( ! [X0,X1] : (u1_struct_0(k1_pre_topc(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 1.30/0.54    inference(cnf_transformation,[],[f23])).
% 1.30/0.54  fof(f23,plain,(
% 1.30/0.54    ! [X0] : (! [X1] : (u1_struct_0(k1_pre_topc(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.30/0.54    inference(ennf_transformation,[],[f7])).
% 1.30/0.54  fof(f7,axiom,(
% 1.30/0.54    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => u1_struct_0(k1_pre_topc(X0,X1)) = X1))),
% 1.30/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_pre_topc)).
% 1.30/0.54  fof(f58,plain,(
% 1.30/0.54    m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK5)))),
% 1.30/0.54    inference(cnf_transformation,[],[f40])).
% 1.30/0.54  fof(f363,plain,(
% 1.30/0.54    ~sP3(k1_pre_topc(sK5,sK6),sK6) | ~m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(k1_pre_topc(sK5,sK6))))),
% 1.30/0.54    inference(duplicate_literal_removal,[],[f359])).
% 1.30/0.54  fof(f359,plain,(
% 1.30/0.54    ~sP3(k1_pre_topc(sK5,sK6),sK6) | ~m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(k1_pre_topc(sK5,sK6)))) | ~sP3(k1_pre_topc(sK5,sK6),sK6)),
% 1.30/0.54    inference(resolution,[],[f296,f81])).
% 1.30/0.54  fof(f81,plain,(
% 1.30/0.54    ( ! [X0,X3] : (v2_compts_1(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) | ~sP3(X0,X3)) )),
% 1.30/0.54    inference(equality_resolution,[],[f69])).
% 1.30/0.54  fof(f69,plain,(
% 1.30/0.54    ( ! [X0,X3,X1] : (v2_compts_1(X3,X0) | X1 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) | ~sP3(X0,X1)) )),
% 1.30/0.54    inference(cnf_transformation,[],[f47])).
% 1.30/0.54  fof(f47,plain,(
% 1.30/0.54    ! [X0,X1] : ((sP3(X0,X1) | (~v2_compts_1(sK7(X0,X1),X0) & sK7(X0,X1) = X1 & m1_subset_1(sK7(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))) & (! [X3] : (v2_compts_1(X3,X0) | X1 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~sP3(X0,X1)))),
% 1.30/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f45,f46])).
% 1.30/0.54  fof(f46,plain,(
% 1.30/0.54    ! [X1,X0] : (? [X2] : (~v2_compts_1(X2,X0) & X1 = X2 & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) => (~v2_compts_1(sK7(X0,X1),X0) & sK7(X0,X1) = X1 & m1_subset_1(sK7(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 1.30/0.54    introduced(choice_axiom,[])).
% 1.30/0.54  fof(f45,plain,(
% 1.30/0.54    ! [X0,X1] : ((sP3(X0,X1) | ? [X2] : (~v2_compts_1(X2,X0) & X1 = X2 & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X3] : (v2_compts_1(X3,X0) | X1 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~sP3(X0,X1)))),
% 1.30/0.54    inference(rectify,[],[f44])).
% 1.30/0.54  fof(f44,plain,(
% 1.30/0.54    ! [X1,X2] : ((sP3(X1,X2) | ? [X3] : (~v2_compts_1(X3,X1) & X2 = X3 & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))))) & (! [X3] : (v2_compts_1(X3,X1) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) | ~sP3(X1,X2)))),
% 1.30/0.54    inference(nnf_transformation,[],[f30])).
% 1.30/0.54  fof(f30,plain,(
% 1.30/0.54    ! [X1,X2] : (sP3(X1,X2) <=> ! [X3] : (v2_compts_1(X3,X1) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))))),
% 1.30/0.54    introduced(predicate_definition_introduction,[new_symbols(naming,[sP3])])).
% 1.30/0.54  fof(f296,plain,(
% 1.30/0.54    ~v2_compts_1(sK6,k1_pre_topc(sK5,sK6)) | ~sP3(k1_pre_topc(sK5,sK6),sK6)),
% 1.30/0.54    inference(resolution,[],[f248,f178])).
% 1.30/0.54  fof(f178,plain,(
% 1.30/0.54    v1_compts_1(k1_pre_topc(sK5,sK6)) | ~v2_compts_1(sK6,k1_pre_topc(sK5,sK6))),
% 1.30/0.54    inference(subsumption_resolution,[],[f176,f117])).
% 1.30/0.54  fof(f117,plain,(
% 1.30/0.54    l1_pre_topc(k1_pre_topc(sK5,sK6))),
% 1.30/0.54    inference(resolution,[],[f100,f88])).
% 1.30/0.54  fof(f88,plain,(
% 1.30/0.54    ( ! [X0] : (~m1_pre_topc(X0,sK5) | l1_pre_topc(X0)) )),
% 1.30/0.54    inference(resolution,[],[f57,f65])).
% 1.30/0.54  fof(f65,plain,(
% 1.30/0.54    ( ! [X0,X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 1.30/0.54    inference(cnf_transformation,[],[f19])).
% 1.30/0.54  fof(f19,plain,(
% 1.30/0.54    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 1.30/0.54    inference(ennf_transformation,[],[f6])).
% 1.30/0.54  fof(f6,axiom,(
% 1.30/0.54    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 1.30/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).
% 1.30/0.54  fof(f100,plain,(
% 1.30/0.54    m1_pre_topc(k1_pre_topc(sK5,sK6),sK5)),
% 1.30/0.54    inference(subsumption_resolution,[],[f93,f57])).
% 1.30/0.54  fof(f93,plain,(
% 1.30/0.54    m1_pre_topc(k1_pre_topc(sK5,sK6),sK5) | ~l1_pre_topc(sK5)),
% 1.30/0.54    inference(resolution,[],[f58,f75])).
% 1.30/0.54  fof(f75,plain,(
% 1.30/0.54    ( ! [X0,X1] : (m1_pre_topc(k1_pre_topc(X0,X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 1.30/0.54    inference(cnf_transformation,[],[f25])).
% 1.30/0.54  fof(f25,plain,(
% 1.30/0.54    ! [X0,X1] : (m1_pre_topc(k1_pre_topc(X0,X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 1.30/0.54    inference(flattening,[],[f24])).
% 1.30/0.54  fof(f24,plain,(
% 1.30/0.54    ! [X0,X1] : (m1_pre_topc(k1_pre_topc(X0,X1),X0) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 1.30/0.54    inference(ennf_transformation,[],[f14])).
% 1.30/0.54  fof(f14,plain,(
% 1.30/0.54    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => m1_pre_topc(k1_pre_topc(X0,X1),X0))),
% 1.30/0.54    inference(pure_predicate_removal,[],[f4])).
% 1.30/0.54  fof(f4,axiom,(
% 1.30/0.54    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => (m1_pre_topc(k1_pre_topc(X0,X1),X0) & v1_pre_topc(k1_pre_topc(X0,X1))))),
% 1.30/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_pre_topc)).
% 1.30/0.54  fof(f176,plain,(
% 1.30/0.54    ~v2_compts_1(sK6,k1_pre_topc(sK5,sK6)) | v1_compts_1(k1_pre_topc(sK5,sK6)) | ~l1_pre_topc(k1_pre_topc(sK5,sK6))),
% 1.30/0.54    inference(superposition,[],[f64,f162])).
% 1.30/0.54  fof(f162,plain,(
% 1.30/0.54    sK6 = k2_struct_0(k1_pre_topc(sK5,sK6))),
% 1.30/0.54    inference(subsumption_resolution,[],[f153,f124])).
% 1.30/0.54  fof(f124,plain,(
% 1.30/0.54    l1_struct_0(k1_pre_topc(sK5,sK6))),
% 1.30/0.54    inference(resolution,[],[f117,f62])).
% 1.30/0.54  fof(f62,plain,(
% 1.30/0.54    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 1.30/0.54    inference(cnf_transformation,[],[f17])).
% 1.30/0.54  fof(f17,plain,(
% 1.30/0.54    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 1.30/0.54    inference(ennf_transformation,[],[f5])).
% 1.30/0.54  fof(f5,axiom,(
% 1.30/0.54    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 1.30/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).
% 1.30/0.54  fof(f153,plain,(
% 1.30/0.54    sK6 = k2_struct_0(k1_pre_topc(sK5,sK6)) | ~l1_struct_0(k1_pre_topc(sK5,sK6))),
% 1.30/0.54    inference(superposition,[],[f101,f61])).
% 1.30/0.54  fof(f61,plain,(
% 1.30/0.54    ( ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0)) )),
% 1.30/0.54    inference(cnf_transformation,[],[f16])).
% 1.30/0.54  fof(f16,plain,(
% 1.30/0.54    ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0))),
% 1.30/0.54    inference(ennf_transformation,[],[f3])).
% 1.30/0.54  fof(f3,axiom,(
% 1.30/0.54    ! [X0] : (l1_struct_0(X0) => k2_struct_0(X0) = u1_struct_0(X0))),
% 1.30/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).
% 1.30/0.54  fof(f64,plain,(
% 1.30/0.54    ( ! [X0] : (v1_compts_1(X0) | ~v2_compts_1(k2_struct_0(X0),X0) | ~l1_pre_topc(X0)) )),
% 1.30/0.54    inference(cnf_transformation,[],[f41])).
% 1.30/0.54  fof(f41,plain,(
% 1.30/0.54    ! [X0] : (((v1_compts_1(X0) | ~v2_compts_1(k2_struct_0(X0),X0)) & (v2_compts_1(k2_struct_0(X0),X0) | ~v1_compts_1(X0))) | ~l1_pre_topc(X0))),
% 1.30/0.54    inference(nnf_transformation,[],[f18])).
% 1.30/0.54  fof(f18,plain,(
% 1.30/0.54    ! [X0] : ((v1_compts_1(X0) <=> v2_compts_1(k2_struct_0(X0),X0)) | ~l1_pre_topc(X0))),
% 1.30/0.54    inference(ennf_transformation,[],[f9])).
% 1.30/0.54  fof(f9,axiom,(
% 1.30/0.54    ! [X0] : (l1_pre_topc(X0) => (v1_compts_1(X0) <=> v2_compts_1(k2_struct_0(X0),X0)))),
% 1.30/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_compts_1)).
% 1.30/0.54  fof(f248,plain,(
% 1.30/0.54    ~v1_compts_1(k1_pre_topc(sK5,sK6)) | ~sP3(k1_pre_topc(sK5,sK6),sK6)),
% 1.30/0.54    inference(resolution,[],[f244,f173])).
% 1.30/0.54  fof(f173,plain,(
% 1.30/0.54    ~v2_compts_1(sK6,sK5) | ~v1_compts_1(k1_pre_topc(sK5,sK6))),
% 1.30/0.54    inference(subsumption_resolution,[],[f171,f56])).
% 1.30/0.54  fof(f56,plain,(
% 1.30/0.54    ( ! [X0,X1] : (~v1_compts_1(k1_pre_topc(X1,X0)) | ~v2_compts_1(X0,X1) | ~sP0(X0,X1)) )),
% 1.30/0.54    inference(cnf_transformation,[],[f37])).
% 1.30/0.54  fof(f37,plain,(
% 1.30/0.54    ! [X0,X1] : (((~v1_compts_1(k1_pre_topc(X1,X0)) | ~v2_compts_1(X0,X1)) & (v1_compts_1(k1_pre_topc(X1,X0)) | v2_compts_1(X0,X1))) | ~sP0(X0,X1))),
% 1.30/0.54    inference(rectify,[],[f36])).
% 1.30/0.54  fof(f36,plain,(
% 1.30/0.54    ! [X1,X0] : (((~v1_compts_1(k1_pre_topc(X0,X1)) | ~v2_compts_1(X1,X0)) & (v1_compts_1(k1_pre_topc(X0,X1)) | v2_compts_1(X1,X0))) | ~sP0(X1,X0))),
% 1.30/0.54    inference(nnf_transformation,[],[f26])).
% 1.30/0.54  fof(f171,plain,(
% 1.30/0.54    sP0(sK6,sK5) | ~v1_compts_1(k1_pre_topc(sK5,sK6)) | ~v2_compts_1(sK6,sK5)),
% 1.30/0.54    inference(resolution,[],[f116,f54])).
% 1.30/0.54  fof(f54,plain,(
% 1.30/0.54    ( ! [X0,X1] : (~v1_compts_1(k1_pre_topc(X1,X0)) | ~v2_compts_1(X0,X1) | ~sP1(X0,X1)) )),
% 1.30/0.54    inference(cnf_transformation,[],[f35])).
% 1.30/0.54  fof(f35,plain,(
% 1.30/0.54    ! [X0,X1] : (((~v1_compts_1(k1_pre_topc(X1,X0)) | ~v2_compts_1(X0,X1)) & (v1_compts_1(k1_pre_topc(X1,X0)) | v2_compts_1(X0,X1))) | ~sP1(X0,X1))),
% 1.30/0.54    inference(rectify,[],[f34])).
% 1.30/0.54  fof(f34,plain,(
% 1.30/0.54    ! [X1,X0] : (((~v1_compts_1(k1_pre_topc(X0,X1)) | ~v2_compts_1(X1,X0)) & (v1_compts_1(k1_pre_topc(X0,X1)) | v2_compts_1(X1,X0))) | ~sP1(X1,X0))),
% 1.30/0.54    inference(nnf_transformation,[],[f27])).
% 1.30/0.54  fof(f116,plain,(
% 1.30/0.54    sP1(sK6,sK5) | sP0(sK6,sK5)),
% 1.30/0.54    inference(resolution,[],[f60,f52])).
% 1.30/0.54  fof(f52,plain,(
% 1.30/0.54    ( ! [X0,X1] : (sP0(X1,X0) | ~sP2(X0,X1)) )),
% 1.30/0.54    inference(cnf_transformation,[],[f33])).
% 1.30/0.54  fof(f33,plain,(
% 1.30/0.54    ! [X0,X1] : ((sP0(X1,X0) & k1_xboole_0 = X1) | ~sP2(X0,X1))),
% 1.30/0.54    inference(nnf_transformation,[],[f28])).
% 1.30/0.54  fof(f60,plain,(
% 1.30/0.54    sP2(sK5,sK6) | sP1(sK6,sK5)),
% 1.30/0.54    inference(cnf_transformation,[],[f40])).
% 1.30/0.54  fof(f244,plain,(
% 1.30/0.54    v2_compts_1(sK6,sK5) | ~sP3(k1_pre_topc(sK5,sK6),sK6)),
% 1.30/0.54    inference(resolution,[],[f240,f68])).
% 1.30/0.54  fof(f68,plain,(
% 1.30/0.54    ( ! [X2,X0,X1] : (v2_compts_1(X0,X2) | ~sP3(X1,X0) | ~sP4(X0,X1,X2)) )),
% 1.30/0.54    inference(cnf_transformation,[],[f43])).
% 1.30/0.54  fof(f43,plain,(
% 1.30/0.54    ! [X0,X1,X2] : (((v2_compts_1(X0,X2) | ~sP3(X1,X0)) & (sP3(X1,X0) | ~v2_compts_1(X0,X2))) | ~sP4(X0,X1,X2))),
% 1.30/0.54    inference(rectify,[],[f42])).
% 1.30/0.54  fof(f42,plain,(
% 1.30/0.54    ! [X2,X1,X0] : (((v2_compts_1(X2,X0) | ~sP3(X1,X2)) & (sP3(X1,X2) | ~v2_compts_1(X2,X0))) | ~sP4(X2,X1,X0))),
% 1.30/0.54    inference(nnf_transformation,[],[f31])).
% 1.30/0.54  fof(f31,plain,(
% 1.30/0.54    ! [X2,X1,X0] : ((v2_compts_1(X2,X0) <=> sP3(X1,X2)) | ~sP4(X2,X1,X0))),
% 1.30/0.54    introduced(predicate_definition_introduction,[new_symbols(naming,[sP4])])).
% 1.30/0.54  fof(f240,plain,(
% 1.30/0.54    sP4(sK6,k1_pre_topc(sK5,sK6),sK5)),
% 1.30/0.54    inference(subsumption_resolution,[],[f239,f83])).
% 1.30/0.54  fof(f239,plain,(
% 1.30/0.54    ~r1_tarski(sK6,sK6) | sP4(sK6,k1_pre_topc(sK5,sK6),sK5)),
% 1.30/0.54    inference(forward_demodulation,[],[f236,f162])).
% 1.30/0.54  fof(f236,plain,(
% 1.30/0.54    ~r1_tarski(sK6,k2_struct_0(k1_pre_topc(sK5,sK6))) | sP4(sK6,k1_pre_topc(sK5,sK6),sK5)),
% 1.30/0.54    inference(resolution,[],[f102,f100])).
% 1.30/0.54  fof(f102,plain,(
% 1.30/0.54    ( ! [X0] : (~m1_pre_topc(X0,sK5) | ~r1_tarski(sK6,k2_struct_0(X0)) | sP4(sK6,X0,sK5)) )),
% 1.30/0.54    inference(subsumption_resolution,[],[f95,f57])).
% 1.30/0.54  fof(f95,plain,(
% 1.30/0.54    ( ! [X0] : (sP4(sK6,X0,sK5) | ~r1_tarski(sK6,k2_struct_0(X0)) | ~m1_pre_topc(X0,sK5) | ~l1_pre_topc(sK5)) )),
% 1.30/0.54    inference(resolution,[],[f58,f73])).
% 1.30/0.54  fof(f73,plain,(
% 1.30/0.54    ( ! [X2,X0,X1] : (sP4(X2,X1,X0) | ~r1_tarski(X2,k2_struct_0(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 1.30/0.54    inference(cnf_transformation,[],[f32])).
% 1.30/0.54  fof(f32,plain,(
% 1.30/0.54    ! [X0] : (! [X1] : (! [X2] : (sP4(X2,X1,X0) | ~r1_tarski(X2,k2_struct_0(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 1.30/0.54    inference(definition_folding,[],[f22,f31,f30])).
% 1.30/0.54  fof(f22,plain,(
% 1.30/0.54    ! [X0] : (! [X1] : (! [X2] : ((v2_compts_1(X2,X0) <=> ! [X3] : (v2_compts_1(X3,X1) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))))) | ~r1_tarski(X2,k2_struct_0(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 1.30/0.54    inference(flattening,[],[f21])).
% 1.30/0.54  fof(f21,plain,(
% 1.30/0.54    ! [X0] : (! [X1] : (! [X2] : (((v2_compts_1(X2,X0) <=> ! [X3] : ((v2_compts_1(X3,X1) | X2 != X3) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))))) | ~r1_tarski(X2,k2_struct_0(X1))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 1.30/0.54    inference(ennf_transformation,[],[f10])).
% 1.30/0.54  fof(f10,axiom,(
% 1.30/0.54    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (r1_tarski(X2,k2_struct_0(X1)) => (v2_compts_1(X2,X0) <=> ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) => (X2 = X3 => v2_compts_1(X3,X1))))))))),
% 1.30/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_compts_1)).
% 1.30/0.54  fof(f421,plain,(
% 1.30/0.54    sP3(k1_pre_topc(sK5,sK6),sK6)),
% 1.30/0.54    inference(subsumption_resolution,[],[f418,f401])).
% 1.30/0.54  fof(f401,plain,(
% 1.30/0.54    v2_compts_1(sK6,k1_pre_topc(sK5,sK6))),
% 1.30/0.54    inference(forward_demodulation,[],[f400,f162])).
% 1.30/0.54  fof(f400,plain,(
% 1.30/0.54    v2_compts_1(k2_struct_0(k1_pre_topc(sK5,sK6)),k1_pre_topc(sK5,sK6))),
% 1.30/0.54    inference(subsumption_resolution,[],[f399,f117])).
% 1.30/0.54  fof(f399,plain,(
% 1.30/0.54    v2_compts_1(k2_struct_0(k1_pre_topc(sK5,sK6)),k1_pre_topc(sK5,sK6)) | ~l1_pre_topc(k1_pre_topc(sK5,sK6))),
% 1.30/0.54    inference(resolution,[],[f378,f63])).
% 1.30/0.54  fof(f63,plain,(
% 1.30/0.54    ( ! [X0] : (v2_compts_1(k2_struct_0(X0),X0) | ~v1_compts_1(X0) | ~l1_pre_topc(X0)) )),
% 1.30/0.54    inference(cnf_transformation,[],[f41])).
% 1.30/0.54  fof(f378,plain,(
% 1.30/0.54    v1_compts_1(k1_pre_topc(sK5,sK6))),
% 1.30/0.54    inference(resolution,[],[f368,f172])).
% 1.30/0.54  fof(f172,plain,(
% 1.30/0.54    v2_compts_1(sK6,sK5) | v1_compts_1(k1_pre_topc(sK5,sK6))),
% 1.30/0.54    inference(subsumption_resolution,[],[f170,f55])).
% 1.30/0.54  fof(f55,plain,(
% 1.30/0.54    ( ! [X0,X1] : (v1_compts_1(k1_pre_topc(X1,X0)) | v2_compts_1(X0,X1) | ~sP0(X0,X1)) )),
% 1.30/0.54    inference(cnf_transformation,[],[f37])).
% 1.30/0.54  fof(f170,plain,(
% 1.30/0.54    sP0(sK6,sK5) | v1_compts_1(k1_pre_topc(sK5,sK6)) | v2_compts_1(sK6,sK5)),
% 1.30/0.54    inference(resolution,[],[f116,f53])).
% 1.30/0.54  fof(f53,plain,(
% 1.30/0.54    ( ! [X0,X1] : (v1_compts_1(k1_pre_topc(X1,X0)) | v2_compts_1(X0,X1) | ~sP1(X0,X1)) )),
% 1.30/0.54    inference(cnf_transformation,[],[f35])).
% 1.30/0.54  fof(f368,plain,(
% 1.30/0.54    ~v2_compts_1(sK6,sK5)),
% 1.30/0.54    inference(resolution,[],[f366,f243])).
% 1.30/0.54  fof(f243,plain,(
% 1.30/0.54    sP3(k1_pre_topc(sK5,sK6),sK6) | ~v2_compts_1(sK6,sK5)),
% 1.30/0.54    inference(resolution,[],[f240,f67])).
% 1.30/0.54  fof(f67,plain,(
% 1.30/0.54    ( ! [X2,X0,X1] : (sP3(X1,X0) | ~v2_compts_1(X0,X2) | ~sP4(X0,X1,X2)) )),
% 1.30/0.54    inference(cnf_transformation,[],[f43])).
% 1.30/0.54  fof(f418,plain,(
% 1.30/0.54    ~v2_compts_1(sK6,k1_pre_topc(sK5,sK6)) | sP3(k1_pre_topc(sK5,sK6),sK6)),
% 1.30/0.54    inference(superposition,[],[f72,f372])).
% 1.30/0.54  fof(f372,plain,(
% 1.30/0.54    sK6 = sK7(k1_pre_topc(sK5,sK6),sK6)),
% 1.30/0.54    inference(resolution,[],[f366,f71])).
% 1.30/0.54  fof(f71,plain,(
% 1.30/0.54    ( ! [X0,X1] : (sP3(X0,X1) | sK7(X0,X1) = X1) )),
% 1.30/0.54    inference(cnf_transformation,[],[f47])).
% 1.30/0.54  fof(f72,plain,(
% 1.30/0.54    ( ! [X0,X1] : (sP3(X0,X1) | ~v2_compts_1(sK7(X0,X1),X0)) )),
% 1.30/0.54    inference(cnf_transformation,[],[f47])).
% 1.30/0.54  % SZS output end Proof for theBenchmark
% 1.30/0.54  % (31725)------------------------------
% 1.30/0.54  % (31725)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.30/0.54  % (31725)Termination reason: Refutation
% 1.30/0.54  
% 1.30/0.54  % (31725)Memory used [KB]: 1791
% 1.30/0.54  % (31725)Time elapsed: 0.104 s
% 1.30/0.54  % (31725)------------------------------
% 1.30/0.54  % (31725)------------------------------
% 1.30/0.54  % (31717)Refutation not found, incomplete strategy% (31717)------------------------------
% 1.30/0.54  % (31717)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.30/0.54  % (31717)Termination reason: Refutation not found, incomplete strategy
% 1.30/0.54  
% 1.30/0.54  % (31717)Memory used [KB]: 10618
% 1.30/0.54  % (31717)Time elapsed: 0.090 s
% 1.30/0.54  % (31717)------------------------------
% 1.30/0.54  % (31717)------------------------------
% 1.30/0.54  % (31716)Success in time 0.174 s
%------------------------------------------------------------------------------
