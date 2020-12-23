%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:14:43 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 1.39s
% Verified   : 
% Statistics : Number of formulae       :  113 (1482 expanded)
%              Number of leaves         :   19 ( 578 expanded)
%              Depth                    :   24
%              Number of atoms          :  368 (7211 expanded)
%              Number of equality atoms :   49 (1375 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f524,plain,(
    $false ),
    inference(subsumption_resolution,[],[f523,f433])).

fof(f433,plain,(
    ~ sP3(k1_pre_topc(sK5,sK6),sK6) ),
    inference(subsumption_resolution,[],[f432,f284])).

fof(f284,plain,
    ( ~ v2_compts_1(sK6,k1_pre_topc(sK5,sK6))
    | ~ sP3(k1_pre_topc(sK5,sK6),sK6) ),
    inference(resolution,[],[f251,f166])).

fof(f166,plain,
    ( v1_compts_1(k1_pre_topc(sK5,sK6))
    | ~ v2_compts_1(sK6,k1_pre_topc(sK5,sK6)) ),
    inference(subsumption_resolution,[],[f164,f105])).

fof(f105,plain,(
    l1_pre_topc(k1_pre_topc(sK5,sK6)) ),
    inference(resolution,[],[f99,f88])).

fof(f88,plain,(
    ! [X0] :
      ( ~ m1_pre_topc(X0,sK5)
      | l1_pre_topc(X0) ) ),
    inference(resolution,[],[f57,f67])).

fof(f67,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).

fof(f57,plain,(
    l1_pre_topc(sK5) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,
    ( ( ( sP1(sK6,sK5)
        & k1_xboole_0 != sK6 )
      | sP2(sK5,sK6) )
    & m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK5)))
    & l1_pre_topc(sK5) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6])],[f30,f40,f39])).

fof(f39,plain,
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

fof(f40,plain,
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

fof(f30,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ( sP1(X1,X0)
              & k1_xboole_0 != X1 )
            | sP2(X0,X1) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(definition_folding,[],[f16,f29,f28,f27])).

fof(f27,plain,(
    ! [X1,X0] :
      ( ( v2_compts_1(X1,X0)
      <~> v1_compts_1(k1_pre_topc(X0,X1)) )
      | ~ sP0(X1,X0) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f28,plain,(
    ! [X1,X0] :
      ( ( v2_compts_1(X1,X0)
      <~> v1_compts_1(k1_pre_topc(X0,X1)) )
      | ~ sP1(X1,X0) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( sP0(X1,X0)
        & k1_xboole_0 = X1 )
      | ~ sP2(X0,X1) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).

fof(f16,plain,(
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
    inference(ennf_transformation,[],[f14])).

fof(f14,plain,(
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
    inference(pure_predicate_removal,[],[f13])).

fof(f13,negated_conjecture,(
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
    inference(negated_conjecture,[],[f12])).

fof(f12,conjecture,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_compts_1)).

fof(f99,plain,(
    m1_pre_topc(k1_pre_topc(sK5,sK6),sK5) ),
    inference(subsumption_resolution,[],[f93,f57])).

fof(f93,plain,
    ( m1_pre_topc(k1_pre_topc(sK5,sK6),sK5)
    | ~ l1_pre_topc(sK5) ),
    inference(resolution,[],[f58,f77])).

fof(f77,plain,(
    ! [X0,X1] :
      ( m1_pre_topc(k1_pre_topc(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( m1_pre_topc(k1_pre_topc(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( m1_pre_topc(k1_pre_topc(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_pre_topc(k1_pre_topc(X0,X1),X0) ) ),
    inference(pure_predicate_removal,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => ( m1_pre_topc(k1_pre_topc(X0,X1),X0)
        & v1_pre_topc(k1_pre_topc(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_pre_topc)).

fof(f58,plain,(
    m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK5))) ),
    inference(cnf_transformation,[],[f41])).

fof(f164,plain,
    ( ~ v2_compts_1(sK6,k1_pre_topc(sK5,sK6))
    | v1_compts_1(k1_pre_topc(sK5,sK6))
    | ~ l1_pre_topc(k1_pre_topc(sK5,sK6)) ),
    inference(superposition,[],[f66,f150])).

fof(f150,plain,(
    sK6 = k2_struct_0(k1_pre_topc(sK5,sK6)) ),
    inference(subsumption_resolution,[],[f141,f112])).

fof(f112,plain,(
    l1_struct_0(k1_pre_topc(sK5,sK6)) ),
    inference(resolution,[],[f105,f64])).

fof(f64,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(f141,plain,
    ( sK6 = k2_struct_0(k1_pre_topc(sK5,sK6))
    | ~ l1_struct_0(k1_pre_topc(sK5,sK6)) ),
    inference(superposition,[],[f100,f63])).

fof(f63,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k2_struct_0(X0) = u1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).

fof(f100,plain,(
    sK6 = u1_struct_0(k1_pre_topc(sK5,sK6)) ),
    inference(subsumption_resolution,[],[f94,f57])).

fof(f94,plain,
    ( sK6 = u1_struct_0(k1_pre_topc(sK5,sK6))
    | ~ l1_pre_topc(sK5) ),
    inference(resolution,[],[f58,f76])).

fof(f76,plain,(
    ! [X0,X1] :
      ( u1_struct_0(k1_pre_topc(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( u1_struct_0(k1_pre_topc(X0,X1)) = X1
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => u1_struct_0(k1_pre_topc(X0,X1)) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_pre_topc)).

fof(f66,plain,(
    ! [X0] :
      ( v1_compts_1(X0)
      | ~ v2_compts_1(k2_struct_0(X0),X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0] :
      ( ( ( v1_compts_1(X0)
          | ~ v2_compts_1(k2_struct_0(X0),X0) )
        & ( v2_compts_1(k2_struct_0(X0),X0)
          | ~ v1_compts_1(X0) ) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ( v1_compts_1(X0)
      <=> v2_compts_1(k2_struct_0(X0),X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ( v1_compts_1(X0)
      <=> v2_compts_1(k2_struct_0(X0),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_compts_1)).

fof(f251,plain,
    ( ~ v1_compts_1(k1_pre_topc(sK5,sK6))
    | ~ sP3(k1_pre_topc(sK5,sK6),sK6) ),
    inference(resolution,[],[f247,f161])).

fof(f161,plain,
    ( ~ v2_compts_1(sK6,sK5)
    | ~ v1_compts_1(k1_pre_topc(sK5,sK6)) ),
    inference(subsumption_resolution,[],[f159,f56])).

fof(f56,plain,(
    ! [X0,X1] :
      ( ~ v1_compts_1(k1_pre_topc(X1,X0))
      | ~ v2_compts_1(X0,X1)
      | ~ sP0(X0,X1) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( ( ~ v1_compts_1(k1_pre_topc(X1,X0))
          | ~ v2_compts_1(X0,X1) )
        & ( v1_compts_1(k1_pre_topc(X1,X0))
          | v2_compts_1(X0,X1) ) )
      | ~ sP0(X0,X1) ) ),
    inference(rectify,[],[f37])).

fof(f37,plain,(
    ! [X1,X0] :
      ( ( ( ~ v1_compts_1(k1_pre_topc(X0,X1))
          | ~ v2_compts_1(X1,X0) )
        & ( v1_compts_1(k1_pre_topc(X0,X1))
          | v2_compts_1(X1,X0) ) )
      | ~ sP0(X1,X0) ) ),
    inference(nnf_transformation,[],[f27])).

fof(f159,plain,
    ( sP0(sK6,sK5)
    | ~ v1_compts_1(k1_pre_topc(sK5,sK6))
    | ~ v2_compts_1(sK6,sK5) ),
    inference(resolution,[],[f121,f54])).

fof(f54,plain,(
    ! [X0,X1] :
      ( ~ v1_compts_1(k1_pre_topc(X1,X0))
      | ~ v2_compts_1(X0,X1)
      | ~ sP1(X0,X1) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( ( ~ v1_compts_1(k1_pre_topc(X1,X0))
          | ~ v2_compts_1(X0,X1) )
        & ( v1_compts_1(k1_pre_topc(X1,X0))
          | v2_compts_1(X0,X1) ) )
      | ~ sP1(X0,X1) ) ),
    inference(rectify,[],[f35])).

fof(f35,plain,(
    ! [X1,X0] :
      ( ( ( ~ v1_compts_1(k1_pre_topc(X0,X1))
          | ~ v2_compts_1(X1,X0) )
        & ( v1_compts_1(k1_pre_topc(X0,X1))
          | v2_compts_1(X1,X0) ) )
      | ~ sP1(X1,X0) ) ),
    inference(nnf_transformation,[],[f28])).

fof(f121,plain,
    ( sP1(sK6,sK5)
    | sP0(sK6,sK5) ),
    inference(resolution,[],[f60,f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( sP0(X1,X0)
      | ~ sP2(X0,X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( sP0(X1,X0)
        & k1_xboole_0 = X1 )
      | ~ sP2(X0,X1) ) ),
    inference(nnf_transformation,[],[f29])).

fof(f60,plain,
    ( sP2(sK5,sK6)
    | sP1(sK6,sK5) ),
    inference(cnf_transformation,[],[f41])).

fof(f247,plain,
    ( v2_compts_1(sK6,sK5)
    | ~ sP3(k1_pre_topc(sK5,sK6),sK6) ),
    inference(resolution,[],[f243,f70])).

fof(f70,plain,(
    ! [X2,X0,X1] :
      ( v2_compts_1(X0,X2)
      | ~ sP3(X1,X0)
      | ~ sP4(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0,X1,X2] :
      ( ( ( v2_compts_1(X0,X2)
          | ~ sP3(X1,X0) )
        & ( sP3(X1,X0)
          | ~ v2_compts_1(X0,X2) ) )
      | ~ sP4(X0,X1,X2) ) ),
    inference(rectify,[],[f43])).

fof(f43,plain,(
    ! [X2,X1,X0] :
      ( ( ( v2_compts_1(X2,X0)
          | ~ sP3(X1,X2) )
        & ( sP3(X1,X2)
          | ~ v2_compts_1(X2,X0) ) )
      | ~ sP4(X2,X1,X0) ) ),
    inference(nnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X2,X1,X0] :
      ( ( v2_compts_1(X2,X0)
      <=> sP3(X1,X2) )
      | ~ sP4(X2,X1,X0) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP4])])).

fof(f243,plain,(
    sP4(sK6,k1_pre_topc(sK5,sK6),sK5) ),
    inference(subsumption_resolution,[],[f242,f83])).

fof(f83,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f78])).

fof(f78,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
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
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f242,plain,
    ( ~ r1_tarski(sK6,sK6)
    | sP4(sK6,k1_pre_topc(sK5,sK6),sK5) ),
    inference(forward_demodulation,[],[f239,f150])).

fof(f239,plain,
    ( ~ r1_tarski(sK6,k2_struct_0(k1_pre_topc(sK5,sK6)))
    | sP4(sK6,k1_pre_topc(sK5,sK6),sK5) ),
    inference(resolution,[],[f101,f99])).

fof(f101,plain,(
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
    inference(resolution,[],[f58,f75])).

fof(f75,plain,(
    ! [X2,X0,X1] :
      ( sP4(X2,X1,X0)
      | ~ r1_tarski(X2,k2_struct_0(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( sP4(X2,X1,X0)
              | ~ r1_tarski(X2,k2_struct_0(X1))
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(definition_folding,[],[f23,f32,f31])).

fof(f31,plain,(
    ! [X1,X2] :
      ( sP3(X1,X2)
    <=> ! [X3] :
          ( v2_compts_1(X3,X1)
          | X2 != X3
          | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP3])])).

fof(f23,plain,(
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
    inference(flattening,[],[f22])).

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
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_compts_1)).

fof(f432,plain,
    ( ~ sP3(k1_pre_topc(sK5,sK6),sK6)
    | v2_compts_1(sK6,k1_pre_topc(sK5,sK6)) ),
    inference(forward_demodulation,[],[f431,f61])).

fof(f61,plain,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).

fof(f431,plain,
    ( v2_compts_1(sK6,k1_pre_topc(sK5,sK6))
    | ~ sP3(k1_pre_topc(sK5,sK6),k2_subset_1(sK6)) ),
    inference(forward_demodulation,[],[f430,f61])).

fof(f430,plain,
    ( v2_compts_1(k2_subset_1(sK6),k1_pre_topc(sK5,sK6))
    | ~ sP3(k1_pre_topc(sK5,sK6),k2_subset_1(sK6)) ),
    inference(resolution,[],[f149,f62])).

fof(f62,plain,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_subset_1)).

fof(f149,plain,(
    ! [X9] :
      ( ~ m1_subset_1(X9,k1_zfmisc_1(sK6))
      | v2_compts_1(X9,k1_pre_topc(sK5,sK6))
      | ~ sP3(k1_pre_topc(sK5,sK6),X9) ) ),
    inference(superposition,[],[f81,f100])).

fof(f81,plain,(
    ! [X0,X3] :
      ( v2_compts_1(X3,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ sP3(X0,X3) ) ),
    inference(equality_resolution,[],[f71])).

fof(f71,plain,(
    ! [X0,X3,X1] :
      ( v2_compts_1(X3,X0)
      | X1 != X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ sP3(X0,X1) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f48,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f46,f47])).

fof(f47,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ v2_compts_1(X2,X0)
          & X1 = X2
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ~ v2_compts_1(sK7(X0,X1),X0)
        & sK7(X0,X1) = X1
        & m1_subset_1(sK7(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f46,plain,(
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
    inference(rectify,[],[f45])).

fof(f45,plain,(
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
    inference(nnf_transformation,[],[f31])).

fof(f523,plain,(
    sP3(k1_pre_topc(sK5,sK6),sK6) ),
    inference(subsumption_resolution,[],[f520,f477])).

fof(f477,plain,(
    v2_compts_1(sK6,k1_pre_topc(sK5,sK6)) ),
    inference(forward_demodulation,[],[f476,f150])).

fof(f476,plain,(
    v2_compts_1(k2_struct_0(k1_pre_topc(sK5,sK6)),k1_pre_topc(sK5,sK6)) ),
    inference(subsumption_resolution,[],[f474,f105])).

fof(f474,plain,
    ( v2_compts_1(k2_struct_0(k1_pre_topc(sK5,sK6)),k1_pre_topc(sK5,sK6))
    | ~ l1_pre_topc(k1_pre_topc(sK5,sK6)) ),
    inference(resolution,[],[f442,f65])).

fof(f65,plain,(
    ! [X0] :
      ( v2_compts_1(k2_struct_0(X0),X0)
      | ~ v1_compts_1(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f442,plain,(
    v1_compts_1(k1_pre_topc(sK5,sK6)) ),
    inference(subsumption_resolution,[],[f436,f243])).

fof(f436,plain,
    ( v1_compts_1(k1_pre_topc(sK5,sK6))
    | ~ sP4(sK6,k1_pre_topc(sK5,sK6),sK5) ),
    inference(resolution,[],[f433,f168])).

fof(f168,plain,(
    ! [X0] :
      ( sP3(X0,sK6)
      | v1_compts_1(k1_pre_topc(sK5,sK6))
      | ~ sP4(sK6,X0,sK5) ) ),
    inference(resolution,[],[f160,f69])).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( sP3(X1,X0)
      | ~ v2_compts_1(X0,X2)
      | ~ sP4(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f160,plain,
    ( v2_compts_1(sK6,sK5)
    | v1_compts_1(k1_pre_topc(sK5,sK6)) ),
    inference(subsumption_resolution,[],[f158,f55])).

fof(f55,plain,(
    ! [X0,X1] :
      ( v1_compts_1(k1_pre_topc(X1,X0))
      | v2_compts_1(X0,X1)
      | ~ sP0(X0,X1) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f158,plain,
    ( sP0(sK6,sK5)
    | v1_compts_1(k1_pre_topc(sK5,sK6))
    | v2_compts_1(sK6,sK5) ),
    inference(resolution,[],[f121,f53])).

fof(f53,plain,(
    ! [X0,X1] :
      ( v1_compts_1(k1_pre_topc(X1,X0))
      | v2_compts_1(X0,X1)
      | ~ sP1(X0,X1) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f520,plain,
    ( ~ v2_compts_1(sK6,k1_pre_topc(sK5,sK6))
    | sP3(k1_pre_topc(sK5,sK6),sK6) ),
    inference(superposition,[],[f74,f439])).

fof(f439,plain,(
    sK6 = sK7(k1_pre_topc(sK5,sK6),sK6) ),
    inference(resolution,[],[f433,f73])).

fof(f73,plain,(
    ! [X0,X1] :
      ( sP3(X0,X1)
      | sK7(X0,X1) = X1 ) ),
    inference(cnf_transformation,[],[f48])).

fof(f74,plain,(
    ! [X0,X1] :
      ( sP3(X0,X1)
      | ~ v2_compts_1(sK7(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f48])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n003.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 11:31:27 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.50  % (13445)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.51  % (13448)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.21/0.51  % (13468)dis+2_128_add=large:afp=100000:afq=1.4:amm=sco:anc=none:lma=on:nm=2:newcnf=on:nwc=1:nicw=on:sas=z3:sos=theory:sac=on:updr=off_288 on theBenchmark
% 0.21/0.51  % (13460)lrs+4_5:4_av=off:bd=off:er=filter:lma=on:lwlo=on:nwc=1:stl=30:sp=occurrence:updr=off_230 on theBenchmark
% 0.21/0.51  % (13456)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 0.21/0.51  % (13454)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 0.21/0.51  % (13447)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.21/0.52  % (13452)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 0.21/0.52  % (13464)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 0.21/0.52  % (13462)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 0.21/0.53  % (13461)lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_145 on theBenchmark
% 0.21/0.53  % (13449)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.21/0.53  % (13449)Refutation not found, incomplete strategy% (13449)------------------------------
% 0.21/0.53  % (13449)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (13449)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (13449)Memory used [KB]: 6140
% 0.21/0.53  % (13449)Time elapsed: 0.113 s
% 0.21/0.53  % (13449)------------------------------
% 0.21/0.53  % (13449)------------------------------
% 0.21/0.53  % (13467)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 0.21/0.53  % (13466)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 0.21/0.53  % (13446)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.21/0.53  % (13459)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 0.21/0.54  % (13444)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 0.21/0.54  % (13444)Refutation not found, incomplete strategy% (13444)------------------------------
% 0.21/0.54  % (13444)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (13444)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (13444)Memory used [KB]: 10618
% 0.21/0.54  % (13444)Time elapsed: 0.105 s
% 0.21/0.54  % (13444)------------------------------
% 0.21/0.54  % (13444)------------------------------
% 0.21/0.54  % (13455)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 0.21/0.54  % (13452)Refutation found. Thanks to Tanya!
% 0.21/0.54  % SZS status Theorem for theBenchmark
% 0.21/0.54  % (13458)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.21/0.54  % (13463)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 1.39/0.54  % (13450)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 1.39/0.54  % (13469)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_364 on theBenchmark
% 1.39/0.54  % (13465)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 1.39/0.54  % (13451)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 1.39/0.55  % (13457)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 1.39/0.55  % (13453)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
% 1.39/0.55  % (13457)Refutation not found, incomplete strategy% (13457)------------------------------
% 1.39/0.55  % (13457)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.39/0.55  % (13457)Termination reason: Refutation not found, incomplete strategy
% 1.39/0.55  
% 1.39/0.55  % (13457)Memory used [KB]: 6140
% 1.39/0.55  % (13457)Time elapsed: 0.136 s
% 1.39/0.55  % (13457)------------------------------
% 1.39/0.55  % (13457)------------------------------
% 1.39/0.55  % SZS output start Proof for theBenchmark
% 1.39/0.55  fof(f524,plain,(
% 1.39/0.55    $false),
% 1.39/0.55    inference(subsumption_resolution,[],[f523,f433])).
% 1.39/0.55  fof(f433,plain,(
% 1.39/0.55    ~sP3(k1_pre_topc(sK5,sK6),sK6)),
% 1.39/0.55    inference(subsumption_resolution,[],[f432,f284])).
% 1.39/0.55  fof(f284,plain,(
% 1.39/0.55    ~v2_compts_1(sK6,k1_pre_topc(sK5,sK6)) | ~sP3(k1_pre_topc(sK5,sK6),sK6)),
% 1.39/0.55    inference(resolution,[],[f251,f166])).
% 1.39/0.55  fof(f166,plain,(
% 1.39/0.55    v1_compts_1(k1_pre_topc(sK5,sK6)) | ~v2_compts_1(sK6,k1_pre_topc(sK5,sK6))),
% 1.39/0.55    inference(subsumption_resolution,[],[f164,f105])).
% 1.39/0.55  fof(f105,plain,(
% 1.39/0.55    l1_pre_topc(k1_pre_topc(sK5,sK6))),
% 1.39/0.55    inference(resolution,[],[f99,f88])).
% 1.39/0.55  fof(f88,plain,(
% 1.39/0.55    ( ! [X0] : (~m1_pre_topc(X0,sK5) | l1_pre_topc(X0)) )),
% 1.39/0.55    inference(resolution,[],[f57,f67])).
% 1.39/0.55  fof(f67,plain,(
% 1.39/0.55    ( ! [X0,X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 1.39/0.55    inference(cnf_transformation,[],[f20])).
% 1.39/0.55  fof(f20,plain,(
% 1.39/0.55    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 1.39/0.55    inference(ennf_transformation,[],[f7])).
% 1.39/0.55  fof(f7,axiom,(
% 1.39/0.55    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 1.39/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).
% 1.39/0.55  fof(f57,plain,(
% 1.39/0.55    l1_pre_topc(sK5)),
% 1.39/0.55    inference(cnf_transformation,[],[f41])).
% 1.39/0.55  fof(f41,plain,(
% 1.39/0.55    (((sP1(sK6,sK5) & k1_xboole_0 != sK6) | sP2(sK5,sK6)) & m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK5)))) & l1_pre_topc(sK5)),
% 1.39/0.55    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6])],[f30,f40,f39])).
% 1.39/0.55  fof(f39,plain,(
% 1.39/0.55    ? [X0] : (? [X1] : (((sP1(X1,X0) & k1_xboole_0 != X1) | sP2(X0,X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0)) => (? [X1] : (((sP1(X1,sK5) & k1_xboole_0 != X1) | sP2(sK5,X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK5)))) & l1_pre_topc(sK5))),
% 1.39/0.55    introduced(choice_axiom,[])).
% 1.39/0.55  fof(f40,plain,(
% 1.39/0.55    ? [X1] : (((sP1(X1,sK5) & k1_xboole_0 != X1) | sP2(sK5,X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK5)))) => (((sP1(sK6,sK5) & k1_xboole_0 != sK6) | sP2(sK5,sK6)) & m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK5))))),
% 1.39/0.55    introduced(choice_axiom,[])).
% 1.39/0.55  fof(f30,plain,(
% 1.39/0.55    ? [X0] : (? [X1] : (((sP1(X1,X0) & k1_xboole_0 != X1) | sP2(X0,X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 1.39/0.55    inference(definition_folding,[],[f16,f29,f28,f27])).
% 1.39/0.55  fof(f27,plain,(
% 1.39/0.55    ! [X1,X0] : ((v2_compts_1(X1,X0) <~> v1_compts_1(k1_pre_topc(X0,X1))) | ~sP0(X1,X0))),
% 1.39/0.55    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 1.39/0.55  fof(f28,plain,(
% 1.39/0.55    ! [X1,X0] : ((v2_compts_1(X1,X0) <~> v1_compts_1(k1_pre_topc(X0,X1))) | ~sP1(X1,X0))),
% 1.39/0.55    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 1.39/0.55  fof(f29,plain,(
% 1.39/0.55    ! [X0,X1] : ((sP0(X1,X0) & k1_xboole_0 = X1) | ~sP2(X0,X1))),
% 1.39/0.55    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).
% 1.39/0.55  fof(f16,plain,(
% 1.39/0.55    ? [X0] : (? [X1] : ((((v2_compts_1(X1,X0) <~> v1_compts_1(k1_pre_topc(X0,X1))) & k1_xboole_0 != X1) | ((v2_compts_1(X1,X0) <~> v1_compts_1(k1_pre_topc(X0,X1))) & k1_xboole_0 = X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 1.39/0.55    inference(ennf_transformation,[],[f14])).
% 1.39/0.55  fof(f14,plain,(
% 1.39/0.55    ~! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (((v2_compts_1(X1,X0) <=> v1_compts_1(k1_pre_topc(X0,X1))) | k1_xboole_0 = X1) & (k1_xboole_0 = X1 => (v2_compts_1(X1,X0) <=> v1_compts_1(k1_pre_topc(X0,X1)))))))),
% 1.39/0.55    inference(pure_predicate_removal,[],[f13])).
% 1.39/0.55  fof(f13,negated_conjecture,(
% 1.39/0.55    ~! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ((v2_pre_topc(X0) => ((v2_compts_1(X1,X0) <=> v1_compts_1(k1_pre_topc(X0,X1))) | k1_xboole_0 = X1)) & (k1_xboole_0 = X1 => (v2_compts_1(X1,X0) <=> v1_compts_1(k1_pre_topc(X0,X1)))))))),
% 1.39/0.55    inference(negated_conjecture,[],[f12])).
% 1.39/0.55  fof(f12,conjecture,(
% 1.39/0.55    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ((v2_pre_topc(X0) => ((v2_compts_1(X1,X0) <=> v1_compts_1(k1_pre_topc(X0,X1))) | k1_xboole_0 = X1)) & (k1_xboole_0 = X1 => (v2_compts_1(X1,X0) <=> v1_compts_1(k1_pre_topc(X0,X1)))))))),
% 1.39/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_compts_1)).
% 1.39/0.55  fof(f99,plain,(
% 1.39/0.55    m1_pre_topc(k1_pre_topc(sK5,sK6),sK5)),
% 1.39/0.55    inference(subsumption_resolution,[],[f93,f57])).
% 1.39/0.55  fof(f93,plain,(
% 1.39/0.55    m1_pre_topc(k1_pre_topc(sK5,sK6),sK5) | ~l1_pre_topc(sK5)),
% 1.39/0.55    inference(resolution,[],[f58,f77])).
% 1.39/0.55  fof(f77,plain,(
% 1.39/0.55    ( ! [X0,X1] : (m1_pre_topc(k1_pre_topc(X0,X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 1.39/0.55    inference(cnf_transformation,[],[f26])).
% 1.39/0.55  fof(f26,plain,(
% 1.39/0.55    ! [X0,X1] : (m1_pre_topc(k1_pre_topc(X0,X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 1.39/0.55    inference(flattening,[],[f25])).
% 1.39/0.55  fof(f25,plain,(
% 1.39/0.55    ! [X0,X1] : (m1_pre_topc(k1_pre_topc(X0,X1),X0) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 1.39/0.55    inference(ennf_transformation,[],[f15])).
% 1.39/0.55  fof(f15,plain,(
% 1.39/0.55    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => m1_pre_topc(k1_pre_topc(X0,X1),X0))),
% 1.39/0.55    inference(pure_predicate_removal,[],[f5])).
% 1.39/0.55  fof(f5,axiom,(
% 1.39/0.55    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => (m1_pre_topc(k1_pre_topc(X0,X1),X0) & v1_pre_topc(k1_pre_topc(X0,X1))))),
% 1.39/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_pre_topc)).
% 1.39/0.55  fof(f58,plain,(
% 1.39/0.55    m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK5)))),
% 1.39/0.55    inference(cnf_transformation,[],[f41])).
% 1.39/0.55  fof(f164,plain,(
% 1.39/0.55    ~v2_compts_1(sK6,k1_pre_topc(sK5,sK6)) | v1_compts_1(k1_pre_topc(sK5,sK6)) | ~l1_pre_topc(k1_pre_topc(sK5,sK6))),
% 1.39/0.55    inference(superposition,[],[f66,f150])).
% 1.39/0.55  fof(f150,plain,(
% 1.39/0.55    sK6 = k2_struct_0(k1_pre_topc(sK5,sK6))),
% 1.39/0.55    inference(subsumption_resolution,[],[f141,f112])).
% 1.39/0.55  fof(f112,plain,(
% 1.39/0.55    l1_struct_0(k1_pre_topc(sK5,sK6))),
% 1.39/0.55    inference(resolution,[],[f105,f64])).
% 1.39/0.55  fof(f64,plain,(
% 1.39/0.55    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 1.39/0.55    inference(cnf_transformation,[],[f18])).
% 1.39/0.55  fof(f18,plain,(
% 1.39/0.55    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 1.39/0.55    inference(ennf_transformation,[],[f6])).
% 1.39/0.55  fof(f6,axiom,(
% 1.39/0.55    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 1.39/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).
% 1.39/0.55  fof(f141,plain,(
% 1.39/0.55    sK6 = k2_struct_0(k1_pre_topc(sK5,sK6)) | ~l1_struct_0(k1_pre_topc(sK5,sK6))),
% 1.39/0.55    inference(superposition,[],[f100,f63])).
% 1.39/0.55  fof(f63,plain,(
% 1.39/0.55    ( ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0)) )),
% 1.39/0.55    inference(cnf_transformation,[],[f17])).
% 1.39/0.55  fof(f17,plain,(
% 1.39/0.55    ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0))),
% 1.39/0.55    inference(ennf_transformation,[],[f4])).
% 1.39/0.55  fof(f4,axiom,(
% 1.39/0.55    ! [X0] : (l1_struct_0(X0) => k2_struct_0(X0) = u1_struct_0(X0))),
% 1.39/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).
% 1.39/0.55  fof(f100,plain,(
% 1.39/0.55    sK6 = u1_struct_0(k1_pre_topc(sK5,sK6))),
% 1.39/0.55    inference(subsumption_resolution,[],[f94,f57])).
% 1.39/0.55  fof(f94,plain,(
% 1.39/0.55    sK6 = u1_struct_0(k1_pre_topc(sK5,sK6)) | ~l1_pre_topc(sK5)),
% 1.39/0.55    inference(resolution,[],[f58,f76])).
% 1.39/0.55  fof(f76,plain,(
% 1.39/0.55    ( ! [X0,X1] : (u1_struct_0(k1_pre_topc(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 1.39/0.55    inference(cnf_transformation,[],[f24])).
% 1.39/0.55  fof(f24,plain,(
% 1.39/0.55    ! [X0] : (! [X1] : (u1_struct_0(k1_pre_topc(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.39/0.55    inference(ennf_transformation,[],[f8])).
% 1.39/0.55  fof(f8,axiom,(
% 1.39/0.55    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => u1_struct_0(k1_pre_topc(X0,X1)) = X1))),
% 1.39/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_pre_topc)).
% 1.39/0.55  fof(f66,plain,(
% 1.39/0.55    ( ! [X0] : (v1_compts_1(X0) | ~v2_compts_1(k2_struct_0(X0),X0) | ~l1_pre_topc(X0)) )),
% 1.39/0.55    inference(cnf_transformation,[],[f42])).
% 1.39/0.55  fof(f42,plain,(
% 1.39/0.55    ! [X0] : (((v1_compts_1(X0) | ~v2_compts_1(k2_struct_0(X0),X0)) & (v2_compts_1(k2_struct_0(X0),X0) | ~v1_compts_1(X0))) | ~l1_pre_topc(X0))),
% 1.39/0.55    inference(nnf_transformation,[],[f19])).
% 1.39/0.55  fof(f19,plain,(
% 1.39/0.55    ! [X0] : ((v1_compts_1(X0) <=> v2_compts_1(k2_struct_0(X0),X0)) | ~l1_pre_topc(X0))),
% 1.39/0.55    inference(ennf_transformation,[],[f10])).
% 1.39/0.55  fof(f10,axiom,(
% 1.39/0.55    ! [X0] : (l1_pre_topc(X0) => (v1_compts_1(X0) <=> v2_compts_1(k2_struct_0(X0),X0)))),
% 1.39/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_compts_1)).
% 1.39/0.55  fof(f251,plain,(
% 1.39/0.55    ~v1_compts_1(k1_pre_topc(sK5,sK6)) | ~sP3(k1_pre_topc(sK5,sK6),sK6)),
% 1.39/0.55    inference(resolution,[],[f247,f161])).
% 1.39/0.55  fof(f161,plain,(
% 1.39/0.55    ~v2_compts_1(sK6,sK5) | ~v1_compts_1(k1_pre_topc(sK5,sK6))),
% 1.39/0.55    inference(subsumption_resolution,[],[f159,f56])).
% 1.39/0.55  fof(f56,plain,(
% 1.39/0.55    ( ! [X0,X1] : (~v1_compts_1(k1_pre_topc(X1,X0)) | ~v2_compts_1(X0,X1) | ~sP0(X0,X1)) )),
% 1.39/0.55    inference(cnf_transformation,[],[f38])).
% 1.39/0.55  fof(f38,plain,(
% 1.39/0.55    ! [X0,X1] : (((~v1_compts_1(k1_pre_topc(X1,X0)) | ~v2_compts_1(X0,X1)) & (v1_compts_1(k1_pre_topc(X1,X0)) | v2_compts_1(X0,X1))) | ~sP0(X0,X1))),
% 1.39/0.55    inference(rectify,[],[f37])).
% 1.39/0.55  fof(f37,plain,(
% 1.39/0.55    ! [X1,X0] : (((~v1_compts_1(k1_pre_topc(X0,X1)) | ~v2_compts_1(X1,X0)) & (v1_compts_1(k1_pre_topc(X0,X1)) | v2_compts_1(X1,X0))) | ~sP0(X1,X0))),
% 1.39/0.55    inference(nnf_transformation,[],[f27])).
% 1.39/0.55  fof(f159,plain,(
% 1.39/0.55    sP0(sK6,sK5) | ~v1_compts_1(k1_pre_topc(sK5,sK6)) | ~v2_compts_1(sK6,sK5)),
% 1.39/0.55    inference(resolution,[],[f121,f54])).
% 1.39/0.55  fof(f54,plain,(
% 1.39/0.55    ( ! [X0,X1] : (~v1_compts_1(k1_pre_topc(X1,X0)) | ~v2_compts_1(X0,X1) | ~sP1(X0,X1)) )),
% 1.39/0.55    inference(cnf_transformation,[],[f36])).
% 1.39/0.55  fof(f36,plain,(
% 1.39/0.55    ! [X0,X1] : (((~v1_compts_1(k1_pre_topc(X1,X0)) | ~v2_compts_1(X0,X1)) & (v1_compts_1(k1_pre_topc(X1,X0)) | v2_compts_1(X0,X1))) | ~sP1(X0,X1))),
% 1.39/0.55    inference(rectify,[],[f35])).
% 1.39/0.55  fof(f35,plain,(
% 1.39/0.55    ! [X1,X0] : (((~v1_compts_1(k1_pre_topc(X0,X1)) | ~v2_compts_1(X1,X0)) & (v1_compts_1(k1_pre_topc(X0,X1)) | v2_compts_1(X1,X0))) | ~sP1(X1,X0))),
% 1.39/0.55    inference(nnf_transformation,[],[f28])).
% 1.39/0.55  fof(f121,plain,(
% 1.39/0.55    sP1(sK6,sK5) | sP0(sK6,sK5)),
% 1.39/0.55    inference(resolution,[],[f60,f52])).
% 1.39/0.55  fof(f52,plain,(
% 1.39/0.55    ( ! [X0,X1] : (sP0(X1,X0) | ~sP2(X0,X1)) )),
% 1.39/0.55    inference(cnf_transformation,[],[f34])).
% 1.39/0.55  fof(f34,plain,(
% 1.39/0.55    ! [X0,X1] : ((sP0(X1,X0) & k1_xboole_0 = X1) | ~sP2(X0,X1))),
% 1.39/0.55    inference(nnf_transformation,[],[f29])).
% 1.39/0.55  fof(f60,plain,(
% 1.39/0.55    sP2(sK5,sK6) | sP1(sK6,sK5)),
% 1.39/0.55    inference(cnf_transformation,[],[f41])).
% 1.39/0.55  fof(f247,plain,(
% 1.39/0.55    v2_compts_1(sK6,sK5) | ~sP3(k1_pre_topc(sK5,sK6),sK6)),
% 1.39/0.55    inference(resolution,[],[f243,f70])).
% 1.39/0.55  fof(f70,plain,(
% 1.39/0.55    ( ! [X2,X0,X1] : (v2_compts_1(X0,X2) | ~sP3(X1,X0) | ~sP4(X0,X1,X2)) )),
% 1.39/0.55    inference(cnf_transformation,[],[f44])).
% 1.39/0.55  fof(f44,plain,(
% 1.39/0.55    ! [X0,X1,X2] : (((v2_compts_1(X0,X2) | ~sP3(X1,X0)) & (sP3(X1,X0) | ~v2_compts_1(X0,X2))) | ~sP4(X0,X1,X2))),
% 1.39/0.55    inference(rectify,[],[f43])).
% 1.39/0.55  fof(f43,plain,(
% 1.39/0.55    ! [X2,X1,X0] : (((v2_compts_1(X2,X0) | ~sP3(X1,X2)) & (sP3(X1,X2) | ~v2_compts_1(X2,X0))) | ~sP4(X2,X1,X0))),
% 1.39/0.55    inference(nnf_transformation,[],[f32])).
% 1.39/0.55  fof(f32,plain,(
% 1.39/0.55    ! [X2,X1,X0] : ((v2_compts_1(X2,X0) <=> sP3(X1,X2)) | ~sP4(X2,X1,X0))),
% 1.39/0.55    introduced(predicate_definition_introduction,[new_symbols(naming,[sP4])])).
% 1.39/0.55  fof(f243,plain,(
% 1.39/0.55    sP4(sK6,k1_pre_topc(sK5,sK6),sK5)),
% 1.39/0.55    inference(subsumption_resolution,[],[f242,f83])).
% 1.39/0.55  fof(f83,plain,(
% 1.39/0.55    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 1.39/0.55    inference(equality_resolution,[],[f78])).
% 1.39/0.55  fof(f78,plain,(
% 1.39/0.55    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 1.39/0.55    inference(cnf_transformation,[],[f50])).
% 1.39/0.55  fof(f50,plain,(
% 1.39/0.55    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.39/0.55    inference(flattening,[],[f49])).
% 1.39/0.55  fof(f49,plain,(
% 1.39/0.55    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.39/0.55    inference(nnf_transformation,[],[f1])).
% 1.39/0.55  fof(f1,axiom,(
% 1.39/0.55    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.39/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 1.39/0.55  fof(f242,plain,(
% 1.39/0.55    ~r1_tarski(sK6,sK6) | sP4(sK6,k1_pre_topc(sK5,sK6),sK5)),
% 1.39/0.55    inference(forward_demodulation,[],[f239,f150])).
% 1.39/0.55  fof(f239,plain,(
% 1.39/0.55    ~r1_tarski(sK6,k2_struct_0(k1_pre_topc(sK5,sK6))) | sP4(sK6,k1_pre_topc(sK5,sK6),sK5)),
% 1.39/0.55    inference(resolution,[],[f101,f99])).
% 1.39/0.55  fof(f101,plain,(
% 1.39/0.55    ( ! [X0] : (~m1_pre_topc(X0,sK5) | ~r1_tarski(sK6,k2_struct_0(X0)) | sP4(sK6,X0,sK5)) )),
% 1.39/0.55    inference(subsumption_resolution,[],[f95,f57])).
% 1.39/0.55  fof(f95,plain,(
% 1.39/0.55    ( ! [X0] : (sP4(sK6,X0,sK5) | ~r1_tarski(sK6,k2_struct_0(X0)) | ~m1_pre_topc(X0,sK5) | ~l1_pre_topc(sK5)) )),
% 1.39/0.55    inference(resolution,[],[f58,f75])).
% 1.39/0.55  fof(f75,plain,(
% 1.39/0.55    ( ! [X2,X0,X1] : (sP4(X2,X1,X0) | ~r1_tarski(X2,k2_struct_0(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 1.39/0.55    inference(cnf_transformation,[],[f33])).
% 1.39/0.55  fof(f33,plain,(
% 1.39/0.55    ! [X0] : (! [X1] : (! [X2] : (sP4(X2,X1,X0) | ~r1_tarski(X2,k2_struct_0(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 1.39/0.55    inference(definition_folding,[],[f23,f32,f31])).
% 1.39/0.55  fof(f31,plain,(
% 1.39/0.55    ! [X1,X2] : (sP3(X1,X2) <=> ! [X3] : (v2_compts_1(X3,X1) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))))),
% 1.39/0.55    introduced(predicate_definition_introduction,[new_symbols(naming,[sP3])])).
% 1.39/0.55  fof(f23,plain,(
% 1.39/0.55    ! [X0] : (! [X1] : (! [X2] : ((v2_compts_1(X2,X0) <=> ! [X3] : (v2_compts_1(X3,X1) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))))) | ~r1_tarski(X2,k2_struct_0(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 1.39/0.55    inference(flattening,[],[f22])).
% 1.39/0.55  fof(f22,plain,(
% 1.39/0.55    ! [X0] : (! [X1] : (! [X2] : (((v2_compts_1(X2,X0) <=> ! [X3] : ((v2_compts_1(X3,X1) | X2 != X3) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))))) | ~r1_tarski(X2,k2_struct_0(X1))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 1.39/0.55    inference(ennf_transformation,[],[f11])).
% 1.39/0.55  fof(f11,axiom,(
% 1.39/0.55    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (r1_tarski(X2,k2_struct_0(X1)) => (v2_compts_1(X2,X0) <=> ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) => (X2 = X3 => v2_compts_1(X3,X1))))))))),
% 1.39/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_compts_1)).
% 1.39/0.55  fof(f432,plain,(
% 1.39/0.55    ~sP3(k1_pre_topc(sK5,sK6),sK6) | v2_compts_1(sK6,k1_pre_topc(sK5,sK6))),
% 1.39/0.55    inference(forward_demodulation,[],[f431,f61])).
% 1.39/0.55  fof(f61,plain,(
% 1.39/0.55    ( ! [X0] : (k2_subset_1(X0) = X0) )),
% 1.39/0.55    inference(cnf_transformation,[],[f2])).
% 1.39/0.55  fof(f2,axiom,(
% 1.39/0.55    ! [X0] : k2_subset_1(X0) = X0),
% 1.39/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).
% 1.39/0.55  fof(f431,plain,(
% 1.39/0.55    v2_compts_1(sK6,k1_pre_topc(sK5,sK6)) | ~sP3(k1_pre_topc(sK5,sK6),k2_subset_1(sK6))),
% 1.39/0.55    inference(forward_demodulation,[],[f430,f61])).
% 1.39/0.55  fof(f430,plain,(
% 1.39/0.55    v2_compts_1(k2_subset_1(sK6),k1_pre_topc(sK5,sK6)) | ~sP3(k1_pre_topc(sK5,sK6),k2_subset_1(sK6))),
% 1.39/0.55    inference(resolution,[],[f149,f62])).
% 1.39/0.55  fof(f62,plain,(
% 1.39/0.55    ( ! [X0] : (m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))) )),
% 1.39/0.55    inference(cnf_transformation,[],[f3])).
% 1.39/0.55  fof(f3,axiom,(
% 1.39/0.55    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))),
% 1.39/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_subset_1)).
% 1.39/0.55  fof(f149,plain,(
% 1.39/0.55    ( ! [X9] : (~m1_subset_1(X9,k1_zfmisc_1(sK6)) | v2_compts_1(X9,k1_pre_topc(sK5,sK6)) | ~sP3(k1_pre_topc(sK5,sK6),X9)) )),
% 1.39/0.55    inference(superposition,[],[f81,f100])).
% 1.39/0.55  fof(f81,plain,(
% 1.39/0.55    ( ! [X0,X3] : (v2_compts_1(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) | ~sP3(X0,X3)) )),
% 1.39/0.55    inference(equality_resolution,[],[f71])).
% 1.39/0.55  fof(f71,plain,(
% 1.39/0.55    ( ! [X0,X3,X1] : (v2_compts_1(X3,X0) | X1 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) | ~sP3(X0,X1)) )),
% 1.39/0.55    inference(cnf_transformation,[],[f48])).
% 1.39/0.55  fof(f48,plain,(
% 1.39/0.55    ! [X0,X1] : ((sP3(X0,X1) | (~v2_compts_1(sK7(X0,X1),X0) & sK7(X0,X1) = X1 & m1_subset_1(sK7(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))) & (! [X3] : (v2_compts_1(X3,X0) | X1 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~sP3(X0,X1)))),
% 1.39/0.55    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f46,f47])).
% 1.39/0.55  fof(f47,plain,(
% 1.39/0.55    ! [X1,X0] : (? [X2] : (~v2_compts_1(X2,X0) & X1 = X2 & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) => (~v2_compts_1(sK7(X0,X1),X0) & sK7(X0,X1) = X1 & m1_subset_1(sK7(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 1.39/0.55    introduced(choice_axiom,[])).
% 1.39/0.55  fof(f46,plain,(
% 1.39/0.55    ! [X0,X1] : ((sP3(X0,X1) | ? [X2] : (~v2_compts_1(X2,X0) & X1 = X2 & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X3] : (v2_compts_1(X3,X0) | X1 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~sP3(X0,X1)))),
% 1.39/0.55    inference(rectify,[],[f45])).
% 1.39/0.55  fof(f45,plain,(
% 1.39/0.55    ! [X1,X2] : ((sP3(X1,X2) | ? [X3] : (~v2_compts_1(X3,X1) & X2 = X3 & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))))) & (! [X3] : (v2_compts_1(X3,X1) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) | ~sP3(X1,X2)))),
% 1.39/0.55    inference(nnf_transformation,[],[f31])).
% 1.39/0.55  fof(f523,plain,(
% 1.39/0.55    sP3(k1_pre_topc(sK5,sK6),sK6)),
% 1.39/0.55    inference(subsumption_resolution,[],[f520,f477])).
% 1.39/0.55  fof(f477,plain,(
% 1.39/0.55    v2_compts_1(sK6,k1_pre_topc(sK5,sK6))),
% 1.39/0.55    inference(forward_demodulation,[],[f476,f150])).
% 1.39/0.55  fof(f476,plain,(
% 1.39/0.55    v2_compts_1(k2_struct_0(k1_pre_topc(sK5,sK6)),k1_pre_topc(sK5,sK6))),
% 1.39/0.55    inference(subsumption_resolution,[],[f474,f105])).
% 1.39/0.55  fof(f474,plain,(
% 1.39/0.55    v2_compts_1(k2_struct_0(k1_pre_topc(sK5,sK6)),k1_pre_topc(sK5,sK6)) | ~l1_pre_topc(k1_pre_topc(sK5,sK6))),
% 1.39/0.55    inference(resolution,[],[f442,f65])).
% 1.39/0.55  fof(f65,plain,(
% 1.39/0.55    ( ! [X0] : (v2_compts_1(k2_struct_0(X0),X0) | ~v1_compts_1(X0) | ~l1_pre_topc(X0)) )),
% 1.39/0.55    inference(cnf_transformation,[],[f42])).
% 1.39/0.55  fof(f442,plain,(
% 1.39/0.55    v1_compts_1(k1_pre_topc(sK5,sK6))),
% 1.39/0.55    inference(subsumption_resolution,[],[f436,f243])).
% 1.39/0.55  fof(f436,plain,(
% 1.39/0.55    v1_compts_1(k1_pre_topc(sK5,sK6)) | ~sP4(sK6,k1_pre_topc(sK5,sK6),sK5)),
% 1.39/0.55    inference(resolution,[],[f433,f168])).
% 1.39/0.55  fof(f168,plain,(
% 1.39/0.55    ( ! [X0] : (sP3(X0,sK6) | v1_compts_1(k1_pre_topc(sK5,sK6)) | ~sP4(sK6,X0,sK5)) )),
% 1.39/0.55    inference(resolution,[],[f160,f69])).
% 1.39/0.55  fof(f69,plain,(
% 1.39/0.55    ( ! [X2,X0,X1] : (sP3(X1,X0) | ~v2_compts_1(X0,X2) | ~sP4(X0,X1,X2)) )),
% 1.39/0.55    inference(cnf_transformation,[],[f44])).
% 1.39/0.55  fof(f160,plain,(
% 1.39/0.55    v2_compts_1(sK6,sK5) | v1_compts_1(k1_pre_topc(sK5,sK6))),
% 1.39/0.55    inference(subsumption_resolution,[],[f158,f55])).
% 1.39/0.55  fof(f55,plain,(
% 1.39/0.55    ( ! [X0,X1] : (v1_compts_1(k1_pre_topc(X1,X0)) | v2_compts_1(X0,X1) | ~sP0(X0,X1)) )),
% 1.39/0.55    inference(cnf_transformation,[],[f38])).
% 1.39/0.55  fof(f158,plain,(
% 1.39/0.55    sP0(sK6,sK5) | v1_compts_1(k1_pre_topc(sK5,sK6)) | v2_compts_1(sK6,sK5)),
% 1.39/0.55    inference(resolution,[],[f121,f53])).
% 1.39/0.55  fof(f53,plain,(
% 1.39/0.55    ( ! [X0,X1] : (v1_compts_1(k1_pre_topc(X1,X0)) | v2_compts_1(X0,X1) | ~sP1(X0,X1)) )),
% 1.39/0.55    inference(cnf_transformation,[],[f36])).
% 1.39/0.55  fof(f520,plain,(
% 1.39/0.55    ~v2_compts_1(sK6,k1_pre_topc(sK5,sK6)) | sP3(k1_pre_topc(sK5,sK6),sK6)),
% 1.39/0.55    inference(superposition,[],[f74,f439])).
% 1.39/0.55  fof(f439,plain,(
% 1.39/0.55    sK6 = sK7(k1_pre_topc(sK5,sK6),sK6)),
% 1.39/0.55    inference(resolution,[],[f433,f73])).
% 1.39/0.55  fof(f73,plain,(
% 1.39/0.55    ( ! [X0,X1] : (sP3(X0,X1) | sK7(X0,X1) = X1) )),
% 1.39/0.55    inference(cnf_transformation,[],[f48])).
% 1.39/0.55  fof(f74,plain,(
% 1.39/0.55    ( ! [X0,X1] : (sP3(X0,X1) | ~v2_compts_1(sK7(X0,X1),X0)) )),
% 1.39/0.55    inference(cnf_transformation,[],[f48])).
% 1.39/0.55  % SZS output end Proof for theBenchmark
% 1.39/0.55  % (13452)------------------------------
% 1.39/0.55  % (13452)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.39/0.55  % (13452)Termination reason: Refutation
% 1.39/0.55  
% 1.39/0.55  % (13452)Memory used [KB]: 1791
% 1.39/0.55  % (13452)Time elapsed: 0.135 s
% 1.39/0.55  % (13452)------------------------------
% 1.39/0.55  % (13452)------------------------------
% 1.39/0.56  % (13443)Success in time 0.194 s
%------------------------------------------------------------------------------
