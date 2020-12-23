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
% DateTime   : Thu Dec  3 13:16:45 EST 2020

% Result     : Theorem 2.22s
% Output     : Refutation 2.22s
% Verified   : 
% Statistics : Number of formulae       :   91 ( 293 expanded)
%              Number of leaves         :   19 (  76 expanded)
%              Depth                    :   17
%              Number of atoms          :  284 (1054 expanded)
%              Number of equality atoms :   28 ( 150 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2673,plain,(
    $false ),
    inference(subsumption_resolution,[],[f2671,f2638])).

fof(f2638,plain,(
    r2_hidden(sK11(u1_pre_topc(sK6),u1_struct_0(sK6)),u1_pre_topc(sK6)) ),
    inference(resolution,[],[f2636,f101])).

fof(f101,plain,(
    ! [X0,X1] :
      ( r1_tarski(k3_tarski(X0),X1)
      | r2_hidden(sK11(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f62])).

fof(f62,plain,(
    ! [X0,X1] :
      ( r1_tarski(k3_tarski(X0),X1)
      | ( ~ r1_tarski(sK11(X0,X1),X1)
        & r2_hidden(sK11(X0,X1),X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK11])],[f28,f61])).

fof(f61,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r1_tarski(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r1_tarski(sK11(X0,X1),X1)
        & r2_hidden(sK11(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,(
    ! [X0,X1] :
      ( r1_tarski(k3_tarski(X0),X1)
      | ? [X2] :
          ( ~ r1_tarski(X2,X1)
          & r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
         => r1_tarski(X2,X1) )
     => r1_tarski(k3_tarski(X0),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_zfmisc_1)).

fof(f2636,plain,(
    ~ r1_tarski(k3_tarski(u1_pre_topc(sK6)),u1_struct_0(sK6)) ),
    inference(subsumption_resolution,[],[f2631,f178])).

fof(f178,plain,(
    u1_struct_0(sK6) != k3_tarski(u1_pre_topc(sK6)) ),
    inference(subsumption_resolution,[],[f138,f128])).

fof(f128,plain,(
    r2_hidden(u1_struct_0(sK6),u1_pre_topc(sK6)) ),
    inference(resolution,[],[f127,f83])).

fof(f83,plain,(
    ! [X0] :
      ( r2_hidden(u1_struct_0(X0),u1_pre_topc(X0))
      | ~ sP2(X0) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,(
    ! [X0] :
      ( ( sP2(X0)
        | ~ sP1(X0)
        | ~ sP0(X0)
        | ~ r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)) )
      & ( ( sP1(X0)
          & sP0(X0)
          & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)) )
        | ~ sP2(X0) ) ) ),
    inference(flattening,[],[f46])).

fof(f46,plain,(
    ! [X0] :
      ( ( sP2(X0)
        | ~ sP1(X0)
        | ~ sP0(X0)
        | ~ r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)) )
      & ( ( sP1(X0)
          & sP0(X0)
          & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)) )
        | ~ sP2(X0) ) ) ),
    inference(nnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0] :
      ( sP2(X0)
    <=> ( sP1(X0)
        & sP0(X0)
        & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).

fof(f127,plain,(
    sP2(sK6) ),
    inference(subsumption_resolution,[],[f125,f74])).

fof(f74,plain,(
    v2_pre_topc(sK6) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,
    ( u1_struct_0(sK6) != k4_yellow_0(k2_yellow_1(u1_pre_topc(sK6)))
    & l1_pre_topc(sK6)
    & v2_pre_topc(sK6) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f20,f43])).

fof(f43,plain,
    ( ? [X0] :
        ( u1_struct_0(X0) != k4_yellow_0(k2_yellow_1(u1_pre_topc(X0)))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
   => ( u1_struct_0(sK6) != k4_yellow_0(k2_yellow_1(u1_pre_topc(sK6)))
      & l1_pre_topc(sK6)
      & v2_pre_topc(sK6) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,(
    ? [X0] :
      ( u1_struct_0(X0) != k4_yellow_0(k2_yellow_1(u1_pre_topc(X0)))
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ? [X0] :
      ( u1_struct_0(X0) != k4_yellow_0(k2_yellow_1(u1_pre_topc(X0)))
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,plain,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0) )
       => u1_struct_0(X0) = k4_yellow_0(k2_yellow_1(u1_pre_topc(X0))) ) ),
    inference(pure_predicate_removal,[],[f16])).

fof(f16,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => u1_struct_0(X0) = k4_yellow_0(k2_yellow_1(u1_pre_topc(X0))) ) ),
    inference(negated_conjecture,[],[f15])).

fof(f15,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => u1_struct_0(X0) = k4_yellow_0(k2_yellow_1(u1_pre_topc(X0))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t24_yellow_1)).

fof(f125,plain,
    ( sP2(sK6)
    | ~ v2_pre_topc(sK6) ),
    inference(resolution,[],[f123,f81])).

fof(f81,plain,(
    ! [X0] :
      ( sP2(X0)
      | ~ v2_pre_topc(X0)
      | ~ sP3(X0) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0] :
      ( ( ( v2_pre_topc(X0)
          | ~ sP2(X0) )
        & ( sP2(X0)
          | ~ v2_pre_topc(X0) ) )
      | ~ sP3(X0) ) ),
    inference(nnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0] :
      ( ( v2_pre_topc(X0)
      <=> sP2(X0) )
      | ~ sP3(X0) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP3])])).

fof(f123,plain,(
    sP3(sK6) ),
    inference(resolution,[],[f75,f97])).

fof(f97,plain,(
    ! [X0] :
      ( sP3(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0] :
      ( sP3(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(definition_folding,[],[f25,f38,f37,f36,f35])).

fof(f35,plain,(
    ! [X0] :
      ( sP0(X0)
    <=> ! [X3] :
          ( r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0))
          | ~ r1_tarski(X3,u1_pre_topc(X0))
          | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f36,plain,(
    ! [X0] :
      ( sP1(X0)
    <=> ! [X1] :
          ( ! [X2] :
              ( r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),u1_pre_topc(X0))
              | ~ r2_hidden(X2,u1_pre_topc(X0))
              | ~ r2_hidden(X1,u1_pre_topc(X0))
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f25,plain,(
    ! [X0] :
      ( ( v2_pre_topc(X0)
      <=> ( ! [X1] :
              ( ! [X2] :
                  ( r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),u1_pre_topc(X0))
                  | ~ r2_hidden(X2,u1_pre_topc(X0))
                  | ~ r2_hidden(X1,u1_pre_topc(X0))
                  | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
          & ! [X3] :
              ( r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0))
              | ~ r1_tarski(X3,u1_pre_topc(X0))
              | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)) ) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ( v2_pre_topc(X0)
      <=> ( ! [X1] :
              ( ! [X2] :
                  ( r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),u1_pre_topc(X0))
                  | ~ r2_hidden(X2,u1_pre_topc(X0))
                  | ~ r2_hidden(X1,u1_pre_topc(X0))
                  | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
          & ! [X3] :
              ( r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0))
              | ~ r1_tarski(X3,u1_pre_topc(X0))
              | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)) ) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ( v2_pre_topc(X0)
      <=> ( ! [X1] :
              ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
             => ! [X2] :
                  ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
                 => ( ( r2_hidden(X2,u1_pre_topc(X0))
                      & r2_hidden(X1,u1_pre_topc(X0)) )
                   => r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),u1_pre_topc(X0)) ) ) )
          & ! [X3] :
              ( m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
             => ( r1_tarski(X3,u1_pre_topc(X0))
               => r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0)) ) )
          & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)) ) ) ) ),
    inference(rectify,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ( v2_pre_topc(X0)
      <=> ( ! [X1] :
              ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
             => ! [X2] :
                  ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
                 => ( ( r2_hidden(X2,u1_pre_topc(X0))
                      & r2_hidden(X1,u1_pre_topc(X0)) )
                   => r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),u1_pre_topc(X0)) ) ) )
          & ! [X1] :
              ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
             => ( r1_tarski(X1,u1_pre_topc(X0))
               => r2_hidden(k5_setfam_1(u1_struct_0(X0),X1),u1_pre_topc(X0)) ) )
          & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_pre_topc)).

fof(f75,plain,(
    l1_pre_topc(sK6) ),
    inference(cnf_transformation,[],[f44])).

fof(f138,plain,
    ( u1_struct_0(sK6) != k3_tarski(u1_pre_topc(sK6))
    | ~ r2_hidden(u1_struct_0(sK6),u1_pre_topc(sK6)) ),
    inference(inner_rewriting,[],[f137])).

fof(f137,plain,
    ( u1_struct_0(sK6) != k3_tarski(u1_pre_topc(sK6))
    | ~ r2_hidden(k3_tarski(u1_pre_topc(sK6)),u1_pre_topc(sK6)) ),
    inference(subsumption_resolution,[],[f136,f98])).

fof(f98,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f60])).

fof(f60,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | r2_hidden(sK10(X0),X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK10])],[f58,f59])).

fof(f59,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK10(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f58,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(rectify,[],[f57])).

fof(f57,plain,(
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

fof(f136,plain,
    ( u1_struct_0(sK6) != k3_tarski(u1_pre_topc(sK6))
    | ~ r2_hidden(k3_tarski(u1_pre_topc(sK6)),u1_pre_topc(sK6))
    | v1_xboole_0(u1_pre_topc(sK6)) ),
    inference(superposition,[],[f76,f79])).

fof(f79,plain,(
    ! [X0] :
      ( k3_tarski(X0) = k4_yellow_0(k2_yellow_1(X0))
      | ~ r2_hidden(k3_tarski(X0),X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( k3_tarski(X0) = k4_yellow_0(k2_yellow_1(X0))
      | ~ r2_hidden(k3_tarski(X0),X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( k3_tarski(X0) = k4_yellow_0(k2_yellow_1(X0))
      | ~ r2_hidden(k3_tarski(X0),X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ( r2_hidden(k3_tarski(X0),X0)
       => k3_tarski(X0) = k4_yellow_0(k2_yellow_1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t14_yellow_1)).

fof(f76,plain,(
    u1_struct_0(sK6) != k4_yellow_0(k2_yellow_1(u1_pre_topc(sK6))) ),
    inference(cnf_transformation,[],[f44])).

fof(f2631,plain,
    ( u1_struct_0(sK6) = k3_tarski(u1_pre_topc(sK6))
    | ~ r1_tarski(k3_tarski(u1_pre_topc(sK6)),u1_struct_0(sK6)) ),
    inference(resolution,[],[f265,f120])).

fof(f120,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f103])).

fof(f103,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f64])).

fof(f64,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f63])).

fof(f63,plain,(
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

fof(f265,plain,(
    ! [X2] :
      ( ~ r1_tarski(k3_tarski(u1_pre_topc(sK6)),X2)
      | u1_struct_0(sK6) = X2
      | ~ r1_tarski(X2,u1_struct_0(sK6)) ) ),
    inference(resolution,[],[f148,f105])).

fof(f105,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f64])).

fof(f148,plain,(
    ! [X6] :
      ( r1_tarski(u1_struct_0(sK6),X6)
      | ~ r1_tarski(k3_tarski(u1_pre_topc(sK6)),X6) ) ),
    inference(resolution,[],[f128,f117])).

fof(f117,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X2,X1)
      | ~ r2_hidden(X2,X0)
      | ~ r1_tarski(k3_tarski(X0),X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X2,X1)
      | ~ r2_hidden(X2,X0)
      | ~ r1_tarski(k3_tarski(X0),X1) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X2,X1)
      | ~ r2_hidden(X2,X0)
      | ~ r1_tarski(k3_tarski(X0),X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X2,X0)
        & r1_tarski(k3_tarski(X0),X1) )
     => r1_tarski(X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t56_setfam_1)).

fof(f2671,plain,(
    ~ r2_hidden(sK11(u1_pre_topc(sK6),u1_struct_0(sK6)),u1_pre_topc(sK6)) ),
    inference(resolution,[],[f2639,f654])).

fof(f654,plain,(
    ! [X2] :
      ( r1_tarski(X2,u1_struct_0(sK6))
      | ~ r2_hidden(X2,u1_pre_topc(sK6)) ) ),
    inference(resolution,[],[f236,f120])).

fof(f236,plain,(
    ! [X10,X11] :
      ( ~ r1_tarski(u1_struct_0(sK6),X11)
      | ~ r2_hidden(X10,u1_pre_topc(sK6))
      | r1_tarski(X10,X11) ) ),
    inference(forward_demodulation,[],[f232,f78])).

fof(f78,plain,(
    ! [X0] : k3_tarski(k1_zfmisc_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : k3_tarski(k1_zfmisc_1(X0)) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t99_zfmisc_1)).

fof(f232,plain,(
    ! [X10,X11] :
      ( ~ r2_hidden(X10,u1_pre_topc(sK6))
      | r1_tarski(X10,X11)
      | ~ r1_tarski(k3_tarski(k1_zfmisc_1(u1_struct_0(sK6))),X11) ) ),
    inference(resolution,[],[f211,f117])).

fof(f211,plain,(
    ! [X8] :
      ( r2_hidden(X8,k1_zfmisc_1(u1_struct_0(sK6)))
      | ~ r2_hidden(X8,u1_pre_topc(sK6)) ) ),
    inference(subsumption_resolution,[],[f204,f157])).

fof(f157,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k1_zfmisc_1(u1_struct_0(sK6)))
      | ~ r2_hidden(X0,u1_pre_topc(sK6)) ) ),
    inference(resolution,[],[f124,f118])).

fof(f118,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).

fof(f124,plain,(
    m1_subset_1(u1_pre_topc(sK6),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK6)))) ),
    inference(resolution,[],[f75,f80])).

fof(f80,plain,(
    ! [X0] :
      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_u1_pre_topc)).

fof(f204,plain,(
    ! [X8] :
      ( ~ r2_hidden(X8,u1_pre_topc(sK6))
      | r2_hidden(X8,k1_zfmisc_1(u1_struct_0(sK6)))
      | v1_xboole_0(k1_zfmisc_1(u1_struct_0(sK6))) ) ),
    inference(resolution,[],[f158,f100])).

fof(f100,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

fof(f158,plain,(
    ! [X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK6)))
      | ~ r2_hidden(X1,u1_pre_topc(sK6)) ) ),
    inference(resolution,[],[f124,f116])).

fof(f116,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).

fof(f2639,plain,(
    ~ r1_tarski(sK11(u1_pre_topc(sK6),u1_struct_0(sK6)),u1_struct_0(sK6)) ),
    inference(resolution,[],[f2636,f102])).

fof(f102,plain,(
    ! [X0,X1] :
      ( r1_tarski(k3_tarski(X0),X1)
      | ~ r1_tarski(sK11(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f62])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 10:07:44 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.22/0.50  % (19938)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
% 0.22/0.50  % (19929)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 0.22/0.50  % (19932)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.22/0.50  % (19952)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 0.22/0.51  % (19950)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 0.22/0.51  % (19935)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 0.22/0.51  % (19941)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 0.22/0.51  % (19944)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 0.22/0.51  % (19929)Refutation not found, incomplete strategy% (19929)------------------------------
% 0.22/0.51  % (19929)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.51  % (19936)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 0.22/0.51  % (19942)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 0.22/0.51  % (19929)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.51  
% 0.22/0.51  % (19929)Memory used [KB]: 10618
% 0.22/0.51  % (19929)Time elapsed: 0.102 s
% 0.22/0.51  % (19929)------------------------------
% 0.22/0.51  % (19929)------------------------------
% 0.22/0.51  % (19937)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 0.22/0.51  % (19939)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 0.22/0.51  % (19942)Refutation not found, incomplete strategy% (19942)------------------------------
% 0.22/0.51  % (19942)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.52  % (19942)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.52  
% 0.22/0.52  % (19942)Memory used [KB]: 6140
% 0.22/0.52  % (19942)Time elapsed: 0.106 s
% 0.22/0.52  % (19942)------------------------------
% 0.22/0.52  % (19942)------------------------------
% 0.22/0.52  % (19935)Refutation not found, incomplete strategy% (19935)------------------------------
% 0.22/0.52  % (19935)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.52  % (19935)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.52  
% 0.22/0.52  % (19935)Memory used [KB]: 10618
% 0.22/0.52  % (19935)Time elapsed: 0.113 s
% 0.22/0.52  % (19935)------------------------------
% 0.22/0.52  % (19935)------------------------------
% 0.22/0.52  % (19945)lrs+4_5:4_av=off:bd=off:er=filter:lma=on:lwlo=on:nwc=1:stl=30:sp=occurrence:updr=off_230 on theBenchmark
% 0.22/0.52  % (19946)lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_145 on theBenchmark
% 0.22/0.52  % (19949)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 0.22/0.52  % (19933)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.22/0.52  % (19953)dis+2_128_add=large:afp=100000:afq=1.4:amm=sco:anc=none:lma=on:nm=2:newcnf=on:nwc=1:nicw=on:sas=z3:sos=theory:sac=on:updr=off_288 on theBenchmark
% 0.22/0.53  % (19930)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 0.22/0.53  % (19931)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.22/0.53  % (19930)Refutation not found, incomplete strategy% (19930)------------------------------
% 0.22/0.53  % (19930)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.53  % (19930)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.53  
% 0.22/0.53  % (19930)Memory used [KB]: 10618
% 0.22/0.53  % (19930)Time elapsed: 0.124 s
% 0.22/0.53  % (19930)------------------------------
% 0.22/0.53  % (19930)------------------------------
% 0.22/0.54  % (19954)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_364 on theBenchmark
% 0.22/0.54  % (19943)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.22/0.55  % (19951)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 0.22/0.55  % (19948)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 0.22/0.57  % (19940)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 0.22/0.59  % (19934)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 1.82/0.59  % (19947)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 2.02/0.63  % (19938)Refutation not found, incomplete strategy% (19938)------------------------------
% 2.02/0.63  % (19938)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.02/0.63  % (19938)Termination reason: Refutation not found, incomplete strategy
% 2.02/0.63  
% 2.02/0.63  % (19938)Memory used [KB]: 6140
% 2.02/0.63  % (19938)Time elapsed: 0.228 s
% 2.02/0.63  % (19938)------------------------------
% 2.02/0.63  % (19938)------------------------------
% 2.22/0.67  % (19937)Refutation found. Thanks to Tanya!
% 2.22/0.67  % SZS status Theorem for theBenchmark
% 2.22/0.67  % SZS output start Proof for theBenchmark
% 2.22/0.67  fof(f2673,plain,(
% 2.22/0.67    $false),
% 2.22/0.67    inference(subsumption_resolution,[],[f2671,f2638])).
% 2.22/0.67  fof(f2638,plain,(
% 2.22/0.67    r2_hidden(sK11(u1_pre_topc(sK6),u1_struct_0(sK6)),u1_pre_topc(sK6))),
% 2.22/0.67    inference(resolution,[],[f2636,f101])).
% 2.22/0.67  fof(f101,plain,(
% 2.22/0.67    ( ! [X0,X1] : (r1_tarski(k3_tarski(X0),X1) | r2_hidden(sK11(X0,X1),X0)) )),
% 2.22/0.67    inference(cnf_transformation,[],[f62])).
% 2.22/0.67  fof(f62,plain,(
% 2.22/0.67    ! [X0,X1] : (r1_tarski(k3_tarski(X0),X1) | (~r1_tarski(sK11(X0,X1),X1) & r2_hidden(sK11(X0,X1),X0)))),
% 2.22/0.67    inference(skolemisation,[status(esa),new_symbols(skolem,[sK11])],[f28,f61])).
% 2.22/0.67  fof(f61,plain,(
% 2.22/0.67    ! [X1,X0] : (? [X2] : (~r1_tarski(X2,X1) & r2_hidden(X2,X0)) => (~r1_tarski(sK11(X0,X1),X1) & r2_hidden(sK11(X0,X1),X0)))),
% 2.22/0.67    introduced(choice_axiom,[])).
% 2.22/0.67  fof(f28,plain,(
% 2.22/0.67    ! [X0,X1] : (r1_tarski(k3_tarski(X0),X1) | ? [X2] : (~r1_tarski(X2,X1) & r2_hidden(X2,X0)))),
% 2.22/0.67    inference(ennf_transformation,[],[f4])).
% 2.22/0.67  fof(f4,axiom,(
% 2.22/0.67    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) => r1_tarski(X2,X1)) => r1_tarski(k3_tarski(X0),X1))),
% 2.22/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_zfmisc_1)).
% 2.22/0.67  fof(f2636,plain,(
% 2.22/0.67    ~r1_tarski(k3_tarski(u1_pre_topc(sK6)),u1_struct_0(sK6))),
% 2.22/0.67    inference(subsumption_resolution,[],[f2631,f178])).
% 2.22/0.67  fof(f178,plain,(
% 2.22/0.67    u1_struct_0(sK6) != k3_tarski(u1_pre_topc(sK6))),
% 2.22/0.67    inference(subsumption_resolution,[],[f138,f128])).
% 2.22/0.67  fof(f128,plain,(
% 2.22/0.67    r2_hidden(u1_struct_0(sK6),u1_pre_topc(sK6))),
% 2.22/0.67    inference(resolution,[],[f127,f83])).
% 2.22/0.67  fof(f83,plain,(
% 2.22/0.67    ( ! [X0] : (r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)) | ~sP2(X0)) )),
% 2.22/0.67    inference(cnf_transformation,[],[f47])).
% 2.22/0.67  fof(f47,plain,(
% 2.22/0.67    ! [X0] : ((sP2(X0) | ~sP1(X0) | ~sP0(X0) | ~r2_hidden(u1_struct_0(X0),u1_pre_topc(X0))) & ((sP1(X0) & sP0(X0) & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0))) | ~sP2(X0)))),
% 2.22/0.67    inference(flattening,[],[f46])).
% 2.22/0.67  fof(f46,plain,(
% 2.22/0.67    ! [X0] : ((sP2(X0) | (~sP1(X0) | ~sP0(X0) | ~r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)))) & ((sP1(X0) & sP0(X0) & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0))) | ~sP2(X0)))),
% 2.22/0.67    inference(nnf_transformation,[],[f37])).
% 2.22/0.67  fof(f37,plain,(
% 2.22/0.67    ! [X0] : (sP2(X0) <=> (sP1(X0) & sP0(X0) & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0))))),
% 2.22/0.67    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).
% 2.22/0.67  fof(f127,plain,(
% 2.22/0.67    sP2(sK6)),
% 2.22/0.67    inference(subsumption_resolution,[],[f125,f74])).
% 2.22/0.67  fof(f74,plain,(
% 2.22/0.67    v2_pre_topc(sK6)),
% 2.22/0.67    inference(cnf_transformation,[],[f44])).
% 2.22/0.67  fof(f44,plain,(
% 2.22/0.67    u1_struct_0(sK6) != k4_yellow_0(k2_yellow_1(u1_pre_topc(sK6))) & l1_pre_topc(sK6) & v2_pre_topc(sK6)),
% 2.22/0.67    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f20,f43])).
% 2.22/0.67  fof(f43,plain,(
% 2.22/0.67    ? [X0] : (u1_struct_0(X0) != k4_yellow_0(k2_yellow_1(u1_pre_topc(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0)) => (u1_struct_0(sK6) != k4_yellow_0(k2_yellow_1(u1_pre_topc(sK6))) & l1_pre_topc(sK6) & v2_pre_topc(sK6))),
% 2.22/0.67    introduced(choice_axiom,[])).
% 2.22/0.67  fof(f20,plain,(
% 2.22/0.67    ? [X0] : (u1_struct_0(X0) != k4_yellow_0(k2_yellow_1(u1_pre_topc(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 2.22/0.67    inference(flattening,[],[f19])).
% 2.22/0.67  fof(f19,plain,(
% 2.22/0.67    ? [X0] : (u1_struct_0(X0) != k4_yellow_0(k2_yellow_1(u1_pre_topc(X0))) & (l1_pre_topc(X0) & v2_pre_topc(X0)))),
% 2.22/0.67    inference(ennf_transformation,[],[f18])).
% 2.22/0.67  fof(f18,plain,(
% 2.22/0.67    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => u1_struct_0(X0) = k4_yellow_0(k2_yellow_1(u1_pre_topc(X0))))),
% 2.22/0.67    inference(pure_predicate_removal,[],[f16])).
% 2.22/0.67  fof(f16,negated_conjecture,(
% 2.22/0.67    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => u1_struct_0(X0) = k4_yellow_0(k2_yellow_1(u1_pre_topc(X0))))),
% 2.22/0.67    inference(negated_conjecture,[],[f15])).
% 2.22/0.67  fof(f15,conjecture,(
% 2.22/0.67    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => u1_struct_0(X0) = k4_yellow_0(k2_yellow_1(u1_pre_topc(X0))))),
% 2.22/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t24_yellow_1)).
% 2.22/0.67  fof(f125,plain,(
% 2.22/0.67    sP2(sK6) | ~v2_pre_topc(sK6)),
% 2.22/0.67    inference(resolution,[],[f123,f81])).
% 2.22/0.67  fof(f81,plain,(
% 2.22/0.67    ( ! [X0] : (sP2(X0) | ~v2_pre_topc(X0) | ~sP3(X0)) )),
% 2.22/0.67    inference(cnf_transformation,[],[f45])).
% 2.22/0.67  fof(f45,plain,(
% 2.22/0.67    ! [X0] : (((v2_pre_topc(X0) | ~sP2(X0)) & (sP2(X0) | ~v2_pre_topc(X0))) | ~sP3(X0))),
% 2.22/0.67    inference(nnf_transformation,[],[f38])).
% 2.22/0.67  fof(f38,plain,(
% 2.22/0.67    ! [X0] : ((v2_pre_topc(X0) <=> sP2(X0)) | ~sP3(X0))),
% 2.22/0.67    introduced(predicate_definition_introduction,[new_symbols(naming,[sP3])])).
% 2.22/0.68  fof(f123,plain,(
% 2.22/0.68    sP3(sK6)),
% 2.22/0.68    inference(resolution,[],[f75,f97])).
% 2.22/0.68  fof(f97,plain,(
% 2.22/0.68    ( ! [X0] : (sP3(X0) | ~l1_pre_topc(X0)) )),
% 2.22/0.68    inference(cnf_transformation,[],[f39])).
% 2.22/0.68  fof(f39,plain,(
% 2.22/0.68    ! [X0] : (sP3(X0) | ~l1_pre_topc(X0))),
% 2.22/0.68    inference(definition_folding,[],[f25,f38,f37,f36,f35])).
% 2.22/0.68  fof(f35,plain,(
% 2.22/0.68    ! [X0] : (sP0(X0) <=> ! [X3] : (r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0)) | ~r1_tarski(X3,u1_pre_topc(X0)) | ~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))))),
% 2.22/0.68    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 2.22/0.68  fof(f36,plain,(
% 2.22/0.68    ! [X0] : (sP1(X0) <=> ! [X1] : (! [X2] : (r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),u1_pre_topc(X0)) | ~r2_hidden(X2,u1_pre_topc(X0)) | ~r2_hidden(X1,u1_pre_topc(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))))),
% 2.22/0.68    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 2.22/0.68  fof(f25,plain,(
% 2.22/0.68    ! [X0] : ((v2_pre_topc(X0) <=> (! [X1] : (! [X2] : (r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),u1_pre_topc(X0)) | ~r2_hidden(X2,u1_pre_topc(X0)) | ~r2_hidden(X1,u1_pre_topc(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & ! [X3] : (r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0)) | ~r1_tarski(X3,u1_pre_topc(X0)) | ~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)))) | ~l1_pre_topc(X0))),
% 2.22/0.68    inference(flattening,[],[f24])).
% 2.22/0.68  fof(f24,plain,(
% 2.22/0.68    ! [X0] : ((v2_pre_topc(X0) <=> (! [X1] : (! [X2] : ((r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),u1_pre_topc(X0)) | (~r2_hidden(X2,u1_pre_topc(X0)) | ~r2_hidden(X1,u1_pre_topc(X0)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & ! [X3] : ((r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0)) | ~r1_tarski(X3,u1_pre_topc(X0))) | ~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)))) | ~l1_pre_topc(X0))),
% 2.22/0.68    inference(ennf_transformation,[],[f17])).
% 2.22/0.68  fof(f17,plain,(
% 2.22/0.68    ! [X0] : (l1_pre_topc(X0) => (v2_pre_topc(X0) <=> (! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((r2_hidden(X2,u1_pre_topc(X0)) & r2_hidden(X1,u1_pre_topc(X0))) => r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),u1_pre_topc(X0))))) & ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => (r1_tarski(X3,u1_pre_topc(X0)) => r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0)))) & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)))))),
% 2.22/0.68    inference(rectify,[],[f12])).
% 2.22/0.68  fof(f12,axiom,(
% 2.22/0.68    ! [X0] : (l1_pre_topc(X0) => (v2_pre_topc(X0) <=> (! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((r2_hidden(X2,u1_pre_topc(X0)) & r2_hidden(X1,u1_pre_topc(X0))) => r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),u1_pre_topc(X0))))) & ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => (r1_tarski(X1,u1_pre_topc(X0)) => r2_hidden(k5_setfam_1(u1_struct_0(X0),X1),u1_pre_topc(X0)))) & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)))))),
% 2.22/0.68    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_pre_topc)).
% 2.22/0.68  fof(f75,plain,(
% 2.22/0.68    l1_pre_topc(sK6)),
% 2.22/0.68    inference(cnf_transformation,[],[f44])).
% 2.22/0.68  fof(f138,plain,(
% 2.22/0.68    u1_struct_0(sK6) != k3_tarski(u1_pre_topc(sK6)) | ~r2_hidden(u1_struct_0(sK6),u1_pre_topc(sK6))),
% 2.22/0.68    inference(inner_rewriting,[],[f137])).
% 2.22/0.68  fof(f137,plain,(
% 2.22/0.68    u1_struct_0(sK6) != k3_tarski(u1_pre_topc(sK6)) | ~r2_hidden(k3_tarski(u1_pre_topc(sK6)),u1_pre_topc(sK6))),
% 2.22/0.68    inference(subsumption_resolution,[],[f136,f98])).
% 2.22/0.68  fof(f98,plain,(
% 2.22/0.68    ( ! [X2,X0] : (~r2_hidden(X2,X0) | ~v1_xboole_0(X0)) )),
% 2.22/0.68    inference(cnf_transformation,[],[f60])).
% 2.22/0.68  fof(f60,plain,(
% 2.22/0.68    ! [X0] : ((v1_xboole_0(X0) | r2_hidden(sK10(X0),X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 2.22/0.68    inference(skolemisation,[status(esa),new_symbols(skolem,[sK10])],[f58,f59])).
% 2.22/0.68  fof(f59,plain,(
% 2.22/0.68    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK10(X0),X0))),
% 2.22/0.68    introduced(choice_axiom,[])).
% 2.22/0.68  fof(f58,plain,(
% 2.22/0.68    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 2.22/0.68    inference(rectify,[],[f57])).
% 2.22/0.68  fof(f57,plain,(
% 2.22/0.68    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0)))),
% 2.22/0.68    inference(nnf_transformation,[],[f1])).
% 2.22/0.68  fof(f1,axiom,(
% 2.22/0.68    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 2.22/0.68    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).
% 2.22/0.68  fof(f136,plain,(
% 2.22/0.68    u1_struct_0(sK6) != k3_tarski(u1_pre_topc(sK6)) | ~r2_hidden(k3_tarski(u1_pre_topc(sK6)),u1_pre_topc(sK6)) | v1_xboole_0(u1_pre_topc(sK6))),
% 2.22/0.68    inference(superposition,[],[f76,f79])).
% 2.22/0.68  fof(f79,plain,(
% 2.22/0.68    ( ! [X0] : (k3_tarski(X0) = k4_yellow_0(k2_yellow_1(X0)) | ~r2_hidden(k3_tarski(X0),X0) | v1_xboole_0(X0)) )),
% 2.22/0.68    inference(cnf_transformation,[],[f22])).
% 2.22/0.68  fof(f22,plain,(
% 2.22/0.68    ! [X0] : (k3_tarski(X0) = k4_yellow_0(k2_yellow_1(X0)) | ~r2_hidden(k3_tarski(X0),X0) | v1_xboole_0(X0))),
% 2.22/0.68    inference(flattening,[],[f21])).
% 2.22/0.68  fof(f21,plain,(
% 2.22/0.68    ! [X0] : ((k3_tarski(X0) = k4_yellow_0(k2_yellow_1(X0)) | ~r2_hidden(k3_tarski(X0),X0)) | v1_xboole_0(X0))),
% 2.22/0.68    inference(ennf_transformation,[],[f14])).
% 2.22/0.68  fof(f14,axiom,(
% 2.22/0.68    ! [X0] : (~v1_xboole_0(X0) => (r2_hidden(k3_tarski(X0),X0) => k3_tarski(X0) = k4_yellow_0(k2_yellow_1(X0))))),
% 2.22/0.68    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t14_yellow_1)).
% 2.22/0.68  fof(f76,plain,(
% 2.22/0.68    u1_struct_0(sK6) != k4_yellow_0(k2_yellow_1(u1_pre_topc(sK6)))),
% 2.22/0.68    inference(cnf_transformation,[],[f44])).
% 2.22/0.68  fof(f2631,plain,(
% 2.22/0.68    u1_struct_0(sK6) = k3_tarski(u1_pre_topc(sK6)) | ~r1_tarski(k3_tarski(u1_pre_topc(sK6)),u1_struct_0(sK6))),
% 2.22/0.68    inference(resolution,[],[f265,f120])).
% 2.22/0.68  fof(f120,plain,(
% 2.22/0.68    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 2.22/0.68    inference(equality_resolution,[],[f103])).
% 2.22/0.68  fof(f103,plain,(
% 2.22/0.68    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 2.22/0.68    inference(cnf_transformation,[],[f64])).
% 2.22/0.68  fof(f64,plain,(
% 2.22/0.68    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.22/0.68    inference(flattening,[],[f63])).
% 2.22/0.68  fof(f63,plain,(
% 2.22/0.68    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.22/0.68    inference(nnf_transformation,[],[f2])).
% 2.22/0.68  fof(f2,axiom,(
% 2.22/0.68    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 2.22/0.68    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 2.22/0.68  fof(f265,plain,(
% 2.22/0.68    ( ! [X2] : (~r1_tarski(k3_tarski(u1_pre_topc(sK6)),X2) | u1_struct_0(sK6) = X2 | ~r1_tarski(X2,u1_struct_0(sK6))) )),
% 2.22/0.68    inference(resolution,[],[f148,f105])).
% 2.22/0.68  fof(f105,plain,(
% 2.22/0.68    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 2.22/0.68    inference(cnf_transformation,[],[f64])).
% 2.22/0.68  fof(f148,plain,(
% 2.22/0.68    ( ! [X6] : (r1_tarski(u1_struct_0(sK6),X6) | ~r1_tarski(k3_tarski(u1_pre_topc(sK6)),X6)) )),
% 2.22/0.68    inference(resolution,[],[f128,f117])).
% 2.22/0.68  fof(f117,plain,(
% 2.22/0.68    ( ! [X2,X0,X1] : (r1_tarski(X2,X1) | ~r2_hidden(X2,X0) | ~r1_tarski(k3_tarski(X0),X1)) )),
% 2.22/0.68    inference(cnf_transformation,[],[f33])).
% 2.22/0.68  fof(f33,plain,(
% 2.22/0.68    ! [X0,X1,X2] : (r1_tarski(X2,X1) | ~r2_hidden(X2,X0) | ~r1_tarski(k3_tarski(X0),X1))),
% 2.22/0.68    inference(flattening,[],[f32])).
% 2.22/0.68  fof(f32,plain,(
% 2.22/0.68    ! [X0,X1,X2] : (r1_tarski(X2,X1) | (~r2_hidden(X2,X0) | ~r1_tarski(k3_tarski(X0),X1)))),
% 2.22/0.68    inference(ennf_transformation,[],[f9])).
% 2.22/0.68  fof(f9,axiom,(
% 2.22/0.68    ! [X0,X1,X2] : ((r2_hidden(X2,X0) & r1_tarski(k3_tarski(X0),X1)) => r1_tarski(X2,X1))),
% 2.22/0.68    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t56_setfam_1)).
% 2.22/0.68  fof(f2671,plain,(
% 2.22/0.68    ~r2_hidden(sK11(u1_pre_topc(sK6),u1_struct_0(sK6)),u1_pre_topc(sK6))),
% 2.22/0.68    inference(resolution,[],[f2639,f654])).
% 2.22/0.68  fof(f654,plain,(
% 2.22/0.68    ( ! [X2] : (r1_tarski(X2,u1_struct_0(sK6)) | ~r2_hidden(X2,u1_pre_topc(sK6))) )),
% 2.22/0.68    inference(resolution,[],[f236,f120])).
% 2.22/0.68  fof(f236,plain,(
% 2.22/0.68    ( ! [X10,X11] : (~r1_tarski(u1_struct_0(sK6),X11) | ~r2_hidden(X10,u1_pre_topc(sK6)) | r1_tarski(X10,X11)) )),
% 2.22/0.68    inference(forward_demodulation,[],[f232,f78])).
% 2.22/0.68  fof(f78,plain,(
% 2.22/0.68    ( ! [X0] : (k3_tarski(k1_zfmisc_1(X0)) = X0) )),
% 2.22/0.68    inference(cnf_transformation,[],[f5])).
% 2.22/0.68  fof(f5,axiom,(
% 2.22/0.68    ! [X0] : k3_tarski(k1_zfmisc_1(X0)) = X0),
% 2.22/0.68    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t99_zfmisc_1)).
% 2.22/0.68  fof(f232,plain,(
% 2.22/0.68    ( ! [X10,X11] : (~r2_hidden(X10,u1_pre_topc(sK6)) | r1_tarski(X10,X11) | ~r1_tarski(k3_tarski(k1_zfmisc_1(u1_struct_0(sK6))),X11)) )),
% 2.22/0.68    inference(resolution,[],[f211,f117])).
% 2.22/0.68  fof(f211,plain,(
% 2.22/0.68    ( ! [X8] : (r2_hidden(X8,k1_zfmisc_1(u1_struct_0(sK6))) | ~r2_hidden(X8,u1_pre_topc(sK6))) )),
% 2.22/0.68    inference(subsumption_resolution,[],[f204,f157])).
% 2.22/0.68  fof(f157,plain,(
% 2.22/0.68    ( ! [X0] : (~v1_xboole_0(k1_zfmisc_1(u1_struct_0(sK6))) | ~r2_hidden(X0,u1_pre_topc(sK6))) )),
% 2.22/0.68    inference(resolution,[],[f124,f118])).
% 2.22/0.68  fof(f118,plain,(
% 2.22/0.68    ( ! [X2,X0,X1] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) )),
% 2.22/0.68    inference(cnf_transformation,[],[f34])).
% 2.22/0.68  fof(f34,plain,(
% 2.22/0.68    ! [X0,X1,X2] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 2.22/0.68    inference(ennf_transformation,[],[f10])).
% 2.22/0.68  fof(f10,axiom,(
% 2.22/0.68    ! [X0,X1,X2] : ~(v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1))),
% 2.22/0.68    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).
% 2.22/0.68  fof(f124,plain,(
% 2.22/0.68    m1_subset_1(u1_pre_topc(sK6),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK6))))),
% 2.22/0.68    inference(resolution,[],[f75,f80])).
% 2.22/0.68  fof(f80,plain,(
% 2.22/0.68    ( ! [X0] : (m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0)) )),
% 2.22/0.68    inference(cnf_transformation,[],[f23])).
% 2.22/0.68  fof(f23,plain,(
% 2.22/0.68    ! [X0] : (m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.22/0.68    inference(ennf_transformation,[],[f13])).
% 2.22/0.68  fof(f13,axiom,(
% 2.22/0.68    ! [X0] : (l1_pre_topc(X0) => m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))))),
% 2.22/0.68    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_u1_pre_topc)).
% 2.22/0.68  fof(f204,plain,(
% 2.22/0.68    ( ! [X8] : (~r2_hidden(X8,u1_pre_topc(sK6)) | r2_hidden(X8,k1_zfmisc_1(u1_struct_0(sK6))) | v1_xboole_0(k1_zfmisc_1(u1_struct_0(sK6)))) )),
% 2.22/0.68    inference(resolution,[],[f158,f100])).
% 2.22/0.68  fof(f100,plain,(
% 2.22/0.68    ( ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1)) )),
% 2.22/0.68    inference(cnf_transformation,[],[f27])).
% 2.22/0.68  fof(f27,plain,(
% 2.22/0.68    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 2.22/0.68    inference(flattening,[],[f26])).
% 2.22/0.68  fof(f26,plain,(
% 2.22/0.68    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 2.22/0.68    inference(ennf_transformation,[],[f7])).
% 2.22/0.68  fof(f7,axiom,(
% 2.22/0.68    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 2.22/0.68    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).
% 2.22/0.68  fof(f158,plain,(
% 2.22/0.68    ( ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK6))) | ~r2_hidden(X1,u1_pre_topc(sK6))) )),
% 2.22/0.68    inference(resolution,[],[f124,f116])).
% 2.22/0.68  fof(f116,plain,(
% 2.22/0.68    ( ! [X2,X0,X1] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) )),
% 2.22/0.68    inference(cnf_transformation,[],[f31])).
% 2.22/0.68  fof(f31,plain,(
% 2.22/0.68    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 2.22/0.68    inference(flattening,[],[f30])).
% 2.22/0.68  fof(f30,plain,(
% 2.22/0.68    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)))),
% 2.22/0.68    inference(ennf_transformation,[],[f8])).
% 2.22/0.68  fof(f8,axiom,(
% 2.22/0.68    ! [X0,X1,X2] : ((m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1)) => m1_subset_1(X0,X2))),
% 2.22/0.68    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).
% 2.22/0.68  fof(f2639,plain,(
% 2.22/0.68    ~r1_tarski(sK11(u1_pre_topc(sK6),u1_struct_0(sK6)),u1_struct_0(sK6))),
% 2.22/0.68    inference(resolution,[],[f2636,f102])).
% 2.22/0.68  fof(f102,plain,(
% 2.22/0.68    ( ! [X0,X1] : (r1_tarski(k3_tarski(X0),X1) | ~r1_tarski(sK11(X0,X1),X1)) )),
% 2.22/0.68    inference(cnf_transformation,[],[f62])).
% 2.22/0.68  % SZS output end Proof for theBenchmark
% 2.22/0.68  % (19937)------------------------------
% 2.22/0.68  % (19937)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.22/0.68  % (19937)Termination reason: Refutation
% 2.22/0.68  
% 2.22/0.68  % (19937)Memory used [KB]: 2558
% 2.22/0.68  % (19937)Time elapsed: 0.272 s
% 2.22/0.68  % (19937)------------------------------
% 2.22/0.68  % (19937)------------------------------
% 2.22/0.68  % (19928)Success in time 0.328 s
%------------------------------------------------------------------------------
