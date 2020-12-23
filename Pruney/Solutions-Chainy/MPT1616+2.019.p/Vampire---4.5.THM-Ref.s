%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:16:46 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   97 ( 234 expanded)
%              Number of leaves         :   20 (  62 expanded)
%              Depth                    :   24
%              Number of atoms          :  286 ( 803 expanded)
%              Number of equality atoms :   27 ( 106 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f741,plain,(
    $false ),
    inference(subsumption_resolution,[],[f739,f103])).

fof(f103,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f95])).

fof(f95,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f63])).

fof(f63,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f62])).

fof(f62,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f739,plain,(
    ~ r1_tarski(k3_tarski(u1_pre_topc(sK4)),k3_tarski(u1_pre_topc(sK4))) ),
    inference(resolution,[],[f728,f125])).

fof(f125,plain,(
    ! [X3] :
      ( r1_tarski(u1_struct_0(sK4),X3)
      | ~ r1_tarski(k3_tarski(u1_pre_topc(sK4)),X3) ) ),
    inference(resolution,[],[f110,f100])).

fof(f100,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X2,X1)
      | ~ r2_hidden(X2,X0)
      | ~ r1_tarski(k3_tarski(X0),X1) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X2,X1)
      | ~ r2_hidden(X2,X0)
      | ~ r1_tarski(k3_tarski(X0),X1) ) ),
    inference(flattening,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X2,X1)
      | ~ r2_hidden(X2,X0)
      | ~ r1_tarski(k3_tarski(X0),X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X2,X0)
        & r1_tarski(k3_tarski(X0),X1) )
     => r1_tarski(X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t56_setfam_1)).

fof(f110,plain,(
    r2_hidden(u1_struct_0(sK4),u1_pre_topc(sK4)) ),
    inference(resolution,[],[f109,f74])).

fof(f74,plain,(
    ! [X0] :
      ( r2_hidden(u1_struct_0(X0),u1_pre_topc(X0))
      | ~ sP2(X0) ) ),
    inference(cnf_transformation,[],[f46])).

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
    inference(flattening,[],[f45])).

fof(f45,plain,(
    ! [X0] :
      ( ( sP2(X0)
        | ~ sP1(X0)
        | ~ sP0(X0)
        | ~ r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)) )
      & ( ( sP1(X0)
          & sP0(X0)
          & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)) )
        | ~ sP2(X0) ) ) ),
    inference(nnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0] :
      ( sP2(X0)
    <=> ( sP1(X0)
        & sP0(X0)
        & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).

fof(f109,plain,(
    sP2(sK4) ),
    inference(subsumption_resolution,[],[f107,f64])).

fof(f64,plain,(
    v2_pre_topc(sK4) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,
    ( u1_struct_0(sK4) != k4_yellow_0(k2_yellow_1(u1_pre_topc(sK4)))
    & l1_pre_topc(sK4)
    & v2_pre_topc(sK4) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f21,f42])).

fof(f42,plain,
    ( ? [X0] :
        ( u1_struct_0(X0) != k4_yellow_0(k2_yellow_1(u1_pre_topc(X0)))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
   => ( u1_struct_0(sK4) != k4_yellow_0(k2_yellow_1(u1_pre_topc(sK4)))
      & l1_pre_topc(sK4)
      & v2_pre_topc(sK4) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,(
    ? [X0] :
      ( u1_struct_0(X0) != k4_yellow_0(k2_yellow_1(u1_pre_topc(X0)))
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ? [X0] :
      ( u1_struct_0(X0) != k4_yellow_0(k2_yellow_1(u1_pre_topc(X0)))
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,plain,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0) )
       => u1_struct_0(X0) = k4_yellow_0(k2_yellow_1(u1_pre_topc(X0))) ) ),
    inference(pure_predicate_removal,[],[f17])).

fof(f17,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => u1_struct_0(X0) = k4_yellow_0(k2_yellow_1(u1_pre_topc(X0))) ) ),
    inference(negated_conjecture,[],[f16])).

fof(f16,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => u1_struct_0(X0) = k4_yellow_0(k2_yellow_1(u1_pre_topc(X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t24_yellow_1)).

fof(f107,plain,
    ( sP2(sK4)
    | ~ v2_pre_topc(sK4) ),
    inference(resolution,[],[f105,f72])).

fof(f72,plain,(
    ! [X0] :
      ( sP2(X0)
      | ~ v2_pre_topc(X0)
      | ~ sP3(X0) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0] :
      ( ( ( v2_pre_topc(X0)
          | ~ sP2(X0) )
        & ( sP2(X0)
          | ~ v2_pre_topc(X0) ) )
      | ~ sP3(X0) ) ),
    inference(nnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0] :
      ( ( v2_pre_topc(X0)
      <=> sP2(X0) )
      | ~ sP3(X0) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP3])])).

fof(f105,plain,(
    sP3(sK4) ),
    inference(resolution,[],[f65,f88])).

fof(f88,plain,(
    ! [X0] :
      ( sP3(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0] :
      ( sP3(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(definition_folding,[],[f26,f40,f39,f38,f37])).

fof(f37,plain,(
    ! [X0] :
      ( sP0(X0)
    <=> ! [X3] :
          ( r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0))
          | ~ r1_tarski(X3,u1_pre_topc(X0))
          | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f38,plain,(
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

fof(f26,plain,(
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
    inference(flattening,[],[f25])).

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
    inference(ennf_transformation,[],[f18])).

fof(f18,plain,(
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
    inference(rectify,[],[f13])).

fof(f13,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_pre_topc)).

fof(f65,plain,(
    l1_pre_topc(sK4) ),
    inference(cnf_transformation,[],[f43])).

fof(f728,plain,(
    ~ r1_tarski(u1_struct_0(sK4),k3_tarski(u1_pre_topc(sK4))) ),
    inference(subsumption_resolution,[],[f725,f154])).

fof(f154,plain,(
    u1_struct_0(sK4) != k3_tarski(u1_pre_topc(sK4)) ),
    inference(subsumption_resolution,[],[f120,f110])).

fof(f120,plain,
    ( u1_struct_0(sK4) != k3_tarski(u1_pre_topc(sK4))
    | ~ r2_hidden(u1_struct_0(sK4),u1_pre_topc(sK4)) ),
    inference(inner_rewriting,[],[f119])).

fof(f119,plain,
    ( u1_struct_0(sK4) != k3_tarski(u1_pre_topc(sK4))
    | ~ r2_hidden(k3_tarski(u1_pre_topc(sK4)),u1_pre_topc(sK4)) ),
    inference(subsumption_resolution,[],[f118,f89])).

fof(f89,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f59])).

fof(f59,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | r2_hidden(sK8(X0),X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8])],[f57,f58])).

fof(f58,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK8(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f57,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(rectify,[],[f56])).

fof(f56,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

fof(f118,plain,
    ( u1_struct_0(sK4) != k3_tarski(u1_pre_topc(sK4))
    | ~ r2_hidden(k3_tarski(u1_pre_topc(sK4)),u1_pre_topc(sK4))
    | v1_xboole_0(u1_pre_topc(sK4)) ),
    inference(superposition,[],[f66,f70])).

fof(f70,plain,(
    ! [X0] :
      ( k3_tarski(X0) = k4_yellow_0(k2_yellow_1(X0))
      | ~ r2_hidden(k3_tarski(X0),X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( k3_tarski(X0) = k4_yellow_0(k2_yellow_1(X0))
      | ~ r2_hidden(k3_tarski(X0),X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( k3_tarski(X0) = k4_yellow_0(k2_yellow_1(X0))
      | ~ r2_hidden(k3_tarski(X0),X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ( r2_hidden(k3_tarski(X0),X0)
       => k3_tarski(X0) = k4_yellow_0(k2_yellow_1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t14_yellow_1)).

fof(f66,plain,(
    u1_struct_0(sK4) != k4_yellow_0(k2_yellow_1(u1_pre_topc(sK4))) ),
    inference(cnf_transformation,[],[f43])).

fof(f725,plain,
    ( u1_struct_0(sK4) = k3_tarski(u1_pre_topc(sK4))
    | ~ r1_tarski(u1_struct_0(sK4),k3_tarski(u1_pre_topc(sK4))) ),
    inference(resolution,[],[f719,f97])).

fof(f97,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f63])).

fof(f719,plain,(
    r1_tarski(k3_tarski(u1_pre_topc(sK4)),u1_struct_0(sK4)) ),
    inference(forward_demodulation,[],[f717,f68])).

fof(f68,plain,(
    ! [X0] : k3_tarski(k1_zfmisc_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : k3_tarski(k1_zfmisc_1(X0)) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t99_zfmisc_1)).

fof(f717,plain,(
    r1_tarski(k3_tarski(u1_pre_topc(sK4)),k3_tarski(k1_zfmisc_1(u1_struct_0(sK4)))) ),
    inference(resolution,[],[f707,f92])).

fof(f92,plain,(
    ! [X0,X1] :
      ( r1_tarski(k3_tarski(X0),k3_tarski(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( r1_tarski(k3_tarski(X0),k3_tarski(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => r1_tarski(k3_tarski(X0),k3_tarski(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t95_zfmisc_1)).

fof(f707,plain,(
    r1_tarski(u1_pre_topc(sK4),k1_zfmisc_1(u1_struct_0(sK4))) ),
    inference(resolution,[],[f678,f103])).

fof(f678,plain,(
    ! [X1] :
      ( ~ r1_tarski(k1_zfmisc_1(u1_struct_0(sK4)),X1)
      | r1_tarski(u1_pre_topc(sK4),X1) ) ),
    inference(forward_demodulation,[],[f671,f68])).

fof(f671,plain,(
    ! [X1] :
      ( r1_tarski(u1_pre_topc(sK4),X1)
      | ~ r1_tarski(k3_tarski(k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK4)))),X1) ) ),
    inference(resolution,[],[f664,f100])).

fof(f664,plain,(
    r2_hidden(u1_pre_topc(sK4),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK4)))) ),
    inference(subsumption_resolution,[],[f662,f106])).

fof(f106,plain,(
    m1_subset_1(u1_pre_topc(sK4),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK4)))) ),
    inference(resolution,[],[f65,f71])).

fof(f71,plain,(
    ! [X0] :
      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_u1_pre_topc)).

fof(f662,plain,
    ( r2_hidden(u1_pre_topc(sK4),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK4))))
    | ~ m1_subset_1(u1_pre_topc(sK4),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK4)))) ),
    inference(resolution,[],[f305,f252])).

fof(f252,plain,(
    ! [X10] :
      ( ~ r1_tarski(X10,sK8(X10))
      | ~ m1_subset_1(u1_pre_topc(sK4),k1_zfmisc_1(X10)) ) ),
    inference(resolution,[],[f152,f98])).

fof(f98,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ~ ( r1_tarski(X1,X0)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).

fof(f152,plain,(
    ! [X2] :
      ( r2_hidden(sK8(X2),X2)
      | ~ m1_subset_1(u1_pre_topc(sK4),k1_zfmisc_1(X2)) ) ),
    inference(resolution,[],[f124,f90])).

fof(f90,plain,(
    ! [X0] :
      ( v1_xboole_0(X0)
      | r2_hidden(sK8(X0),X0) ) ),
    inference(cnf_transformation,[],[f59])).

fof(f124,plain,(
    ! [X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(u1_pre_topc(sK4),k1_zfmisc_1(X2)) ) ),
    inference(resolution,[],[f110,f101])).

fof(f101,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).

fof(f305,plain,(
    ! [X0] :
      ( r1_tarski(k1_zfmisc_1(u1_struct_0(sK4)),X0)
      | r2_hidden(u1_pre_topc(sK4),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK4)))) ) ),
    inference(forward_demodulation,[],[f303,f68])).

fof(f303,plain,(
    ! [X0] :
      ( r2_hidden(u1_pre_topc(sK4),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK4))))
      | r1_tarski(k3_tarski(k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK4)))),X0) ) ),
    inference(resolution,[],[f203,f93])).

fof(f93,plain,(
    ! [X0,X1] :
      ( r1_tarski(k3_tarski(X0),X1)
      | r2_hidden(sK9(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f61])).

fof(f61,plain,(
    ! [X0,X1] :
      ( r1_tarski(k3_tarski(X0),X1)
      | ( ~ r1_tarski(sK9(X0,X1),X1)
        & r2_hidden(sK9(X0,X1),X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK9])],[f30,f60])).

fof(f60,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r1_tarski(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r1_tarski(sK9(X0,X1),X1)
        & r2_hidden(sK9(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_zfmisc_1)).

fof(f203,plain,(
    ! [X2] :
      ( ~ r2_hidden(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK4))))
      | r2_hidden(u1_pre_topc(sK4),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK4)))) ) ),
    inference(resolution,[],[f138,f89])).

fof(f138,plain,
    ( v1_xboole_0(k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK4))))
    | r2_hidden(u1_pre_topc(sK4),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK4)))) ),
    inference(resolution,[],[f106,f91])).

fof(f91,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 15:41:23 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.48  % (4674)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 0.20/0.48  % (4682)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.20/0.49  % (4688)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 0.20/0.50  % (4672)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.20/0.50  % (4691)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 0.20/0.50  % (4683)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 0.20/0.50  % (4674)Refutation not found, incomplete strategy% (4674)------------------------------
% 0.20/0.50  % (4674)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.50  % (4674)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.50  
% 0.20/0.50  % (4674)Memory used [KB]: 10618
% 0.20/0.50  % (4674)Time elapsed: 0.101 s
% 0.20/0.50  % (4674)------------------------------
% 0.20/0.50  % (4674)------------------------------
% 0.20/0.50  % (4677)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
% 0.20/0.50  % (4673)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.20/0.50  % (4669)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 0.20/0.51  % (4684)lrs+4_5:4_av=off:bd=off:er=filter:lma=on:lwlo=on:nwc=1:stl=30:sp=occurrence:updr=off_230 on theBenchmark
% 0.20/0.51  % (4670)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.20/0.51  % (4680)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 0.20/0.51  % (4690)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 0.20/0.51  % (4687)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 0.20/0.52  % (4668)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 0.20/0.52  % (4689)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 0.20/0.52  % (4686)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 0.20/0.52  % (4668)Refutation not found, incomplete strategy% (4668)------------------------------
% 0.20/0.52  % (4668)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.52  % (4668)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.52  
% 0.20/0.52  % (4668)Memory used [KB]: 10618
% 0.20/0.52  % (4668)Time elapsed: 0.116 s
% 0.20/0.52  % (4668)------------------------------
% 0.20/0.52  % (4668)------------------------------
% 0.20/0.52  % (4676)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 0.20/0.52  % (4681)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 0.20/0.52  % (4685)lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_145 on theBenchmark
% 0.20/0.52  % (4681)Refutation not found, incomplete strategy% (4681)------------------------------
% 0.20/0.52  % (4681)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.52  % (4681)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.52  
% 0.20/0.52  % (4681)Memory used [KB]: 6140
% 0.20/0.52  % (4681)Time elapsed: 0.117 s
% 0.20/0.52  % (4681)------------------------------
% 0.20/0.52  % (4681)------------------------------
% 0.20/0.52  % (4679)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 0.20/0.53  % (4671)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.20/0.53  % (4669)Refutation not found, incomplete strategy% (4669)------------------------------
% 0.20/0.53  % (4669)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.53  % (4669)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.53  
% 0.20/0.53  % (4669)Memory used [KB]: 10618
% 0.20/0.53  % (4669)Time elapsed: 0.092 s
% 0.20/0.53  % (4669)------------------------------
% 0.20/0.53  % (4669)------------------------------
% 0.20/0.53  % (4692)dis+2_128_add=large:afp=100000:afq=1.4:amm=sco:anc=none:lma=on:nm=2:newcnf=on:nwc=1:nicw=on:sas=z3:sos=theory:sac=on:updr=off_288 on theBenchmark
% 0.20/0.53  % (4693)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_364 on theBenchmark
% 0.20/0.54  % (4678)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 0.20/0.55  % (4675)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 0.20/0.55  % (4676)Refutation found. Thanks to Tanya!
% 0.20/0.55  % SZS status Theorem for theBenchmark
% 0.20/0.55  % SZS output start Proof for theBenchmark
% 0.20/0.55  fof(f741,plain,(
% 0.20/0.55    $false),
% 0.20/0.55    inference(subsumption_resolution,[],[f739,f103])).
% 0.20/0.55  fof(f103,plain,(
% 0.20/0.55    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 0.20/0.55    inference(equality_resolution,[],[f95])).
% 0.20/0.55  fof(f95,plain,(
% 0.20/0.55    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 0.20/0.55    inference(cnf_transformation,[],[f63])).
% 0.20/0.55  fof(f63,plain,(
% 0.20/0.55    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.20/0.55    inference(flattening,[],[f62])).
% 0.20/0.55  fof(f62,plain,(
% 0.20/0.55    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.20/0.55    inference(nnf_transformation,[],[f2])).
% 0.20/0.55  fof(f2,axiom,(
% 0.20/0.55    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.20/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.20/0.55  fof(f739,plain,(
% 0.20/0.55    ~r1_tarski(k3_tarski(u1_pre_topc(sK4)),k3_tarski(u1_pre_topc(sK4)))),
% 0.20/0.55    inference(resolution,[],[f728,f125])).
% 0.20/0.55  fof(f125,plain,(
% 0.20/0.55    ( ! [X3] : (r1_tarski(u1_struct_0(sK4),X3) | ~r1_tarski(k3_tarski(u1_pre_topc(sK4)),X3)) )),
% 0.20/0.55    inference(resolution,[],[f110,f100])).
% 0.20/0.55  fof(f100,plain,(
% 0.20/0.55    ( ! [X2,X0,X1] : (r1_tarski(X2,X1) | ~r2_hidden(X2,X0) | ~r1_tarski(k3_tarski(X0),X1)) )),
% 0.20/0.55    inference(cnf_transformation,[],[f35])).
% 0.20/0.55  fof(f35,plain,(
% 0.20/0.55    ! [X0,X1,X2] : (r1_tarski(X2,X1) | ~r2_hidden(X2,X0) | ~r1_tarski(k3_tarski(X0),X1))),
% 0.20/0.55    inference(flattening,[],[f34])).
% 0.20/0.55  fof(f34,plain,(
% 0.20/0.55    ! [X0,X1,X2] : (r1_tarski(X2,X1) | (~r2_hidden(X2,X0) | ~r1_tarski(k3_tarski(X0),X1)))),
% 0.20/0.55    inference(ennf_transformation,[],[f10])).
% 0.20/0.55  fof(f10,axiom,(
% 0.20/0.55    ! [X0,X1,X2] : ((r2_hidden(X2,X0) & r1_tarski(k3_tarski(X0),X1)) => r1_tarski(X2,X1))),
% 0.20/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t56_setfam_1)).
% 0.20/0.55  fof(f110,plain,(
% 0.20/0.55    r2_hidden(u1_struct_0(sK4),u1_pre_topc(sK4))),
% 0.20/0.55    inference(resolution,[],[f109,f74])).
% 0.20/0.55  fof(f74,plain,(
% 0.20/0.55    ( ! [X0] : (r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)) | ~sP2(X0)) )),
% 0.20/0.55    inference(cnf_transformation,[],[f46])).
% 0.20/0.55  fof(f46,plain,(
% 0.20/0.55    ! [X0] : ((sP2(X0) | ~sP1(X0) | ~sP0(X0) | ~r2_hidden(u1_struct_0(X0),u1_pre_topc(X0))) & ((sP1(X0) & sP0(X0) & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0))) | ~sP2(X0)))),
% 0.20/0.55    inference(flattening,[],[f45])).
% 0.20/0.55  fof(f45,plain,(
% 0.20/0.55    ! [X0] : ((sP2(X0) | (~sP1(X0) | ~sP0(X0) | ~r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)))) & ((sP1(X0) & sP0(X0) & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0))) | ~sP2(X0)))),
% 0.20/0.55    inference(nnf_transformation,[],[f39])).
% 0.20/0.55  fof(f39,plain,(
% 0.20/0.55    ! [X0] : (sP2(X0) <=> (sP1(X0) & sP0(X0) & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0))))),
% 0.20/0.55    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).
% 0.20/0.55  fof(f109,plain,(
% 0.20/0.55    sP2(sK4)),
% 0.20/0.55    inference(subsumption_resolution,[],[f107,f64])).
% 0.20/0.55  fof(f64,plain,(
% 0.20/0.55    v2_pre_topc(sK4)),
% 0.20/0.55    inference(cnf_transformation,[],[f43])).
% 0.20/0.55  fof(f43,plain,(
% 0.20/0.55    u1_struct_0(sK4) != k4_yellow_0(k2_yellow_1(u1_pre_topc(sK4))) & l1_pre_topc(sK4) & v2_pre_topc(sK4)),
% 0.20/0.55    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f21,f42])).
% 0.20/0.55  fof(f42,plain,(
% 0.20/0.55    ? [X0] : (u1_struct_0(X0) != k4_yellow_0(k2_yellow_1(u1_pre_topc(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0)) => (u1_struct_0(sK4) != k4_yellow_0(k2_yellow_1(u1_pre_topc(sK4))) & l1_pre_topc(sK4) & v2_pre_topc(sK4))),
% 0.20/0.55    introduced(choice_axiom,[])).
% 0.20/0.55  fof(f21,plain,(
% 0.20/0.55    ? [X0] : (u1_struct_0(X0) != k4_yellow_0(k2_yellow_1(u1_pre_topc(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 0.20/0.55    inference(flattening,[],[f20])).
% 0.20/0.55  fof(f20,plain,(
% 0.20/0.55    ? [X0] : (u1_struct_0(X0) != k4_yellow_0(k2_yellow_1(u1_pre_topc(X0))) & (l1_pre_topc(X0) & v2_pre_topc(X0)))),
% 0.20/0.55    inference(ennf_transformation,[],[f19])).
% 0.20/0.55  fof(f19,plain,(
% 0.20/0.55    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => u1_struct_0(X0) = k4_yellow_0(k2_yellow_1(u1_pre_topc(X0))))),
% 0.20/0.55    inference(pure_predicate_removal,[],[f17])).
% 0.20/0.55  fof(f17,negated_conjecture,(
% 0.20/0.55    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => u1_struct_0(X0) = k4_yellow_0(k2_yellow_1(u1_pre_topc(X0))))),
% 0.20/0.55    inference(negated_conjecture,[],[f16])).
% 0.20/0.55  fof(f16,conjecture,(
% 0.20/0.55    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => u1_struct_0(X0) = k4_yellow_0(k2_yellow_1(u1_pre_topc(X0))))),
% 0.20/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t24_yellow_1)).
% 0.20/0.55  fof(f107,plain,(
% 0.20/0.55    sP2(sK4) | ~v2_pre_topc(sK4)),
% 0.20/0.55    inference(resolution,[],[f105,f72])).
% 0.20/0.55  fof(f72,plain,(
% 0.20/0.55    ( ! [X0] : (sP2(X0) | ~v2_pre_topc(X0) | ~sP3(X0)) )),
% 0.20/0.55    inference(cnf_transformation,[],[f44])).
% 0.20/0.55  fof(f44,plain,(
% 0.20/0.55    ! [X0] : (((v2_pre_topc(X0) | ~sP2(X0)) & (sP2(X0) | ~v2_pre_topc(X0))) | ~sP3(X0))),
% 0.20/0.55    inference(nnf_transformation,[],[f40])).
% 0.20/0.55  fof(f40,plain,(
% 0.20/0.55    ! [X0] : ((v2_pre_topc(X0) <=> sP2(X0)) | ~sP3(X0))),
% 0.20/0.55    introduced(predicate_definition_introduction,[new_symbols(naming,[sP3])])).
% 0.20/0.55  fof(f105,plain,(
% 0.20/0.55    sP3(sK4)),
% 0.20/0.55    inference(resolution,[],[f65,f88])).
% 0.20/0.55  fof(f88,plain,(
% 0.20/0.55    ( ! [X0] : (sP3(X0) | ~l1_pre_topc(X0)) )),
% 0.20/0.55    inference(cnf_transformation,[],[f41])).
% 0.20/0.55  fof(f41,plain,(
% 0.20/0.55    ! [X0] : (sP3(X0) | ~l1_pre_topc(X0))),
% 0.20/0.55    inference(definition_folding,[],[f26,f40,f39,f38,f37])).
% 0.20/0.55  fof(f37,plain,(
% 0.20/0.55    ! [X0] : (sP0(X0) <=> ! [X3] : (r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0)) | ~r1_tarski(X3,u1_pre_topc(X0)) | ~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))))),
% 0.20/0.55    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 0.20/0.55  fof(f38,plain,(
% 0.20/0.55    ! [X0] : (sP1(X0) <=> ! [X1] : (! [X2] : (r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),u1_pre_topc(X0)) | ~r2_hidden(X2,u1_pre_topc(X0)) | ~r2_hidden(X1,u1_pre_topc(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))))),
% 0.20/0.55    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 0.20/0.55  fof(f26,plain,(
% 0.20/0.55    ! [X0] : ((v2_pre_topc(X0) <=> (! [X1] : (! [X2] : (r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),u1_pre_topc(X0)) | ~r2_hidden(X2,u1_pre_topc(X0)) | ~r2_hidden(X1,u1_pre_topc(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & ! [X3] : (r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0)) | ~r1_tarski(X3,u1_pre_topc(X0)) | ~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)))) | ~l1_pre_topc(X0))),
% 0.20/0.55    inference(flattening,[],[f25])).
% 0.20/0.55  fof(f25,plain,(
% 0.20/0.55    ! [X0] : ((v2_pre_topc(X0) <=> (! [X1] : (! [X2] : ((r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),u1_pre_topc(X0)) | (~r2_hidden(X2,u1_pre_topc(X0)) | ~r2_hidden(X1,u1_pre_topc(X0)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & ! [X3] : ((r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0)) | ~r1_tarski(X3,u1_pre_topc(X0))) | ~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)))) | ~l1_pre_topc(X0))),
% 0.20/0.55    inference(ennf_transformation,[],[f18])).
% 0.20/0.55  fof(f18,plain,(
% 0.20/0.55    ! [X0] : (l1_pre_topc(X0) => (v2_pre_topc(X0) <=> (! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((r2_hidden(X2,u1_pre_topc(X0)) & r2_hidden(X1,u1_pre_topc(X0))) => r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),u1_pre_topc(X0))))) & ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => (r1_tarski(X3,u1_pre_topc(X0)) => r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0)))) & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)))))),
% 0.20/0.55    inference(rectify,[],[f13])).
% 0.20/0.55  fof(f13,axiom,(
% 0.20/0.55    ! [X0] : (l1_pre_topc(X0) => (v2_pre_topc(X0) <=> (! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((r2_hidden(X2,u1_pre_topc(X0)) & r2_hidden(X1,u1_pre_topc(X0))) => r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),u1_pre_topc(X0))))) & ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => (r1_tarski(X1,u1_pre_topc(X0)) => r2_hidden(k5_setfam_1(u1_struct_0(X0),X1),u1_pre_topc(X0)))) & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)))))),
% 0.20/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_pre_topc)).
% 0.20/0.55  fof(f65,plain,(
% 0.20/0.55    l1_pre_topc(sK4)),
% 0.20/0.55    inference(cnf_transformation,[],[f43])).
% 0.20/0.55  fof(f728,plain,(
% 0.20/0.55    ~r1_tarski(u1_struct_0(sK4),k3_tarski(u1_pre_topc(sK4)))),
% 0.20/0.55    inference(subsumption_resolution,[],[f725,f154])).
% 0.20/0.55  fof(f154,plain,(
% 0.20/0.55    u1_struct_0(sK4) != k3_tarski(u1_pre_topc(sK4))),
% 0.20/0.55    inference(subsumption_resolution,[],[f120,f110])).
% 0.20/0.55  fof(f120,plain,(
% 0.20/0.55    u1_struct_0(sK4) != k3_tarski(u1_pre_topc(sK4)) | ~r2_hidden(u1_struct_0(sK4),u1_pre_topc(sK4))),
% 0.20/0.55    inference(inner_rewriting,[],[f119])).
% 0.20/0.55  fof(f119,plain,(
% 0.20/0.55    u1_struct_0(sK4) != k3_tarski(u1_pre_topc(sK4)) | ~r2_hidden(k3_tarski(u1_pre_topc(sK4)),u1_pre_topc(sK4))),
% 0.20/0.55    inference(subsumption_resolution,[],[f118,f89])).
% 0.20/0.55  fof(f89,plain,(
% 0.20/0.55    ( ! [X2,X0] : (~r2_hidden(X2,X0) | ~v1_xboole_0(X0)) )),
% 0.20/0.55    inference(cnf_transformation,[],[f59])).
% 0.20/0.55  fof(f59,plain,(
% 0.20/0.55    ! [X0] : ((v1_xboole_0(X0) | r2_hidden(sK8(X0),X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 0.20/0.55    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8])],[f57,f58])).
% 0.20/0.55  fof(f58,plain,(
% 0.20/0.55    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK8(X0),X0))),
% 0.20/0.55    introduced(choice_axiom,[])).
% 0.20/0.55  fof(f57,plain,(
% 0.20/0.55    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 0.20/0.55    inference(rectify,[],[f56])).
% 0.20/0.55  fof(f56,plain,(
% 0.20/0.55    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0)))),
% 0.20/0.55    inference(nnf_transformation,[],[f1])).
% 0.20/0.55  fof(f1,axiom,(
% 0.20/0.55    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 0.20/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).
% 0.20/0.55  fof(f118,plain,(
% 0.20/0.55    u1_struct_0(sK4) != k3_tarski(u1_pre_topc(sK4)) | ~r2_hidden(k3_tarski(u1_pre_topc(sK4)),u1_pre_topc(sK4)) | v1_xboole_0(u1_pre_topc(sK4))),
% 0.20/0.55    inference(superposition,[],[f66,f70])).
% 0.20/0.55  fof(f70,plain,(
% 0.20/0.55    ( ! [X0] : (k3_tarski(X0) = k4_yellow_0(k2_yellow_1(X0)) | ~r2_hidden(k3_tarski(X0),X0) | v1_xboole_0(X0)) )),
% 0.20/0.55    inference(cnf_transformation,[],[f23])).
% 0.20/0.55  fof(f23,plain,(
% 0.20/0.55    ! [X0] : (k3_tarski(X0) = k4_yellow_0(k2_yellow_1(X0)) | ~r2_hidden(k3_tarski(X0),X0) | v1_xboole_0(X0))),
% 0.20/0.55    inference(flattening,[],[f22])).
% 0.20/0.55  fof(f22,plain,(
% 0.20/0.55    ! [X0] : ((k3_tarski(X0) = k4_yellow_0(k2_yellow_1(X0)) | ~r2_hidden(k3_tarski(X0),X0)) | v1_xboole_0(X0))),
% 0.20/0.55    inference(ennf_transformation,[],[f15])).
% 0.20/0.55  fof(f15,axiom,(
% 0.20/0.55    ! [X0] : (~v1_xboole_0(X0) => (r2_hidden(k3_tarski(X0),X0) => k3_tarski(X0) = k4_yellow_0(k2_yellow_1(X0))))),
% 0.20/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t14_yellow_1)).
% 0.20/0.55  fof(f66,plain,(
% 0.20/0.55    u1_struct_0(sK4) != k4_yellow_0(k2_yellow_1(u1_pre_topc(sK4)))),
% 0.20/0.55    inference(cnf_transformation,[],[f43])).
% 0.20/0.55  fof(f725,plain,(
% 0.20/0.55    u1_struct_0(sK4) = k3_tarski(u1_pre_topc(sK4)) | ~r1_tarski(u1_struct_0(sK4),k3_tarski(u1_pre_topc(sK4)))),
% 0.20/0.55    inference(resolution,[],[f719,f97])).
% 0.20/0.55  fof(f97,plain,(
% 0.20/0.55    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 0.20/0.55    inference(cnf_transformation,[],[f63])).
% 0.20/0.55  fof(f719,plain,(
% 0.20/0.55    r1_tarski(k3_tarski(u1_pre_topc(sK4)),u1_struct_0(sK4))),
% 0.20/0.55    inference(forward_demodulation,[],[f717,f68])).
% 0.20/0.55  fof(f68,plain,(
% 0.20/0.55    ( ! [X0] : (k3_tarski(k1_zfmisc_1(X0)) = X0) )),
% 0.20/0.55    inference(cnf_transformation,[],[f6])).
% 0.20/0.55  fof(f6,axiom,(
% 0.20/0.55    ! [X0] : k3_tarski(k1_zfmisc_1(X0)) = X0),
% 0.20/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t99_zfmisc_1)).
% 0.20/0.55  fof(f717,plain,(
% 0.20/0.55    r1_tarski(k3_tarski(u1_pre_topc(sK4)),k3_tarski(k1_zfmisc_1(u1_struct_0(sK4))))),
% 0.20/0.55    inference(resolution,[],[f707,f92])).
% 0.20/0.55  fof(f92,plain,(
% 0.20/0.55    ( ! [X0,X1] : (r1_tarski(k3_tarski(X0),k3_tarski(X1)) | ~r1_tarski(X0,X1)) )),
% 0.20/0.55    inference(cnf_transformation,[],[f29])).
% 0.20/0.55  fof(f29,plain,(
% 0.20/0.55    ! [X0,X1] : (r1_tarski(k3_tarski(X0),k3_tarski(X1)) | ~r1_tarski(X0,X1))),
% 0.20/0.55    inference(ennf_transformation,[],[f5])).
% 0.20/0.55  fof(f5,axiom,(
% 0.20/0.55    ! [X0,X1] : (r1_tarski(X0,X1) => r1_tarski(k3_tarski(X0),k3_tarski(X1)))),
% 0.20/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t95_zfmisc_1)).
% 0.20/0.55  fof(f707,plain,(
% 0.20/0.55    r1_tarski(u1_pre_topc(sK4),k1_zfmisc_1(u1_struct_0(sK4)))),
% 0.20/0.55    inference(resolution,[],[f678,f103])).
% 0.20/0.55  fof(f678,plain,(
% 0.20/0.55    ( ! [X1] : (~r1_tarski(k1_zfmisc_1(u1_struct_0(sK4)),X1) | r1_tarski(u1_pre_topc(sK4),X1)) )),
% 0.20/0.55    inference(forward_demodulation,[],[f671,f68])).
% 0.20/0.55  fof(f671,plain,(
% 0.20/0.55    ( ! [X1] : (r1_tarski(u1_pre_topc(sK4),X1) | ~r1_tarski(k3_tarski(k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK4)))),X1)) )),
% 0.20/0.55    inference(resolution,[],[f664,f100])).
% 0.20/0.55  fof(f664,plain,(
% 0.20/0.55    r2_hidden(u1_pre_topc(sK4),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK4))))),
% 0.20/0.55    inference(subsumption_resolution,[],[f662,f106])).
% 0.20/0.55  fof(f106,plain,(
% 0.20/0.55    m1_subset_1(u1_pre_topc(sK4),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK4))))),
% 0.20/0.55    inference(resolution,[],[f65,f71])).
% 0.20/0.55  fof(f71,plain,(
% 0.20/0.55    ( ! [X0] : (m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0)) )),
% 0.20/0.55    inference(cnf_transformation,[],[f24])).
% 0.20/0.55  fof(f24,plain,(
% 0.20/0.55    ! [X0] : (m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.20/0.55    inference(ennf_transformation,[],[f14])).
% 0.20/0.55  fof(f14,axiom,(
% 0.20/0.55    ! [X0] : (l1_pre_topc(X0) => m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))))),
% 0.20/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_u1_pre_topc)).
% 0.20/0.55  fof(f662,plain,(
% 0.20/0.55    r2_hidden(u1_pre_topc(sK4),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK4)))) | ~m1_subset_1(u1_pre_topc(sK4),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK4))))),
% 0.20/0.55    inference(resolution,[],[f305,f252])).
% 0.20/0.55  fof(f252,plain,(
% 0.20/0.55    ( ! [X10] : (~r1_tarski(X10,sK8(X10)) | ~m1_subset_1(u1_pre_topc(sK4),k1_zfmisc_1(X10))) )),
% 0.20/0.55    inference(resolution,[],[f152,f98])).
% 0.20/0.55  fof(f98,plain,(
% 0.20/0.55    ( ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1)) )),
% 0.20/0.55    inference(cnf_transformation,[],[f31])).
% 0.20/0.55  fof(f31,plain,(
% 0.20/0.55    ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1))),
% 0.20/0.55    inference(ennf_transformation,[],[f12])).
% 0.20/0.55  fof(f12,axiom,(
% 0.20/0.55    ! [X0,X1] : ~(r1_tarski(X1,X0) & r2_hidden(X0,X1))),
% 0.20/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).
% 0.20/0.55  fof(f152,plain,(
% 0.20/0.55    ( ! [X2] : (r2_hidden(sK8(X2),X2) | ~m1_subset_1(u1_pre_topc(sK4),k1_zfmisc_1(X2))) )),
% 0.20/0.55    inference(resolution,[],[f124,f90])).
% 0.20/0.55  fof(f90,plain,(
% 0.20/0.55    ( ! [X0] : (v1_xboole_0(X0) | r2_hidden(sK8(X0),X0)) )),
% 0.20/0.55    inference(cnf_transformation,[],[f59])).
% 0.20/0.55  fof(f124,plain,(
% 0.20/0.55    ( ! [X2] : (~v1_xboole_0(X2) | ~m1_subset_1(u1_pre_topc(sK4),k1_zfmisc_1(X2))) )),
% 0.20/0.55    inference(resolution,[],[f110,f101])).
% 0.20/0.55  fof(f101,plain,(
% 0.20/0.55    ( ! [X2,X0,X1] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) )),
% 0.20/0.55    inference(cnf_transformation,[],[f36])).
% 0.20/0.55  fof(f36,plain,(
% 0.20/0.55    ! [X0,X1,X2] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 0.20/0.55    inference(ennf_transformation,[],[f11])).
% 0.20/0.55  fof(f11,axiom,(
% 0.20/0.55    ! [X0,X1,X2] : ~(v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1))),
% 0.20/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).
% 0.20/0.55  fof(f305,plain,(
% 0.20/0.55    ( ! [X0] : (r1_tarski(k1_zfmisc_1(u1_struct_0(sK4)),X0) | r2_hidden(u1_pre_topc(sK4),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK4))))) )),
% 0.20/0.55    inference(forward_demodulation,[],[f303,f68])).
% 0.20/0.55  fof(f303,plain,(
% 0.20/0.55    ( ! [X0] : (r2_hidden(u1_pre_topc(sK4),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK4)))) | r1_tarski(k3_tarski(k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK4)))),X0)) )),
% 0.20/0.55    inference(resolution,[],[f203,f93])).
% 0.20/0.55  fof(f93,plain,(
% 0.20/0.55    ( ! [X0,X1] : (r1_tarski(k3_tarski(X0),X1) | r2_hidden(sK9(X0,X1),X0)) )),
% 0.20/0.55    inference(cnf_transformation,[],[f61])).
% 0.20/0.55  fof(f61,plain,(
% 0.20/0.55    ! [X0,X1] : (r1_tarski(k3_tarski(X0),X1) | (~r1_tarski(sK9(X0,X1),X1) & r2_hidden(sK9(X0,X1),X0)))),
% 0.20/0.55    inference(skolemisation,[status(esa),new_symbols(skolem,[sK9])],[f30,f60])).
% 0.20/0.55  fof(f60,plain,(
% 0.20/0.55    ! [X1,X0] : (? [X2] : (~r1_tarski(X2,X1) & r2_hidden(X2,X0)) => (~r1_tarski(sK9(X0,X1),X1) & r2_hidden(sK9(X0,X1),X0)))),
% 0.20/0.55    introduced(choice_axiom,[])).
% 0.20/0.55  fof(f30,plain,(
% 0.20/0.55    ! [X0,X1] : (r1_tarski(k3_tarski(X0),X1) | ? [X2] : (~r1_tarski(X2,X1) & r2_hidden(X2,X0)))),
% 0.20/0.55    inference(ennf_transformation,[],[f4])).
% 0.20/0.55  fof(f4,axiom,(
% 0.20/0.55    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) => r1_tarski(X2,X1)) => r1_tarski(k3_tarski(X0),X1))),
% 0.20/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_zfmisc_1)).
% 0.20/0.55  fof(f203,plain,(
% 0.20/0.55    ( ! [X2] : (~r2_hidden(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK4)))) | r2_hidden(u1_pre_topc(sK4),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK4))))) )),
% 0.20/0.55    inference(resolution,[],[f138,f89])).
% 0.20/0.55  fof(f138,plain,(
% 0.20/0.55    v1_xboole_0(k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK4)))) | r2_hidden(u1_pre_topc(sK4),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK4))))),
% 0.20/0.55    inference(resolution,[],[f106,f91])).
% 0.20/0.55  fof(f91,plain,(
% 0.20/0.55    ( ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1)) )),
% 0.20/0.55    inference(cnf_transformation,[],[f28])).
% 0.20/0.55  fof(f28,plain,(
% 0.20/0.55    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 0.20/0.55    inference(flattening,[],[f27])).
% 0.20/0.55  fof(f27,plain,(
% 0.20/0.55    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 0.20/0.55    inference(ennf_transformation,[],[f8])).
% 0.20/0.55  fof(f8,axiom,(
% 0.20/0.55    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 0.20/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).
% 0.20/0.55  % SZS output end Proof for theBenchmark
% 0.20/0.55  % (4676)------------------------------
% 0.20/0.55  % (4676)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.55  % (4676)Termination reason: Refutation
% 0.20/0.55  
% 0.20/0.55  % (4676)Memory used [KB]: 1918
% 0.20/0.55  % (4676)Time elapsed: 0.091 s
% 0.20/0.55  % (4676)------------------------------
% 0.20/0.55  % (4676)------------------------------
% 0.20/0.55  % (4667)Success in time 0.194 s
%------------------------------------------------------------------------------
