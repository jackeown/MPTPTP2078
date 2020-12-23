%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:13:10 EST 2020

% Result     : Theorem 0.23s
% Output     : Refutation 0.23s
% Verified   : 
% Statistics : Number of formulae       :  135 (1948 expanded)
%              Number of leaves         :   15 ( 591 expanded)
%              Depth                    :   32
%              Number of atoms          :  365 (8909 expanded)
%              Number of equality atoms :   23 ( 120 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f644,plain,(
    $false ),
    inference(subsumption_resolution,[],[f643,f64])).

fof(f64,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f60])).

fof(f60,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f40])).

fof(f40,plain,(
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

fof(f643,plain,(
    ~ r1_tarski(k1_tops_1(sK2,sK3),k1_tops_1(sK2,sK3)) ),
    inference(forward_demodulation,[],[f642,f572])).

fof(f572,plain,(
    k1_tops_1(sK2,sK3) = k1_tops_1(sK2,k2_pre_topc(sK2,sK3)) ),
    inference(subsumption_resolution,[],[f568,f474])).

fof(f474,plain,(
    r1_tarski(k1_tops_1(sK2,sK3),k1_tops_1(sK2,k2_pre_topc(sK2,sK3))) ),
    inference(subsumption_resolution,[],[f467,f94])).

fof(f94,plain,(
    m1_subset_1(k2_pre_topc(sK2,sK3),k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(subsumption_resolution,[],[f83,f42])).

fof(f42,plain,(
    l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,
    ( ( ~ v4_tops_1(k2_pre_topc(sK2,sK3),sK2)
      | ~ v4_tops_1(k1_tops_1(sK2,sK3),sK2) )
    & v4_tops_1(sK3,sK2)
    & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))
    & l1_pre_topc(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f14,f34,f33])).

fof(f33,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ( ~ v4_tops_1(k2_pre_topc(X0,X1),X0)
              | ~ v4_tops_1(k1_tops_1(X0,X1),X0) )
            & v4_tops_1(X1,X0)
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_pre_topc(X0) )
   => ( ? [X1] :
          ( ( ~ v4_tops_1(k2_pre_topc(sK2,X1),sK2)
            | ~ v4_tops_1(k1_tops_1(sK2,X1),sK2) )
          & v4_tops_1(X1,sK2)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2))) )
      & l1_pre_topc(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,
    ( ? [X1] :
        ( ( ~ v4_tops_1(k2_pre_topc(sK2,X1),sK2)
          | ~ v4_tops_1(k1_tops_1(sK2,X1),sK2) )
        & v4_tops_1(X1,sK2)
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2))) )
   => ( ( ~ v4_tops_1(k2_pre_topc(sK2,sK3),sK2)
        | ~ v4_tops_1(k1_tops_1(sK2,sK3),sK2) )
      & v4_tops_1(sK3,sK2)
      & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) ) ),
    introduced(choice_axiom,[])).

fof(f14,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ~ v4_tops_1(k2_pre_topc(X0,X1),X0)
            | ~ v4_tops_1(k1_tops_1(X0,X1),X0) )
          & v4_tops_1(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ~ v4_tops_1(k2_pre_topc(X0,X1),X0)
            | ~ v4_tops_1(k1_tops_1(X0,X1),X0) )
          & v4_tops_1(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,negated_conjecture,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( v4_tops_1(X1,X0)
             => ( v4_tops_1(k2_pre_topc(X0,X1),X0)
                & v4_tops_1(k1_tops_1(X0,X1),X0) ) ) ) ) ),
    inference(negated_conjecture,[],[f11])).

fof(f11,conjecture,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v4_tops_1(X1,X0)
           => ( v4_tops_1(k2_pre_topc(X0,X1),X0)
              & v4_tops_1(k1_tops_1(X0,X1),X0) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t111_tops_1)).

fof(f83,plain,
    ( m1_subset_1(k2_pre_topc(sK2,sK3),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ l1_pre_topc(sK2) ),
    inference(resolution,[],[f43,f57])).

fof(f57,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f24])).

% (9132)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
fof(f24,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_pre_topc)).

fof(f43,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(cnf_transformation,[],[f35])).

fof(f467,plain,
    ( r1_tarski(k1_tops_1(sK2,sK3),k1_tops_1(sK2,k2_pre_topc(sK2,sK3)))
    | ~ m1_subset_1(k2_pre_topc(sK2,sK3),k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(resolution,[],[f91,f86])).

fof(f86,plain,(
    r1_tarski(sK3,k2_pre_topc(sK2,sK3)) ),
    inference(subsumption_resolution,[],[f75,f42])).

fof(f75,plain,
    ( r1_tarski(sK3,k2_pre_topc(sK2,sK3))
    | ~ l1_pre_topc(sK2) ),
    inference(resolution,[],[f43,f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,k2_pre_topc(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(X1,k2_pre_topc(X0,X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => r1_tarski(X1,k2_pre_topc(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_pre_topc)).

fof(f91,plain,(
    ! [X2] :
      ( ~ r1_tarski(sK3,X2)
      | r1_tarski(k1_tops_1(sK2,sK3),k1_tops_1(sK2,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK2))) ) ),
    inference(subsumption_resolution,[],[f80,f42])).

fof(f80,plain,(
    ! [X2] :
      ( r1_tarski(k1_tops_1(sK2,sK3),k1_tops_1(sK2,X2))
      | ~ r1_tarski(sK3,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK2)))
      | ~ l1_pre_topc(sK2) ) ),
    inference(resolution,[],[f43,f55])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2))
      | ~ r1_tarski(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2))
              | ~ r1_tarski(X1,X2)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2))
              | ~ r1_tarski(X1,X2)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( r1_tarski(X1,X2)
               => r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_tops_1)).

fof(f568,plain,
    ( k1_tops_1(sK2,sK3) = k1_tops_1(sK2,k2_pre_topc(sK2,sK3))
    | ~ r1_tarski(k1_tops_1(sK2,sK3),k1_tops_1(sK2,k2_pre_topc(sK2,sK3))) ),
    inference(resolution,[],[f567,f62])).

fof(f62,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f567,plain,(
    r1_tarski(k1_tops_1(sK2,k2_pre_topc(sK2,sK3)),k1_tops_1(sK2,sK3)) ),
    inference(subsumption_resolution,[],[f566,f42])).

fof(f566,plain,
    ( r1_tarski(k1_tops_1(sK2,k2_pre_topc(sK2,sK3)),k1_tops_1(sK2,sK3))
    | ~ l1_pre_topc(sK2) ),
    inference(subsumption_resolution,[],[f565,f94])).

fof(f565,plain,
    ( r1_tarski(k1_tops_1(sK2,k2_pre_topc(sK2,sK3)),k1_tops_1(sK2,sK3))
    | ~ m1_subset_1(k2_pre_topc(sK2,sK3),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ l1_pre_topc(sK2) ),
    inference(superposition,[],[f528,f58])).

fof(f58,plain,(
    ! [X0,X1] :
      ( k1_tops_1(X0,X1) = k1_tops_1(X0,k1_tops_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( k1_tops_1(X0,X1) = k1_tops_1(X0,k1_tops_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( k1_tops_1(X0,X1) = k1_tops_1(X0,k1_tops_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => k1_tops_1(X0,X1) = k1_tops_1(X0,k1_tops_1(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',projectivity_k1_tops_1)).

fof(f528,plain,(
    r1_tarski(k1_tops_1(sK2,k1_tops_1(sK2,k2_pre_topc(sK2,sK3))),k1_tops_1(sK2,sK3)) ),
    inference(subsumption_resolution,[],[f526,f154])).

fof(f154,plain,(
    m1_subset_1(k1_tops_1(sK2,k2_pre_topc(sK2,sK3)),k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(subsumption_resolution,[],[f143,f42])).

fof(f143,plain,
    ( m1_subset_1(k1_tops_1(sK2,k2_pre_topc(sK2,sK3)),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ l1_pre_topc(sK2) ),
    inference(resolution,[],[f94,f56])).

fof(f56,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_tops_1)).

fof(f526,plain,
    ( r1_tarski(k1_tops_1(sK2,k1_tops_1(sK2,k2_pre_topc(sK2,sK3))),k1_tops_1(sK2,sK3))
    | ~ m1_subset_1(k1_tops_1(sK2,k2_pre_topc(sK2,sK3)),k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(resolution,[],[f92,f100])).

fof(f100,plain,(
    r1_tarski(k1_tops_1(sK2,k2_pre_topc(sK2,sK3)),sK3) ),
    inference(resolution,[],[f99,f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_tops_1(X1,k2_pre_topc(X1,X0)),X0)
      | ~ sP0(X0,X1) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ( sP0(X0,X1)
        | ~ r1_tarski(X0,k2_pre_topc(X1,k1_tops_1(X1,X0)))
        | ~ r1_tarski(k1_tops_1(X1,k2_pre_topc(X1,X0)),X0) )
      & ( ( r1_tarski(X0,k2_pre_topc(X1,k1_tops_1(X1,X0)))
          & r1_tarski(k1_tops_1(X1,k2_pre_topc(X1,X0)),X0) )
        | ~ sP0(X0,X1) ) ) ),
    inference(rectify,[],[f38])).

fof(f38,plain,(
    ! [X1,X0] :
      ( ( sP0(X1,X0)
        | ~ r1_tarski(X1,k2_pre_topc(X0,k1_tops_1(X0,X1)))
        | ~ r1_tarski(k1_tops_1(X0,k2_pre_topc(X0,X1)),X1) )
      & ( ( r1_tarski(X1,k2_pre_topc(X0,k1_tops_1(X0,X1)))
          & r1_tarski(k1_tops_1(X0,k2_pre_topc(X0,X1)),X1) )
        | ~ sP0(X1,X0) ) ) ),
    inference(flattening,[],[f37])).

fof(f37,plain,(
    ! [X1,X0] :
      ( ( sP0(X1,X0)
        | ~ r1_tarski(X1,k2_pre_topc(X0,k1_tops_1(X0,X1)))
        | ~ r1_tarski(k1_tops_1(X0,k2_pre_topc(X0,X1)),X1) )
      & ( ( r1_tarski(X1,k2_pre_topc(X0,k1_tops_1(X0,X1)))
          & r1_tarski(k1_tops_1(X0,k2_pre_topc(X0,X1)),X1) )
        | ~ sP0(X1,X0) ) ) ),
    inference(nnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X1,X0] :
      ( sP0(X1,X0)
    <=> ( r1_tarski(X1,k2_pre_topc(X0,k1_tops_1(X0,X1)))
        & r1_tarski(k1_tops_1(X0,k2_pre_topc(X0,X1)),X1) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f99,plain,(
    sP0(sK3,sK2) ),
    inference(subsumption_resolution,[],[f97,f44])).

fof(f44,plain,(
    v4_tops_1(sK3,sK2) ),
    inference(cnf_transformation,[],[f35])).

fof(f97,plain,
    ( sP0(sK3,sK2)
    | ~ v4_tops_1(sK3,sK2) ),
    inference(resolution,[],[f88,f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( sP0(X1,X0)
      | ~ v4_tops_1(X1,X0)
      | ~ sP1(X0,X1) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( ( v4_tops_1(X1,X0)
          | ~ sP0(X1,X0) )
        & ( sP0(X1,X0)
          | ~ v4_tops_1(X1,X0) ) )
      | ~ sP1(X0,X1) ) ),
    inference(nnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( v4_tops_1(X1,X0)
      <=> sP0(X1,X0) )
      | ~ sP1(X0,X1) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f88,plain,(
    sP1(sK2,sK3) ),
    inference(subsumption_resolution,[],[f77,f42])).

fof(f77,plain,
    ( sP1(sK2,sK3)
    | ~ l1_pre_topc(sK2) ),
    inference(resolution,[],[f43,f53])).

fof(f53,plain,(
    ! [X0,X1] :
      ( sP1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( sP1(X0,X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(definition_folding,[],[f17,f31,f30])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v4_tops_1(X1,X0)
          <=> ( r1_tarski(X1,k2_pre_topc(X0,k1_tops_1(X0,X1)))
              & r1_tarski(k1_tops_1(X0,k2_pre_topc(X0,X1)),X1) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v4_tops_1(X1,X0)
          <=> ( r1_tarski(X1,k2_pre_topc(X0,k1_tops_1(X0,X1)))
              & r1_tarski(k1_tops_1(X0,k2_pre_topc(X0,X1)),X1) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d6_tops_1)).

fof(f92,plain,(
    ! [X3] :
      ( ~ r1_tarski(X3,sK3)
      | r1_tarski(k1_tops_1(sK2,X3),k1_tops_1(sK2,sK3))
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK2))) ) ),
    inference(subsumption_resolution,[],[f81,f42])).

fof(f81,plain,(
    ! [X3] :
      ( r1_tarski(k1_tops_1(sK2,X3),k1_tops_1(sK2,sK3))
      | ~ r1_tarski(X3,sK3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK2)))
      | ~ l1_pre_topc(sK2) ) ),
    inference(resolution,[],[f43,f55])).

fof(f642,plain,(
    ~ r1_tarski(k1_tops_1(sK2,k2_pre_topc(sK2,sK3)),k1_tops_1(sK2,sK3)) ),
    inference(forward_demodulation,[],[f641,f486])).

fof(f486,plain,(
    k2_pre_topc(sK2,sK3) = k2_pre_topc(sK2,k1_tops_1(sK2,sK3)) ),
    inference(subsumption_resolution,[],[f482,f452])).

fof(f452,plain,(
    r1_tarski(k2_pre_topc(sK2,k1_tops_1(sK2,sK3)),k2_pre_topc(sK2,sK3)) ),
    inference(subsumption_resolution,[],[f449,f93])).

fof(f93,plain,(
    m1_subset_1(k1_tops_1(sK2,sK3),k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(subsumption_resolution,[],[f82,f42])).

fof(f82,plain,
    ( m1_subset_1(k1_tops_1(sK2,sK3),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ l1_pre_topc(sK2) ),
    inference(resolution,[],[f43,f56])).

fof(f449,plain,
    ( r1_tarski(k2_pre_topc(sK2,k1_tops_1(sK2,sK3)),k2_pre_topc(sK2,sK3))
    | ~ m1_subset_1(k1_tops_1(sK2,sK3),k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(resolution,[],[f90,f87])).

fof(f87,plain,(
    r1_tarski(k1_tops_1(sK2,sK3),sK3) ),
    inference(subsumption_resolution,[],[f76,f42])).

fof(f76,plain,
    ( r1_tarski(k1_tops_1(sK2,sK3),sK3)
    | ~ l1_pre_topc(sK2) ),
    inference(resolution,[],[f43,f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_tops_1(X0,X1),X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k1_tops_1(X0,X1),X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => r1_tarski(k1_tops_1(X0,X1),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_tops_1)).

fof(f90,plain,(
    ! [X1] :
      ( ~ r1_tarski(X1,sK3)
      | r1_tarski(k2_pre_topc(sK2,X1),k2_pre_topc(sK2,sK3))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2))) ) ),
    inference(subsumption_resolution,[],[f79,f42])).

fof(f79,plain,(
    ! [X1] :
      ( r1_tarski(k2_pre_topc(sK2,X1),k2_pre_topc(sK2,sK3))
      | ~ r1_tarski(X1,sK3)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
      | ~ l1_pre_topc(sK2) ) ),
    inference(resolution,[],[f43,f54])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k2_pre_topc(X0,X1),k2_pre_topc(X0,X2))
      | ~ r1_tarski(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(k2_pre_topc(X0,X1),k2_pre_topc(X0,X2))
              | ~ r1_tarski(X1,X2)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(k2_pre_topc(X0,X1),k2_pre_topc(X0,X2))
              | ~ r1_tarski(X1,X2)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( r1_tarski(X1,X2)
               => r1_tarski(k2_pre_topc(X0,X1),k2_pre_topc(X0,X2)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_pre_topc)).

fof(f482,plain,
    ( k2_pre_topc(sK2,sK3) = k2_pre_topc(sK2,k1_tops_1(sK2,sK3))
    | ~ r1_tarski(k2_pre_topc(sK2,k1_tops_1(sK2,sK3)),k2_pre_topc(sK2,sK3)) ),
    inference(resolution,[],[f466,f62])).

fof(f466,plain,(
    r1_tarski(k2_pre_topc(sK2,sK3),k2_pre_topc(sK2,k1_tops_1(sK2,sK3))) ),
    inference(subsumption_resolution,[],[f465,f42])).

fof(f465,plain,
    ( r1_tarski(k2_pre_topc(sK2,sK3),k2_pre_topc(sK2,k1_tops_1(sK2,sK3)))
    | ~ l1_pre_topc(sK2) ),
    inference(subsumption_resolution,[],[f464,f93])).

fof(f464,plain,
    ( r1_tarski(k2_pre_topc(sK2,sK3),k2_pre_topc(sK2,k1_tops_1(sK2,sK3)))
    | ~ m1_subset_1(k1_tops_1(sK2,sK3),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ l1_pre_topc(sK2) ),
    inference(superposition,[],[f442,f59])).

fof(f59,plain,(
    ! [X0,X1] :
      ( k2_pre_topc(X0,X1) = k2_pre_topc(X0,k2_pre_topc(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( k2_pre_topc(X0,X1) = k2_pre_topc(X0,k2_pre_topc(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( k2_pre_topc(X0,X1) = k2_pre_topc(X0,k2_pre_topc(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => k2_pre_topc(X0,X1) = k2_pre_topc(X0,k2_pre_topc(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',projectivity_k2_pre_topc)).

fof(f442,plain,(
    r1_tarski(k2_pre_topc(sK2,sK3),k2_pre_topc(sK2,k2_pre_topc(sK2,k1_tops_1(sK2,sK3)))) ),
    inference(subsumption_resolution,[],[f436,f131])).

fof(f131,plain,(
    m1_subset_1(k2_pre_topc(sK2,k1_tops_1(sK2,sK3)),k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(subsumption_resolution,[],[f120,f42])).

fof(f120,plain,
    ( m1_subset_1(k2_pre_topc(sK2,k1_tops_1(sK2,sK3)),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ l1_pre_topc(sK2) ),
    inference(resolution,[],[f93,f57])).

fof(f436,plain,
    ( r1_tarski(k2_pre_topc(sK2,sK3),k2_pre_topc(sK2,k2_pre_topc(sK2,k1_tops_1(sK2,sK3))))
    | ~ m1_subset_1(k2_pre_topc(sK2,k1_tops_1(sK2,sK3)),k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(resolution,[],[f89,f101])).

fof(f101,plain,(
    r1_tarski(sK3,k2_pre_topc(sK2,k1_tops_1(sK2,sK3))) ),
    inference(resolution,[],[f99,f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k2_pre_topc(X1,k1_tops_1(X1,X0)))
      | ~ sP0(X0,X1) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f89,plain,(
    ! [X0] :
      ( ~ r1_tarski(sK3,X0)
      | r1_tarski(k2_pre_topc(sK2,sK3),k2_pre_topc(sK2,X0))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) ) ),
    inference(subsumption_resolution,[],[f78,f42])).

fof(f78,plain,(
    ! [X0] :
      ( r1_tarski(k2_pre_topc(sK2,sK3),k2_pre_topc(sK2,X0))
      | ~ r1_tarski(sK3,X0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
      | ~ l1_pre_topc(sK2) ) ),
    inference(resolution,[],[f43,f54])).

fof(f641,plain,(
    ~ r1_tarski(k1_tops_1(sK2,k2_pre_topc(sK2,k1_tops_1(sK2,sK3))),k1_tops_1(sK2,sK3)) ),
    inference(subsumption_resolution,[],[f640,f489])).

fof(f489,plain,(
    r1_tarski(k1_tops_1(sK2,sK3),k2_pre_topc(sK2,sK3)) ),
    inference(backward_demodulation,[],[f123,f486])).

fof(f123,plain,(
    r1_tarski(k1_tops_1(sK2,sK3),k2_pre_topc(sK2,k1_tops_1(sK2,sK3))) ),
    inference(subsumption_resolution,[],[f112,f42])).

fof(f112,plain,
    ( r1_tarski(k1_tops_1(sK2,sK3),k2_pre_topc(sK2,k1_tops_1(sK2,sK3)))
    | ~ l1_pre_topc(sK2) ),
    inference(resolution,[],[f93,f46])).

fof(f640,plain,
    ( ~ r1_tarski(k1_tops_1(sK2,sK3),k2_pre_topc(sK2,sK3))
    | ~ r1_tarski(k1_tops_1(sK2,k2_pre_topc(sK2,k1_tops_1(sK2,sK3))),k1_tops_1(sK2,sK3)) ),
    inference(forward_demodulation,[],[f639,f486])).

fof(f639,plain,
    ( ~ r1_tarski(k1_tops_1(sK2,sK3),k2_pre_topc(sK2,k1_tops_1(sK2,sK3)))
    | ~ r1_tarski(k1_tops_1(sK2,k2_pre_topc(sK2,k1_tops_1(sK2,sK3))),k1_tops_1(sK2,sK3)) ),
    inference(forward_demodulation,[],[f637,f95])).

fof(f95,plain,(
    k1_tops_1(sK2,sK3) = k1_tops_1(sK2,k1_tops_1(sK2,sK3)) ),
    inference(subsumption_resolution,[],[f84,f42])).

fof(f84,plain,
    ( k1_tops_1(sK2,sK3) = k1_tops_1(sK2,k1_tops_1(sK2,sK3))
    | ~ l1_pre_topc(sK2) ),
    inference(resolution,[],[f43,f58])).

fof(f637,plain,
    ( ~ r1_tarski(k1_tops_1(sK2,sK3),k2_pre_topc(sK2,k1_tops_1(sK2,k1_tops_1(sK2,sK3))))
    | ~ r1_tarski(k1_tops_1(sK2,k2_pre_topc(sK2,k1_tops_1(sK2,sK3))),k1_tops_1(sK2,sK3)) ),
    inference(resolution,[],[f632,f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( sP0(X0,X1)
      | ~ r1_tarski(X0,k2_pre_topc(X1,k1_tops_1(X1,X0)))
      | ~ r1_tarski(k1_tops_1(X1,k2_pre_topc(X1,X0)),X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f632,plain,(
    ~ sP0(k1_tops_1(sK2,sK3),sK2) ),
    inference(resolution,[],[f621,f533])).

fof(f533,plain,
    ( ~ v4_tops_1(k2_pre_topc(sK2,sK3),sK2)
    | ~ sP0(k1_tops_1(sK2,sK3),sK2) ),
    inference(subsumption_resolution,[],[f107,f125])).

fof(f125,plain,(
    sP1(sK2,k1_tops_1(sK2,sK3)) ),
    inference(subsumption_resolution,[],[f114,f42])).

fof(f114,plain,
    ( sP1(sK2,k1_tops_1(sK2,sK3))
    | ~ l1_pre_topc(sK2) ),
    inference(resolution,[],[f93,f53])).

fof(f107,plain,
    ( ~ v4_tops_1(k2_pre_topc(sK2,sK3),sK2)
    | ~ sP0(k1_tops_1(sK2,sK3),sK2)
    | ~ sP1(sK2,k1_tops_1(sK2,sK3)) ),
    inference(resolution,[],[f45,f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( v4_tops_1(X1,X0)
      | ~ sP0(X1,X0)
      | ~ sP1(X0,X1) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f45,plain,
    ( ~ v4_tops_1(k1_tops_1(sK2,sK3),sK2)
    | ~ v4_tops_1(k2_pre_topc(sK2,sK3),sK2) ),
    inference(cnf_transformation,[],[f35])).

fof(f621,plain,(
    v4_tops_1(k2_pre_topc(sK2,sK3),sK2) ),
    inference(resolution,[],[f607,f159])).

fof(f159,plain,
    ( ~ sP0(k2_pre_topc(sK2,sK3),sK2)
    | v4_tops_1(k2_pre_topc(sK2,sK3),sK2) ),
    inference(resolution,[],[f149,f49])).

fof(f149,plain,(
    sP1(sK2,k2_pre_topc(sK2,sK3)) ),
    inference(subsumption_resolution,[],[f138,f42])).

fof(f138,plain,
    ( sP1(sK2,k2_pre_topc(sK2,sK3))
    | ~ l1_pre_topc(sK2) ),
    inference(resolution,[],[f94,f53])).

fof(f607,plain,(
    sP0(k2_pre_topc(sK2,sK3),sK2) ),
    inference(subsumption_resolution,[],[f606,f489])).

fof(f606,plain,
    ( ~ r1_tarski(k1_tops_1(sK2,sK3),k2_pre_topc(sK2,sK3))
    | sP0(k2_pre_topc(sK2,sK3),sK2) ),
    inference(forward_demodulation,[],[f605,f572])).

fof(f605,plain,
    ( ~ r1_tarski(k1_tops_1(sK2,k2_pre_topc(sK2,sK3)),k2_pre_topc(sK2,sK3))
    | sP0(k2_pre_topc(sK2,sK3),sK2) ),
    inference(forward_demodulation,[],[f604,f96])).

fof(f96,plain,(
    k2_pre_topc(sK2,sK3) = k2_pre_topc(sK2,k2_pre_topc(sK2,sK3)) ),
    inference(subsumption_resolution,[],[f85,f42])).

fof(f85,plain,
    ( k2_pre_topc(sK2,sK3) = k2_pre_topc(sK2,k2_pre_topc(sK2,sK3))
    | ~ l1_pre_topc(sK2) ),
    inference(resolution,[],[f43,f59])).

fof(f604,plain,
    ( sP0(k2_pre_topc(sK2,sK3),sK2)
    | ~ r1_tarski(k1_tops_1(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,sK3))),k2_pre_topc(sK2,sK3)) ),
    inference(subsumption_resolution,[],[f603,f64])).

fof(f603,plain,
    ( ~ r1_tarski(k2_pre_topc(sK2,sK3),k2_pre_topc(sK2,sK3))
    | sP0(k2_pre_topc(sK2,sK3),sK2)
    | ~ r1_tarski(k1_tops_1(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,sK3))),k2_pre_topc(sK2,sK3)) ),
    inference(forward_demodulation,[],[f591,f486])).

fof(f591,plain,
    ( ~ r1_tarski(k2_pre_topc(sK2,sK3),k2_pre_topc(sK2,k1_tops_1(sK2,sK3)))
    | sP0(k2_pre_topc(sK2,sK3),sK2)
    | ~ r1_tarski(k1_tops_1(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,sK3))),k2_pre_topc(sK2,sK3)) ),
    inference(superposition,[],[f52,f572])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.14  % Command    : run_vampire %s %d
% 0.14/0.36  % Computer   : n007.cluster.edu
% 0.14/0.36  % Model      : x86_64 x86_64
% 0.14/0.36  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.36  % Memory     : 8042.1875MB
% 0.14/0.36  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.36  % CPULimit   : 60
% 0.14/0.36  % WCLimit    : 600
% 0.14/0.36  % DateTime   : Tue Dec  1 21:05:51 EST 2020
% 0.14/0.36  % CPUTime    : 
% 0.23/0.49  % (9151)dis+2_128_add=large:afp=100000:afq=1.4:amm=sco:anc=none:lma=on:nm=2:newcnf=on:nwc=1:nicw=on:sas=z3:sos=theory:sac=on:updr=off_288 on theBenchmark
% 0.23/0.49  % (9143)lrs+4_5:4_av=off:bd=off:er=filter:lma=on:lwlo=on:nwc=1:stl=30:sp=occurrence:updr=off_230 on theBenchmark
% 0.23/0.50  % (9131)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.23/0.52  % (9146)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 0.23/0.52  % (9129)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.23/0.52  % (9127)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 0.23/0.52  % (9130)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.23/0.52  % (9135)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 0.23/0.52  % (9138)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 0.23/0.52  % (9144)lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_145 on theBenchmark
% 0.23/0.53  % (9141)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.23/0.53  % (9142)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 0.23/0.53  % (9149)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 0.23/0.53  % (9136)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
% 0.23/0.53  % (9137)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 0.23/0.53  % (9134)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 0.23/0.54  % (9134)Refutation not found, incomplete strategy% (9134)------------------------------
% 0.23/0.54  % (9134)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.23/0.54  % (9134)Termination reason: Refutation not found, incomplete strategy
% 0.23/0.54  
% 0.23/0.54  % (9134)Memory used [KB]: 1663
% 0.23/0.54  % (9134)Time elapsed: 0.119 s
% 0.23/0.54  % (9134)------------------------------
% 0.23/0.54  % (9134)------------------------------
% 0.23/0.54  % (9128)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 0.23/0.54  % (9139)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 0.23/0.55  % (9133)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 0.23/0.55  % (9145)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 0.23/0.55  % (9135)Refutation found. Thanks to Tanya!
% 0.23/0.55  % SZS status Theorem for theBenchmark
% 0.23/0.55  % SZS output start Proof for theBenchmark
% 0.23/0.55  fof(f644,plain,(
% 0.23/0.55    $false),
% 0.23/0.55    inference(subsumption_resolution,[],[f643,f64])).
% 0.23/0.55  fof(f64,plain,(
% 0.23/0.55    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 0.23/0.55    inference(equality_resolution,[],[f60])).
% 0.23/0.55  fof(f60,plain,(
% 0.23/0.55    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 0.23/0.55    inference(cnf_transformation,[],[f41])).
% 0.23/0.55  fof(f41,plain,(
% 0.23/0.55    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.23/0.55    inference(flattening,[],[f40])).
% 0.23/0.55  fof(f40,plain,(
% 0.23/0.55    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.23/0.55    inference(nnf_transformation,[],[f1])).
% 0.23/0.55  fof(f1,axiom,(
% 0.23/0.55    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.23/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.23/0.55  fof(f643,plain,(
% 0.23/0.55    ~r1_tarski(k1_tops_1(sK2,sK3),k1_tops_1(sK2,sK3))),
% 0.23/0.55    inference(forward_demodulation,[],[f642,f572])).
% 0.23/0.55  fof(f572,plain,(
% 0.23/0.55    k1_tops_1(sK2,sK3) = k1_tops_1(sK2,k2_pre_topc(sK2,sK3))),
% 0.23/0.55    inference(subsumption_resolution,[],[f568,f474])).
% 0.23/0.55  fof(f474,plain,(
% 0.23/0.55    r1_tarski(k1_tops_1(sK2,sK3),k1_tops_1(sK2,k2_pre_topc(sK2,sK3)))),
% 0.23/0.55    inference(subsumption_resolution,[],[f467,f94])).
% 0.23/0.55  fof(f94,plain,(
% 0.23/0.55    m1_subset_1(k2_pre_topc(sK2,sK3),k1_zfmisc_1(u1_struct_0(sK2)))),
% 0.23/0.55    inference(subsumption_resolution,[],[f83,f42])).
% 0.23/0.55  fof(f42,plain,(
% 0.23/0.55    l1_pre_topc(sK2)),
% 0.23/0.55    inference(cnf_transformation,[],[f35])).
% 0.23/0.55  fof(f35,plain,(
% 0.23/0.55    ((~v4_tops_1(k2_pre_topc(sK2,sK3),sK2) | ~v4_tops_1(k1_tops_1(sK2,sK3),sK2)) & v4_tops_1(sK3,sK2) & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))) & l1_pre_topc(sK2)),
% 0.23/0.55    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f14,f34,f33])).
% 0.23/0.55  fof(f33,plain,(
% 0.23/0.55    ? [X0] : (? [X1] : ((~v4_tops_1(k2_pre_topc(X0,X1),X0) | ~v4_tops_1(k1_tops_1(X0,X1),X0)) & v4_tops_1(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0)) => (? [X1] : ((~v4_tops_1(k2_pre_topc(sK2,X1),sK2) | ~v4_tops_1(k1_tops_1(sK2,X1),sK2)) & v4_tops_1(X1,sK2) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))) & l1_pre_topc(sK2))),
% 0.23/0.55    introduced(choice_axiom,[])).
% 0.23/0.55  fof(f34,plain,(
% 0.23/0.55    ? [X1] : ((~v4_tops_1(k2_pre_topc(sK2,X1),sK2) | ~v4_tops_1(k1_tops_1(sK2,X1),sK2)) & v4_tops_1(X1,sK2) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))) => ((~v4_tops_1(k2_pre_topc(sK2,sK3),sK2) | ~v4_tops_1(k1_tops_1(sK2,sK3),sK2)) & v4_tops_1(sK3,sK2) & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))))),
% 0.23/0.55    introduced(choice_axiom,[])).
% 0.23/0.55  fof(f14,plain,(
% 0.23/0.55    ? [X0] : (? [X1] : ((~v4_tops_1(k2_pre_topc(X0,X1),X0) | ~v4_tops_1(k1_tops_1(X0,X1),X0)) & v4_tops_1(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 0.23/0.55    inference(flattening,[],[f13])).
% 0.23/0.55  fof(f13,plain,(
% 0.23/0.55    ? [X0] : (? [X1] : (((~v4_tops_1(k2_pre_topc(X0,X1),X0) | ~v4_tops_1(k1_tops_1(X0,X1),X0)) & v4_tops_1(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 0.23/0.55    inference(ennf_transformation,[],[f12])).
% 0.23/0.55  fof(f12,negated_conjecture,(
% 0.23/0.55    ~! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_tops_1(X1,X0) => (v4_tops_1(k2_pre_topc(X0,X1),X0) & v4_tops_1(k1_tops_1(X0,X1),X0)))))),
% 0.23/0.55    inference(negated_conjecture,[],[f11])).
% 0.23/0.55  fof(f11,conjecture,(
% 0.23/0.55    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_tops_1(X1,X0) => (v4_tops_1(k2_pre_topc(X0,X1),X0) & v4_tops_1(k1_tops_1(X0,X1),X0)))))),
% 0.23/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t111_tops_1)).
% 0.23/0.55  fof(f83,plain,(
% 0.23/0.55    m1_subset_1(k2_pre_topc(sK2,sK3),k1_zfmisc_1(u1_struct_0(sK2))) | ~l1_pre_topc(sK2)),
% 0.23/0.55    inference(resolution,[],[f43,f57])).
% 0.23/0.55  fof(f57,plain,(
% 0.23/0.55    ( ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.23/0.55    inference(cnf_transformation,[],[f25])).
% 0.23/0.55  fof(f25,plain,(
% 0.23/0.55    ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 0.23/0.55    inference(flattening,[],[f24])).
% 0.23/0.55  % (9132)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.23/0.55  fof(f24,plain,(
% 0.23/0.55    ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 0.23/0.55    inference(ennf_transformation,[],[f2])).
% 0.23/0.55  fof(f2,axiom,(
% 0.23/0.55    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 0.23/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_pre_topc)).
% 0.23/0.55  fof(f43,plain,(
% 0.23/0.55    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))),
% 0.23/0.55    inference(cnf_transformation,[],[f35])).
% 0.23/0.55  fof(f467,plain,(
% 0.23/0.55    r1_tarski(k1_tops_1(sK2,sK3),k1_tops_1(sK2,k2_pre_topc(sK2,sK3))) | ~m1_subset_1(k2_pre_topc(sK2,sK3),k1_zfmisc_1(u1_struct_0(sK2)))),
% 0.23/0.55    inference(resolution,[],[f91,f86])).
% 0.23/0.55  fof(f86,plain,(
% 0.23/0.55    r1_tarski(sK3,k2_pre_topc(sK2,sK3))),
% 0.23/0.55    inference(subsumption_resolution,[],[f75,f42])).
% 0.23/0.55  fof(f75,plain,(
% 0.23/0.55    r1_tarski(sK3,k2_pre_topc(sK2,sK3)) | ~l1_pre_topc(sK2)),
% 0.23/0.55    inference(resolution,[],[f43,f46])).
% 0.23/0.55  fof(f46,plain,(
% 0.23/0.55    ( ! [X0,X1] : (r1_tarski(X1,k2_pre_topc(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.23/0.55    inference(cnf_transformation,[],[f15])).
% 0.23/0.55  fof(f15,plain,(
% 0.23/0.55    ! [X0] : (! [X1] : (r1_tarski(X1,k2_pre_topc(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.23/0.55    inference(ennf_transformation,[],[f4])).
% 0.23/0.55  fof(f4,axiom,(
% 0.23/0.55    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => r1_tarski(X1,k2_pre_topc(X0,X1))))),
% 0.23/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_pre_topc)).
% 0.23/0.55  fof(f91,plain,(
% 0.23/0.55    ( ! [X2] : (~r1_tarski(sK3,X2) | r1_tarski(k1_tops_1(sK2,sK3),k1_tops_1(sK2,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK2)))) )),
% 0.23/0.55    inference(subsumption_resolution,[],[f80,f42])).
% 0.23/0.55  fof(f80,plain,(
% 0.23/0.55    ( ! [X2] : (r1_tarski(k1_tops_1(sK2,sK3),k1_tops_1(sK2,X2)) | ~r1_tarski(sK3,X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK2))) | ~l1_pre_topc(sK2)) )),
% 0.23/0.55    inference(resolution,[],[f43,f55])).
% 0.23/0.55  fof(f55,plain,(
% 0.23/0.55    ( ! [X2,X0,X1] : (r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2)) | ~r1_tarski(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.23/0.55    inference(cnf_transformation,[],[f21])).
% 0.23/0.55  fof(f21,plain,(
% 0.23/0.55    ! [X0] : (! [X1] : (! [X2] : (r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2)) | ~r1_tarski(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.23/0.55    inference(flattening,[],[f20])).
% 0.23/0.55  fof(f20,plain,(
% 0.23/0.55    ! [X0] : (! [X1] : (! [X2] : ((r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2)) | ~r1_tarski(X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.23/0.55    inference(ennf_transformation,[],[f10])).
% 0.23/0.55  fof(f10,axiom,(
% 0.23/0.55    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (r1_tarski(X1,X2) => r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2))))))),
% 0.23/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_tops_1)).
% 0.23/0.55  fof(f568,plain,(
% 0.23/0.55    k1_tops_1(sK2,sK3) = k1_tops_1(sK2,k2_pre_topc(sK2,sK3)) | ~r1_tarski(k1_tops_1(sK2,sK3),k1_tops_1(sK2,k2_pre_topc(sK2,sK3)))),
% 0.23/0.55    inference(resolution,[],[f567,f62])).
% 0.23/0.55  fof(f62,plain,(
% 0.23/0.55    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 0.23/0.55    inference(cnf_transformation,[],[f41])).
% 0.23/0.55  fof(f567,plain,(
% 0.23/0.55    r1_tarski(k1_tops_1(sK2,k2_pre_topc(sK2,sK3)),k1_tops_1(sK2,sK3))),
% 0.23/0.55    inference(subsumption_resolution,[],[f566,f42])).
% 0.23/0.55  fof(f566,plain,(
% 0.23/0.55    r1_tarski(k1_tops_1(sK2,k2_pre_topc(sK2,sK3)),k1_tops_1(sK2,sK3)) | ~l1_pre_topc(sK2)),
% 0.23/0.55    inference(subsumption_resolution,[],[f565,f94])).
% 0.23/0.55  fof(f565,plain,(
% 0.23/0.55    r1_tarski(k1_tops_1(sK2,k2_pre_topc(sK2,sK3)),k1_tops_1(sK2,sK3)) | ~m1_subset_1(k2_pre_topc(sK2,sK3),k1_zfmisc_1(u1_struct_0(sK2))) | ~l1_pre_topc(sK2)),
% 0.23/0.55    inference(superposition,[],[f528,f58])).
% 0.23/0.55  fof(f58,plain,(
% 0.23/0.55    ( ! [X0,X1] : (k1_tops_1(X0,X1) = k1_tops_1(X0,k1_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.23/0.55    inference(cnf_transformation,[],[f27])).
% 0.23/0.55  fof(f27,plain,(
% 0.23/0.55    ! [X0,X1] : (k1_tops_1(X0,X1) = k1_tops_1(X0,k1_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 0.23/0.55    inference(flattening,[],[f26])).
% 0.23/0.55  fof(f26,plain,(
% 0.23/0.55    ! [X0,X1] : (k1_tops_1(X0,X1) = k1_tops_1(X0,k1_tops_1(X0,X1)) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 0.23/0.55    inference(ennf_transformation,[],[f8])).
% 0.23/0.55  fof(f8,axiom,(
% 0.23/0.55    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => k1_tops_1(X0,X1) = k1_tops_1(X0,k1_tops_1(X0,X1)))),
% 0.23/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',projectivity_k1_tops_1)).
% 0.23/0.55  fof(f528,plain,(
% 0.23/0.55    r1_tarski(k1_tops_1(sK2,k1_tops_1(sK2,k2_pre_topc(sK2,sK3))),k1_tops_1(sK2,sK3))),
% 0.23/0.55    inference(subsumption_resolution,[],[f526,f154])).
% 0.23/0.55  fof(f154,plain,(
% 0.23/0.55    m1_subset_1(k1_tops_1(sK2,k2_pre_topc(sK2,sK3)),k1_zfmisc_1(u1_struct_0(sK2)))),
% 0.23/0.55    inference(subsumption_resolution,[],[f143,f42])).
% 0.23/0.55  fof(f143,plain,(
% 0.23/0.55    m1_subset_1(k1_tops_1(sK2,k2_pre_topc(sK2,sK3)),k1_zfmisc_1(u1_struct_0(sK2))) | ~l1_pre_topc(sK2)),
% 0.23/0.55    inference(resolution,[],[f94,f56])).
% 0.23/0.55  fof(f56,plain,(
% 0.23/0.55    ( ! [X0,X1] : (m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.23/0.55    inference(cnf_transformation,[],[f23])).
% 0.23/0.55  fof(f23,plain,(
% 0.23/0.55    ! [X0,X1] : (m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 0.23/0.55    inference(flattening,[],[f22])).
% 0.23/0.55  fof(f22,plain,(
% 0.23/0.55    ! [X0,X1] : (m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 0.23/0.55    inference(ennf_transformation,[],[f7])).
% 0.23/0.55  fof(f7,axiom,(
% 0.23/0.55    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 0.23/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_tops_1)).
% 0.23/0.55  fof(f526,plain,(
% 0.23/0.55    r1_tarski(k1_tops_1(sK2,k1_tops_1(sK2,k2_pre_topc(sK2,sK3))),k1_tops_1(sK2,sK3)) | ~m1_subset_1(k1_tops_1(sK2,k2_pre_topc(sK2,sK3)),k1_zfmisc_1(u1_struct_0(sK2)))),
% 0.23/0.55    inference(resolution,[],[f92,f100])).
% 0.23/0.55  fof(f100,plain,(
% 0.23/0.55    r1_tarski(k1_tops_1(sK2,k2_pre_topc(sK2,sK3)),sK3)),
% 0.23/0.55    inference(resolution,[],[f99,f50])).
% 0.23/0.55  fof(f50,plain,(
% 0.23/0.55    ( ! [X0,X1] : (r1_tarski(k1_tops_1(X1,k2_pre_topc(X1,X0)),X0) | ~sP0(X0,X1)) )),
% 0.23/0.55    inference(cnf_transformation,[],[f39])).
% 0.23/0.55  fof(f39,plain,(
% 0.23/0.55    ! [X0,X1] : ((sP0(X0,X1) | ~r1_tarski(X0,k2_pre_topc(X1,k1_tops_1(X1,X0))) | ~r1_tarski(k1_tops_1(X1,k2_pre_topc(X1,X0)),X0)) & ((r1_tarski(X0,k2_pre_topc(X1,k1_tops_1(X1,X0))) & r1_tarski(k1_tops_1(X1,k2_pre_topc(X1,X0)),X0)) | ~sP0(X0,X1)))),
% 0.23/0.55    inference(rectify,[],[f38])).
% 0.23/0.55  fof(f38,plain,(
% 0.23/0.55    ! [X1,X0] : ((sP0(X1,X0) | ~r1_tarski(X1,k2_pre_topc(X0,k1_tops_1(X0,X1))) | ~r1_tarski(k1_tops_1(X0,k2_pre_topc(X0,X1)),X1)) & ((r1_tarski(X1,k2_pre_topc(X0,k1_tops_1(X0,X1))) & r1_tarski(k1_tops_1(X0,k2_pre_topc(X0,X1)),X1)) | ~sP0(X1,X0)))),
% 0.23/0.55    inference(flattening,[],[f37])).
% 0.23/0.55  fof(f37,plain,(
% 0.23/0.55    ! [X1,X0] : ((sP0(X1,X0) | (~r1_tarski(X1,k2_pre_topc(X0,k1_tops_1(X0,X1))) | ~r1_tarski(k1_tops_1(X0,k2_pre_topc(X0,X1)),X1))) & ((r1_tarski(X1,k2_pre_topc(X0,k1_tops_1(X0,X1))) & r1_tarski(k1_tops_1(X0,k2_pre_topc(X0,X1)),X1)) | ~sP0(X1,X0)))),
% 0.23/0.55    inference(nnf_transformation,[],[f30])).
% 0.23/0.55  fof(f30,plain,(
% 0.23/0.55    ! [X1,X0] : (sP0(X1,X0) <=> (r1_tarski(X1,k2_pre_topc(X0,k1_tops_1(X0,X1))) & r1_tarski(k1_tops_1(X0,k2_pre_topc(X0,X1)),X1)))),
% 0.23/0.55    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 0.23/0.55  fof(f99,plain,(
% 0.23/0.55    sP0(sK3,sK2)),
% 0.23/0.55    inference(subsumption_resolution,[],[f97,f44])).
% 0.23/0.55  fof(f44,plain,(
% 0.23/0.55    v4_tops_1(sK3,sK2)),
% 0.23/0.55    inference(cnf_transformation,[],[f35])).
% 0.23/0.55  fof(f97,plain,(
% 0.23/0.55    sP0(sK3,sK2) | ~v4_tops_1(sK3,sK2)),
% 0.23/0.55    inference(resolution,[],[f88,f48])).
% 0.23/0.55  fof(f48,plain,(
% 0.23/0.55    ( ! [X0,X1] : (sP0(X1,X0) | ~v4_tops_1(X1,X0) | ~sP1(X0,X1)) )),
% 0.23/0.55    inference(cnf_transformation,[],[f36])).
% 0.23/0.55  fof(f36,plain,(
% 0.23/0.55    ! [X0,X1] : (((v4_tops_1(X1,X0) | ~sP0(X1,X0)) & (sP0(X1,X0) | ~v4_tops_1(X1,X0))) | ~sP1(X0,X1))),
% 0.23/0.55    inference(nnf_transformation,[],[f31])).
% 0.23/0.55  fof(f31,plain,(
% 0.23/0.55    ! [X0,X1] : ((v4_tops_1(X1,X0) <=> sP0(X1,X0)) | ~sP1(X0,X1))),
% 0.23/0.55    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 0.23/0.55  fof(f88,plain,(
% 0.23/0.55    sP1(sK2,sK3)),
% 0.23/0.55    inference(subsumption_resolution,[],[f77,f42])).
% 0.23/0.55  fof(f77,plain,(
% 0.23/0.55    sP1(sK2,sK3) | ~l1_pre_topc(sK2)),
% 0.23/0.55    inference(resolution,[],[f43,f53])).
% 0.23/0.55  fof(f53,plain,(
% 0.23/0.55    ( ! [X0,X1] : (sP1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.23/0.55    inference(cnf_transformation,[],[f32])).
% 0.23/0.55  fof(f32,plain,(
% 0.23/0.55    ! [X0] : (! [X1] : (sP1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.23/0.55    inference(definition_folding,[],[f17,f31,f30])).
% 0.23/0.55  fof(f17,plain,(
% 0.23/0.55    ! [X0] : (! [X1] : ((v4_tops_1(X1,X0) <=> (r1_tarski(X1,k2_pre_topc(X0,k1_tops_1(X0,X1))) & r1_tarski(k1_tops_1(X0,k2_pre_topc(X0,X1)),X1))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.23/0.55    inference(ennf_transformation,[],[f6])).
% 0.23/0.55  fof(f6,axiom,(
% 0.23/0.55    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_tops_1(X1,X0) <=> (r1_tarski(X1,k2_pre_topc(X0,k1_tops_1(X0,X1))) & r1_tarski(k1_tops_1(X0,k2_pre_topc(X0,X1)),X1)))))),
% 0.23/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d6_tops_1)).
% 0.23/0.55  fof(f92,plain,(
% 0.23/0.55    ( ! [X3] : (~r1_tarski(X3,sK3) | r1_tarski(k1_tops_1(sK2,X3),k1_tops_1(sK2,sK3)) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK2)))) )),
% 0.23/0.55    inference(subsumption_resolution,[],[f81,f42])).
% 0.23/0.55  fof(f81,plain,(
% 0.23/0.55    ( ! [X3] : (r1_tarski(k1_tops_1(sK2,X3),k1_tops_1(sK2,sK3)) | ~r1_tarski(X3,sK3) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK2))) | ~l1_pre_topc(sK2)) )),
% 0.23/0.55    inference(resolution,[],[f43,f55])).
% 0.23/0.55  fof(f642,plain,(
% 0.23/0.55    ~r1_tarski(k1_tops_1(sK2,k2_pre_topc(sK2,sK3)),k1_tops_1(sK2,sK3))),
% 0.23/0.55    inference(forward_demodulation,[],[f641,f486])).
% 0.23/0.55  fof(f486,plain,(
% 0.23/0.55    k2_pre_topc(sK2,sK3) = k2_pre_topc(sK2,k1_tops_1(sK2,sK3))),
% 0.23/0.55    inference(subsumption_resolution,[],[f482,f452])).
% 0.23/0.55  fof(f452,plain,(
% 0.23/0.55    r1_tarski(k2_pre_topc(sK2,k1_tops_1(sK2,sK3)),k2_pre_topc(sK2,sK3))),
% 0.23/0.55    inference(subsumption_resolution,[],[f449,f93])).
% 0.23/0.55  fof(f93,plain,(
% 0.23/0.55    m1_subset_1(k1_tops_1(sK2,sK3),k1_zfmisc_1(u1_struct_0(sK2)))),
% 0.23/0.55    inference(subsumption_resolution,[],[f82,f42])).
% 0.23/0.55  fof(f82,plain,(
% 0.23/0.55    m1_subset_1(k1_tops_1(sK2,sK3),k1_zfmisc_1(u1_struct_0(sK2))) | ~l1_pre_topc(sK2)),
% 0.23/0.55    inference(resolution,[],[f43,f56])).
% 0.23/0.55  fof(f449,plain,(
% 0.23/0.55    r1_tarski(k2_pre_topc(sK2,k1_tops_1(sK2,sK3)),k2_pre_topc(sK2,sK3)) | ~m1_subset_1(k1_tops_1(sK2,sK3),k1_zfmisc_1(u1_struct_0(sK2)))),
% 0.23/0.55    inference(resolution,[],[f90,f87])).
% 0.23/0.55  fof(f87,plain,(
% 0.23/0.55    r1_tarski(k1_tops_1(sK2,sK3),sK3)),
% 0.23/0.55    inference(subsumption_resolution,[],[f76,f42])).
% 0.23/0.55  fof(f76,plain,(
% 0.23/0.55    r1_tarski(k1_tops_1(sK2,sK3),sK3) | ~l1_pre_topc(sK2)),
% 0.23/0.55    inference(resolution,[],[f43,f47])).
% 0.23/0.55  fof(f47,plain,(
% 0.23/0.55    ( ! [X0,X1] : (r1_tarski(k1_tops_1(X0,X1),X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.23/0.55    inference(cnf_transformation,[],[f16])).
% 0.23/0.55  fof(f16,plain,(
% 0.23/0.55    ! [X0] : (! [X1] : (r1_tarski(k1_tops_1(X0,X1),X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.23/0.55    inference(ennf_transformation,[],[f9])).
% 0.23/0.55  fof(f9,axiom,(
% 0.23/0.55    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => r1_tarski(k1_tops_1(X0,X1),X1)))),
% 0.23/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_tops_1)).
% 0.23/0.55  fof(f90,plain,(
% 0.23/0.55    ( ! [X1] : (~r1_tarski(X1,sK3) | r1_tarski(k2_pre_topc(sK2,X1),k2_pre_topc(sK2,sK3)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))) )),
% 0.23/0.55    inference(subsumption_resolution,[],[f79,f42])).
% 0.23/0.55  fof(f79,plain,(
% 0.23/0.55    ( ! [X1] : (r1_tarski(k2_pre_topc(sK2,X1),k2_pre_topc(sK2,sK3)) | ~r1_tarski(X1,sK3) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2))) | ~l1_pre_topc(sK2)) )),
% 0.23/0.55    inference(resolution,[],[f43,f54])).
% 0.23/0.55  fof(f54,plain,(
% 0.23/0.55    ( ! [X2,X0,X1] : (r1_tarski(k2_pre_topc(X0,X1),k2_pre_topc(X0,X2)) | ~r1_tarski(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.23/0.55    inference(cnf_transformation,[],[f19])).
% 0.23/0.55  fof(f19,plain,(
% 0.23/0.55    ! [X0] : (! [X1] : (! [X2] : (r1_tarski(k2_pre_topc(X0,X1),k2_pre_topc(X0,X2)) | ~r1_tarski(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.23/0.55    inference(flattening,[],[f18])).
% 0.23/0.55  fof(f18,plain,(
% 0.23/0.55    ! [X0] : (! [X1] : (! [X2] : ((r1_tarski(k2_pre_topc(X0,X1),k2_pre_topc(X0,X2)) | ~r1_tarski(X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.23/0.55    inference(ennf_transformation,[],[f5])).
% 0.23/0.55  fof(f5,axiom,(
% 0.23/0.55    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (r1_tarski(X1,X2) => r1_tarski(k2_pre_topc(X0,X1),k2_pre_topc(X0,X2))))))),
% 0.23/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_pre_topc)).
% 0.23/0.55  fof(f482,plain,(
% 0.23/0.55    k2_pre_topc(sK2,sK3) = k2_pre_topc(sK2,k1_tops_1(sK2,sK3)) | ~r1_tarski(k2_pre_topc(sK2,k1_tops_1(sK2,sK3)),k2_pre_topc(sK2,sK3))),
% 0.23/0.55    inference(resolution,[],[f466,f62])).
% 0.23/0.55  fof(f466,plain,(
% 0.23/0.55    r1_tarski(k2_pre_topc(sK2,sK3),k2_pre_topc(sK2,k1_tops_1(sK2,sK3)))),
% 0.23/0.55    inference(subsumption_resolution,[],[f465,f42])).
% 0.23/0.55  fof(f465,plain,(
% 0.23/0.55    r1_tarski(k2_pre_topc(sK2,sK3),k2_pre_topc(sK2,k1_tops_1(sK2,sK3))) | ~l1_pre_topc(sK2)),
% 0.23/0.55    inference(subsumption_resolution,[],[f464,f93])).
% 0.23/0.55  fof(f464,plain,(
% 0.23/0.55    r1_tarski(k2_pre_topc(sK2,sK3),k2_pre_topc(sK2,k1_tops_1(sK2,sK3))) | ~m1_subset_1(k1_tops_1(sK2,sK3),k1_zfmisc_1(u1_struct_0(sK2))) | ~l1_pre_topc(sK2)),
% 0.23/0.55    inference(superposition,[],[f442,f59])).
% 0.23/0.55  fof(f59,plain,(
% 0.23/0.55    ( ! [X0,X1] : (k2_pre_topc(X0,X1) = k2_pre_topc(X0,k2_pre_topc(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.23/0.55    inference(cnf_transformation,[],[f29])).
% 0.23/0.55  fof(f29,plain,(
% 0.23/0.55    ! [X0,X1] : (k2_pre_topc(X0,X1) = k2_pre_topc(X0,k2_pre_topc(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 0.23/0.55    inference(flattening,[],[f28])).
% 0.23/0.55  fof(f28,plain,(
% 0.23/0.55    ! [X0,X1] : (k2_pre_topc(X0,X1) = k2_pre_topc(X0,k2_pre_topc(X0,X1)) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 0.23/0.55    inference(ennf_transformation,[],[f3])).
% 0.23/0.55  fof(f3,axiom,(
% 0.23/0.55    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => k2_pre_topc(X0,X1) = k2_pre_topc(X0,k2_pre_topc(X0,X1)))),
% 0.23/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',projectivity_k2_pre_topc)).
% 0.23/0.55  fof(f442,plain,(
% 0.23/0.55    r1_tarski(k2_pre_topc(sK2,sK3),k2_pre_topc(sK2,k2_pre_topc(sK2,k1_tops_1(sK2,sK3))))),
% 0.23/0.55    inference(subsumption_resolution,[],[f436,f131])).
% 0.23/0.55  fof(f131,plain,(
% 0.23/0.55    m1_subset_1(k2_pre_topc(sK2,k1_tops_1(sK2,sK3)),k1_zfmisc_1(u1_struct_0(sK2)))),
% 0.23/0.55    inference(subsumption_resolution,[],[f120,f42])).
% 0.23/0.55  fof(f120,plain,(
% 0.23/0.55    m1_subset_1(k2_pre_topc(sK2,k1_tops_1(sK2,sK3)),k1_zfmisc_1(u1_struct_0(sK2))) | ~l1_pre_topc(sK2)),
% 0.23/0.55    inference(resolution,[],[f93,f57])).
% 0.23/0.55  fof(f436,plain,(
% 0.23/0.55    r1_tarski(k2_pre_topc(sK2,sK3),k2_pre_topc(sK2,k2_pre_topc(sK2,k1_tops_1(sK2,sK3)))) | ~m1_subset_1(k2_pre_topc(sK2,k1_tops_1(sK2,sK3)),k1_zfmisc_1(u1_struct_0(sK2)))),
% 0.23/0.55    inference(resolution,[],[f89,f101])).
% 0.23/0.55  fof(f101,plain,(
% 0.23/0.55    r1_tarski(sK3,k2_pre_topc(sK2,k1_tops_1(sK2,sK3)))),
% 0.23/0.55    inference(resolution,[],[f99,f51])).
% 0.23/0.55  fof(f51,plain,(
% 0.23/0.55    ( ! [X0,X1] : (r1_tarski(X0,k2_pre_topc(X1,k1_tops_1(X1,X0))) | ~sP0(X0,X1)) )),
% 0.23/0.55    inference(cnf_transformation,[],[f39])).
% 0.23/0.55  fof(f89,plain,(
% 0.23/0.55    ( ! [X0] : (~r1_tarski(sK3,X0) | r1_tarski(k2_pre_topc(sK2,sK3),k2_pre_topc(sK2,X0)) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))) )),
% 0.23/0.55    inference(subsumption_resolution,[],[f78,f42])).
% 0.23/0.55  fof(f78,plain,(
% 0.23/0.55    ( ! [X0] : (r1_tarski(k2_pre_topc(sK2,sK3),k2_pre_topc(sK2,X0)) | ~r1_tarski(sK3,X0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) | ~l1_pre_topc(sK2)) )),
% 0.23/0.55    inference(resolution,[],[f43,f54])).
% 0.23/0.55  fof(f641,plain,(
% 0.23/0.55    ~r1_tarski(k1_tops_1(sK2,k2_pre_topc(sK2,k1_tops_1(sK2,sK3))),k1_tops_1(sK2,sK3))),
% 0.23/0.55    inference(subsumption_resolution,[],[f640,f489])).
% 0.23/0.55  fof(f489,plain,(
% 0.23/0.55    r1_tarski(k1_tops_1(sK2,sK3),k2_pre_topc(sK2,sK3))),
% 0.23/0.55    inference(backward_demodulation,[],[f123,f486])).
% 0.23/0.55  fof(f123,plain,(
% 0.23/0.55    r1_tarski(k1_tops_1(sK2,sK3),k2_pre_topc(sK2,k1_tops_1(sK2,sK3)))),
% 0.23/0.55    inference(subsumption_resolution,[],[f112,f42])).
% 0.23/0.55  fof(f112,plain,(
% 0.23/0.55    r1_tarski(k1_tops_1(sK2,sK3),k2_pre_topc(sK2,k1_tops_1(sK2,sK3))) | ~l1_pre_topc(sK2)),
% 0.23/0.55    inference(resolution,[],[f93,f46])).
% 0.23/0.55  fof(f640,plain,(
% 0.23/0.55    ~r1_tarski(k1_tops_1(sK2,sK3),k2_pre_topc(sK2,sK3)) | ~r1_tarski(k1_tops_1(sK2,k2_pre_topc(sK2,k1_tops_1(sK2,sK3))),k1_tops_1(sK2,sK3))),
% 0.23/0.55    inference(forward_demodulation,[],[f639,f486])).
% 0.23/0.55  fof(f639,plain,(
% 0.23/0.55    ~r1_tarski(k1_tops_1(sK2,sK3),k2_pre_topc(sK2,k1_tops_1(sK2,sK3))) | ~r1_tarski(k1_tops_1(sK2,k2_pre_topc(sK2,k1_tops_1(sK2,sK3))),k1_tops_1(sK2,sK3))),
% 0.23/0.55    inference(forward_demodulation,[],[f637,f95])).
% 0.23/0.55  fof(f95,plain,(
% 0.23/0.55    k1_tops_1(sK2,sK3) = k1_tops_1(sK2,k1_tops_1(sK2,sK3))),
% 0.23/0.55    inference(subsumption_resolution,[],[f84,f42])).
% 0.23/0.55  fof(f84,plain,(
% 0.23/0.55    k1_tops_1(sK2,sK3) = k1_tops_1(sK2,k1_tops_1(sK2,sK3)) | ~l1_pre_topc(sK2)),
% 0.23/0.55    inference(resolution,[],[f43,f58])).
% 0.23/0.55  fof(f637,plain,(
% 0.23/0.55    ~r1_tarski(k1_tops_1(sK2,sK3),k2_pre_topc(sK2,k1_tops_1(sK2,k1_tops_1(sK2,sK3)))) | ~r1_tarski(k1_tops_1(sK2,k2_pre_topc(sK2,k1_tops_1(sK2,sK3))),k1_tops_1(sK2,sK3))),
% 0.23/0.55    inference(resolution,[],[f632,f52])).
% 0.23/0.55  fof(f52,plain,(
% 0.23/0.55    ( ! [X0,X1] : (sP0(X0,X1) | ~r1_tarski(X0,k2_pre_topc(X1,k1_tops_1(X1,X0))) | ~r1_tarski(k1_tops_1(X1,k2_pre_topc(X1,X0)),X0)) )),
% 0.23/0.55    inference(cnf_transformation,[],[f39])).
% 0.23/0.55  fof(f632,plain,(
% 0.23/0.55    ~sP0(k1_tops_1(sK2,sK3),sK2)),
% 0.23/0.55    inference(resolution,[],[f621,f533])).
% 0.23/0.55  fof(f533,plain,(
% 0.23/0.55    ~v4_tops_1(k2_pre_topc(sK2,sK3),sK2) | ~sP0(k1_tops_1(sK2,sK3),sK2)),
% 0.23/0.55    inference(subsumption_resolution,[],[f107,f125])).
% 0.23/0.55  fof(f125,plain,(
% 0.23/0.55    sP1(sK2,k1_tops_1(sK2,sK3))),
% 0.23/0.55    inference(subsumption_resolution,[],[f114,f42])).
% 0.23/0.55  fof(f114,plain,(
% 0.23/0.55    sP1(sK2,k1_tops_1(sK2,sK3)) | ~l1_pre_topc(sK2)),
% 0.23/0.55    inference(resolution,[],[f93,f53])).
% 0.23/0.55  fof(f107,plain,(
% 0.23/0.55    ~v4_tops_1(k2_pre_topc(sK2,sK3),sK2) | ~sP0(k1_tops_1(sK2,sK3),sK2) | ~sP1(sK2,k1_tops_1(sK2,sK3))),
% 0.23/0.55    inference(resolution,[],[f45,f49])).
% 0.23/0.55  fof(f49,plain,(
% 0.23/0.55    ( ! [X0,X1] : (v4_tops_1(X1,X0) | ~sP0(X1,X0) | ~sP1(X0,X1)) )),
% 0.23/0.55    inference(cnf_transformation,[],[f36])).
% 0.23/0.55  fof(f45,plain,(
% 0.23/0.55    ~v4_tops_1(k1_tops_1(sK2,sK3),sK2) | ~v4_tops_1(k2_pre_topc(sK2,sK3),sK2)),
% 0.23/0.55    inference(cnf_transformation,[],[f35])).
% 0.23/0.55  fof(f621,plain,(
% 0.23/0.55    v4_tops_1(k2_pre_topc(sK2,sK3),sK2)),
% 0.23/0.55    inference(resolution,[],[f607,f159])).
% 0.23/0.55  fof(f159,plain,(
% 0.23/0.55    ~sP0(k2_pre_topc(sK2,sK3),sK2) | v4_tops_1(k2_pre_topc(sK2,sK3),sK2)),
% 0.23/0.55    inference(resolution,[],[f149,f49])).
% 0.23/0.55  fof(f149,plain,(
% 0.23/0.55    sP1(sK2,k2_pre_topc(sK2,sK3))),
% 0.23/0.55    inference(subsumption_resolution,[],[f138,f42])).
% 0.23/0.55  fof(f138,plain,(
% 0.23/0.55    sP1(sK2,k2_pre_topc(sK2,sK3)) | ~l1_pre_topc(sK2)),
% 0.23/0.55    inference(resolution,[],[f94,f53])).
% 0.23/0.55  fof(f607,plain,(
% 0.23/0.55    sP0(k2_pre_topc(sK2,sK3),sK2)),
% 0.23/0.55    inference(subsumption_resolution,[],[f606,f489])).
% 0.23/0.55  fof(f606,plain,(
% 0.23/0.55    ~r1_tarski(k1_tops_1(sK2,sK3),k2_pre_topc(sK2,sK3)) | sP0(k2_pre_topc(sK2,sK3),sK2)),
% 0.23/0.55    inference(forward_demodulation,[],[f605,f572])).
% 0.23/0.55  fof(f605,plain,(
% 0.23/0.55    ~r1_tarski(k1_tops_1(sK2,k2_pre_topc(sK2,sK3)),k2_pre_topc(sK2,sK3)) | sP0(k2_pre_topc(sK2,sK3),sK2)),
% 0.23/0.55    inference(forward_demodulation,[],[f604,f96])).
% 0.23/0.55  fof(f96,plain,(
% 0.23/0.55    k2_pre_topc(sK2,sK3) = k2_pre_topc(sK2,k2_pre_topc(sK2,sK3))),
% 0.23/0.55    inference(subsumption_resolution,[],[f85,f42])).
% 0.23/0.55  fof(f85,plain,(
% 0.23/0.55    k2_pre_topc(sK2,sK3) = k2_pre_topc(sK2,k2_pre_topc(sK2,sK3)) | ~l1_pre_topc(sK2)),
% 0.23/0.55    inference(resolution,[],[f43,f59])).
% 0.23/0.55  fof(f604,plain,(
% 0.23/0.55    sP0(k2_pre_topc(sK2,sK3),sK2) | ~r1_tarski(k1_tops_1(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,sK3))),k2_pre_topc(sK2,sK3))),
% 0.23/0.55    inference(subsumption_resolution,[],[f603,f64])).
% 0.23/0.55  fof(f603,plain,(
% 0.23/0.55    ~r1_tarski(k2_pre_topc(sK2,sK3),k2_pre_topc(sK2,sK3)) | sP0(k2_pre_topc(sK2,sK3),sK2) | ~r1_tarski(k1_tops_1(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,sK3))),k2_pre_topc(sK2,sK3))),
% 0.23/0.55    inference(forward_demodulation,[],[f591,f486])).
% 0.23/0.55  fof(f591,plain,(
% 0.23/0.55    ~r1_tarski(k2_pre_topc(sK2,sK3),k2_pre_topc(sK2,k1_tops_1(sK2,sK3))) | sP0(k2_pre_topc(sK2,sK3),sK2) | ~r1_tarski(k1_tops_1(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,sK3))),k2_pre_topc(sK2,sK3))),
% 0.23/0.55    inference(superposition,[],[f52,f572])).
% 0.23/0.55  % SZS output end Proof for theBenchmark
% 0.23/0.55  % (9135)------------------------------
% 0.23/0.55  % (9135)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.23/0.55  % (9135)Termination reason: Refutation
% 0.23/0.55  
% 0.23/0.55  % (9135)Memory used [KB]: 1791
% 0.23/0.55  % (9135)Time elapsed: 0.101 s
% 0.23/0.55  % (9135)------------------------------
% 0.23/0.56  % (9135)------------------------------
% 0.23/0.56  % (9150)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 0.23/0.56  % (9133)Refutation not found, incomplete strategy% (9133)------------------------------
% 0.23/0.56  % (9133)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.23/0.56  % (9133)Termination reason: Refutation not found, incomplete strategy
% 0.23/0.56  
% 0.23/0.56  % (9133)Memory used [KB]: 10618
% 0.23/0.56  % (9133)Time elapsed: 0.104 s
% 0.23/0.56  % (9133)------------------------------
% 0.23/0.56  % (9133)------------------------------
% 0.23/0.56  % (9126)Success in time 0.187 s
%------------------------------------------------------------------------------
