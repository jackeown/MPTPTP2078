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
% DateTime   : Thu Dec  3 13:12:10 EST 2020

% Result     : Theorem 0.23s
% Output     : Refutation 0.23s
% Verified   : 
% Statistics : Number of formulae       :   89 ( 277 expanded)
%              Number of leaves         :   15 (  74 expanded)
%              Depth                    :   31
%              Number of atoms          :  265 (1373 expanded)
%              Number of equality atoms :   70 ( 390 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f896,plain,(
    $false ),
    inference(subsumption_resolution,[],[f894,f96])).

fof(f96,plain,(
    r1_tarski(k2_tops_1(sK0,sK1),sK1) ),
    inference(subsumption_resolution,[],[f95,f90])).

fof(f90,plain,
    ( r1_tarski(k2_tops_1(sK0,sK1),sK1)
    | v4_pre_topc(sK1,sK0) ),
    inference(superposition,[],[f44,f87])).

fof(f87,plain,
    ( k2_tops_1(sK0,sK1) = k4_xboole_0(sK1,k1_tops_1(sK0,sK1))
    | v4_pre_topc(sK1,sK0) ),
    inference(subsumption_resolution,[],[f84,f38])).

fof(f38,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,
    ( ( k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))
      | ~ v4_pre_topc(sK1,sK0) )
    & ( k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))
      | v4_pre_topc(sK1,sK0) )
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f32,f34,f33])).

fof(f33,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ( k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1))
              | ~ v4_pre_topc(X1,X0) )
            & ( k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1))
              | v4_pre_topc(X1,X0) )
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
   => ( ? [X1] :
          ( ( k2_tops_1(sK0,X1) != k7_subset_1(u1_struct_0(sK0),X1,k1_tops_1(sK0,X1))
            | ~ v4_pre_topc(X1,sK0) )
          & ( k2_tops_1(sK0,X1) = k7_subset_1(u1_struct_0(sK0),X1,k1_tops_1(sK0,X1))
            | v4_pre_topc(X1,sK0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
      & l1_pre_topc(sK0)
      & v2_pre_topc(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,
    ( ? [X1] :
        ( ( k2_tops_1(sK0,X1) != k7_subset_1(u1_struct_0(sK0),X1,k1_tops_1(sK0,X1))
          | ~ v4_pre_topc(X1,sK0) )
        & ( k2_tops_1(sK0,X1) = k7_subset_1(u1_struct_0(sK0),X1,k1_tops_1(sK0,X1))
          | v4_pre_topc(X1,sK0) )
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
   => ( ( k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))
        | ~ v4_pre_topc(sK1,sK0) )
      & ( k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))
        | v4_pre_topc(sK1,sK0) )
      & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1))
            | ~ v4_pre_topc(X1,X0) )
          & ( k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1))
            | v4_pre_topc(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1))
            | ~ v4_pre_topc(X1,X0) )
          & ( k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1))
            | v4_pre_topc(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f18])).

fof(f18,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v4_pre_topc(X1,X0)
          <~> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v4_pre_topc(X1,X0)
          <~> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( v4_pre_topc(X1,X0)
            <=> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) ) ) ) ),
    inference(negated_conjecture,[],[f15])).

fof(f15,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v4_pre_topc(X1,X0)
          <=> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t77_tops_1)).

fof(f84,plain,
    ( k2_tops_1(sK0,sK1) = k4_xboole_0(sK1,k1_tops_1(sK0,sK1))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | v4_pre_topc(sK1,sK0) ),
    inference(superposition,[],[f53,f39])).

fof(f39,plain,
    ( k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))
    | v4_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f35])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

fof(f44,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

fof(f95,plain,
    ( ~ v4_pre_topc(sK1,sK0)
    | r1_tarski(k2_tops_1(sK0,sK1),sK1) ),
    inference(subsumption_resolution,[],[f92,f37])).

fof(f37,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f35])).

fof(f92,plain,
    ( ~ v4_pre_topc(sK1,sK0)
    | r1_tarski(k2_tops_1(sK0,sK1),sK1)
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f43,f38])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v4_pre_topc(X1,X0)
      | r1_tarski(k2_tops_1(X0,X1),X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k2_tops_1(X0,X1),X1)
          | ~ v4_pre_topc(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k2_tops_1(X0,X1),X1)
          | ~ v4_pre_topc(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v4_pre_topc(X1,X0)
           => r1_tarski(k2_tops_1(X0,X1),X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_tops_1)).

fof(f894,plain,(
    ~ r1_tarski(k2_tops_1(sK0,sK1),sK1) ),
    inference(trivial_inequality_removal,[],[f892])).

fof(f892,plain,
    ( k2_tops_1(sK0,sK1) != k2_tops_1(sK0,sK1)
    | ~ r1_tarski(k2_tops_1(sK0,sK1),sK1) ),
    inference(superposition,[],[f885,f60])).

fof(f60,plain,(
    ! [X2,X3] :
      ( k3_xboole_0(X3,X2) = X2
      | ~ r1_tarski(X2,X3) ) ),
    inference(superposition,[],[f50,f45])).

% (23454)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
fof(f45,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f50,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f885,plain,(
    k2_tops_1(sK0,sK1) != k3_xboole_0(sK1,k2_tops_1(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f884,f37])).

fof(f884,plain,
    ( k2_tops_1(sK0,sK1) != k3_xboole_0(sK1,k2_tops_1(sK0,sK1))
    | ~ l1_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f883,f38])).

fof(f883,plain,
    ( k2_tops_1(sK0,sK1) != k3_xboole_0(sK1,k2_tops_1(sK0,sK1))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f877,f175])).

fof(f175,plain,(
    v4_pre_topc(sK1,sK0) ),
    inference(subsumption_resolution,[],[f174,f36])).

fof(f36,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f35])).

fof(f174,plain,
    ( v4_pre_topc(sK1,sK0)
    | ~ v2_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f173,f37])).

fof(f173,plain,
    ( v4_pre_topc(sK1,sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f172,f38])).

fof(f172,plain,
    ( v4_pre_topc(sK1,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0) ),
    inference(duplicate_literal_removal,[],[f171])).

fof(f171,plain,
    ( v4_pre_topc(sK1,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v4_pre_topc(sK1,sK0) ),
    inference(superposition,[],[f51,f170])).

fof(f170,plain,
    ( sK1 = k2_pre_topc(sK0,sK1)
    | v4_pre_topc(sK1,sK0) ),
    inference(subsumption_resolution,[],[f169,f37])).

fof(f169,plain,
    ( sK1 = k2_pre_topc(sK0,sK1)
    | ~ l1_pre_topc(sK0)
    | v4_pre_topc(sK1,sK0) ),
    inference(subsumption_resolution,[],[f167,f38])).

fof(f167,plain,
    ( sK1 = k2_pre_topc(sK0,sK1)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | v4_pre_topc(sK1,sK0) ),
    inference(superposition,[],[f104,f131])).

fof(f131,plain,
    ( sK1 = k2_xboole_0(sK1,k2_tops_1(sK0,sK1))
    | v4_pre_topc(sK1,sK0) ),
    inference(superposition,[],[f46,f128])).

fof(f128,plain,
    ( k2_tops_1(sK0,sK1) = k3_xboole_0(sK1,k2_tops_1(sK0,sK1))
    | v4_pre_topc(sK1,sK0) ),
    inference(duplicate_literal_removal,[],[f120])).

fof(f120,plain,
    ( k2_tops_1(sK0,sK1) = k3_xboole_0(sK1,k2_tops_1(sK0,sK1))
    | v4_pre_topc(sK1,sK0)
    | v4_pre_topc(sK1,sK0) ),
    inference(superposition,[],[f113,f87])).

fof(f113,plain,
    ( k4_xboole_0(sK1,k1_tops_1(sK0,sK1)) = k3_xboole_0(sK1,k2_tops_1(sK0,sK1))
    | v4_pre_topc(sK1,sK0) ),
    inference(subsumption_resolution,[],[f105,f44])).

fof(f105,plain,
    ( k4_xboole_0(sK1,k1_tops_1(sK0,sK1)) = k3_xboole_0(sK1,k2_tops_1(sK0,sK1))
    | v4_pre_topc(sK1,sK0)
    | ~ r1_tarski(k4_xboole_0(sK1,k1_tops_1(sK0,sK1)),sK1) ),
    inference(superposition,[],[f99,f60])).

fof(f99,plain,
    ( k3_xboole_0(sK1,k2_tops_1(sK0,sK1)) = k3_xboole_0(sK1,k4_xboole_0(sK1,k1_tops_1(sK0,sK1)))
    | v4_pre_topc(sK1,sK0) ),
    inference(forward_demodulation,[],[f97,f78])).

fof(f78,plain,(
    ! [X0,X1] : k3_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(superposition,[],[f49,f49])).

fof(f49,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f97,plain,
    ( k3_xboole_0(sK1,k2_tops_1(sK0,sK1)) = k4_xboole_0(sK1,k3_xboole_0(sK1,k1_tops_1(sK0,sK1)))
    | v4_pre_topc(sK1,sK0) ),
    inference(superposition,[],[f49,f89])).

fof(f89,plain,
    ( k3_xboole_0(sK1,k1_tops_1(sK0,sK1)) = k4_xboole_0(sK1,k2_tops_1(sK0,sK1))
    | v4_pre_topc(sK1,sK0) ),
    inference(superposition,[],[f49,f87])).

fof(f46,plain,(
    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_xboole_1)).

fof(f104,plain,(
    ! [X2,X3] :
      ( k2_xboole_0(X3,k2_tops_1(X2,X3)) = k2_pre_topc(X2,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
      | ~ l1_pre_topc(X2) ) ),
    inference(subsumption_resolution,[],[f103,f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_tops_1)).

fof(f103,plain,(
    ! [X2,X3] :
      ( k2_xboole_0(X3,k2_tops_1(X2,X3)) = k2_pre_topc(X2,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
      | ~ l1_pre_topc(X2)
      | ~ m1_subset_1(k2_tops_1(X2,X3),k1_zfmisc_1(u1_struct_0(X2))) ) ),
    inference(duplicate_literal_removal,[],[f100])).

fof(f100,plain,(
    ! [X2,X3] :
      ( k2_xboole_0(X3,k2_tops_1(X2,X3)) = k2_pre_topc(X2,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
      | ~ l1_pre_topc(X2)
      | ~ m1_subset_1(k2_tops_1(X2,X3),k1_zfmisc_1(u1_struct_0(X2)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) ) ),
    inference(superposition,[],[f41,f54])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X0))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

fof(f41,plain,(
    ! [X0,X1] :
      ( k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_tops_1)).

fof(f51,plain,(
    ! [X0,X1] :
      ( v4_pre_topc(k2_pre_topc(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( v4_pre_topc(k2_pre_topc(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( v4_pre_topc(k2_pre_topc(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => v4_pre_topc(k2_pre_topc(X0,X1),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_tops_1)).

fof(f877,plain,
    ( k2_tops_1(sK0,sK1) != k3_xboole_0(sK1,k2_tops_1(sK0,sK1))
    | ~ v4_pre_topc(sK1,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0) ),
    inference(superposition,[],[f88,f179])).

fof(f179,plain,(
    ! [X2,X3] :
      ( k3_xboole_0(X2,k2_tops_1(X3,X2)) = k4_xboole_0(X2,k1_tops_1(X3,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3)))
      | ~ l1_pre_topc(X3) ) ),
    inference(superposition,[],[f49,f119])).

fof(f119,plain,(
    ! [X2,X3] :
      ( k4_xboole_0(X3,k2_tops_1(X2,X3)) = k1_tops_1(X2,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
      | ~ l1_pre_topc(X2) ) ),
    inference(duplicate_literal_removal,[],[f116])).

fof(f116,plain,(
    ! [X2,X3] :
      ( k4_xboole_0(X3,k2_tops_1(X2,X3)) = k1_tops_1(X2,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
      | ~ l1_pre_topc(X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) ) ),
    inference(superposition,[],[f42,f53])).

fof(f42,plain,(
    ! [X0,X1] :
      ( k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_tops_1)).

fof(f88,plain,
    ( k2_tops_1(sK0,sK1) != k4_xboole_0(sK1,k1_tops_1(sK0,sK1))
    | ~ v4_pre_topc(sK1,sK0) ),
    inference(subsumption_resolution,[],[f85,f38])).

fof(f85,plain,
    ( k2_tops_1(sK0,sK1) != k4_xboole_0(sK1,k1_tops_1(sK0,sK1))
    | ~ v4_pre_topc(sK1,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(superposition,[],[f40,f53])).

fof(f40,plain,
    ( k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))
    | ~ v4_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f35])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.15  % Command    : run_vampire %s %d
% 0.15/0.36  % Computer   : n023.cluster.edu
% 0.15/0.36  % Model      : x86_64 x86_64
% 0.15/0.36  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.36  % Memory     : 8042.1875MB
% 0.15/0.36  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.36  % CPULimit   : 60
% 0.15/0.36  % WCLimit    : 600
% 0.15/0.36  % DateTime   : Tue Dec  1 18:57:50 EST 2020
% 0.15/0.36  % CPUTime    : 
% 0.23/0.48  % (23452)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.23/0.49  % (23463)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.23/0.49  % (23453)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.23/0.49  % (23457)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 0.23/0.49  % (23455)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.23/0.49  % (23459)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.23/0.49  % (23451)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.23/0.50  % (23461)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.23/0.50  % (23449)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.23/0.50  % (23465)ott-1_50_afr=on:afp=1000:afq=1.2:amm=sco:anc=none:bsr=on:cond=fast:fsr=off:fde=none:irw=on:nm=16:nwc=1.5:updr=off:uhcvi=on_1883 on theBenchmark
% 0.23/0.50  % (23460)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.23/0.51  % (23452)Refutation found. Thanks to Tanya!
% 0.23/0.51  % SZS status Theorem for theBenchmark
% 0.23/0.51  % SZS output start Proof for theBenchmark
% 0.23/0.51  fof(f896,plain,(
% 0.23/0.51    $false),
% 0.23/0.51    inference(subsumption_resolution,[],[f894,f96])).
% 0.23/0.51  fof(f96,plain,(
% 0.23/0.51    r1_tarski(k2_tops_1(sK0,sK1),sK1)),
% 0.23/0.51    inference(subsumption_resolution,[],[f95,f90])).
% 0.23/0.51  fof(f90,plain,(
% 0.23/0.51    r1_tarski(k2_tops_1(sK0,sK1),sK1) | v4_pre_topc(sK1,sK0)),
% 0.23/0.51    inference(superposition,[],[f44,f87])).
% 0.23/0.51  fof(f87,plain,(
% 0.23/0.51    k2_tops_1(sK0,sK1) = k4_xboole_0(sK1,k1_tops_1(sK0,sK1)) | v4_pre_topc(sK1,sK0)),
% 0.23/0.51    inference(subsumption_resolution,[],[f84,f38])).
% 0.23/0.51  fof(f38,plain,(
% 0.23/0.51    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.23/0.51    inference(cnf_transformation,[],[f35])).
% 0.23/0.51  fof(f35,plain,(
% 0.23/0.51    ((k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) | ~v4_pre_topc(sK1,sK0)) & (k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) | v4_pre_topc(sK1,sK0)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0)),
% 0.23/0.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f32,f34,f33])).
% 0.23/0.51  fof(f33,plain,(
% 0.23/0.51    ? [X0] : (? [X1] : ((k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) | ~v4_pre_topc(X1,X0)) & (k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) | v4_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0)) => (? [X1] : ((k2_tops_1(sK0,X1) != k7_subset_1(u1_struct_0(sK0),X1,k1_tops_1(sK0,X1)) | ~v4_pre_topc(X1,sK0)) & (k2_tops_1(sK0,X1) = k7_subset_1(u1_struct_0(sK0),X1,k1_tops_1(sK0,X1)) | v4_pre_topc(X1,sK0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0))),
% 0.23/0.51    introduced(choice_axiom,[])).
% 0.23/0.51  fof(f34,plain,(
% 0.23/0.51    ? [X1] : ((k2_tops_1(sK0,X1) != k7_subset_1(u1_struct_0(sK0),X1,k1_tops_1(sK0,X1)) | ~v4_pre_topc(X1,sK0)) & (k2_tops_1(sK0,X1) = k7_subset_1(u1_struct_0(sK0),X1,k1_tops_1(sK0,X1)) | v4_pre_topc(X1,sK0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) => ((k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) | ~v4_pre_topc(sK1,sK0)) & (k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) | v4_pre_topc(sK1,sK0)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.23/0.51    introduced(choice_axiom,[])).
% 0.23/0.51  fof(f32,plain,(
% 0.23/0.51    ? [X0] : (? [X1] : ((k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) | ~v4_pre_topc(X1,X0)) & (k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) | v4_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 0.23/0.51    inference(flattening,[],[f31])).
% 0.23/0.51  fof(f31,plain,(
% 0.23/0.51    ? [X0] : (? [X1] : (((k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) | ~v4_pre_topc(X1,X0)) & (k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) | v4_pre_topc(X1,X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 0.23/0.51    inference(nnf_transformation,[],[f18])).
% 0.23/0.51  fof(f18,plain,(
% 0.23/0.51    ? [X0] : (? [X1] : ((v4_pre_topc(X1,X0) <~> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 0.23/0.51    inference(flattening,[],[f17])).
% 0.23/0.51  fof(f17,plain,(
% 0.23/0.51    ? [X0] : (? [X1] : ((v4_pre_topc(X1,X0) <~> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_pre_topc(X0) & v2_pre_topc(X0)))),
% 0.23/0.51    inference(ennf_transformation,[],[f16])).
% 0.23/0.51  fof(f16,negated_conjecture,(
% 0.23/0.51    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_pre_topc(X1,X0) <=> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)))))),
% 0.23/0.51    inference(negated_conjecture,[],[f15])).
% 0.23/0.51  fof(f15,conjecture,(
% 0.23/0.51    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_pre_topc(X1,X0) <=> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)))))),
% 0.23/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t77_tops_1)).
% 0.23/0.51  fof(f84,plain,(
% 0.23/0.51    k2_tops_1(sK0,sK1) = k4_xboole_0(sK1,k1_tops_1(sK0,sK1)) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | v4_pre_topc(sK1,sK0)),
% 0.23/0.51    inference(superposition,[],[f53,f39])).
% 0.23/0.51  fof(f39,plain,(
% 0.23/0.51    k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) | v4_pre_topc(sK1,sK0)),
% 0.23/0.51    inference(cnf_transformation,[],[f35])).
% 0.23/0.51  fof(f53,plain,(
% 0.23/0.51    ( ! [X2,X0,X1] : (k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.23/0.51    inference(cnf_transformation,[],[f28])).
% 0.23/0.51  fof(f28,plain,(
% 0.23/0.51    ! [X0,X1,X2] : (k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.23/0.51    inference(ennf_transformation,[],[f8])).
% 0.23/0.51  fof(f8,axiom,(
% 0.23/0.51    ! [X0,X1,X2] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2))),
% 0.23/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_subset_1)).
% 0.23/0.51  fof(f44,plain,(
% 0.23/0.51    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 0.23/0.51    inference(cnf_transformation,[],[f5])).
% 0.23/0.51  fof(f5,axiom,(
% 0.23/0.51    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 0.23/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).
% 0.23/0.51  fof(f95,plain,(
% 0.23/0.51    ~v4_pre_topc(sK1,sK0) | r1_tarski(k2_tops_1(sK0,sK1),sK1)),
% 0.23/0.51    inference(subsumption_resolution,[],[f92,f37])).
% 0.23/0.51  fof(f37,plain,(
% 0.23/0.51    l1_pre_topc(sK0)),
% 0.23/0.51    inference(cnf_transformation,[],[f35])).
% 0.23/0.51  fof(f92,plain,(
% 0.23/0.51    ~v4_pre_topc(sK1,sK0) | r1_tarski(k2_tops_1(sK0,sK1),sK1) | ~l1_pre_topc(sK0)),
% 0.23/0.51    inference(resolution,[],[f43,f38])).
% 0.23/0.51  fof(f43,plain,(
% 0.23/0.51    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v4_pre_topc(X1,X0) | r1_tarski(k2_tops_1(X0,X1),X1) | ~l1_pre_topc(X0)) )),
% 0.23/0.51    inference(cnf_transformation,[],[f22])).
% 0.23/0.51  fof(f22,plain,(
% 0.23/0.51    ! [X0] : (! [X1] : (r1_tarski(k2_tops_1(X0,X1),X1) | ~v4_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.23/0.51    inference(flattening,[],[f21])).
% 0.23/0.51  fof(f21,plain,(
% 0.23/0.51    ! [X0] : (! [X1] : ((r1_tarski(k2_tops_1(X0,X1),X1) | ~v4_pre_topc(X1,X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.23/0.51    inference(ennf_transformation,[],[f13])).
% 0.23/0.51  fof(f13,axiom,(
% 0.23/0.51    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_pre_topc(X1,X0) => r1_tarski(k2_tops_1(X0,X1),X1))))),
% 0.23/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_tops_1)).
% 0.23/0.51  fof(f894,plain,(
% 0.23/0.51    ~r1_tarski(k2_tops_1(sK0,sK1),sK1)),
% 0.23/0.51    inference(trivial_inequality_removal,[],[f892])).
% 0.23/0.51  fof(f892,plain,(
% 0.23/0.51    k2_tops_1(sK0,sK1) != k2_tops_1(sK0,sK1) | ~r1_tarski(k2_tops_1(sK0,sK1),sK1)),
% 0.23/0.51    inference(superposition,[],[f885,f60])).
% 0.23/0.51  fof(f60,plain,(
% 0.23/0.51    ( ! [X2,X3] : (k3_xboole_0(X3,X2) = X2 | ~r1_tarski(X2,X3)) )),
% 0.23/0.51    inference(superposition,[],[f50,f45])).
% 0.23/0.51  % (23454)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.23/0.51  fof(f45,plain,(
% 0.23/0.51    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 0.23/0.51    inference(cnf_transformation,[],[f1])).
% 0.23/0.51  fof(f1,axiom,(
% 0.23/0.51    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 0.23/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 0.23/0.51  fof(f50,plain,(
% 0.23/0.51    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 0.23/0.51    inference(cnf_transformation,[],[f23])).
% 0.23/0.51  fof(f23,plain,(
% 0.23/0.51    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 0.23/0.51    inference(ennf_transformation,[],[f4])).
% 0.23/0.51  fof(f4,axiom,(
% 0.23/0.51    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 0.23/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).
% 0.23/0.51  fof(f885,plain,(
% 0.23/0.51    k2_tops_1(sK0,sK1) != k3_xboole_0(sK1,k2_tops_1(sK0,sK1))),
% 0.23/0.51    inference(subsumption_resolution,[],[f884,f37])).
% 0.23/0.51  fof(f884,plain,(
% 0.23/0.51    k2_tops_1(sK0,sK1) != k3_xboole_0(sK1,k2_tops_1(sK0,sK1)) | ~l1_pre_topc(sK0)),
% 0.23/0.51    inference(subsumption_resolution,[],[f883,f38])).
% 0.23/0.51  fof(f883,plain,(
% 0.23/0.51    k2_tops_1(sK0,sK1) != k3_xboole_0(sK1,k2_tops_1(sK0,sK1)) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0)),
% 0.23/0.51    inference(subsumption_resolution,[],[f877,f175])).
% 0.23/0.51  fof(f175,plain,(
% 0.23/0.51    v4_pre_topc(sK1,sK0)),
% 0.23/0.51    inference(subsumption_resolution,[],[f174,f36])).
% 0.23/0.51  fof(f36,plain,(
% 0.23/0.51    v2_pre_topc(sK0)),
% 0.23/0.51    inference(cnf_transformation,[],[f35])).
% 0.23/0.51  fof(f174,plain,(
% 0.23/0.51    v4_pre_topc(sK1,sK0) | ~v2_pre_topc(sK0)),
% 0.23/0.51    inference(subsumption_resolution,[],[f173,f37])).
% 0.23/0.51  fof(f173,plain,(
% 0.23/0.51    v4_pre_topc(sK1,sK0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0)),
% 0.23/0.51    inference(subsumption_resolution,[],[f172,f38])).
% 0.23/0.51  fof(f172,plain,(
% 0.23/0.51    v4_pre_topc(sK1,sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0)),
% 0.23/0.51    inference(duplicate_literal_removal,[],[f171])).
% 0.23/0.51  fof(f171,plain,(
% 0.23/0.51    v4_pre_topc(sK1,sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v4_pre_topc(sK1,sK0)),
% 0.23/0.51    inference(superposition,[],[f51,f170])).
% 0.23/0.51  fof(f170,plain,(
% 0.23/0.51    sK1 = k2_pre_topc(sK0,sK1) | v4_pre_topc(sK1,sK0)),
% 0.23/0.51    inference(subsumption_resolution,[],[f169,f37])).
% 0.23/0.51  fof(f169,plain,(
% 0.23/0.51    sK1 = k2_pre_topc(sK0,sK1) | ~l1_pre_topc(sK0) | v4_pre_topc(sK1,sK0)),
% 0.23/0.51    inference(subsumption_resolution,[],[f167,f38])).
% 0.23/0.51  fof(f167,plain,(
% 0.23/0.51    sK1 = k2_pre_topc(sK0,sK1) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | v4_pre_topc(sK1,sK0)),
% 0.23/0.51    inference(superposition,[],[f104,f131])).
% 0.23/0.51  fof(f131,plain,(
% 0.23/0.51    sK1 = k2_xboole_0(sK1,k2_tops_1(sK0,sK1)) | v4_pre_topc(sK1,sK0)),
% 0.23/0.51    inference(superposition,[],[f46,f128])).
% 0.23/0.51  fof(f128,plain,(
% 0.23/0.51    k2_tops_1(sK0,sK1) = k3_xboole_0(sK1,k2_tops_1(sK0,sK1)) | v4_pre_topc(sK1,sK0)),
% 0.23/0.51    inference(duplicate_literal_removal,[],[f120])).
% 0.23/0.51  fof(f120,plain,(
% 0.23/0.51    k2_tops_1(sK0,sK1) = k3_xboole_0(sK1,k2_tops_1(sK0,sK1)) | v4_pre_topc(sK1,sK0) | v4_pre_topc(sK1,sK0)),
% 0.23/0.51    inference(superposition,[],[f113,f87])).
% 0.23/0.51  fof(f113,plain,(
% 0.23/0.51    k4_xboole_0(sK1,k1_tops_1(sK0,sK1)) = k3_xboole_0(sK1,k2_tops_1(sK0,sK1)) | v4_pre_topc(sK1,sK0)),
% 0.23/0.51    inference(subsumption_resolution,[],[f105,f44])).
% 0.23/0.51  fof(f105,plain,(
% 0.23/0.51    k4_xboole_0(sK1,k1_tops_1(sK0,sK1)) = k3_xboole_0(sK1,k2_tops_1(sK0,sK1)) | v4_pre_topc(sK1,sK0) | ~r1_tarski(k4_xboole_0(sK1,k1_tops_1(sK0,sK1)),sK1)),
% 0.23/0.51    inference(superposition,[],[f99,f60])).
% 0.23/0.51  fof(f99,plain,(
% 0.23/0.51    k3_xboole_0(sK1,k2_tops_1(sK0,sK1)) = k3_xboole_0(sK1,k4_xboole_0(sK1,k1_tops_1(sK0,sK1))) | v4_pre_topc(sK1,sK0)),
% 0.23/0.51    inference(forward_demodulation,[],[f97,f78])).
% 0.23/0.51  fof(f78,plain,(
% 0.23/0.51    ( ! [X0,X1] : (k3_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 0.23/0.51    inference(superposition,[],[f49,f49])).
% 0.23/0.51  fof(f49,plain,(
% 0.23/0.51    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 0.23/0.51    inference(cnf_transformation,[],[f6])).
% 0.23/0.51  fof(f6,axiom,(
% 0.23/0.51    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 0.23/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).
% 0.23/0.51  fof(f97,plain,(
% 0.23/0.51    k3_xboole_0(sK1,k2_tops_1(sK0,sK1)) = k4_xboole_0(sK1,k3_xboole_0(sK1,k1_tops_1(sK0,sK1))) | v4_pre_topc(sK1,sK0)),
% 0.23/0.51    inference(superposition,[],[f49,f89])).
% 0.23/0.51  fof(f89,plain,(
% 0.23/0.51    k3_xboole_0(sK1,k1_tops_1(sK0,sK1)) = k4_xboole_0(sK1,k2_tops_1(sK0,sK1)) | v4_pre_topc(sK1,sK0)),
% 0.23/0.51    inference(superposition,[],[f49,f87])).
% 0.23/0.51  fof(f46,plain,(
% 0.23/0.51    ( ! [X0,X1] : (k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0) )),
% 0.23/0.51    inference(cnf_transformation,[],[f3])).
% 0.23/0.51  fof(f3,axiom,(
% 0.23/0.51    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0),
% 0.23/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_xboole_1)).
% 0.23/0.51  fof(f104,plain,(
% 0.23/0.51    ( ! [X2,X3] : (k2_xboole_0(X3,k2_tops_1(X2,X3)) = k2_pre_topc(X2,X3) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) | ~l1_pre_topc(X2)) )),
% 0.23/0.51    inference(subsumption_resolution,[],[f103,f52])).
% 0.23/0.51  fof(f52,plain,(
% 0.23/0.51    ( ! [X0,X1] : (m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.23/0.51    inference(cnf_transformation,[],[f27])).
% 0.23/0.51  fof(f27,plain,(
% 0.23/0.51    ! [X0,X1] : (m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 0.23/0.51    inference(flattening,[],[f26])).
% 0.23/0.51  fof(f26,plain,(
% 0.23/0.51    ! [X0,X1] : (m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 0.23/0.51    inference(ennf_transformation,[],[f10])).
% 0.23/0.51  fof(f10,axiom,(
% 0.23/0.51    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 0.23/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_tops_1)).
% 0.23/0.51  fof(f103,plain,(
% 0.23/0.51    ( ! [X2,X3] : (k2_xboole_0(X3,k2_tops_1(X2,X3)) = k2_pre_topc(X2,X3) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) | ~l1_pre_topc(X2) | ~m1_subset_1(k2_tops_1(X2,X3),k1_zfmisc_1(u1_struct_0(X2)))) )),
% 0.23/0.51    inference(duplicate_literal_removal,[],[f100])).
% 0.23/0.51  fof(f100,plain,(
% 0.23/0.51    ( ! [X2,X3] : (k2_xboole_0(X3,k2_tops_1(X2,X3)) = k2_pre_topc(X2,X3) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) | ~l1_pre_topc(X2) | ~m1_subset_1(k2_tops_1(X2,X3),k1_zfmisc_1(u1_struct_0(X2))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))) )),
% 0.23/0.51    inference(superposition,[],[f41,f54])).
% 0.23/0.51  fof(f54,plain,(
% 0.23/0.51    ( ! [X2,X0,X1] : (k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.23/0.51    inference(cnf_transformation,[],[f30])).
% 0.23/0.51  fof(f30,plain,(
% 0.23/0.51    ! [X0,X1,X2] : (k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.23/0.51    inference(flattening,[],[f29])).
% 0.23/0.51  fof(f29,plain,(
% 0.23/0.51    ! [X0,X1,X2] : (k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) | (~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))))),
% 0.23/0.51    inference(ennf_transformation,[],[f7])).
% 0.23/0.51  fof(f7,axiom,(
% 0.23/0.51    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2))),
% 0.23/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k4_subset_1)).
% 0.23/0.51  fof(f41,plain,(
% 0.23/0.51    ( ! [X0,X1] : (k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.23/0.51    inference(cnf_transformation,[],[f19])).
% 0.23/0.51  fof(f19,plain,(
% 0.23/0.51    ! [X0] : (! [X1] : (k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.23/0.51    inference(ennf_transformation,[],[f12])).
% 0.23/0.51  fof(f12,axiom,(
% 0.23/0.51    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))))),
% 0.23/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_tops_1)).
% 0.23/0.51  fof(f51,plain,(
% 0.23/0.51    ( ! [X0,X1] : (v4_pre_topc(k2_pre_topc(X0,X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 0.23/0.51    inference(cnf_transformation,[],[f25])).
% 0.23/0.51  fof(f25,plain,(
% 0.23/0.51    ! [X0,X1] : (v4_pre_topc(k2_pre_topc(X0,X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.23/0.51    inference(flattening,[],[f24])).
% 0.23/0.51  fof(f24,plain,(
% 0.23/0.51    ! [X0,X1] : (v4_pre_topc(k2_pre_topc(X0,X1),X0) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 0.23/0.51    inference(ennf_transformation,[],[f11])).
% 0.23/0.51  fof(f11,axiom,(
% 0.23/0.51    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0)) => v4_pre_topc(k2_pre_topc(X0,X1),X0))),
% 0.23/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_tops_1)).
% 0.23/0.51  fof(f877,plain,(
% 0.23/0.51    k2_tops_1(sK0,sK1) != k3_xboole_0(sK1,k2_tops_1(sK0,sK1)) | ~v4_pre_topc(sK1,sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0)),
% 0.23/0.51    inference(superposition,[],[f88,f179])).
% 0.23/0.51  fof(f179,plain,(
% 0.23/0.51    ( ! [X2,X3] : (k3_xboole_0(X2,k2_tops_1(X3,X2)) = k4_xboole_0(X2,k1_tops_1(X3,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3))) | ~l1_pre_topc(X3)) )),
% 0.23/0.51    inference(superposition,[],[f49,f119])).
% 0.23/0.51  fof(f119,plain,(
% 0.23/0.51    ( ! [X2,X3] : (k4_xboole_0(X3,k2_tops_1(X2,X3)) = k1_tops_1(X2,X3) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) | ~l1_pre_topc(X2)) )),
% 0.23/0.51    inference(duplicate_literal_removal,[],[f116])).
% 0.23/0.51  fof(f116,plain,(
% 0.23/0.51    ( ! [X2,X3] : (k4_xboole_0(X3,k2_tops_1(X2,X3)) = k1_tops_1(X2,X3) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) | ~l1_pre_topc(X2) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))) )),
% 0.23/0.51    inference(superposition,[],[f42,f53])).
% 0.23/0.51  fof(f42,plain,(
% 0.23/0.51    ( ! [X0,X1] : (k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.23/0.51    inference(cnf_transformation,[],[f20])).
% 0.23/0.51  fof(f20,plain,(
% 0.23/0.51    ! [X0] : (! [X1] : (k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.23/0.51    inference(ennf_transformation,[],[f14])).
% 0.23/0.51  fof(f14,axiom,(
% 0.23/0.51    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))))),
% 0.23/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_tops_1)).
% 0.23/0.51  fof(f88,plain,(
% 0.23/0.51    k2_tops_1(sK0,sK1) != k4_xboole_0(sK1,k1_tops_1(sK0,sK1)) | ~v4_pre_topc(sK1,sK0)),
% 0.23/0.51    inference(subsumption_resolution,[],[f85,f38])).
% 0.23/0.51  fof(f85,plain,(
% 0.23/0.51    k2_tops_1(sK0,sK1) != k4_xboole_0(sK1,k1_tops_1(sK0,sK1)) | ~v4_pre_topc(sK1,sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.23/0.51    inference(superposition,[],[f40,f53])).
% 0.23/0.51  fof(f40,plain,(
% 0.23/0.51    k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) | ~v4_pre_topc(sK1,sK0)),
% 0.23/0.51    inference(cnf_transformation,[],[f35])).
% 0.23/0.51  % SZS output end Proof for theBenchmark
% 0.23/0.51  % (23452)------------------------------
% 0.23/0.51  % (23452)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.23/0.51  % (23452)Termination reason: Refutation
% 0.23/0.51  
% 0.23/0.51  % (23452)Memory used [KB]: 2046
% 0.23/0.51  % (23452)Time elapsed: 0.065 s
% 0.23/0.51  % (23452)------------------------------
% 0.23/0.51  % (23452)------------------------------
% 0.23/0.51  % (23464)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.23/0.52  % (23444)Success in time 0.14 s
%------------------------------------------------------------------------------
