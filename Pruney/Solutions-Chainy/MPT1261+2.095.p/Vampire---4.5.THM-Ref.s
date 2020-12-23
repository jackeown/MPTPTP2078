%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:12:02 EST 2020

% Result     : Theorem 1.64s
% Output     : Refutation 1.64s
% Verified   : 
% Statistics : Number of formulae       :  134 ( 495 expanded)
%              Number of leaves         :   19 ( 143 expanded)
%              Depth                    :   34
%              Number of atoms          :  338 (1768 expanded)
%              Number of equality atoms :  120 ( 622 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2399,plain,(
    $false ),
    inference(subsumption_resolution,[],[f2397,f143])).

fof(f143,plain,(
    r1_tarski(k2_tops_1(sK0,sK1),sK1) ),
    inference(subsumption_resolution,[],[f142,f129])).

fof(f129,plain,
    ( r1_tarski(k2_tops_1(sK0,sK1),sK1)
    | v4_pre_topc(sK1,sK0) ),
    inference(superposition,[],[f57,f125])).

fof(f125,plain,
    ( k2_tops_1(sK0,sK1) = k4_xboole_0(sK1,k1_tops_1(sK0,sK1))
    | v4_pre_topc(sK1,sK0) ),
    inference(subsumption_resolution,[],[f122,f48])).

fof(f48,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,
    ( ( k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))
      | ~ v4_pre_topc(sK1,sK0) )
    & ( k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))
      | v4_pre_topc(sK1,sK0) )
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f41,f43,f42])).

fof(f42,plain,
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

fof(f43,plain,
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

fof(f41,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1))
            | ~ v4_pre_topc(X1,X0) )
          & ( k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1))
            | v4_pre_topc(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f40])).

fof(f40,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1))
            | ~ v4_pre_topc(X1,X0) )
          & ( k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1))
            | v4_pre_topc(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f24])).

fof(f24,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v4_pre_topc(X1,X0)
          <~> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v4_pre_topc(X1,X0)
          <~> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( v4_pre_topc(X1,X0)
            <=> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) ) ) ) ),
    inference(negated_conjecture,[],[f21])).

fof(f21,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v4_pre_topc(X1,X0)
          <=> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t77_tops_1)).

fof(f122,plain,
    ( k2_tops_1(sK0,sK1) = k4_xboole_0(sK1,k1_tops_1(sK0,sK1))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | v4_pre_topc(sK1,sK0) ),
    inference(superposition,[],[f70,f49])).

fof(f49,plain,
    ( k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))
    | v4_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f44])).

fof(f70,plain,(
    ! [X2,X0,X1] :
      ( k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

fof(f57,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

fof(f142,plain,
    ( ~ v4_pre_topc(sK1,sK0)
    | r1_tarski(k2_tops_1(sK0,sK1),sK1) ),
    inference(subsumption_resolution,[],[f138,f47])).

fof(f47,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f44])).

fof(f138,plain,
    ( ~ v4_pre_topc(sK1,sK0)
    | r1_tarski(k2_tops_1(sK0,sK1),sK1)
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f56,f48])).

fof(f56,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v4_pre_topc(X1,X0)
      | r1_tarski(k2_tops_1(X0,X1),X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k2_tops_1(X0,X1),X1)
          | ~ v4_pre_topc(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k2_tops_1(X0,X1),X1)
          | ~ v4_pre_topc(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v4_pre_topc(X1,X0)
           => r1_tarski(k2_tops_1(X0,X1),X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_tops_1)).

fof(f2397,plain,(
    ~ r1_tarski(k2_tops_1(sK0,sK1),sK1) ),
    inference(trivial_inequality_removal,[],[f2395])).

fof(f2395,plain,
    ( k2_tops_1(sK0,sK1) != k2_tops_1(sK0,sK1)
    | ~ r1_tarski(k2_tops_1(sK0,sK1),sK1) ),
    inference(superposition,[],[f2392,f84])).

fof(f84,plain,(
    ! [X2,X3] :
      ( k3_xboole_0(X3,X2) = X2
      | ~ r1_tarski(X2,X3) ) ),
    inference(superposition,[],[f64,f58])).

fof(f58,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f64,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f2392,plain,(
    k2_tops_1(sK0,sK1) != k3_xboole_0(sK1,k2_tops_1(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f2391,f47])).

fof(f2391,plain,
    ( k2_tops_1(sK0,sK1) != k3_xboole_0(sK1,k2_tops_1(sK0,sK1))
    | ~ l1_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f2390,f48])).

fof(f2390,plain,
    ( k2_tops_1(sK0,sK1) != k3_xboole_0(sK1,k2_tops_1(sK0,sK1))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f2379,f1608])).

fof(f1608,plain,(
    v4_pre_topc(sK1,sK0) ),
    inference(trivial_inequality_removal,[],[f1600])).

fof(f1600,plain,
    ( sK1 != sK1
    | v4_pre_topc(sK1,sK0) ),
    inference(backward_demodulation,[],[f150,f1599])).

fof(f1599,plain,(
    sK1 = k2_pre_topc(sK0,sK1) ),
    inference(subsumption_resolution,[],[f1598,f137])).

fof(f137,plain,
    ( sK1 = k2_pre_topc(sK0,sK1)
    | ~ v4_pre_topc(sK1,sK0) ),
    inference(subsumption_resolution,[],[f133,f47])).

fof(f133,plain,
    ( ~ v4_pre_topc(sK1,sK0)
    | sK1 = k2_pre_topc(sK0,sK1)
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f54,f48])).

fof(f54,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v4_pre_topc(X1,X0)
      | k2_pre_topc(X0,X1) = X1
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_pre_topc(X1,X0)
              | k2_pre_topc(X0,X1) != X1
              | ~ v2_pre_topc(X0) )
            & ( k2_pre_topc(X0,X1) = X1
              | ~ v4_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_pre_topc(X1,X0)
              | k2_pre_topc(X0,X1) != X1
              | ~ v2_pre_topc(X0) )
            & ( k2_pre_topc(X0,X1) = X1
              | ~ v4_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( ( ( k2_pre_topc(X0,X1) = X1
                & v2_pre_topc(X0) )
             => v4_pre_topc(X1,X0) )
            & ( v4_pre_topc(X1,X0)
             => k2_pre_topc(X0,X1) = X1 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_pre_topc)).

fof(f1598,plain,
    ( sK1 = k2_pre_topc(sK0,sK1)
    | v4_pre_topc(sK1,sK0) ),
    inference(subsumption_resolution,[],[f1597,f47])).

fof(f1597,plain,
    ( sK1 = k2_pre_topc(sK0,sK1)
    | v4_pre_topc(sK1,sK0)
    | ~ l1_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f1586,f48])).

fof(f1586,plain,
    ( sK1 = k2_pre_topc(sK0,sK1)
    | v4_pre_topc(sK1,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0) ),
    inference(superposition,[],[f1222,f165])).

fof(f165,plain,(
    ! [X2,X3] :
      ( k2_xboole_0(X3,k2_tops_1(X2,X3)) = k2_pre_topc(X2,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
      | ~ l1_pre_topc(X2) ) ),
    inference(subsumption_resolution,[],[f164,f67])).

fof(f67,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_tops_1)).

fof(f164,plain,(
    ! [X2,X3] :
      ( k2_xboole_0(X3,k2_tops_1(X2,X3)) = k2_pre_topc(X2,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
      | ~ l1_pre_topc(X2)
      | ~ m1_subset_1(k2_tops_1(X2,X3),k1_zfmisc_1(u1_struct_0(X2))) ) ),
    inference(duplicate_literal_removal,[],[f161])).

fof(f161,plain,(
    ! [X2,X3] :
      ( k2_xboole_0(X3,k2_tops_1(X2,X3)) = k2_pre_topc(X2,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
      | ~ l1_pre_topc(X2)
      | ~ m1_subset_1(k2_tops_1(X2,X3),k1_zfmisc_1(u1_struct_0(X2)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) ) ),
    inference(superposition,[],[f53,f72])).

fof(f72,plain,(
    ! [X2,X0,X1] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f38])).

fof(f38,plain,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X0))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

fof(f53,plain,(
    ! [X0,X1] :
      ( k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_tops_1)).

fof(f1222,plain,
    ( sK1 = k2_xboole_0(sK1,k2_tops_1(sK0,sK1))
    | v4_pre_topc(sK1,sK0) ),
    inference(forward_demodulation,[],[f1171,f51])).

fof(f51,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).

fof(f1171,plain,
    ( k2_xboole_0(sK1,k2_tops_1(sK0,sK1)) = k2_xboole_0(sK1,k1_xboole_0)
    | v4_pre_topc(sK1,sK0) ),
    inference(backward_demodulation,[],[f971,f1161])).

fof(f1161,plain,(
    ! [X8] : k1_xboole_0 = k3_xboole_0(k1_xboole_0,X8) ),
    inference(forward_demodulation,[],[f1160,f51])).

fof(f1160,plain,(
    ! [X8] : k2_xboole_0(k1_xboole_0,k1_xboole_0) = k3_xboole_0(k1_xboole_0,X8) ),
    inference(subsumption_resolution,[],[f1153,f186])).

fof(f186,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(resolution,[],[f107,f57])).

fof(f107,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k4_xboole_0(X1,X0),k1_xboole_0)
      | r1_tarski(X1,X0) ) ),
    inference(superposition,[],[f71,f51])).

fof(f71,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k2_xboole_0(X1,X2))
      | ~ r1_tarski(k4_xboole_0(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_xboole_0(X1,X2))
      | ~ r1_tarski(k4_xboole_0(X0,X1),X2) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k4_xboole_0(X0,X1),X2)
     => r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_xboole_1)).

fof(f1153,plain,(
    ! [X8] :
      ( k2_xboole_0(k1_xboole_0,k1_xboole_0) = k3_xboole_0(k1_xboole_0,X8)
      | ~ r1_tarski(k1_xboole_0,X8) ) ),
    inference(superposition,[],[f635,f74])).

fof(f74,plain,(
    ! [X0] : k2_xboole_0(k1_xboole_0,X0) = X0 ),
    inference(superposition,[],[f59,f51])).

fof(f59,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(f635,plain,(
    ! [X2,X3] :
      ( k2_xboole_0(X2,k3_xboole_0(X2,X3)) = k2_xboole_0(X2,X2)
      | ~ r1_tarski(X2,X3) ) ),
    inference(forward_demodulation,[],[f634,f567])).

fof(f567,plain,(
    ! [X2,X3] : k2_xboole_0(X2,k4_xboole_0(X2,X3)) = k2_xboole_0(X2,k3_xboole_0(X2,X3)) ),
    inference(backward_demodulation,[],[f326,f557])).

fof(f557,plain,(
    ! [X4,X5] : k2_xboole_0(X4,k3_xboole_0(X4,X5)) = k2_xboole_0(k3_xboole_0(X4,X5),k4_xboole_0(X4,X5)) ),
    inference(backward_demodulation,[],[f240,f551])).

fof(f551,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k3_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(backward_demodulation,[],[f88,f550])).

fof(f550,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(subsumption_resolution,[],[f542,f89])).

fof(f89,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(superposition,[],[f57,f61])).

fof(f61,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f542,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))
      | ~ r1_tarski(k3_xboole_0(X0,X1),X0) ) ),
    inference(superposition,[],[f172,f63])).

fof(f63,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f172,plain,(
    ! [X4,X5] :
      ( k4_xboole_0(X4,X5) = k5_xboole_0(X4,X5)
      | ~ r1_tarski(X5,X4) ) ),
    inference(superposition,[],[f63,f84])).

fof(f88,plain,(
    ! [X0,X1] : k3_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(superposition,[],[f61,f61])).

fof(f240,plain,(
    ! [X4,X5] : k2_xboole_0(k3_xboole_0(X4,X5),k3_xboole_0(X4,k4_xboole_0(X4,X5))) = k2_xboole_0(X4,k3_xboole_0(X4,X5)) ),
    inference(forward_demodulation,[],[f234,f59])).

fof(f234,plain,(
    ! [X4,X5] : k2_xboole_0(k3_xboole_0(X4,X5),X4) = k2_xboole_0(k3_xboole_0(X4,X5),k3_xboole_0(X4,k4_xboole_0(X4,X5))) ),
    inference(superposition,[],[f62,f88])).

fof(f62,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).

fof(f326,plain,(
    ! [X2,X3] : k2_xboole_0(X2,k4_xboole_0(X2,X3)) = k2_xboole_0(k3_xboole_0(X2,X3),k4_xboole_0(X2,X3)) ),
    inference(superposition,[],[f96,f59])).

fof(f96,plain,(
    ! [X0,X1] : k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X1)) = k2_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(forward_demodulation,[],[f93,f59])).

fof(f93,plain,(
    ! [X0,X1] : k2_xboole_0(k4_xboole_0(X0,X1),X0) = k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    inference(superposition,[],[f62,f61])).

fof(f634,plain,(
    ! [X2,X3] :
      ( k2_xboole_0(X2,k4_xboole_0(X2,X3)) = k2_xboole_0(X2,X2)
      | ~ r1_tarski(X2,X3) ) ),
    inference(forward_demodulation,[],[f615,f59])).

fof(f615,plain,(
    ! [X2,X3] :
      ( k2_xboole_0(k4_xboole_0(X2,X3),X2) = k2_xboole_0(X2,X2)
      | ~ r1_tarski(X2,X3) ) ),
    inference(superposition,[],[f568,f64])).

fof(f568,plain,(
    ! [X0,X1] : k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X1)) = k2_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(backward_demodulation,[],[f96,f567])).

fof(f971,plain,
    ( k2_xboole_0(sK1,k2_tops_1(sK0,sK1)) = k2_xboole_0(sK1,k3_xboole_0(k1_xboole_0,k2_tops_1(sK0,sK1)))
    | v4_pre_topc(sK1,sK0) ),
    inference(superposition,[],[f62,f688])).

fof(f688,plain,
    ( k4_xboole_0(k2_tops_1(sK0,sK1),sK1) = k3_xboole_0(k1_xboole_0,k2_tops_1(sK0,sK1))
    | v4_pre_topc(sK1,sK0) ),
    inference(forward_demodulation,[],[f687,f58])).

fof(f687,plain,
    ( k4_xboole_0(k2_tops_1(sK0,sK1),sK1) = k3_xboole_0(k2_tops_1(sK0,sK1),k1_xboole_0)
    | v4_pre_topc(sK1,sK0) ),
    inference(forward_demodulation,[],[f667,f105])).

fof(f105,plain,(
    ! [X1] : k3_xboole_0(X1,k1_xboole_0) = k4_xboole_0(X1,X1) ),
    inference(superposition,[],[f61,f97])).

fof(f97,plain,(
    ! [X6] : k4_xboole_0(X6,k1_xboole_0) = X6 ),
    inference(forward_demodulation,[],[f94,f74])).

fof(f94,plain,(
    ! [X6] : k4_xboole_0(X6,k1_xboole_0) = k2_xboole_0(k1_xboole_0,X6) ),
    inference(superposition,[],[f62,f74])).

fof(f667,plain,
    ( k4_xboole_0(k2_tops_1(sK0,sK1),sK1) = k4_xboole_0(k2_tops_1(sK0,sK1),k2_tops_1(sK0,sK1))
    | v4_pre_topc(sK1,sK0) ),
    inference(superposition,[],[f552,f257])).

fof(f257,plain,
    ( k2_tops_1(sK0,sK1) = k3_xboole_0(sK1,k2_tops_1(sK0,sK1))
    | v4_pre_topc(sK1,sK0) ),
    inference(duplicate_literal_removal,[],[f241])).

fof(f241,plain,
    ( k2_tops_1(sK0,sK1) = k3_xboole_0(sK1,k2_tops_1(sK0,sK1))
    | v4_pre_topc(sK1,sK0)
    | v4_pre_topc(sK1,sK0) ),
    inference(superposition,[],[f183,f125])).

fof(f183,plain,
    ( k4_xboole_0(sK1,k1_tops_1(sK0,sK1)) = k3_xboole_0(sK1,k2_tops_1(sK0,sK1))
    | v4_pre_topc(sK1,sK0) ),
    inference(subsumption_resolution,[],[f176,f57])).

fof(f176,plain,
    ( k4_xboole_0(sK1,k1_tops_1(sK0,sK1)) = k3_xboole_0(sK1,k2_tops_1(sK0,sK1))
    | v4_pre_topc(sK1,sK0)
    | ~ r1_tarski(k4_xboole_0(sK1,k1_tops_1(sK0,sK1)),sK1) ),
    inference(superposition,[],[f160,f84])).

fof(f160,plain,
    ( k3_xboole_0(sK1,k2_tops_1(sK0,sK1)) = k3_xboole_0(sK1,k4_xboole_0(sK1,k1_tops_1(sK0,sK1)))
    | v4_pre_topc(sK1,sK0) ),
    inference(forward_demodulation,[],[f157,f88])).

fof(f157,plain,
    ( k3_xboole_0(sK1,k2_tops_1(sK0,sK1)) = k4_xboole_0(sK1,k3_xboole_0(sK1,k1_tops_1(sK0,sK1)))
    | v4_pre_topc(sK1,sK0) ),
    inference(superposition,[],[f61,f128])).

fof(f128,plain,
    ( k3_xboole_0(sK1,k1_tops_1(sK0,sK1)) = k4_xboole_0(sK1,k2_tops_1(sK0,sK1))
    | v4_pre_topc(sK1,sK0) ),
    inference(superposition,[],[f61,f125])).

fof(f552,plain,(
    ! [X4,X5] : k4_xboole_0(X4,X5) = k4_xboole_0(X4,k3_xboole_0(X5,X4)) ),
    inference(backward_demodulation,[],[f228,f551])).

fof(f228,plain,(
    ! [X4,X5] : k3_xboole_0(X4,k4_xboole_0(X4,X5)) = k4_xboole_0(X4,k3_xboole_0(X5,X4)) ),
    inference(superposition,[],[f88,f58])).

fof(f150,plain,
    ( sK1 != k2_pre_topc(sK0,sK1)
    | v4_pre_topc(sK1,sK0) ),
    inference(subsumption_resolution,[],[f149,f47])).

fof(f149,plain,
    ( sK1 != k2_pre_topc(sK0,sK1)
    | v4_pre_topc(sK1,sK0)
    | ~ l1_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f145,f46])).

fof(f46,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f44])).

fof(f145,plain,
    ( sK1 != k2_pre_topc(sK0,sK1)
    | ~ v2_pre_topc(sK0)
    | v4_pre_topc(sK1,sK0)
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f55,f48])).

fof(f55,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | k2_pre_topc(X0,X1) != X1
      | ~ v2_pre_topc(X0)
      | v4_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f2379,plain,
    ( k2_tops_1(sK0,sK1) != k3_xboole_0(sK1,k2_tops_1(sK0,sK1))
    | ~ v4_pre_topc(sK1,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0) ),
    inference(superposition,[],[f126,f384])).

fof(f384,plain,(
    ! [X2,X3] :
      ( k3_xboole_0(X2,k2_tops_1(X3,X2)) = k4_xboole_0(X2,k1_tops_1(X3,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3)))
      | ~ l1_pre_topc(X3) ) ),
    inference(superposition,[],[f61,f155])).

fof(f155,plain,(
    ! [X2,X3] :
      ( k4_xboole_0(X3,k2_tops_1(X2,X3)) = k1_tops_1(X2,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
      | ~ l1_pre_topc(X2) ) ),
    inference(duplicate_literal_removal,[],[f152])).

fof(f152,plain,(
    ! [X2,X3] :
      ( k4_xboole_0(X3,k2_tops_1(X2,X3)) = k1_tops_1(X2,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
      | ~ l1_pre_topc(X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) ) ),
    inference(superposition,[],[f52,f70])).

fof(f52,plain,(
    ! [X0,X1] :
      ( k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_tops_1)).

fof(f126,plain,
    ( k2_tops_1(sK0,sK1) != k4_xboole_0(sK1,k1_tops_1(sK0,sK1))
    | ~ v4_pre_topc(sK1,sK0) ),
    inference(subsumption_resolution,[],[f123,f48])).

fof(f123,plain,
    ( k2_tops_1(sK0,sK1) != k4_xboole_0(sK1,k1_tops_1(sK0,sK1))
    | ~ v4_pre_topc(sK1,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(superposition,[],[f50,f70])).

fof(f50,plain,
    ( k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))
    | ~ v4_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f44])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n022.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 13:33:11 EST 2020
% 0.15/0.36  % CPUTime    : 
% 0.22/0.48  % (8890)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.22/0.48  % (8888)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.22/0.49  % (8898)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.22/0.49  % (8886)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.22/0.49  % (8884)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.22/0.49  % (8883)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.22/0.49  % (8897)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.22/0.49  % (8895)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.22/0.49  % (8896)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.22/0.50  % (8891)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 0.22/0.50  % (8894)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.22/0.50  % (8892)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 0.22/0.51  % (8899)ott-1_50_afr=on:afp=1000:afq=1.2:amm=sco:anc=none:bsr=on:cond=fast:fsr=off:fde=none:irw=on:nm=16:nwc=1.5:updr=off:uhcvi=on_1883 on theBenchmark
% 0.22/0.51  % (8893)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.22/0.51  % (8887)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.22/0.51  % (8889)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.22/0.51  % (8885)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.22/0.52  % (8900)lrs+11_64_acc=model:afp=100000:afq=1.2:anc=all_dependent:bd=off:bs=unit_only:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:irw=on:lma=on:nwc=1:stl=150:sac=on:sp=reverse_arity:urr=on:updr=off_893 on theBenchmark
% 1.64/0.58  % (8886)Refutation found. Thanks to Tanya!
% 1.64/0.58  % SZS status Theorem for theBenchmark
% 1.64/0.58  % SZS output start Proof for theBenchmark
% 1.64/0.58  fof(f2399,plain,(
% 1.64/0.58    $false),
% 1.64/0.58    inference(subsumption_resolution,[],[f2397,f143])).
% 1.64/0.58  fof(f143,plain,(
% 1.64/0.58    r1_tarski(k2_tops_1(sK0,sK1),sK1)),
% 1.64/0.58    inference(subsumption_resolution,[],[f142,f129])).
% 1.64/0.58  fof(f129,plain,(
% 1.64/0.58    r1_tarski(k2_tops_1(sK0,sK1),sK1) | v4_pre_topc(sK1,sK0)),
% 1.64/0.58    inference(superposition,[],[f57,f125])).
% 1.64/0.58  fof(f125,plain,(
% 1.64/0.58    k2_tops_1(sK0,sK1) = k4_xboole_0(sK1,k1_tops_1(sK0,sK1)) | v4_pre_topc(sK1,sK0)),
% 1.64/0.58    inference(subsumption_resolution,[],[f122,f48])).
% 1.64/0.58  fof(f48,plain,(
% 1.64/0.58    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.64/0.58    inference(cnf_transformation,[],[f44])).
% 1.64/0.58  fof(f44,plain,(
% 1.64/0.58    ((k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) | ~v4_pre_topc(sK1,sK0)) & (k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) | v4_pre_topc(sK1,sK0)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0)),
% 1.64/0.58    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f41,f43,f42])).
% 1.64/0.58  fof(f42,plain,(
% 1.64/0.58    ? [X0] : (? [X1] : ((k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) | ~v4_pre_topc(X1,X0)) & (k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) | v4_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0)) => (? [X1] : ((k2_tops_1(sK0,X1) != k7_subset_1(u1_struct_0(sK0),X1,k1_tops_1(sK0,X1)) | ~v4_pre_topc(X1,sK0)) & (k2_tops_1(sK0,X1) = k7_subset_1(u1_struct_0(sK0),X1,k1_tops_1(sK0,X1)) | v4_pre_topc(X1,sK0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0))),
% 1.64/0.58    introduced(choice_axiom,[])).
% 1.64/0.58  fof(f43,plain,(
% 1.64/0.58    ? [X1] : ((k2_tops_1(sK0,X1) != k7_subset_1(u1_struct_0(sK0),X1,k1_tops_1(sK0,X1)) | ~v4_pre_topc(X1,sK0)) & (k2_tops_1(sK0,X1) = k7_subset_1(u1_struct_0(sK0),X1,k1_tops_1(sK0,X1)) | v4_pre_topc(X1,sK0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) => ((k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) | ~v4_pre_topc(sK1,sK0)) & (k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) | v4_pre_topc(sK1,sK0)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))))),
% 1.64/0.58    introduced(choice_axiom,[])).
% 1.64/0.58  fof(f41,plain,(
% 1.64/0.58    ? [X0] : (? [X1] : ((k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) | ~v4_pre_topc(X1,X0)) & (k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) | v4_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 1.64/0.58    inference(flattening,[],[f40])).
% 1.64/0.58  fof(f40,plain,(
% 1.64/0.58    ? [X0] : (? [X1] : (((k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) | ~v4_pre_topc(X1,X0)) & (k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) | v4_pre_topc(X1,X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 1.64/0.58    inference(nnf_transformation,[],[f24])).
% 1.64/0.58  fof(f24,plain,(
% 1.64/0.58    ? [X0] : (? [X1] : ((v4_pre_topc(X1,X0) <~> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 1.64/0.58    inference(flattening,[],[f23])).
% 1.64/0.58  fof(f23,plain,(
% 1.64/0.58    ? [X0] : (? [X1] : ((v4_pre_topc(X1,X0) <~> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_pre_topc(X0) & v2_pre_topc(X0)))),
% 1.64/0.58    inference(ennf_transformation,[],[f22])).
% 1.64/0.58  fof(f22,negated_conjecture,(
% 1.64/0.58    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_pre_topc(X1,X0) <=> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)))))),
% 1.64/0.58    inference(negated_conjecture,[],[f21])).
% 1.64/0.58  fof(f21,conjecture,(
% 1.64/0.58    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_pre_topc(X1,X0) <=> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)))))),
% 1.64/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t77_tops_1)).
% 1.64/0.58  fof(f122,plain,(
% 1.64/0.58    k2_tops_1(sK0,sK1) = k4_xboole_0(sK1,k1_tops_1(sK0,sK1)) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | v4_pre_topc(sK1,sK0)),
% 1.64/0.58    inference(superposition,[],[f70,f49])).
% 1.64/0.58  fof(f49,plain,(
% 1.64/0.58    k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) | v4_pre_topc(sK1,sK0)),
% 1.64/0.58    inference(cnf_transformation,[],[f44])).
% 1.64/0.58  fof(f70,plain,(
% 1.64/0.58    ( ! [X2,X0,X1] : (k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 1.64/0.58    inference(cnf_transformation,[],[f36])).
% 1.64/0.58  fof(f36,plain,(
% 1.64/0.58    ! [X0,X1,X2] : (k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.64/0.58    inference(ennf_transformation,[],[f13])).
% 1.64/0.58  fof(f13,axiom,(
% 1.64/0.58    ! [X0,X1,X2] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2))),
% 1.64/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_subset_1)).
% 1.64/0.58  fof(f57,plain,(
% 1.64/0.58    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 1.64/0.58    inference(cnf_transformation,[],[f6])).
% 1.64/0.58  fof(f6,axiom,(
% 1.64/0.58    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 1.64/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).
% 1.64/0.58  fof(f142,plain,(
% 1.64/0.58    ~v4_pre_topc(sK1,sK0) | r1_tarski(k2_tops_1(sK0,sK1),sK1)),
% 1.64/0.58    inference(subsumption_resolution,[],[f138,f47])).
% 1.64/0.58  fof(f47,plain,(
% 1.64/0.58    l1_pre_topc(sK0)),
% 1.64/0.58    inference(cnf_transformation,[],[f44])).
% 1.64/0.58  fof(f138,plain,(
% 1.64/0.58    ~v4_pre_topc(sK1,sK0) | r1_tarski(k2_tops_1(sK0,sK1),sK1) | ~l1_pre_topc(sK0)),
% 1.64/0.58    inference(resolution,[],[f56,f48])).
% 1.64/0.58  fof(f56,plain,(
% 1.64/0.58    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v4_pre_topc(X1,X0) | r1_tarski(k2_tops_1(X0,X1),X1) | ~l1_pre_topc(X0)) )),
% 1.64/0.58    inference(cnf_transformation,[],[f30])).
% 1.64/0.58  fof(f30,plain,(
% 1.64/0.58    ! [X0] : (! [X1] : (r1_tarski(k2_tops_1(X0,X1),X1) | ~v4_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.64/0.58    inference(flattening,[],[f29])).
% 1.64/0.58  fof(f29,plain,(
% 1.64/0.58    ! [X0] : (! [X1] : ((r1_tarski(k2_tops_1(X0,X1),X1) | ~v4_pre_topc(X1,X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.64/0.58    inference(ennf_transformation,[],[f19])).
% 1.64/0.58  fof(f19,axiom,(
% 1.64/0.58    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_pre_topc(X1,X0) => r1_tarski(k2_tops_1(X0,X1),X1))))),
% 1.64/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_tops_1)).
% 1.64/0.58  fof(f2397,plain,(
% 1.64/0.58    ~r1_tarski(k2_tops_1(sK0,sK1),sK1)),
% 1.64/0.58    inference(trivial_inequality_removal,[],[f2395])).
% 1.64/0.58  fof(f2395,plain,(
% 1.64/0.58    k2_tops_1(sK0,sK1) != k2_tops_1(sK0,sK1) | ~r1_tarski(k2_tops_1(sK0,sK1),sK1)),
% 1.64/0.58    inference(superposition,[],[f2392,f84])).
% 1.64/0.58  fof(f84,plain,(
% 1.64/0.58    ( ! [X2,X3] : (k3_xboole_0(X3,X2) = X2 | ~r1_tarski(X2,X3)) )),
% 1.64/0.58    inference(superposition,[],[f64,f58])).
% 1.64/0.58  fof(f58,plain,(
% 1.64/0.58    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 1.64/0.58    inference(cnf_transformation,[],[f2])).
% 1.64/0.58  fof(f2,axiom,(
% 1.64/0.58    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 1.64/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 1.64/0.58  fof(f64,plain,(
% 1.64/0.58    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 1.64/0.58    inference(cnf_transformation,[],[f31])).
% 1.64/0.58  fof(f31,plain,(
% 1.64/0.58    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 1.64/0.58    inference(ennf_transformation,[],[f5])).
% 1.64/0.58  fof(f5,axiom,(
% 1.64/0.58    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 1.64/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).
% 1.64/0.58  fof(f2392,plain,(
% 1.64/0.58    k2_tops_1(sK0,sK1) != k3_xboole_0(sK1,k2_tops_1(sK0,sK1))),
% 1.64/0.58    inference(subsumption_resolution,[],[f2391,f47])).
% 1.64/0.58  fof(f2391,plain,(
% 1.64/0.58    k2_tops_1(sK0,sK1) != k3_xboole_0(sK1,k2_tops_1(sK0,sK1)) | ~l1_pre_topc(sK0)),
% 1.64/0.58    inference(subsumption_resolution,[],[f2390,f48])).
% 1.64/0.58  fof(f2390,plain,(
% 1.64/0.58    k2_tops_1(sK0,sK1) != k3_xboole_0(sK1,k2_tops_1(sK0,sK1)) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0)),
% 1.64/0.58    inference(subsumption_resolution,[],[f2379,f1608])).
% 1.64/0.58  fof(f1608,plain,(
% 1.64/0.58    v4_pre_topc(sK1,sK0)),
% 1.64/0.58    inference(trivial_inequality_removal,[],[f1600])).
% 1.64/0.58  fof(f1600,plain,(
% 1.64/0.58    sK1 != sK1 | v4_pre_topc(sK1,sK0)),
% 1.64/0.58    inference(backward_demodulation,[],[f150,f1599])).
% 1.64/0.58  fof(f1599,plain,(
% 1.64/0.58    sK1 = k2_pre_topc(sK0,sK1)),
% 1.64/0.58    inference(subsumption_resolution,[],[f1598,f137])).
% 1.64/0.58  fof(f137,plain,(
% 1.64/0.58    sK1 = k2_pre_topc(sK0,sK1) | ~v4_pre_topc(sK1,sK0)),
% 1.64/0.58    inference(subsumption_resolution,[],[f133,f47])).
% 1.64/0.58  fof(f133,plain,(
% 1.64/0.58    ~v4_pre_topc(sK1,sK0) | sK1 = k2_pre_topc(sK0,sK1) | ~l1_pre_topc(sK0)),
% 1.64/0.58    inference(resolution,[],[f54,f48])).
% 1.64/0.58  fof(f54,plain,(
% 1.64/0.58    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v4_pre_topc(X1,X0) | k2_pre_topc(X0,X1) = X1 | ~l1_pre_topc(X0)) )),
% 1.64/0.58    inference(cnf_transformation,[],[f28])).
% 1.64/0.58  fof(f28,plain,(
% 1.64/0.58    ! [X0] : (! [X1] : (((v4_pre_topc(X1,X0) | k2_pre_topc(X0,X1) != X1 | ~v2_pre_topc(X0)) & (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.64/0.58    inference(flattening,[],[f27])).
% 1.64/0.58  fof(f27,plain,(
% 1.64/0.58    ! [X0] : (! [X1] : (((v4_pre_topc(X1,X0) | (k2_pre_topc(X0,X1) != X1 | ~v2_pre_topc(X0))) & (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.64/0.58    inference(ennf_transformation,[],[f16])).
% 1.64/0.58  fof(f16,axiom,(
% 1.64/0.58    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (((k2_pre_topc(X0,X1) = X1 & v2_pre_topc(X0)) => v4_pre_topc(X1,X0)) & (v4_pre_topc(X1,X0) => k2_pre_topc(X0,X1) = X1))))),
% 1.64/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_pre_topc)).
% 1.64/0.58  fof(f1598,plain,(
% 1.64/0.58    sK1 = k2_pre_topc(sK0,sK1) | v4_pre_topc(sK1,sK0)),
% 1.64/0.58    inference(subsumption_resolution,[],[f1597,f47])).
% 1.64/0.58  fof(f1597,plain,(
% 1.64/0.58    sK1 = k2_pre_topc(sK0,sK1) | v4_pre_topc(sK1,sK0) | ~l1_pre_topc(sK0)),
% 1.64/0.58    inference(subsumption_resolution,[],[f1586,f48])).
% 1.64/0.58  fof(f1586,plain,(
% 1.64/0.58    sK1 = k2_pre_topc(sK0,sK1) | v4_pre_topc(sK1,sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0)),
% 1.64/0.58    inference(superposition,[],[f1222,f165])).
% 1.64/0.58  fof(f165,plain,(
% 1.64/0.58    ( ! [X2,X3] : (k2_xboole_0(X3,k2_tops_1(X2,X3)) = k2_pre_topc(X2,X3) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) | ~l1_pre_topc(X2)) )),
% 1.64/0.58    inference(subsumption_resolution,[],[f164,f67])).
% 1.64/0.58  fof(f67,plain,(
% 1.64/0.58    ( ! [X0,X1] : (m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 1.64/0.58    inference(cnf_transformation,[],[f35])).
% 1.64/0.58  fof(f35,plain,(
% 1.64/0.58    ! [X0,X1] : (m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 1.64/0.58    inference(flattening,[],[f34])).
% 1.64/0.58  fof(f34,plain,(
% 1.64/0.58    ! [X0,X1] : (m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 1.64/0.58    inference(ennf_transformation,[],[f17])).
% 1.64/0.58  fof(f17,axiom,(
% 1.64/0.58    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 1.64/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_tops_1)).
% 1.64/0.58  fof(f164,plain,(
% 1.64/0.58    ( ! [X2,X3] : (k2_xboole_0(X3,k2_tops_1(X2,X3)) = k2_pre_topc(X2,X3) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) | ~l1_pre_topc(X2) | ~m1_subset_1(k2_tops_1(X2,X3),k1_zfmisc_1(u1_struct_0(X2)))) )),
% 1.64/0.58    inference(duplicate_literal_removal,[],[f161])).
% 1.64/0.58  fof(f161,plain,(
% 1.64/0.58    ( ! [X2,X3] : (k2_xboole_0(X3,k2_tops_1(X2,X3)) = k2_pre_topc(X2,X3) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) | ~l1_pre_topc(X2) | ~m1_subset_1(k2_tops_1(X2,X3),k1_zfmisc_1(u1_struct_0(X2))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))) )),
% 1.64/0.58    inference(superposition,[],[f53,f72])).
% 1.64/0.58  fof(f72,plain,(
% 1.64/0.58    ( ! [X2,X0,X1] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 1.64/0.58    inference(cnf_transformation,[],[f39])).
% 1.64/0.58  fof(f39,plain,(
% 1.64/0.58    ! [X0,X1,X2] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.64/0.58    inference(flattening,[],[f38])).
% 1.64/0.58  fof(f38,plain,(
% 1.64/0.58    ! [X0,X1,X2] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | (~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))))),
% 1.64/0.58    inference(ennf_transformation,[],[f12])).
% 1.64/0.58  fof(f12,axiom,(
% 1.64/0.58    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2))),
% 1.64/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k4_subset_1)).
% 1.64/0.58  fof(f53,plain,(
% 1.64/0.58    ( ! [X0,X1] : (k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 1.64/0.58    inference(cnf_transformation,[],[f26])).
% 1.64/0.58  fof(f26,plain,(
% 1.64/0.58    ! [X0] : (! [X1] : (k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.64/0.58    inference(ennf_transformation,[],[f18])).
% 1.64/0.58  fof(f18,axiom,(
% 1.64/0.58    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))))),
% 1.64/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_tops_1)).
% 1.64/0.58  fof(f1222,plain,(
% 1.64/0.58    sK1 = k2_xboole_0(sK1,k2_tops_1(sK0,sK1)) | v4_pre_topc(sK1,sK0)),
% 1.64/0.58    inference(forward_demodulation,[],[f1171,f51])).
% 1.64/0.58  fof(f51,plain,(
% 1.64/0.58    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = X0) )),
% 1.64/0.58    inference(cnf_transformation,[],[f4])).
% 1.64/0.58  fof(f4,axiom,(
% 1.64/0.58    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0),
% 1.64/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).
% 1.64/0.58  fof(f1171,plain,(
% 1.64/0.58    k2_xboole_0(sK1,k2_tops_1(sK0,sK1)) = k2_xboole_0(sK1,k1_xboole_0) | v4_pre_topc(sK1,sK0)),
% 1.64/0.58    inference(backward_demodulation,[],[f971,f1161])).
% 1.64/0.58  fof(f1161,plain,(
% 1.64/0.58    ( ! [X8] : (k1_xboole_0 = k3_xboole_0(k1_xboole_0,X8)) )),
% 1.64/0.58    inference(forward_demodulation,[],[f1160,f51])).
% 1.64/0.58  fof(f1160,plain,(
% 1.64/0.58    ( ! [X8] : (k2_xboole_0(k1_xboole_0,k1_xboole_0) = k3_xboole_0(k1_xboole_0,X8)) )),
% 1.64/0.58    inference(subsumption_resolution,[],[f1153,f186])).
% 1.64/0.58  fof(f186,plain,(
% 1.64/0.58    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 1.64/0.58    inference(resolution,[],[f107,f57])).
% 1.64/0.58  fof(f107,plain,(
% 1.64/0.58    ( ! [X0,X1] : (~r1_tarski(k4_xboole_0(X1,X0),k1_xboole_0) | r1_tarski(X1,X0)) )),
% 1.64/0.58    inference(superposition,[],[f71,f51])).
% 1.64/0.58  fof(f71,plain,(
% 1.64/0.58    ( ! [X2,X0,X1] : (r1_tarski(X0,k2_xboole_0(X1,X2)) | ~r1_tarski(k4_xboole_0(X0,X1),X2)) )),
% 1.64/0.58    inference(cnf_transformation,[],[f37])).
% 1.64/0.58  fof(f37,plain,(
% 1.64/0.58    ! [X0,X1,X2] : (r1_tarski(X0,k2_xboole_0(X1,X2)) | ~r1_tarski(k4_xboole_0(X0,X1),X2))),
% 1.64/0.58    inference(ennf_transformation,[],[f8])).
% 1.64/0.58  fof(f8,axiom,(
% 1.64/0.58    ! [X0,X1,X2] : (r1_tarski(k4_xboole_0(X0,X1),X2) => r1_tarski(X0,k2_xboole_0(X1,X2)))),
% 1.64/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_xboole_1)).
% 1.64/0.58  fof(f1153,plain,(
% 1.64/0.58    ( ! [X8] : (k2_xboole_0(k1_xboole_0,k1_xboole_0) = k3_xboole_0(k1_xboole_0,X8) | ~r1_tarski(k1_xboole_0,X8)) )),
% 1.64/0.58    inference(superposition,[],[f635,f74])).
% 1.64/0.58  fof(f74,plain,(
% 1.64/0.58    ( ! [X0] : (k2_xboole_0(k1_xboole_0,X0) = X0) )),
% 1.64/0.58    inference(superposition,[],[f59,f51])).
% 1.64/0.58  fof(f59,plain,(
% 1.64/0.58    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 1.64/0.58    inference(cnf_transformation,[],[f1])).
% 1.64/0.58  fof(f1,axiom,(
% 1.64/0.58    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 1.64/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).
% 1.64/0.58  fof(f635,plain,(
% 1.64/0.58    ( ! [X2,X3] : (k2_xboole_0(X2,k3_xboole_0(X2,X3)) = k2_xboole_0(X2,X2) | ~r1_tarski(X2,X3)) )),
% 1.64/0.58    inference(forward_demodulation,[],[f634,f567])).
% 1.64/0.58  fof(f567,plain,(
% 1.64/0.58    ( ! [X2,X3] : (k2_xboole_0(X2,k4_xboole_0(X2,X3)) = k2_xboole_0(X2,k3_xboole_0(X2,X3))) )),
% 1.64/0.58    inference(backward_demodulation,[],[f326,f557])).
% 1.64/0.58  fof(f557,plain,(
% 1.64/0.58    ( ! [X4,X5] : (k2_xboole_0(X4,k3_xboole_0(X4,X5)) = k2_xboole_0(k3_xboole_0(X4,X5),k4_xboole_0(X4,X5))) )),
% 1.64/0.58    inference(backward_demodulation,[],[f240,f551])).
% 1.64/0.58  fof(f551,plain,(
% 1.64/0.58    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 1.64/0.58    inference(backward_demodulation,[],[f88,f550])).
% 1.64/0.58  fof(f550,plain,(
% 1.64/0.58    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 1.64/0.58    inference(subsumption_resolution,[],[f542,f89])).
% 1.64/0.58  fof(f89,plain,(
% 1.64/0.58    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) )),
% 1.64/0.58    inference(superposition,[],[f57,f61])).
% 1.64/0.58  fof(f61,plain,(
% 1.64/0.58    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 1.64/0.58    inference(cnf_transformation,[],[f9])).
% 1.64/0.58  fof(f9,axiom,(
% 1.64/0.58    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 1.64/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).
% 1.64/0.58  fof(f542,plain,(
% 1.64/0.58    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) | ~r1_tarski(k3_xboole_0(X0,X1),X0)) )),
% 1.64/0.58    inference(superposition,[],[f172,f63])).
% 1.64/0.58  fof(f63,plain,(
% 1.64/0.58    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 1.64/0.58    inference(cnf_transformation,[],[f3])).
% 1.64/0.58  fof(f3,axiom,(
% 1.64/0.58    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 1.64/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).
% 1.64/0.58  fof(f172,plain,(
% 1.64/0.58    ( ! [X4,X5] : (k4_xboole_0(X4,X5) = k5_xboole_0(X4,X5) | ~r1_tarski(X5,X4)) )),
% 1.64/0.58    inference(superposition,[],[f63,f84])).
% 1.64/0.58  fof(f88,plain,(
% 1.64/0.58    ( ! [X0,X1] : (k3_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 1.64/0.58    inference(superposition,[],[f61,f61])).
% 1.64/0.58  fof(f240,plain,(
% 1.64/0.58    ( ! [X4,X5] : (k2_xboole_0(k3_xboole_0(X4,X5),k3_xboole_0(X4,k4_xboole_0(X4,X5))) = k2_xboole_0(X4,k3_xboole_0(X4,X5))) )),
% 1.64/0.58    inference(forward_demodulation,[],[f234,f59])).
% 1.64/0.58  fof(f234,plain,(
% 1.64/0.58    ( ! [X4,X5] : (k2_xboole_0(k3_xboole_0(X4,X5),X4) = k2_xboole_0(k3_xboole_0(X4,X5),k3_xboole_0(X4,k4_xboole_0(X4,X5)))) )),
% 1.64/0.58    inference(superposition,[],[f62,f88])).
% 1.64/0.58  fof(f62,plain,(
% 1.64/0.58    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 1.64/0.58    inference(cnf_transformation,[],[f7])).
% 1.64/0.58  fof(f7,axiom,(
% 1.64/0.58    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))),
% 1.64/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).
% 1.64/0.58  fof(f326,plain,(
% 1.64/0.58    ( ! [X2,X3] : (k2_xboole_0(X2,k4_xboole_0(X2,X3)) = k2_xboole_0(k3_xboole_0(X2,X3),k4_xboole_0(X2,X3))) )),
% 1.64/0.58    inference(superposition,[],[f96,f59])).
% 1.64/0.58  fof(f96,plain,(
% 1.64/0.58    ( ! [X0,X1] : (k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X1)) = k2_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 1.64/0.58    inference(forward_demodulation,[],[f93,f59])).
% 1.64/0.58  fof(f93,plain,(
% 1.64/0.58    ( ! [X0,X1] : (k2_xboole_0(k4_xboole_0(X0,X1),X0) = k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X1))) )),
% 1.64/0.58    inference(superposition,[],[f62,f61])).
% 1.64/0.58  fof(f634,plain,(
% 1.64/0.58    ( ! [X2,X3] : (k2_xboole_0(X2,k4_xboole_0(X2,X3)) = k2_xboole_0(X2,X2) | ~r1_tarski(X2,X3)) )),
% 1.64/0.58    inference(forward_demodulation,[],[f615,f59])).
% 1.64/0.58  fof(f615,plain,(
% 1.64/0.58    ( ! [X2,X3] : (k2_xboole_0(k4_xboole_0(X2,X3),X2) = k2_xboole_0(X2,X2) | ~r1_tarski(X2,X3)) )),
% 1.64/0.58    inference(superposition,[],[f568,f64])).
% 1.64/0.58  fof(f568,plain,(
% 1.64/0.58    ( ! [X0,X1] : (k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X1)) = k2_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 1.64/0.58    inference(backward_demodulation,[],[f96,f567])).
% 1.64/0.58  fof(f971,plain,(
% 1.64/0.58    k2_xboole_0(sK1,k2_tops_1(sK0,sK1)) = k2_xboole_0(sK1,k3_xboole_0(k1_xboole_0,k2_tops_1(sK0,sK1))) | v4_pre_topc(sK1,sK0)),
% 1.64/0.58    inference(superposition,[],[f62,f688])).
% 1.64/0.58  fof(f688,plain,(
% 1.64/0.58    k4_xboole_0(k2_tops_1(sK0,sK1),sK1) = k3_xboole_0(k1_xboole_0,k2_tops_1(sK0,sK1)) | v4_pre_topc(sK1,sK0)),
% 1.64/0.58    inference(forward_demodulation,[],[f687,f58])).
% 1.64/0.58  fof(f687,plain,(
% 1.64/0.58    k4_xboole_0(k2_tops_1(sK0,sK1),sK1) = k3_xboole_0(k2_tops_1(sK0,sK1),k1_xboole_0) | v4_pre_topc(sK1,sK0)),
% 1.64/0.58    inference(forward_demodulation,[],[f667,f105])).
% 1.64/0.58  fof(f105,plain,(
% 1.64/0.58    ( ! [X1] : (k3_xboole_0(X1,k1_xboole_0) = k4_xboole_0(X1,X1)) )),
% 1.64/0.58    inference(superposition,[],[f61,f97])).
% 1.64/0.58  fof(f97,plain,(
% 1.64/0.58    ( ! [X6] : (k4_xboole_0(X6,k1_xboole_0) = X6) )),
% 1.64/0.58    inference(forward_demodulation,[],[f94,f74])).
% 1.64/0.58  fof(f94,plain,(
% 1.64/0.58    ( ! [X6] : (k4_xboole_0(X6,k1_xboole_0) = k2_xboole_0(k1_xboole_0,X6)) )),
% 1.64/0.58    inference(superposition,[],[f62,f74])).
% 1.64/0.58  fof(f667,plain,(
% 1.64/0.58    k4_xboole_0(k2_tops_1(sK0,sK1),sK1) = k4_xboole_0(k2_tops_1(sK0,sK1),k2_tops_1(sK0,sK1)) | v4_pre_topc(sK1,sK0)),
% 1.64/0.58    inference(superposition,[],[f552,f257])).
% 1.64/0.58  fof(f257,plain,(
% 1.64/0.58    k2_tops_1(sK0,sK1) = k3_xboole_0(sK1,k2_tops_1(sK0,sK1)) | v4_pre_topc(sK1,sK0)),
% 1.64/0.58    inference(duplicate_literal_removal,[],[f241])).
% 1.64/0.58  fof(f241,plain,(
% 1.64/0.58    k2_tops_1(sK0,sK1) = k3_xboole_0(sK1,k2_tops_1(sK0,sK1)) | v4_pre_topc(sK1,sK0) | v4_pre_topc(sK1,sK0)),
% 1.64/0.58    inference(superposition,[],[f183,f125])).
% 1.64/0.58  fof(f183,plain,(
% 1.64/0.58    k4_xboole_0(sK1,k1_tops_1(sK0,sK1)) = k3_xboole_0(sK1,k2_tops_1(sK0,sK1)) | v4_pre_topc(sK1,sK0)),
% 1.64/0.58    inference(subsumption_resolution,[],[f176,f57])).
% 1.64/0.58  fof(f176,plain,(
% 1.64/0.58    k4_xboole_0(sK1,k1_tops_1(sK0,sK1)) = k3_xboole_0(sK1,k2_tops_1(sK0,sK1)) | v4_pre_topc(sK1,sK0) | ~r1_tarski(k4_xboole_0(sK1,k1_tops_1(sK0,sK1)),sK1)),
% 1.64/0.58    inference(superposition,[],[f160,f84])).
% 1.64/0.58  fof(f160,plain,(
% 1.64/0.58    k3_xboole_0(sK1,k2_tops_1(sK0,sK1)) = k3_xboole_0(sK1,k4_xboole_0(sK1,k1_tops_1(sK0,sK1))) | v4_pre_topc(sK1,sK0)),
% 1.64/0.58    inference(forward_demodulation,[],[f157,f88])).
% 1.64/0.58  fof(f157,plain,(
% 1.64/0.58    k3_xboole_0(sK1,k2_tops_1(sK0,sK1)) = k4_xboole_0(sK1,k3_xboole_0(sK1,k1_tops_1(sK0,sK1))) | v4_pre_topc(sK1,sK0)),
% 1.64/0.58    inference(superposition,[],[f61,f128])).
% 1.64/0.58  fof(f128,plain,(
% 1.64/0.58    k3_xboole_0(sK1,k1_tops_1(sK0,sK1)) = k4_xboole_0(sK1,k2_tops_1(sK0,sK1)) | v4_pre_topc(sK1,sK0)),
% 1.64/0.58    inference(superposition,[],[f61,f125])).
% 1.64/0.58  fof(f552,plain,(
% 1.64/0.58    ( ! [X4,X5] : (k4_xboole_0(X4,X5) = k4_xboole_0(X4,k3_xboole_0(X5,X4))) )),
% 1.64/0.58    inference(backward_demodulation,[],[f228,f551])).
% 1.64/0.58  fof(f228,plain,(
% 1.64/0.58    ( ! [X4,X5] : (k3_xboole_0(X4,k4_xboole_0(X4,X5)) = k4_xboole_0(X4,k3_xboole_0(X5,X4))) )),
% 1.64/0.58    inference(superposition,[],[f88,f58])).
% 1.64/0.58  fof(f150,plain,(
% 1.64/0.58    sK1 != k2_pre_topc(sK0,sK1) | v4_pre_topc(sK1,sK0)),
% 1.64/0.58    inference(subsumption_resolution,[],[f149,f47])).
% 1.64/0.58  fof(f149,plain,(
% 1.64/0.58    sK1 != k2_pre_topc(sK0,sK1) | v4_pre_topc(sK1,sK0) | ~l1_pre_topc(sK0)),
% 1.64/0.58    inference(subsumption_resolution,[],[f145,f46])).
% 1.64/0.58  fof(f46,plain,(
% 1.64/0.58    v2_pre_topc(sK0)),
% 1.64/0.58    inference(cnf_transformation,[],[f44])).
% 1.64/0.58  fof(f145,plain,(
% 1.64/0.58    sK1 != k2_pre_topc(sK0,sK1) | ~v2_pre_topc(sK0) | v4_pre_topc(sK1,sK0) | ~l1_pre_topc(sK0)),
% 1.64/0.58    inference(resolution,[],[f55,f48])).
% 1.64/0.58  fof(f55,plain,(
% 1.64/0.58    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | k2_pre_topc(X0,X1) != X1 | ~v2_pre_topc(X0) | v4_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 1.64/0.58    inference(cnf_transformation,[],[f28])).
% 1.64/0.58  fof(f2379,plain,(
% 1.64/0.58    k2_tops_1(sK0,sK1) != k3_xboole_0(sK1,k2_tops_1(sK0,sK1)) | ~v4_pre_topc(sK1,sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0)),
% 1.64/0.58    inference(superposition,[],[f126,f384])).
% 1.64/0.58  fof(f384,plain,(
% 1.64/0.58    ( ! [X2,X3] : (k3_xboole_0(X2,k2_tops_1(X3,X2)) = k4_xboole_0(X2,k1_tops_1(X3,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3))) | ~l1_pre_topc(X3)) )),
% 1.64/0.58    inference(superposition,[],[f61,f155])).
% 1.64/0.58  fof(f155,plain,(
% 1.64/0.58    ( ! [X2,X3] : (k4_xboole_0(X3,k2_tops_1(X2,X3)) = k1_tops_1(X2,X3) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) | ~l1_pre_topc(X2)) )),
% 1.64/0.58    inference(duplicate_literal_removal,[],[f152])).
% 1.64/0.58  fof(f152,plain,(
% 1.64/0.58    ( ! [X2,X3] : (k4_xboole_0(X3,k2_tops_1(X2,X3)) = k1_tops_1(X2,X3) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) | ~l1_pre_topc(X2) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))) )),
% 1.64/0.58    inference(superposition,[],[f52,f70])).
% 1.64/0.58  fof(f52,plain,(
% 1.64/0.58    ( ! [X0,X1] : (k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 1.64/0.58    inference(cnf_transformation,[],[f25])).
% 1.64/0.58  fof(f25,plain,(
% 1.64/0.58    ! [X0] : (! [X1] : (k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.64/0.58    inference(ennf_transformation,[],[f20])).
% 1.64/0.58  fof(f20,axiom,(
% 1.64/0.58    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))))),
% 1.64/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_tops_1)).
% 1.64/0.58  fof(f126,plain,(
% 1.64/0.58    k2_tops_1(sK0,sK1) != k4_xboole_0(sK1,k1_tops_1(sK0,sK1)) | ~v4_pre_topc(sK1,sK0)),
% 1.64/0.58    inference(subsumption_resolution,[],[f123,f48])).
% 1.64/0.58  fof(f123,plain,(
% 1.64/0.58    k2_tops_1(sK0,sK1) != k4_xboole_0(sK1,k1_tops_1(sK0,sK1)) | ~v4_pre_topc(sK1,sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.64/0.58    inference(superposition,[],[f50,f70])).
% 1.64/0.58  fof(f50,plain,(
% 1.64/0.58    k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) | ~v4_pre_topc(sK1,sK0)),
% 1.64/0.58    inference(cnf_transformation,[],[f44])).
% 1.64/0.58  % SZS output end Proof for theBenchmark
% 1.64/0.58  % (8886)------------------------------
% 1.64/0.58  % (8886)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.64/0.58  % (8886)Termination reason: Refutation
% 1.64/0.58  
% 1.64/0.58  % (8886)Memory used [KB]: 2686
% 1.64/0.58  % (8886)Time elapsed: 0.152 s
% 1.64/0.58  % (8886)------------------------------
% 1.64/0.58  % (8886)------------------------------
% 1.64/0.58  % (8882)Success in time 0.212 s
%------------------------------------------------------------------------------
