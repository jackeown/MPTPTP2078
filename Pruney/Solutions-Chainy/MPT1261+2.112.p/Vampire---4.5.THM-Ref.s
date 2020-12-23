%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:12:05 EST 2020

% Result     : Theorem 0.38s
% Output     : Refutation 0.38s
% Verified   : 
% Statistics : Number of formulae       :  115 ( 731 expanded)
%              Number of leaves         :   18 ( 192 expanded)
%              Depth                    :   32
%              Number of atoms          :  332 (3906 expanded)
%              Number of equality atoms :  103 (1125 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f405,plain,(
    $false ),
    inference(subsumption_resolution,[],[f404,f154])).

fof(f154,plain,(
    ~ v4_pre_topc(sK1,sK0) ),
    inference(trivial_inequality_removal,[],[f153])).

fof(f153,plain,
    ( k2_tops_1(sK0,sK1) != k2_tops_1(sK0,sK1)
    | ~ v4_pre_topc(sK1,sK0) ),
    inference(backward_demodulation,[],[f49,f152])).

fof(f152,plain,(
    k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f151,f48])).

fof(f48,plain,
    ( k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))
    | v4_pre_topc(sK1,sK0) ),
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
    inference(nnf_transformation,[],[f22])).

fof(f22,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v4_pre_topc(X1,X0)
          <~> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v4_pre_topc(X1,X0)
          <~> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( v4_pre_topc(X1,X0)
            <=> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) ) ) ) ),
    inference(negated_conjecture,[],[f18])).

fof(f18,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v4_pre_topc(X1,X0)
          <=> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t77_tops_1)).

fof(f151,plain,
    ( k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))
    | ~ v4_pre_topc(sK1,sK0) ),
    inference(subsumption_resolution,[],[f150,f46])).

fof(f46,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f44])).

fof(f150,plain,
    ( k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))
    | ~ l1_pre_topc(sK0)
    | ~ v4_pre_topc(sK1,sK0) ),
    inference(subsumption_resolution,[],[f147,f47])).

fof(f47,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f44])).

fof(f147,plain,
    ( k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ v4_pre_topc(sK1,sK0) ),
    inference(superposition,[],[f53,f113])).

fof(f113,plain,
    ( sK1 = k2_pre_topc(sK0,sK1)
    | ~ v4_pre_topc(sK1,sK0) ),
    inference(subsumption_resolution,[],[f111,f46])).

fof(f111,plain,
    ( ~ v4_pre_topc(sK1,sK0)
    | sK1 = k2_pre_topc(sK0,sK1)
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f54,f47])).

fof(f54,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v4_pre_topc(X1,X0)
      | k2_pre_topc(X0,X1) = X1
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f27])).

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
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_pre_topc(X1,X0)
              | k2_pre_topc(X0,X1) != X1
              | ~ v2_pre_topc(X0) )
            & ( k2_pre_topc(X0,X1) = X1
              | ~ v4_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
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

fof(f53,plain,(
    ! [X0,X1] :
      ( k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l78_tops_1)).

fof(f49,plain,
    ( k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))
    | ~ v4_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f44])).

fof(f404,plain,(
    v4_pre_topc(sK1,sK0) ),
    inference(trivial_inequality_removal,[],[f403])).

fof(f403,plain,
    ( sK1 != sK1
    | v4_pre_topc(sK1,sK0) ),
    inference(backward_demodulation,[],[f136,f402])).

fof(f402,plain,(
    sK1 = k2_pre_topc(sK0,sK1) ),
    inference(subsumption_resolution,[],[f401,f46])).

fof(f401,plain,
    ( sK1 = k2_pre_topc(sK0,sK1)
    | ~ l1_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f400,f47])).

fof(f400,plain,
    ( sK1 = k2_pre_topc(sK0,sK1)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f375,f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_tops_1(X0,X1),X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k1_tops_1(X0,X1),X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => r1_tarski(k1_tops_1(X0,X1),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_tops_1)).

fof(f375,plain,
    ( ~ r1_tarski(k1_tops_1(sK0,sK1),sK1)
    | sK1 = k2_pre_topc(sK0,sK1) ),
    inference(resolution,[],[f358,f65])).

fof(f65,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(unused_predicate_definition_removal,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(f358,plain,
    ( ~ m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(sK1))
    | sK1 = k2_pre_topc(sK0,sK1) ),
    inference(subsumption_resolution,[],[f357,f46])).

fof(f357,plain,
    ( sK1 = k2_pre_topc(sK0,sK1)
    | ~ m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(sK1))
    | ~ l1_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f353,f47])).

fof(f353,plain,
    ( sK1 = k2_pre_topc(sK0,sK1)
    | ~ m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(sK1))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0) ),
    inference(superposition,[],[f340,f142])).

fof(f142,plain,(
    ! [X2,X3] :
      ( k2_xboole_0(X3,k2_tops_1(X2,X3)) = k2_pre_topc(X2,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
      | ~ l1_pre_topc(X2) ) ),
    inference(subsumption_resolution,[],[f141,f64])).

fof(f64,plain,(
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
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_tops_1)).

fof(f141,plain,(
    ! [X2,X3] :
      ( k2_xboole_0(X3,k2_tops_1(X2,X3)) = k2_pre_topc(X2,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
      | ~ l1_pre_topc(X2)
      | ~ m1_subset_1(k2_tops_1(X2,X3),k1_zfmisc_1(u1_struct_0(X2))) ) ),
    inference(duplicate_literal_removal,[],[f138])).

fof(f138,plain,(
    ! [X2,X3] :
      ( k2_xboole_0(X3,k2_tops_1(X2,X3)) = k2_pre_topc(X2,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
      | ~ l1_pre_topc(X2)
      | ~ m1_subset_1(k2_tops_1(X2,X3),k1_zfmisc_1(u1_struct_0(X2)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) ) ),
    inference(superposition,[],[f52,f67])).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1,X2] :
      ( k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f38])).

fof(f38,plain,(
    ! [X0,X1,X2] :
      ( k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X0))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

fof(f52,plain,(
    ! [X0,X1] :
      ( k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_tops_1)).

fof(f340,plain,
    ( sK1 = k2_xboole_0(sK1,k2_tops_1(sK0,sK1))
    | ~ m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(sK1)) ),
    inference(duplicate_literal_removal,[],[f335])).

fof(f335,plain,
    ( sK1 = k2_xboole_0(sK1,k2_tops_1(sK0,sK1))
    | ~ m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(sK1))
    | ~ m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(sK1)) ),
    inference(superposition,[],[f213,f212])).

fof(f212,plain,
    ( sK1 = k2_xboole_0(sK1,k1_tops_1(sK0,sK1))
    | ~ m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(sK1)) ),
    inference(subsumption_resolution,[],[f210,f184])).

fof(f184,plain,
    ( m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(sK1))
    | ~ m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(sK1)) ),
    inference(superposition,[],[f71,f169])).

fof(f169,plain,(
    k2_tops_1(sK0,sK1) = k4_xboole_0(sK1,k1_tops_1(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f167,f47])).

fof(f167,plain,
    ( k2_tops_1(sK0,sK1) = k4_xboole_0(sK1,k1_tops_1(sK0,sK1))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(superposition,[],[f152,f66])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

fof(f71,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k4_xboole_0(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(duplicate_literal_removal,[],[f70])).

fof(f70,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k4_xboole_0(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(superposition,[],[f59,f60])).

fof(f60,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).

fof(f59,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_subset_1)).

fof(f210,plain,
    ( sK1 = k2_xboole_0(sK1,k1_tops_1(sK0,sK1))
    | ~ m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(sK1))
    | ~ m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(sK1)) ),
    inference(backward_demodulation,[],[f166,f206])).

fof(f206,plain,(
    k2_xboole_0(k2_tops_1(sK0,sK1),k1_tops_1(sK0,sK1)) = k2_xboole_0(sK1,k1_tops_1(sK0,sK1)) ),
    inference(superposition,[],[f186,f56])).

fof(f56,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(f186,plain,(
    k2_xboole_0(k1_tops_1(sK0,sK1),k2_tops_1(sK0,sK1)) = k2_xboole_0(sK1,k1_tops_1(sK0,sK1)) ),
    inference(forward_demodulation,[],[f185,f56])).

fof(f185,plain,(
    k2_xboole_0(k1_tops_1(sK0,sK1),sK1) = k2_xboole_0(k1_tops_1(sK0,sK1),k2_tops_1(sK0,sK1)) ),
    inference(superposition,[],[f58,f169])).

fof(f58,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).

fof(f166,plain,
    ( sK1 = k2_xboole_0(k2_tops_1(sK0,sK1),k1_tops_1(sK0,sK1))
    | ~ m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(sK1))
    | ~ m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(sK1)) ),
    inference(subsumption_resolution,[],[f158,f154])).

fof(f158,plain,
    ( sK1 = k2_xboole_0(k2_tops_1(sK0,sK1),k1_tops_1(sK0,sK1))
    | ~ m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(sK1))
    | ~ m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(sK1))
    | v4_pre_topc(sK1,sK0) ),
    inference(superposition,[],[f119,f95])).

fof(f95,plain,
    ( k1_tops_1(sK0,sK1) = k3_subset_1(sK1,k2_tops_1(sK0,sK1))
    | ~ m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(sK1))
    | v4_pre_topc(sK1,sK0) ),
    inference(superposition,[],[f76,f93])).

fof(f93,plain,
    ( k2_tops_1(sK0,sK1) = k4_xboole_0(sK1,k1_tops_1(sK0,sK1))
    | v4_pre_topc(sK1,sK0) ),
    inference(subsumption_resolution,[],[f90,f47])).

fof(f90,plain,
    ( k2_tops_1(sK0,sK1) = k4_xboole_0(sK1,k1_tops_1(sK0,sK1))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | v4_pre_topc(sK1,sK0) ),
    inference(superposition,[],[f66,f48])).

fof(f76,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k4_xboole_0(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(duplicate_literal_removal,[],[f72])).

fof(f72,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k4_xboole_0(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(superposition,[],[f61,f60])).

fof(f61,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

fof(f119,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X1,k3_subset_1(X0,X1)) = X0
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(subsumption_resolution,[],[f118,f59])).

fof(f118,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X1,k3_subset_1(X0,X1)) = X0
      | ~ m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(duplicate_literal_removal,[],[f115])).

fof(f115,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X1,k3_subset_1(X0,X1)) = X0
      | ~ m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(superposition,[],[f67,f68])).

fof(f68,plain,(
    ! [X0,X1] :
      ( k4_subset_1(X0,X1,k3_subset_1(X0,X1)) = X0
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(forward_demodulation,[],[f62,f50])).

fof(f50,plain,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).

fof(f62,plain,(
    ! [X0,X1] :
      ( k2_subset_1(X0) = k4_subset_1(X0,X1,k3_subset_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( k2_subset_1(X0) = k4_subset_1(X0,X1,k3_subset_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k2_subset_1(X0) = k4_subset_1(X0,X1,k3_subset_1(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t25_subset_1)).

fof(f213,plain,
    ( k2_xboole_0(sK1,k1_tops_1(sK0,sK1)) = k2_xboole_0(sK1,k2_tops_1(sK0,sK1))
    | ~ m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(sK1)) ),
    inference(subsumption_resolution,[],[f211,f154])).

fof(f211,plain,
    ( k2_xboole_0(sK1,k1_tops_1(sK0,sK1)) = k2_xboole_0(sK1,k2_tops_1(sK0,sK1))
    | ~ m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(sK1))
    | v4_pre_topc(sK1,sK0) ),
    inference(backward_demodulation,[],[f146,f206])).

fof(f146,plain,
    ( k2_xboole_0(k2_tops_1(sK0,sK1),k1_tops_1(sK0,sK1)) = k2_xboole_0(sK1,k2_tops_1(sK0,sK1))
    | ~ m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(sK1))
    | v4_pre_topc(sK1,sK0) ),
    inference(forward_demodulation,[],[f145,f56])).

fof(f145,plain,
    ( k2_xboole_0(k2_tops_1(sK0,sK1),k1_tops_1(sK0,sK1)) = k2_xboole_0(k2_tops_1(sK0,sK1),sK1)
    | ~ m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(sK1))
    | v4_pre_topc(sK1,sK0) ),
    inference(superposition,[],[f58,f126])).

fof(f126,plain,
    ( k1_tops_1(sK0,sK1) = k4_xboole_0(sK1,k2_tops_1(sK0,sK1))
    | ~ m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(sK1))
    | v4_pre_topc(sK1,sK0) ),
    inference(subsumption_resolution,[],[f120,f96])).

fof(f96,plain,
    ( m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(sK1))
    | ~ m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(sK1))
    | v4_pre_topc(sK1,sK0) ),
    inference(superposition,[],[f71,f93])).

fof(f120,plain,
    ( k1_tops_1(sK0,sK1) = k4_xboole_0(sK1,k2_tops_1(sK0,sK1))
    | ~ m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(sK1))
    | v4_pre_topc(sK1,sK0)
    | ~ m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(sK1)) ),
    inference(superposition,[],[f95,f60])).

fof(f136,plain,
    ( sK1 != k2_pre_topc(sK0,sK1)
    | v4_pre_topc(sK1,sK0) ),
    inference(subsumption_resolution,[],[f135,f46])).

fof(f135,plain,
    ( sK1 != k2_pre_topc(sK0,sK1)
    | v4_pre_topc(sK1,sK0)
    | ~ l1_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f133,f45])).

fof(f45,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f44])).

fof(f133,plain,
    ( sK1 != k2_pre_topc(sK0,sK1)
    | ~ v2_pre_topc(sK0)
    | v4_pre_topc(sK1,sK0)
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f55,f47])).

fof(f55,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | k2_pre_topc(X0,X1) != X1
      | ~ v2_pre_topc(X0)
      | v4_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f27])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 12:02:31 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  ipcrm: permission denied for id (806060032)
% 0.13/0.36  ipcrm: permission denied for id (808747009)
% 0.13/0.37  ipcrm: permission denied for id (806092802)
% 0.13/0.37  ipcrm: permission denied for id (811696132)
% 0.13/0.37  ipcrm: permission denied for id (811728901)
% 0.13/0.37  ipcrm: permission denied for id (806223878)
% 0.13/0.37  ipcrm: permission denied for id (806256647)
% 0.13/0.37  ipcrm: permission denied for id (806289416)
% 0.13/0.37  ipcrm: permission denied for id (806322185)
% 0.13/0.38  ipcrm: permission denied for id (808878090)
% 0.13/0.38  ipcrm: permission denied for id (806387723)
% 0.13/0.38  ipcrm: permission denied for id (806420492)
% 0.21/0.38  ipcrm: permission denied for id (811794446)
% 0.21/0.38  ipcrm: permission denied for id (806486031)
% 0.21/0.38  ipcrm: permission denied for id (809009168)
% 0.21/0.38  ipcrm: permission denied for id (806551569)
% 0.21/0.39  ipcrm: permission denied for id (811859987)
% 0.21/0.39  ipcrm: permission denied for id (809140245)
% 0.21/0.39  ipcrm: permission denied for id (811925526)
% 0.21/0.39  ipcrm: permission denied for id (809205783)
% 0.21/0.39  ipcrm: permission denied for id (806715416)
% 0.21/0.39  ipcrm: permission denied for id (809238553)
% 0.21/0.40  ipcrm: permission denied for id (806748187)
% 0.21/0.40  ipcrm: permission denied for id (809304092)
% 0.21/0.40  ipcrm: permission denied for id (811991069)
% 0.21/0.40  ipcrm: permission denied for id (809369630)
% 0.21/0.40  ipcrm: permission denied for id (809402399)
% 0.21/0.40  ipcrm: permission denied for id (806813728)
% 0.21/0.41  ipcrm: permission denied for id (809435169)
% 0.21/0.41  ipcrm: permission denied for id (806846498)
% 0.21/0.41  ipcrm: permission denied for id (806912036)
% 0.21/0.41  ipcrm: permission denied for id (806977575)
% 0.21/0.41  ipcrm: permission denied for id (809566248)
% 0.21/0.42  ipcrm: permission denied for id (809631786)
% 0.21/0.42  ipcrm: permission denied for id (812154923)
% 0.21/0.42  ipcrm: permission denied for id (809697324)
% 0.21/0.42  ipcrm: permission denied for id (809730093)
% 0.21/0.42  ipcrm: permission denied for id (807075887)
% 0.21/0.42  ipcrm: permission denied for id (809828401)
% 0.21/0.43  ipcrm: permission denied for id (809861170)
% 0.21/0.43  ipcrm: permission denied for id (809893939)
% 0.21/0.43  ipcrm: permission denied for id (812286005)
% 0.21/0.43  ipcrm: permission denied for id (807174198)
% 0.21/0.43  ipcrm: permission denied for id (809992247)
% 0.21/0.43  ipcrm: permission denied for id (812384313)
% 0.21/0.44  ipcrm: permission denied for id (812417082)
% 0.21/0.44  ipcrm: permission denied for id (807239739)
% 0.21/0.44  ipcrm: permission denied for id (810156092)
% 0.21/0.44  ipcrm: permission denied for id (812449853)
% 0.21/0.44  ipcrm: permission denied for id (807305278)
% 0.21/0.44  ipcrm: permission denied for id (810221631)
% 0.21/0.44  ipcrm: permission denied for id (807338048)
% 0.21/0.45  ipcrm: permission denied for id (812482625)
% 0.21/0.45  ipcrm: permission denied for id (810319939)
% 0.21/0.45  ipcrm: permission denied for id (807403588)
% 0.21/0.45  ipcrm: permission denied for id (807436357)
% 0.21/0.45  ipcrm: permission denied for id (807469126)
% 0.21/0.45  ipcrm: permission denied for id (812548167)
% 0.21/0.45  ipcrm: permission denied for id (810385480)
% 0.21/0.46  ipcrm: permission denied for id (812580937)
% 0.21/0.46  ipcrm: permission denied for id (807600202)
% 0.21/0.46  ipcrm: permission denied for id (807632971)
% 0.21/0.46  ipcrm: permission denied for id (810582096)
% 0.21/0.47  ipcrm: permission denied for id (810614865)
% 0.21/0.47  ipcrm: permission denied for id (810647634)
% 0.21/0.47  ipcrm: permission denied for id (812777555)
% 0.21/0.47  ipcrm: permission denied for id (810745941)
% 0.21/0.47  ipcrm: permission denied for id (810778710)
% 0.21/0.47  ipcrm: permission denied for id (810811479)
% 0.21/0.47  ipcrm: permission denied for id (810844248)
% 0.21/0.48  ipcrm: permission denied for id (810877017)
% 0.21/0.48  ipcrm: permission denied for id (812843098)
% 0.21/0.48  ipcrm: permission denied for id (810942555)
% 0.21/0.48  ipcrm: permission denied for id (810975324)
% 0.21/0.48  ipcrm: permission denied for id (807862365)
% 0.21/0.48  ipcrm: permission denied for id (807927902)
% 0.21/0.48  ipcrm: permission denied for id (812875871)
% 0.21/0.48  ipcrm: permission denied for id (811040864)
% 0.21/0.48  ipcrm: permission denied for id (811073633)
% 0.21/0.49  ipcrm: permission denied for id (811139171)
% 0.21/0.49  ipcrm: permission denied for id (812941412)
% 0.21/0.49  ipcrm: permission denied for id (811303016)
% 0.21/0.49  ipcrm: permission denied for id (811335785)
% 0.21/0.50  ipcrm: permission denied for id (811368554)
% 0.21/0.50  ipcrm: permission denied for id (808190059)
% 0.21/0.50  ipcrm: permission denied for id (808222828)
% 0.21/0.50  ipcrm: permission denied for id (811401325)
% 0.21/0.50  ipcrm: permission denied for id (808321134)
% 0.21/0.50  ipcrm: permission denied for id (808353903)
% 0.21/0.50  ipcrm: permission denied for id (808386672)
% 0.21/0.50  ipcrm: permission denied for id (808419441)
% 0.21/0.51  ipcrm: permission denied for id (808452210)
% 0.21/0.51  ipcrm: permission denied for id (808484979)
% 0.21/0.51  ipcrm: permission denied for id (808517748)
% 0.21/0.51  ipcrm: permission denied for id (808550517)
% 0.21/0.51  ipcrm: permission denied for id (811466871)
% 0.21/0.51  ipcrm: permission denied for id (811499640)
% 0.21/0.52  ipcrm: permission denied for id (811532409)
% 0.21/0.52  ipcrm: permission denied for id (808583291)
% 0.21/0.52  ipcrm: permission denied for id (811597948)
% 0.21/0.52  ipcrm: permission denied for id (808648829)
% 0.21/0.52  ipcrm: permission denied for id (808681598)
% 0.21/0.52  ipcrm: permission denied for id (808714367)
% 0.38/0.62  % (31518)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.38/0.62  % (31528)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.38/0.62  % (31519)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.38/0.63  % (31521)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.38/0.63  % (31516)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.38/0.64  % (31531)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.38/0.64  % (31533)lrs+11_64_acc=model:afp=100000:afq=1.2:anc=all_dependent:bd=off:bs=unit_only:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:irw=on:lma=on:nwc=1:stl=150:sac=on:sp=reverse_arity:urr=on:updr=off_893 on theBenchmark
% 0.38/0.64  % (31530)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.38/0.64  % (31525)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 0.38/0.64  % (31527)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.38/0.64  % (31532)ott-1_50_afr=on:afp=1000:afq=1.2:amm=sco:anc=none:bsr=on:cond=fast:fsr=off:fde=none:irw=on:nm=16:nwc=1.5:updr=off:uhcvi=on_1883 on theBenchmark
% 0.38/0.64  % (31522)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.38/0.64  % (31529)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.38/0.64  % (31519)Refutation found. Thanks to Tanya!
% 0.38/0.64  % SZS status Theorem for theBenchmark
% 0.38/0.65  % (31523)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.38/0.66  % (31526)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.38/0.66  % SZS output start Proof for theBenchmark
% 0.38/0.66  fof(f405,plain,(
% 0.38/0.66    $false),
% 0.38/0.66    inference(subsumption_resolution,[],[f404,f154])).
% 0.38/0.66  fof(f154,plain,(
% 0.38/0.66    ~v4_pre_topc(sK1,sK0)),
% 0.38/0.66    inference(trivial_inequality_removal,[],[f153])).
% 0.38/0.66  fof(f153,plain,(
% 0.38/0.66    k2_tops_1(sK0,sK1) != k2_tops_1(sK0,sK1) | ~v4_pre_topc(sK1,sK0)),
% 0.38/0.66    inference(backward_demodulation,[],[f49,f152])).
% 0.38/0.66  fof(f152,plain,(
% 0.38/0.66    k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))),
% 0.38/0.66    inference(subsumption_resolution,[],[f151,f48])).
% 0.38/0.66  fof(f48,plain,(
% 0.38/0.66    k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) | v4_pre_topc(sK1,sK0)),
% 0.38/0.66    inference(cnf_transformation,[],[f44])).
% 0.38/0.66  fof(f44,plain,(
% 0.38/0.66    ((k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) | ~v4_pre_topc(sK1,sK0)) & (k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) | v4_pre_topc(sK1,sK0)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0)),
% 0.38/0.66    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f41,f43,f42])).
% 0.38/0.66  fof(f42,plain,(
% 0.38/0.66    ? [X0] : (? [X1] : ((k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) | ~v4_pre_topc(X1,X0)) & (k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) | v4_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0)) => (? [X1] : ((k2_tops_1(sK0,X1) != k7_subset_1(u1_struct_0(sK0),X1,k1_tops_1(sK0,X1)) | ~v4_pre_topc(X1,sK0)) & (k2_tops_1(sK0,X1) = k7_subset_1(u1_struct_0(sK0),X1,k1_tops_1(sK0,X1)) | v4_pre_topc(X1,sK0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0))),
% 0.38/0.66    introduced(choice_axiom,[])).
% 0.38/0.66  fof(f43,plain,(
% 0.38/0.66    ? [X1] : ((k2_tops_1(sK0,X1) != k7_subset_1(u1_struct_0(sK0),X1,k1_tops_1(sK0,X1)) | ~v4_pre_topc(X1,sK0)) & (k2_tops_1(sK0,X1) = k7_subset_1(u1_struct_0(sK0),X1,k1_tops_1(sK0,X1)) | v4_pre_topc(X1,sK0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) => ((k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) | ~v4_pre_topc(sK1,sK0)) & (k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) | v4_pre_topc(sK1,sK0)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.38/0.66    introduced(choice_axiom,[])).
% 0.38/0.66  fof(f41,plain,(
% 0.38/0.66    ? [X0] : (? [X1] : ((k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) | ~v4_pre_topc(X1,X0)) & (k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) | v4_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 0.38/0.66    inference(flattening,[],[f40])).
% 0.38/0.66  fof(f40,plain,(
% 0.38/0.66    ? [X0] : (? [X1] : (((k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) | ~v4_pre_topc(X1,X0)) & (k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) | v4_pre_topc(X1,X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 0.38/0.66    inference(nnf_transformation,[],[f22])).
% 0.38/0.66  fof(f22,plain,(
% 0.38/0.66    ? [X0] : (? [X1] : ((v4_pre_topc(X1,X0) <~> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 0.38/0.66    inference(flattening,[],[f21])).
% 0.38/0.66  fof(f21,plain,(
% 0.38/0.66    ? [X0] : (? [X1] : ((v4_pre_topc(X1,X0) <~> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_pre_topc(X0) & v2_pre_topc(X0)))),
% 0.38/0.66    inference(ennf_transformation,[],[f19])).
% 0.38/0.66  fof(f19,negated_conjecture,(
% 0.38/0.66    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_pre_topc(X1,X0) <=> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)))))),
% 0.38/0.66    inference(negated_conjecture,[],[f18])).
% 0.38/0.66  fof(f18,conjecture,(
% 0.38/0.66    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_pre_topc(X1,X0) <=> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)))))),
% 0.38/0.66    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t77_tops_1)).
% 0.38/0.66  fof(f151,plain,(
% 0.38/0.66    k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) | ~v4_pre_topc(sK1,sK0)),
% 0.38/0.66    inference(subsumption_resolution,[],[f150,f46])).
% 0.38/0.66  fof(f46,plain,(
% 0.38/0.66    l1_pre_topc(sK0)),
% 0.38/0.66    inference(cnf_transformation,[],[f44])).
% 0.38/0.66  fof(f150,plain,(
% 0.38/0.66    k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) | ~l1_pre_topc(sK0) | ~v4_pre_topc(sK1,sK0)),
% 0.38/0.66    inference(subsumption_resolution,[],[f147,f47])).
% 0.38/0.66  fof(f47,plain,(
% 0.38/0.66    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.38/0.66    inference(cnf_transformation,[],[f44])).
% 0.38/0.66  fof(f147,plain,(
% 0.38/0.66    k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~v4_pre_topc(sK1,sK0)),
% 0.38/0.66    inference(superposition,[],[f53,f113])).
% 0.38/0.66  fof(f113,plain,(
% 0.38/0.66    sK1 = k2_pre_topc(sK0,sK1) | ~v4_pre_topc(sK1,sK0)),
% 0.38/0.66    inference(subsumption_resolution,[],[f111,f46])).
% 0.38/0.66  fof(f111,plain,(
% 0.38/0.66    ~v4_pre_topc(sK1,sK0) | sK1 = k2_pre_topc(sK0,sK1) | ~l1_pre_topc(sK0)),
% 0.38/0.66    inference(resolution,[],[f54,f47])).
% 0.38/0.66  fof(f54,plain,(
% 0.38/0.66    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v4_pre_topc(X1,X0) | k2_pre_topc(X0,X1) = X1 | ~l1_pre_topc(X0)) )),
% 0.38/0.66    inference(cnf_transformation,[],[f27])).
% 0.38/0.66  fof(f27,plain,(
% 0.38/0.66    ! [X0] : (! [X1] : (((v4_pre_topc(X1,X0) | k2_pre_topc(X0,X1) != X1 | ~v2_pre_topc(X0)) & (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.38/0.66    inference(flattening,[],[f26])).
% 0.38/0.66  fof(f26,plain,(
% 0.38/0.66    ! [X0] : (! [X1] : (((v4_pre_topc(X1,X0) | (k2_pre_topc(X0,X1) != X1 | ~v2_pre_topc(X0))) & (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.38/0.66    inference(ennf_transformation,[],[f12])).
% 0.38/0.66  fof(f12,axiom,(
% 0.38/0.66    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (((k2_pre_topc(X0,X1) = X1 & v2_pre_topc(X0)) => v4_pre_topc(X1,X0)) & (v4_pre_topc(X1,X0) => k2_pre_topc(X0,X1) = X1))))),
% 0.38/0.66    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_pre_topc)).
% 0.38/0.66  fof(f53,plain,(
% 0.38/0.66    ( ! [X0,X1] : (k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.38/0.66    inference(cnf_transformation,[],[f25])).
% 0.38/0.66  fof(f25,plain,(
% 0.38/0.66    ! [X0] : (! [X1] : (k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.38/0.66    inference(ennf_transformation,[],[f15])).
% 0.38/0.66  fof(f15,axiom,(
% 0.38/0.66    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1))))),
% 0.38/0.66    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l78_tops_1)).
% 0.38/0.66  fof(f49,plain,(
% 0.38/0.66    k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) | ~v4_pre_topc(sK1,sK0)),
% 0.38/0.66    inference(cnf_transformation,[],[f44])).
% 0.38/0.66  fof(f404,plain,(
% 0.38/0.66    v4_pre_topc(sK1,sK0)),
% 0.38/0.66    inference(trivial_inequality_removal,[],[f403])).
% 0.38/0.66  fof(f403,plain,(
% 0.38/0.66    sK1 != sK1 | v4_pre_topc(sK1,sK0)),
% 0.38/0.66    inference(backward_demodulation,[],[f136,f402])).
% 0.38/0.66  fof(f402,plain,(
% 0.38/0.66    sK1 = k2_pre_topc(sK0,sK1)),
% 0.38/0.66    inference(subsumption_resolution,[],[f401,f46])).
% 0.38/0.66  fof(f401,plain,(
% 0.38/0.66    sK1 = k2_pre_topc(sK0,sK1) | ~l1_pre_topc(sK0)),
% 0.38/0.66    inference(subsumption_resolution,[],[f400,f47])).
% 0.38/0.66  fof(f400,plain,(
% 0.38/0.66    sK1 = k2_pre_topc(sK0,sK1) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0)),
% 0.38/0.66    inference(resolution,[],[f375,f51])).
% 0.38/0.66  fof(f51,plain,(
% 0.38/0.66    ( ! [X0,X1] : (r1_tarski(k1_tops_1(X0,X1),X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.38/0.66    inference(cnf_transformation,[],[f23])).
% 0.38/0.66  fof(f23,plain,(
% 0.38/0.66    ! [X0] : (! [X1] : (r1_tarski(k1_tops_1(X0,X1),X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.38/0.66    inference(ennf_transformation,[],[f16])).
% 0.38/0.66  fof(f16,axiom,(
% 0.38/0.66    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => r1_tarski(k1_tops_1(X0,X1),X1)))),
% 0.38/0.66    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_tops_1)).
% 0.38/0.66  fof(f375,plain,(
% 0.38/0.66    ~r1_tarski(k1_tops_1(sK0,sK1),sK1) | sK1 = k2_pre_topc(sK0,sK1)),
% 0.38/0.66    inference(resolution,[],[f358,f65])).
% 0.38/0.66  fof(f65,plain,(
% 0.38/0.66    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 0.38/0.66    inference(cnf_transformation,[],[f36])).
% 0.38/0.66  fof(f36,plain,(
% 0.38/0.66    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1))),
% 0.38/0.66    inference(ennf_transformation,[],[f20])).
% 0.38/0.66  fof(f20,plain,(
% 0.38/0.66    ! [X0,X1] : (r1_tarski(X0,X1) => m1_subset_1(X0,k1_zfmisc_1(X1)))),
% 0.38/0.66    inference(unused_predicate_definition_removal,[],[f11])).
% 0.38/0.66  fof(f11,axiom,(
% 0.38/0.66    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.38/0.66    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).
% 0.38/0.66  fof(f358,plain,(
% 0.38/0.66    ~m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(sK1)) | sK1 = k2_pre_topc(sK0,sK1)),
% 0.38/0.66    inference(subsumption_resolution,[],[f357,f46])).
% 0.38/0.66  fof(f357,plain,(
% 0.38/0.66    sK1 = k2_pre_topc(sK0,sK1) | ~m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(sK1)) | ~l1_pre_topc(sK0)),
% 0.38/0.66    inference(subsumption_resolution,[],[f353,f47])).
% 0.38/0.66  fof(f353,plain,(
% 0.38/0.66    sK1 = k2_pre_topc(sK0,sK1) | ~m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(sK1)) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0)),
% 0.38/0.66    inference(superposition,[],[f340,f142])).
% 0.38/0.66  fof(f142,plain,(
% 0.38/0.66    ( ! [X2,X3] : (k2_xboole_0(X3,k2_tops_1(X2,X3)) = k2_pre_topc(X2,X3) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) | ~l1_pre_topc(X2)) )),
% 0.38/0.66    inference(subsumption_resolution,[],[f141,f64])).
% 0.38/0.66  fof(f64,plain,(
% 0.38/0.66    ( ! [X0,X1] : (m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.38/0.66    inference(cnf_transformation,[],[f35])).
% 0.38/0.66  fof(f35,plain,(
% 0.38/0.66    ! [X0,X1] : (m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 0.38/0.66    inference(flattening,[],[f34])).
% 0.38/0.66  fof(f34,plain,(
% 0.38/0.66    ! [X0,X1] : (m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 0.38/0.66    inference(ennf_transformation,[],[f13])).
% 0.38/0.66  fof(f13,axiom,(
% 0.38/0.66    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 0.38/0.66    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_tops_1)).
% 0.38/0.66  fof(f141,plain,(
% 0.38/0.66    ( ! [X2,X3] : (k2_xboole_0(X3,k2_tops_1(X2,X3)) = k2_pre_topc(X2,X3) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) | ~l1_pre_topc(X2) | ~m1_subset_1(k2_tops_1(X2,X3),k1_zfmisc_1(u1_struct_0(X2)))) )),
% 0.38/0.66    inference(duplicate_literal_removal,[],[f138])).
% 0.38/0.66  fof(f138,plain,(
% 0.38/0.66    ( ! [X2,X3] : (k2_xboole_0(X3,k2_tops_1(X2,X3)) = k2_pre_topc(X2,X3) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) | ~l1_pre_topc(X2) | ~m1_subset_1(k2_tops_1(X2,X3),k1_zfmisc_1(u1_struct_0(X2))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))) )),
% 0.38/0.66    inference(superposition,[],[f52,f67])).
% 0.38/0.66  fof(f67,plain,(
% 0.38/0.66    ( ! [X2,X0,X1] : (k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.38/0.66    inference(cnf_transformation,[],[f39])).
% 0.38/0.66  fof(f39,plain,(
% 0.38/0.66    ! [X0,X1,X2] : (k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.38/0.66    inference(flattening,[],[f38])).
% 0.38/0.66  fof(f38,plain,(
% 0.38/0.66    ! [X0,X1,X2] : (k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) | (~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))))),
% 0.38/0.66    inference(ennf_transformation,[],[f8])).
% 0.38/0.66  fof(f8,axiom,(
% 0.38/0.66    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2))),
% 0.38/0.66    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k4_subset_1)).
% 0.38/0.66  fof(f52,plain,(
% 0.38/0.66    ( ! [X0,X1] : (k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.38/0.66    inference(cnf_transformation,[],[f24])).
% 0.38/0.66  fof(f24,plain,(
% 0.38/0.66    ! [X0] : (! [X1] : (k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.38/0.66    inference(ennf_transformation,[],[f17])).
% 0.38/0.66  fof(f17,axiom,(
% 0.38/0.66    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))))),
% 0.38/0.66    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_tops_1)).
% 0.38/0.66  fof(f340,plain,(
% 0.38/0.66    sK1 = k2_xboole_0(sK1,k2_tops_1(sK0,sK1)) | ~m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(sK1))),
% 0.38/0.66    inference(duplicate_literal_removal,[],[f335])).
% 0.38/0.66  fof(f335,plain,(
% 0.38/0.66    sK1 = k2_xboole_0(sK1,k2_tops_1(sK0,sK1)) | ~m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(sK1)) | ~m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(sK1))),
% 0.38/0.66    inference(superposition,[],[f213,f212])).
% 0.38/0.66  fof(f212,plain,(
% 0.38/0.66    sK1 = k2_xboole_0(sK1,k1_tops_1(sK0,sK1)) | ~m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(sK1))),
% 0.38/0.66    inference(subsumption_resolution,[],[f210,f184])).
% 0.38/0.66  fof(f184,plain,(
% 0.38/0.66    m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(sK1)) | ~m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(sK1))),
% 0.38/0.66    inference(superposition,[],[f71,f169])).
% 0.38/0.66  fof(f169,plain,(
% 0.38/0.66    k2_tops_1(sK0,sK1) = k4_xboole_0(sK1,k1_tops_1(sK0,sK1))),
% 0.38/0.66    inference(subsumption_resolution,[],[f167,f47])).
% 0.38/0.66  fof(f167,plain,(
% 0.38/0.66    k2_tops_1(sK0,sK1) = k4_xboole_0(sK1,k1_tops_1(sK0,sK1)) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.38/0.66    inference(superposition,[],[f152,f66])).
% 0.38/0.66  fof(f66,plain,(
% 0.38/0.66    ( ! [X2,X0,X1] : (k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.38/0.66    inference(cnf_transformation,[],[f37])).
% 0.38/0.66  fof(f37,plain,(
% 0.38/0.66    ! [X0,X1,X2] : (k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.38/0.66    inference(ennf_transformation,[],[f9])).
% 0.38/0.66  fof(f9,axiom,(
% 0.38/0.66    ! [X0,X1,X2] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2))),
% 0.38/0.66    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_subset_1)).
% 0.38/0.66  fof(f71,plain,(
% 0.38/0.66    ( ! [X0,X1] : (m1_subset_1(k4_xboole_0(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.38/0.66    inference(duplicate_literal_removal,[],[f70])).
% 0.38/0.66  fof(f70,plain,(
% 0.38/0.66    ( ! [X0,X1] : (m1_subset_1(k4_xboole_0(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.38/0.66    inference(superposition,[],[f59,f60])).
% 0.38/0.66  fof(f60,plain,(
% 0.38/0.66    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.38/0.66    inference(cnf_transformation,[],[f29])).
% 0.38/0.66  fof(f29,plain,(
% 0.38/0.66    ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.38/0.66    inference(ennf_transformation,[],[f5])).
% 0.38/0.66  fof(f5,axiom,(
% 0.38/0.66    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1))),
% 0.38/0.66    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).
% 0.38/0.66  fof(f59,plain,(
% 0.38/0.66    ( ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.38/0.66    inference(cnf_transformation,[],[f28])).
% 0.38/0.66  fof(f28,plain,(
% 0.38/0.66    ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.38/0.66    inference(ennf_transformation,[],[f6])).
% 0.38/0.66  fof(f6,axiom,(
% 0.38/0.66    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)))),
% 0.38/0.66    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_subset_1)).
% 0.38/0.66  fof(f210,plain,(
% 0.38/0.66    sK1 = k2_xboole_0(sK1,k1_tops_1(sK0,sK1)) | ~m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(sK1)) | ~m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(sK1))),
% 0.38/0.66    inference(backward_demodulation,[],[f166,f206])).
% 0.38/0.66  fof(f206,plain,(
% 0.38/0.66    k2_xboole_0(k2_tops_1(sK0,sK1),k1_tops_1(sK0,sK1)) = k2_xboole_0(sK1,k1_tops_1(sK0,sK1))),
% 0.38/0.66    inference(superposition,[],[f186,f56])).
% 0.38/0.66  fof(f56,plain,(
% 0.38/0.66    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 0.38/0.66    inference(cnf_transformation,[],[f1])).
% 0.38/0.66  fof(f1,axiom,(
% 0.38/0.66    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 0.38/0.66    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).
% 0.38/0.66  fof(f186,plain,(
% 0.38/0.66    k2_xboole_0(k1_tops_1(sK0,sK1),k2_tops_1(sK0,sK1)) = k2_xboole_0(sK1,k1_tops_1(sK0,sK1))),
% 0.38/0.66    inference(forward_demodulation,[],[f185,f56])).
% 0.38/0.66  fof(f185,plain,(
% 0.38/0.66    k2_xboole_0(k1_tops_1(sK0,sK1),sK1) = k2_xboole_0(k1_tops_1(sK0,sK1),k2_tops_1(sK0,sK1))),
% 0.38/0.66    inference(superposition,[],[f58,f169])).
% 0.38/0.66  fof(f58,plain,(
% 0.38/0.66    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 0.38/0.66    inference(cnf_transformation,[],[f3])).
% 0.38/0.66  fof(f3,axiom,(
% 0.38/0.66    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))),
% 0.38/0.66    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).
% 0.38/0.66  fof(f166,plain,(
% 0.38/0.66    sK1 = k2_xboole_0(k2_tops_1(sK0,sK1),k1_tops_1(sK0,sK1)) | ~m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(sK1)) | ~m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(sK1))),
% 0.38/0.66    inference(subsumption_resolution,[],[f158,f154])).
% 0.38/0.66  fof(f158,plain,(
% 0.38/0.66    sK1 = k2_xboole_0(k2_tops_1(sK0,sK1),k1_tops_1(sK0,sK1)) | ~m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(sK1)) | ~m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(sK1)) | v4_pre_topc(sK1,sK0)),
% 0.38/0.66    inference(superposition,[],[f119,f95])).
% 0.38/0.66  fof(f95,plain,(
% 0.38/0.66    k1_tops_1(sK0,sK1) = k3_subset_1(sK1,k2_tops_1(sK0,sK1)) | ~m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(sK1)) | v4_pre_topc(sK1,sK0)),
% 0.38/0.66    inference(superposition,[],[f76,f93])).
% 0.38/0.66  fof(f93,plain,(
% 0.38/0.66    k2_tops_1(sK0,sK1) = k4_xboole_0(sK1,k1_tops_1(sK0,sK1)) | v4_pre_topc(sK1,sK0)),
% 0.38/0.66    inference(subsumption_resolution,[],[f90,f47])).
% 0.38/0.66  fof(f90,plain,(
% 0.38/0.66    k2_tops_1(sK0,sK1) = k4_xboole_0(sK1,k1_tops_1(sK0,sK1)) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | v4_pre_topc(sK1,sK0)),
% 0.38/0.66    inference(superposition,[],[f66,f48])).
% 0.38/0.66  fof(f76,plain,(
% 0.38/0.66    ( ! [X0,X1] : (k3_subset_1(X0,k4_xboole_0(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.38/0.66    inference(duplicate_literal_removal,[],[f72])).
% 0.38/0.66  fof(f72,plain,(
% 0.38/0.66    ( ! [X0,X1] : (k3_subset_1(X0,k4_xboole_0(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.38/0.66    inference(superposition,[],[f61,f60])).
% 0.38/0.66  fof(f61,plain,(
% 0.38/0.66    ( ! [X0,X1] : (k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.38/0.66    inference(cnf_transformation,[],[f30])).
% 0.38/0.66  fof(f30,plain,(
% 0.38/0.66    ! [X0,X1] : (k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.38/0.66    inference(ennf_transformation,[],[f7])).
% 0.38/0.66  fof(f7,axiom,(
% 0.38/0.66    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1)),
% 0.38/0.66    file('/export/starexec/sandbox/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).
% 0.38/0.66  fof(f119,plain,(
% 0.38/0.66    ( ! [X0,X1] : (k2_xboole_0(X1,k3_subset_1(X0,X1)) = X0 | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.38/0.66    inference(subsumption_resolution,[],[f118,f59])).
% 0.38/0.66  fof(f118,plain,(
% 0.38/0.66    ( ! [X0,X1] : (k2_xboole_0(X1,k3_subset_1(X0,X1)) = X0 | ~m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.38/0.66    inference(duplicate_literal_removal,[],[f115])).
% 0.38/0.66  fof(f115,plain,(
% 0.38/0.66    ( ! [X0,X1] : (k2_xboole_0(X1,k3_subset_1(X0,X1)) = X0 | ~m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.38/0.66    inference(superposition,[],[f67,f68])).
% 0.38/0.66  fof(f68,plain,(
% 0.38/0.66    ( ! [X0,X1] : (k4_subset_1(X0,X1,k3_subset_1(X0,X1)) = X0 | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.38/0.66    inference(forward_demodulation,[],[f62,f50])).
% 0.38/0.66  fof(f50,plain,(
% 0.38/0.66    ( ! [X0] : (k2_subset_1(X0) = X0) )),
% 0.38/0.66    inference(cnf_transformation,[],[f4])).
% 0.38/0.66  fof(f4,axiom,(
% 0.38/0.66    ! [X0] : k2_subset_1(X0) = X0),
% 0.38/0.66    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).
% 0.38/0.66  fof(f62,plain,(
% 0.38/0.66    ( ! [X0,X1] : (k2_subset_1(X0) = k4_subset_1(X0,X1,k3_subset_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.38/0.66    inference(cnf_transformation,[],[f31])).
% 0.38/0.66  fof(f31,plain,(
% 0.38/0.66    ! [X0,X1] : (k2_subset_1(X0) = k4_subset_1(X0,X1,k3_subset_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.38/0.66    inference(ennf_transformation,[],[f10])).
% 0.38/0.66  fof(f10,axiom,(
% 0.38/0.66    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k2_subset_1(X0) = k4_subset_1(X0,X1,k3_subset_1(X0,X1)))),
% 0.38/0.66    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t25_subset_1)).
% 0.38/0.66  fof(f213,plain,(
% 0.38/0.66    k2_xboole_0(sK1,k1_tops_1(sK0,sK1)) = k2_xboole_0(sK1,k2_tops_1(sK0,sK1)) | ~m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(sK1))),
% 0.38/0.66    inference(subsumption_resolution,[],[f211,f154])).
% 0.38/0.66  fof(f211,plain,(
% 0.38/0.66    k2_xboole_0(sK1,k1_tops_1(sK0,sK1)) = k2_xboole_0(sK1,k2_tops_1(sK0,sK1)) | ~m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(sK1)) | v4_pre_topc(sK1,sK0)),
% 0.38/0.66    inference(backward_demodulation,[],[f146,f206])).
% 0.38/0.66  fof(f146,plain,(
% 0.38/0.66    k2_xboole_0(k2_tops_1(sK0,sK1),k1_tops_1(sK0,sK1)) = k2_xboole_0(sK1,k2_tops_1(sK0,sK1)) | ~m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(sK1)) | v4_pre_topc(sK1,sK0)),
% 0.38/0.66    inference(forward_demodulation,[],[f145,f56])).
% 0.38/0.66  fof(f145,plain,(
% 0.38/0.66    k2_xboole_0(k2_tops_1(sK0,sK1),k1_tops_1(sK0,sK1)) = k2_xboole_0(k2_tops_1(sK0,sK1),sK1) | ~m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(sK1)) | v4_pre_topc(sK1,sK0)),
% 0.38/0.66    inference(superposition,[],[f58,f126])).
% 0.38/0.66  fof(f126,plain,(
% 0.38/0.66    k1_tops_1(sK0,sK1) = k4_xboole_0(sK1,k2_tops_1(sK0,sK1)) | ~m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(sK1)) | v4_pre_topc(sK1,sK0)),
% 0.38/0.66    inference(subsumption_resolution,[],[f120,f96])).
% 0.38/0.66  fof(f96,plain,(
% 0.38/0.66    m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(sK1)) | ~m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(sK1)) | v4_pre_topc(sK1,sK0)),
% 0.38/0.66    inference(superposition,[],[f71,f93])).
% 0.38/0.66  fof(f120,plain,(
% 0.38/0.66    k1_tops_1(sK0,sK1) = k4_xboole_0(sK1,k2_tops_1(sK0,sK1)) | ~m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(sK1)) | v4_pre_topc(sK1,sK0) | ~m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(sK1))),
% 0.38/0.66    inference(superposition,[],[f95,f60])).
% 0.38/0.66  fof(f136,plain,(
% 0.38/0.66    sK1 != k2_pre_topc(sK0,sK1) | v4_pre_topc(sK1,sK0)),
% 0.38/0.66    inference(subsumption_resolution,[],[f135,f46])).
% 0.38/0.66  fof(f135,plain,(
% 0.38/0.66    sK1 != k2_pre_topc(sK0,sK1) | v4_pre_topc(sK1,sK0) | ~l1_pre_topc(sK0)),
% 0.38/0.66    inference(subsumption_resolution,[],[f133,f45])).
% 0.38/0.66  fof(f45,plain,(
% 0.38/0.66    v2_pre_topc(sK0)),
% 0.38/0.66    inference(cnf_transformation,[],[f44])).
% 0.38/0.66  fof(f133,plain,(
% 0.38/0.66    sK1 != k2_pre_topc(sK0,sK1) | ~v2_pre_topc(sK0) | v4_pre_topc(sK1,sK0) | ~l1_pre_topc(sK0)),
% 0.38/0.66    inference(resolution,[],[f55,f47])).
% 0.38/0.66  fof(f55,plain,(
% 0.38/0.66    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | k2_pre_topc(X0,X1) != X1 | ~v2_pre_topc(X0) | v4_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 0.38/0.66    inference(cnf_transformation,[],[f27])).
% 0.38/0.66  % SZS output end Proof for theBenchmark
% 0.38/0.66  % (31519)------------------------------
% 0.38/0.66  % (31519)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.38/0.66  % (31519)Termination reason: Refutation
% 0.38/0.66  
% 0.38/0.66  % (31519)Memory used [KB]: 1791
% 0.38/0.66  % (31519)Time elapsed: 0.066 s
% 0.38/0.66  % (31519)------------------------------
% 0.38/0.66  % (31519)------------------------------
% 0.38/0.66  % (31381)Success in time 0.302 s
%------------------------------------------------------------------------------
