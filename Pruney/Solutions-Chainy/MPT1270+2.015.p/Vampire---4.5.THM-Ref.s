%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:12:37 EST 2020

% Result     : Theorem 2.40s
% Output     : Refutation 2.40s
% Verified   : 
% Statistics : Number of formulae       :  119 (2381 expanded)
%              Number of leaves         :   17 ( 651 expanded)
%              Depth                    :   33
%              Number of atoms          :  407 (12827 expanded)
%              Number of equality atoms :   77 (1102 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2491,plain,(
    $false ),
    inference(subsumption_resolution,[],[f2490,f51])).

fof(f51,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,
    ( ( ~ r1_tarski(sK1,k2_tops_1(sK0,sK1))
      | ~ v2_tops_1(sK1,sK0) )
    & ( r1_tarski(sK1,k2_tops_1(sK0,sK1))
      | v2_tops_1(sK1,sK0) )
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f34,f36,f35])).

fof(f35,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ( ~ r1_tarski(X1,k2_tops_1(X0,X1))
              | ~ v2_tops_1(X1,X0) )
            & ( r1_tarski(X1,k2_tops_1(X0,X1))
              | v2_tops_1(X1,X0) )
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_pre_topc(X0) )
   => ( ? [X1] :
          ( ( ~ r1_tarski(X1,k2_tops_1(sK0,X1))
            | ~ v2_tops_1(X1,sK0) )
          & ( r1_tarski(X1,k2_tops_1(sK0,X1))
            | v2_tops_1(X1,sK0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
      & l1_pre_topc(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,
    ( ? [X1] :
        ( ( ~ r1_tarski(X1,k2_tops_1(sK0,X1))
          | ~ v2_tops_1(X1,sK0) )
        & ( r1_tarski(X1,k2_tops_1(sK0,X1))
          | v2_tops_1(X1,sK0) )
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
   => ( ( ~ r1_tarski(sK1,k2_tops_1(sK0,sK1))
        | ~ v2_tops_1(sK1,sK0) )
      & ( r1_tarski(sK1,k2_tops_1(sK0,sK1))
        | v2_tops_1(sK1,sK0) )
      & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ~ r1_tarski(X1,k2_tops_1(X0,X1))
            | ~ v2_tops_1(X1,X0) )
          & ( r1_tarski(X1,k2_tops_1(X0,X1))
            | v2_tops_1(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(flattening,[],[f33])).

fof(f33,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ~ r1_tarski(X1,k2_tops_1(X0,X1))
            | ~ v2_tops_1(X1,X0) )
          & ( r1_tarski(X1,k2_tops_1(X0,X1))
            | v2_tops_1(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f23])).

fof(f23,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v2_tops_1(X1,X0)
          <~> r1_tarski(X1,k2_tops_1(X0,X1)) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,negated_conjecture,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( v2_tops_1(X1,X0)
            <=> r1_tarski(X1,k2_tops_1(X0,X1)) ) ) ) ),
    inference(negated_conjecture,[],[f21])).

fof(f21,conjecture,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v2_tops_1(X1,X0)
          <=> r1_tarski(X1,k2_tops_1(X0,X1)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t88_tops_1)).

fof(f2490,plain,(
    ~ l1_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f2489,f52])).

fof(f52,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f37])).

fof(f2489,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f2488,f1710])).

fof(f1710,plain,(
    ~ v2_tops_1(sK1,sK0) ),
    inference(subsumption_resolution,[],[f1628,f90])).

fof(f90,plain,(
    r1_tarski(sK1,k2_pre_topc(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f84,f51])).

fof(f84,plain,
    ( r1_tarski(sK1,k2_pre_topc(sK0,sK1))
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f52,f58])).

fof(f58,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | r1_tarski(X1,k2_pre_topc(X0,X1))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(X1,k2_pre_topc(X0,X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => r1_tarski(X1,k2_pre_topc(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_pre_topc)).

fof(f1628,plain,
    ( ~ r1_tarski(sK1,k2_pre_topc(sK0,sK1))
    | ~ v2_tops_1(sK1,sK0) ),
    inference(backward_demodulation,[],[f54,f1626])).

fof(f1626,plain,(
    k2_tops_1(sK0,sK1) = k2_pre_topc(sK0,sK1) ),
    inference(forward_demodulation,[],[f1255,f74])).

fof(f74,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

fof(f1255,plain,(
    k2_tops_1(sK0,sK1) = k4_xboole_0(k2_pre_topc(sK0,sK1),k1_xboole_0) ),
    inference(backward_demodulation,[],[f130,f1238])).

fof(f1238,plain,(
    k1_xboole_0 = k1_tops_1(sK0,sK1) ),
    inference(subsumption_resolution,[],[f1237,f1177])).

fof(f1177,plain,
    ( r2_hidden(sK4(k1_xboole_0,k1_tops_1(sK0,sK1)),k1_xboole_0)
    | k1_xboole_0 = k1_tops_1(sK0,sK1) ),
    inference(duplicate_literal_removal,[],[f1174])).

fof(f1174,plain,
    ( k1_xboole_0 = k1_tops_1(sK0,sK1)
    | r2_hidden(sK4(k1_xboole_0,k1_tops_1(sK0,sK1)),k1_xboole_0)
    | k1_xboole_0 = k1_tops_1(sK0,sK1) ),
    inference(resolution,[],[f1149,f128])).

fof(f128,plain,(
    ! [X5] :
      ( ~ r2_hidden(sK4(X5,k1_tops_1(sK0,sK1)),k2_tops_1(sK0,sK1))
      | r2_hidden(sK4(X5,k1_tops_1(sK0,sK1)),X5)
      | k1_tops_1(sK0,sK1) = X5 ) ),
    inference(resolution,[],[f117,f72])).

fof(f72,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK4(X0,X1),X1)
      | r2_hidden(sK4(X0,X1),X0)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ( ( ~ r2_hidden(sK4(X0,X1),X1)
          | ~ r2_hidden(sK4(X0,X1),X0) )
        & ( r2_hidden(sK4(X0,X1),X1)
          | r2_hidden(sK4(X0,X1),X0) ) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f48,f49])).

fof(f49,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
          & ( r2_hidden(X2,X1)
            | r2_hidden(X2,X0) ) )
     => ( ( ~ r2_hidden(sK4(X0,X1),X1)
          | ~ r2_hidden(sK4(X0,X1),X0) )
        & ( r2_hidden(sK4(X0,X1),X1)
          | r2_hidden(sK4(X0,X1),X0) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f48,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ? [X2] :
          ( ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
          & ( r2_hidden(X2,X1)
            | r2_hidden(X2,X0) ) ) ) ),
    inference(nnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ? [X2] :
          ( r2_hidden(X2,X0)
        <~> r2_hidden(X2,X1) ) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
        <=> r2_hidden(X2,X1) )
     => X0 = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_tarski)).

fof(f117,plain,(
    ! [X1] :
      ( ~ r2_hidden(X1,k1_tops_1(sK0,sK1))
      | ~ r2_hidden(X1,k2_tops_1(sK0,sK1)) ) ),
    inference(superposition,[],[f78,f114])).

fof(f114,plain,(
    k1_tops_1(sK0,sK1) = k4_xboole_0(sK1,k2_tops_1(sK0,sK1)) ),
    inference(superposition,[],[f88,f85])).

fof(f85,plain,(
    ! [X0] : k7_subset_1(u1_struct_0(sK0),sK1,X0) = k4_xboole_0(sK1,X0) ),
    inference(resolution,[],[f52,f64])).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

fof(f88,plain,(
    k1_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f82,f51])).

fof(f82,plain,
    ( k1_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1))
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f52,f61])).

fof(f61,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_tops_1)).

fof(f78,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,k4_xboole_0(X0,X1))
      | ~ r2_hidden(X4,X1) ) ),
    inference(equality_resolution,[],[f67])).

fof(f67,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ( ( r2_hidden(sK3(X0,X1,X2),X1)
            | ~ r2_hidden(sK3(X0,X1,X2),X0)
            | ~ r2_hidden(sK3(X0,X1,X2),X2) )
          & ( ( ~ r2_hidden(sK3(X0,X1,X2),X1)
              & r2_hidden(sK3(X0,X1,X2),X0) )
            | r2_hidden(sK3(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( ~ r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f45,f46])).

fof(f46,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X3,X2) )
          & ( ( ~ r2_hidden(X3,X1)
              & r2_hidden(X3,X0) )
            | r2_hidden(X3,X2) ) )
     => ( ( r2_hidden(sK3(X0,X1,X2),X1)
          | ~ r2_hidden(sK3(X0,X1,X2),X0)
          | ~ r2_hidden(sK3(X0,X1,X2),X2) )
        & ( ( ~ r2_hidden(sK3(X0,X1,X2),X1)
            & r2_hidden(sK3(X0,X1,X2),X0) )
          | r2_hidden(sK3(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f45,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( ~ r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f44])).

fof(f44,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(flattening,[],[f43])).

fof(f43,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( ~ r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).

fof(f1149,plain,
    ( r2_hidden(sK4(k1_xboole_0,k1_tops_1(sK0,sK1)),k2_tops_1(sK0,sK1))
    | k1_xboole_0 = k1_tops_1(sK0,sK1) ),
    inference(subsumption_resolution,[],[f1148,f498])).

fof(f498,plain,(
    ! [X33,X34] :
      ( k1_xboole_0 = k1_tops_1(sK0,sK1)
      | r2_hidden(sK4(X33,k1_tops_1(sK0,sK1)),X34)
      | r2_hidden(sK4(X33,k1_tops_1(sK0,sK1)),X33)
      | k1_tops_1(sK0,sK1) = X33 ) ),
    inference(subsumption_resolution,[],[f488,f128])).

fof(f488,plain,(
    ! [X33,X34] :
      ( k1_xboole_0 = k1_tops_1(sK0,sK1)
      | r2_hidden(sK4(X33,k1_tops_1(sK0,sK1)),X34)
      | r2_hidden(sK4(X33,k1_tops_1(sK0,sK1)),k2_tops_1(sK0,sK1))
      | r2_hidden(sK4(X33,k1_tops_1(sK0,sK1)),X33)
      | k1_tops_1(sK0,sK1) = X33 ) ),
    inference(resolution,[],[f234,f123])).

fof(f123,plain,(
    ! [X5] :
      ( r2_hidden(sK4(X5,k1_tops_1(sK0,sK1)),sK1)
      | r2_hidden(sK4(X5,k1_tops_1(sK0,sK1)),X5)
      | k1_tops_1(sK0,sK1) = X5 ) ),
    inference(resolution,[],[f116,f72])).

fof(f116,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k1_tops_1(sK0,sK1))
      | r2_hidden(X0,sK1) ) ),
    inference(superposition,[],[f79,f114])).

fof(f79,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,k4_xboole_0(X0,X1))
      | r2_hidden(X4,X0) ) ),
    inference(equality_resolution,[],[f66])).

fof(f66,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f47])).

fof(f234,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,sK1)
      | k1_xboole_0 = k1_tops_1(sK0,sK1)
      | r2_hidden(X0,X1)
      | r2_hidden(X0,k2_tops_1(sK0,sK1)) ) ),
    inference(resolution,[],[f218,f158])).

fof(f158,plain,(
    ! [X2,X3] :
      ( ~ r1_tarski(k1_tops_1(sK0,sK1),X3)
      | ~ r2_hidden(X2,sK1)
      | r2_hidden(X2,X3)
      | r2_hidden(X2,k2_tops_1(sK0,sK1)) ) ),
    inference(resolution,[],[f118,f55])).

fof(f55,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,X0)
      | r2_hidden(X3,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK2(X0,X1),X1)
          & r2_hidden(sK2(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f39,f40])).

fof(f40,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK2(X0,X1),X1)
        & r2_hidden(sK2(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(f118,plain,(
    ! [X2] :
      ( r2_hidden(X2,k1_tops_1(sK0,sK1))
      | r2_hidden(X2,k2_tops_1(sK0,sK1))
      | ~ r2_hidden(X2,sK1) ) ),
    inference(superposition,[],[f77,f114])).

fof(f77,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k4_xboole_0(X0,X1))
      | r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0) ) ),
    inference(equality_resolution,[],[f68])).

fof(f68,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f47])).

fof(f218,plain,(
    ! [X0] :
      ( r1_tarski(k1_tops_1(sK0,sK1),X0)
      | k1_xboole_0 = k1_tops_1(sK0,sK1) ) ),
    inference(resolution,[],[f212,f102])).

fof(f102,plain,
    ( r1_tarski(sK1,k2_tops_1(sK0,sK1))
    | k1_xboole_0 = k1_tops_1(sK0,sK1) ),
    inference(resolution,[],[f87,f53])).

fof(f53,plain,
    ( v2_tops_1(sK1,sK0)
    | r1_tarski(sK1,k2_tops_1(sK0,sK1)) ),
    inference(cnf_transformation,[],[f37])).

fof(f87,plain,
    ( ~ v2_tops_1(sK1,sK0)
    | k1_xboole_0 = k1_tops_1(sK0,sK1) ),
    inference(subsumption_resolution,[],[f81,f51])).

fof(f81,plain,
    ( ~ v2_tops_1(sK1,sK0)
    | k1_xboole_0 = k1_tops_1(sK0,sK1)
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f52,f62])).

fof(f62,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v2_tops_1(X1,X0)
      | k1_xboole_0 = k1_tops_1(X0,X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v2_tops_1(X1,X0)
              | k1_xboole_0 != k1_tops_1(X0,X1) )
            & ( k1_xboole_0 = k1_tops_1(X0,X1)
              | ~ v2_tops_1(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_tops_1(X1,X0)
          <=> k1_xboole_0 = k1_tops_1(X0,X1) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v2_tops_1(X1,X0)
          <=> k1_xboole_0 = k1_tops_1(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t84_tops_1)).

fof(f212,plain,(
    ! [X11] :
      ( ~ r1_tarski(sK1,k2_tops_1(sK0,sK1))
      | r1_tarski(k1_tops_1(sK0,sK1),X11) ) ),
    inference(duplicate_literal_removal,[],[f206])).

fof(f206,plain,(
    ! [X11] :
      ( r1_tarski(k1_tops_1(sK0,sK1),X11)
      | ~ r1_tarski(sK1,k2_tops_1(sK0,sK1))
      | r1_tarski(k1_tops_1(sK0,sK1),X11) ) ),
    inference(resolution,[],[f154,f125])).

fof(f125,plain,(
    ! [X0] :
      ( ~ r2_hidden(sK2(k1_tops_1(sK0,sK1),X0),k2_tops_1(sK0,sK1))
      | r1_tarski(k1_tops_1(sK0,sK1),X0) ) ),
    inference(resolution,[],[f117,f56])).

fof(f56,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK2(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f154,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK2(k1_tops_1(sK0,sK1),X0),X1)
      | r1_tarski(k1_tops_1(sK0,sK1),X0)
      | ~ r1_tarski(sK1,X1) ) ),
    inference(resolution,[],[f120,f55])).

fof(f120,plain,(
    ! [X0] :
      ( r2_hidden(sK2(k1_tops_1(sK0,sK1),X0),sK1)
      | r1_tarski(k1_tops_1(sK0,sK1),X0) ) ),
    inference(resolution,[],[f116,f56])).

fof(f1148,plain,
    ( k1_xboole_0 = k1_tops_1(sK0,sK1)
    | r2_hidden(sK4(k1_xboole_0,k1_tops_1(sK0,sK1)),k2_tops_1(sK0,sK1))
    | ~ r2_hidden(sK4(k1_xboole_0,k1_tops_1(sK0,sK1)),k1_xboole_0) ),
    inference(duplicate_literal_removal,[],[f1143])).

fof(f1143,plain,
    ( k1_xboole_0 = k1_tops_1(sK0,sK1)
    | r2_hidden(sK4(k1_xboole_0,k1_tops_1(sK0,sK1)),k2_tops_1(sK0,sK1))
    | k1_xboole_0 = k1_tops_1(sK0,sK1)
    | ~ r2_hidden(sK4(k1_xboole_0,k1_tops_1(sK0,sK1)),k1_xboole_0) ),
    inference(resolution,[],[f1100,f161])).

fof(f161,plain,(
    ! [X7] :
      ( ~ r2_hidden(sK4(X7,k1_tops_1(sK0,sK1)),sK1)
      | r2_hidden(sK4(X7,k1_tops_1(sK0,sK1)),k2_tops_1(sK0,sK1))
      | k1_tops_1(sK0,sK1) = X7
      | ~ r2_hidden(sK4(X7,k1_tops_1(sK0,sK1)),X7) ) ),
    inference(resolution,[],[f118,f73])).

fof(f73,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK4(X0,X1),X1)
      | X0 = X1
      | ~ r2_hidden(sK4(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f1100,plain,
    ( r2_hidden(sK4(k1_xboole_0,k1_tops_1(sK0,sK1)),sK1)
    | k1_xboole_0 = k1_tops_1(sK0,sK1) ),
    inference(superposition,[],[f1093,f74])).

fof(f1093,plain,(
    ! [X1] :
      ( r2_hidden(sK4(k4_xboole_0(X1,X1),k1_tops_1(sK0,sK1)),sK1)
      | k1_tops_1(sK0,sK1) = k4_xboole_0(X1,X1) ) ),
    inference(duplicate_literal_removal,[],[f1070])).

fof(f1070,plain,(
    ! [X1] :
      ( k1_tops_1(sK0,sK1) = k4_xboole_0(X1,X1)
      | r2_hidden(sK4(k4_xboole_0(X1,X1),k1_tops_1(sK0,sK1)),sK1)
      | r2_hidden(sK4(k4_xboole_0(X1,X1),k1_tops_1(sK0,sK1)),sK1)
      | k1_tops_1(sK0,sK1) = k4_xboole_0(X1,X1) ) ),
    inference(resolution,[],[f223,f222])).

fof(f222,plain,(
    ! [X2,X3] :
      ( r2_hidden(sK4(k4_xboole_0(X2,X3),k1_tops_1(sK0,sK1)),sK1)
      | r2_hidden(sK4(k4_xboole_0(X2,X3),k1_tops_1(sK0,sK1)),X2)
      | k1_tops_1(sK0,sK1) = k4_xboole_0(X2,X3) ) ),
    inference(resolution,[],[f123,f79])).

fof(f223,plain,(
    ! [X4,X5] :
      ( ~ r2_hidden(sK4(k4_xboole_0(X4,X5),k1_tops_1(sK0,sK1)),X5)
      | k1_tops_1(sK0,sK1) = k4_xboole_0(X4,X5)
      | r2_hidden(sK4(k4_xboole_0(X4,X5),k1_tops_1(sK0,sK1)),sK1) ) ),
    inference(resolution,[],[f123,f78])).

fof(f1237,plain,
    ( k1_xboole_0 = k1_tops_1(sK0,sK1)
    | ~ r2_hidden(sK4(k1_xboole_0,k1_tops_1(sK0,sK1)),k1_xboole_0) ),
    inference(duplicate_literal_removal,[],[f1216])).

fof(f1216,plain,
    ( k1_xboole_0 = k1_tops_1(sK0,sK1)
    | k1_xboole_0 = k1_tops_1(sK0,sK1)
    | ~ r2_hidden(sK4(k1_xboole_0,k1_tops_1(sK0,sK1)),k1_xboole_0) ),
    inference(resolution,[],[f1189,f73])).

fof(f1189,plain,(
    ! [X0] :
      ( r2_hidden(sK4(k1_xboole_0,k1_tops_1(sK0,sK1)),X0)
      | k1_xboole_0 = k1_tops_1(sK0,sK1) ) ),
    inference(subsumption_resolution,[],[f1188,f59])).

fof(f59,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f1188,plain,(
    ! [X0] :
      ( k1_xboole_0 = k1_tops_1(sK0,sK1)
      | r2_hidden(sK4(k1_xboole_0,k1_tops_1(sK0,sK1)),X0)
      | ~ r1_tarski(k1_xboole_0,X0) ) ),
    inference(resolution,[],[f1177,f55])).

fof(f130,plain,(
    k2_tops_1(sK0,sK1) = k4_xboole_0(k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1)) ),
    inference(superposition,[],[f96,f89])).

fof(f89,plain,(
    k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f83,f51])).

fof(f83,plain,
    ( k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1))
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f52,f60])).

fof(f60,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l78_tops_1)).

fof(f96,plain,(
    ! [X0] : k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),X0) = k4_xboole_0(k2_pre_topc(sK0,sK1),X0) ),
    inference(resolution,[],[f86,f64])).

fof(f86,plain,(
    m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(subsumption_resolution,[],[f80,f51])).

fof(f80,plain,
    ( m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f52,f65])).

fof(f65,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_pre_topc)).

fof(f54,plain,
    ( ~ r1_tarski(sK1,k2_tops_1(sK0,sK1))
    | ~ v2_tops_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f37])).

fof(f2488,plain,
    ( v2_tops_1(sK1,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0) ),
    inference(trivial_inequality_removal,[],[f2487])).

fof(f2487,plain,
    ( k1_xboole_0 != k1_xboole_0
    | v2_tops_1(sK1,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0) ),
    inference(superposition,[],[f63,f1238])).

fof(f63,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k1_tops_1(X0,X1)
      | v2_tops_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f42])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n019.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 19:41:52 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.51  % (6174)lrs+1011_4:1_acc=model:add=large:afp=40000:afq=1.4:ccuc=first:cond=on:fsr=off:gsp=input_only:gs=on:gsem=off:irw=on:nwc=1:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:urr=on_21 on theBenchmark
% 1.22/0.53  % (6179)dis+1004_1_aac=none:acc=on:afp=40000:afq=1.2:anc=none:cond=on:fde=unused:gs=on:gsem=off:irw=on:nm=32:nwc=2:sd=1:ss=axioms:sos=theory:sp=reverse_arity:urr=ec_only_17 on theBenchmark
% 1.22/0.53  % (6179)Refutation not found, incomplete strategy% (6179)------------------------------
% 1.22/0.53  % (6179)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.22/0.53  % (6179)Termination reason: Refutation not found, incomplete strategy
% 1.22/0.53  
% 1.22/0.53  % (6179)Memory used [KB]: 10746
% 1.22/0.53  % (6179)Time elapsed: 0.105 s
% 1.22/0.53  % (6179)------------------------------
% 1.22/0.53  % (6179)------------------------------
% 1.22/0.53  % (6195)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_157 on theBenchmark
% 1.22/0.53  % (6187)dis+1002_5_av=off:cond=on:gs=on:lma=on:nm=2:nwc=1:sd=3:ss=axioms:st=1.5:sos=on:updr=off_4 on theBenchmark
% 1.34/0.54  % (6178)lrs+11_4_av=off:gsp=input_only:irw=on:lma=on:nm=0:nwc=1.2:stl=30:sd=2:ss=axioms:sp=reverse_arity:urr=on:updr=off_8 on theBenchmark
% 1.34/0.54  % (6177)dis+4_8:1_add=large:afp=100000:afq=1.4:ep=RST:fde=unused:gsp=input_only:lcm=predicate:nwc=1:sos=all:sp=occurrence:updr=off:uhcvi=on_33 on theBenchmark
% 1.34/0.54  % (6175)lrs+1002_8:1_av=off:cond=on:gsp=input_only:gs=on:irw=on:lma=on:nm=0:nwc=1.7:stl=30:sd=2:ss=axioms:sos=on:sp=occurrence:urr=on_41 on theBenchmark
% 1.34/0.54  % (6187)Refutation not found, incomplete strategy% (6187)------------------------------
% 1.34/0.54  % (6187)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.34/0.54  % (6176)lrs+2_5:4_av=off:bce=on:cond=fast:ep=R:fde=none:gs=on:lcm=reverse:lwlo=on:nwc=1:stl=30:sd=1:ss=axioms:sos=all:sp=occurrence_8 on theBenchmark
% 1.34/0.54  % (6187)Termination reason: Refutation not found, incomplete strategy
% 1.34/0.54  
% 1.34/0.54  % (6187)Memory used [KB]: 6268
% 1.34/0.54  % (6187)Time elapsed: 0.123 s
% 1.34/0.54  % (6187)------------------------------
% 1.34/0.54  % (6187)------------------------------
% 1.34/0.54  % (6176)Refutation not found, incomplete strategy% (6176)------------------------------
% 1.34/0.54  % (6176)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.34/0.54  % (6176)Termination reason: Refutation not found, incomplete strategy
% 1.34/0.54  
% 1.34/0.54  % (6176)Memory used [KB]: 6140
% 1.34/0.54  % (6176)Time elapsed: 0.001 s
% 1.34/0.54  % (6176)------------------------------
% 1.34/0.54  % (6176)------------------------------
% 1.34/0.55  % (6200)ott+11_8:1_av=off:bs=on:bce=on:fde=none:gsp=input_only:gs=on:gsem=on:irw=on:lcm=predicate:nm=6:nwc=1.5:sd=2:ss=axioms:st=1.2:sos=theory:urr=on:updr=off_49 on theBenchmark
% 1.34/0.55  % (6182)ott+11_2:1_add=large:afp=40000:afq=2.0:amm=sco:anc=none:br=off:cond=on:irw=on:nwc=1:sd=2:ss=axioms:st=2.0:sos=all:urr=on:updr=off_6 on theBenchmark
% 1.34/0.55  % (6183)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_3 on theBenchmark
% 1.34/0.55  % (6194)ott+11_4:1_awrs=converge:awrsf=16:acc=model:add=large:afr=on:afp=4000:afq=1.4:amm=off:br=off:cond=fast:fde=none:gsp=input_only:nm=64:nwc=2:nicw=on:sd=3:ss=axioms:s2a=on:sac=on:sp=frequency:urr=on:updr=off_70 on theBenchmark
% 1.34/0.55  % (6202)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_48 on theBenchmark
% 1.34/0.55  % (6192)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_6 on theBenchmark
% 1.34/0.55  % (6173)lrs-11_3_av=off:bs=unit_only:bsr=on:cond=on:gsp=input_only:gs=on:gsem=on:lma=on:nm=2:nwc=1:stl=30:sd=3:ss=axioms:st=1.2:sos=all:sp=reverse_arity:urr=on:updr=off_11 on theBenchmark
% 1.34/0.55  % (6191)lrs+1_2:3_aac=none:afr=on:afp=100000:afq=1.0:amm=sco:bd=off:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=on:sac=on:sp=occurrence:urr=ec_only:updr=off:uhcvi=on_11 on theBenchmark
% 1.34/0.55  % (6197)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 1.34/0.55  % (6198)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_88 on theBenchmark
% 1.34/0.55  % (6193)lrs+1010_4:1_aac=none:add=off:afp=40000:afq=2.0:amm=sco:anc=none:gs=on:gsem=off:lma=on:lwlo=on:nm=4:nwc=10:stl=30:sd=3:ss=axioms:sos=all:sac=on_49 on theBenchmark
% 1.34/0.56  % (6185)dis+10_5:4_add=off:afr=on:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gs=on:nm=64:nwc=1:sas=z3:sd=3:ss=axioms:st=3.0:sos=all:sp=occurrence:urr=on:updr=off_15 on theBenchmark
% 1.34/0.56  % (6199)dis+11_2_add=large:afr=on:anc=none:gs=on:gsem=on:lwlo=on:nm=16:nwc=1:sd=1:ss=axioms:st=3.0:sos=on_4 on theBenchmark
% 1.34/0.56  % (6181)lrs+11_2:1_av=off:bsr=on:gs=on:gsem=on:irw=on:lma=on:lwlo=on:nm=16:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sp=reverse_arity_11 on theBenchmark
% 1.34/0.56  % (6190)lrs-2_3:2_av=off:bce=on:cond=on:gsp=input_only:gs=on:gsem=on:lcm=predicate:lma=on:newcnf=on:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=all:sp=occurrence:updr=off:uhcvi=on_62 on theBenchmark
% 1.34/0.56  % (6186)dis+4_2_av=off:bs=on:fsr=off:gsp=input_only:newcnf=on:nwc=1:sd=3:ss=axioms:st=3.0:sos=all:sp=reverse_arity:urr=ec_only:updr=off_127 on theBenchmark
% 1.34/0.56  % (6184)dis+1010_2:3_afr=on:afp=40000:afq=1.4:amm=off:anc=none:lma=on:nm=16:nwc=1:sp=occurrence:updr=off:uhcvi=on_34 on theBenchmark
% 1.34/0.56  % (6189)lrs+1010_4_awrs=decay:awrsf=64:add=large:afp=4000:afq=1.2:amm=off:anc=none:bs=on:bsr=on:fde=none:gs=on:gsaa=from_current:gsem=on:lma=on:newcnf=on:nwc=1.7:sas=z3:stl=30:sd=10:ss=axioms:s2a=on:st=1.2:sp=frequency:updr=off:uhcvi=on_23 on theBenchmark
% 1.34/0.57  % (6201)lrs+1011_10_av=off:bce=on:cond=on:fsr=off:fde=unused:gs=on:nm=2:nwc=1.1:stl=30:sd=4:ss=axioms:s2a=on:st=1.5:sos=on:sp=frequency:urr=on:updr=off:uhcvi=on_4 on theBenchmark
% 1.34/0.57  % (6181)Refutation not found, incomplete strategy% (6181)------------------------------
% 1.34/0.57  % (6181)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.34/0.58  % (6180)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_6 on theBenchmark
% 1.34/0.58  % (6188)lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_7 on theBenchmark
% 1.34/0.58  % (6181)Termination reason: Refutation not found, incomplete strategy
% 1.34/0.58  
% 1.34/0.58  % (6181)Memory used [KB]: 6140
% 1.34/0.58  % (6181)Time elapsed: 0.158 s
% 1.34/0.58  % (6181)------------------------------
% 1.34/0.58  % (6181)------------------------------
% 1.34/0.58  % (6196)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 1.34/0.58  % (6197)Refutation not found, incomplete strategy% (6197)------------------------------
% 1.34/0.58  % (6197)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.34/0.58  % (6197)Termination reason: Refutation not found, incomplete strategy
% 1.34/0.58  
% 1.34/0.58  % (6197)Memory used [KB]: 10618
% 1.34/0.58  % (6197)Time elapsed: 0.157 s
% 1.34/0.58  % (6197)------------------------------
% 1.34/0.58  % (6197)------------------------------
% 2.40/0.70  % (6225)ott+1_5:1_acc=on:add=off:afr=on:afp=100000:afq=1.1:amm=sco:anc=none:lcm=predicate:nm=16:nwc=1.1:sd=1:ss=axioms:st=3.0:sos=on:sac=on:updr=off_18 on theBenchmark
% 2.40/0.71  % (6224)dis+1011_8:1_aac=none:acc=on:afp=1000:afq=1.4:amm=off:anc=all:bs=unit_only:bce=on:ccuc=small_ones:fsr=off:fde=unused:gsp=input_only:gs=on:gsem=off:lma=on:nm=16:nwc=2.5:sd=4:ss=axioms:st=1.5:sos=all:uhcvi=on_65 on theBenchmark
% 2.40/0.71  % (6226)lrs+1002_1_add=large:afp=100000:afq=1.0:amm=off:anc=none:cond=fast:fde=none:gs=on:gsem=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence_8 on theBenchmark
% 2.40/0.71  % (6226)Refutation not found, incomplete strategy% (6226)------------------------------
% 2.40/0.71  % (6226)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.40/0.71  % (6226)Termination reason: Refutation not found, incomplete strategy
% 2.40/0.71  
% 2.40/0.71  % (6226)Memory used [KB]: 10618
% 2.40/0.71  % (6226)Time elapsed: 0.135 s
% 2.40/0.71  % (6226)------------------------------
% 2.40/0.71  % (6226)------------------------------
% 2.40/0.72  % (6180)Refutation not found, incomplete strategy% (6180)------------------------------
% 2.40/0.72  % (6180)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.40/0.73  % (6227)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_4 on theBenchmark
% 2.40/0.73  % (6180)Termination reason: Refutation not found, incomplete strategy
% 2.40/0.73  
% 2.40/0.73  % (6180)Memory used [KB]: 6140
% 2.40/0.73  % (6180)Time elapsed: 0.226 s
% 2.40/0.73  % (6180)------------------------------
% 2.40/0.73  % (6180)------------------------------
% 2.40/0.74  % (6228)lrs+1002_3:1_av=off:bd=off:cond=fast:fde=none:gsp=input_only:lcm=predicate:lma=on:lwlo=on:nm=4:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_134 on theBenchmark
% 2.40/0.74  % (6192)Refutation found. Thanks to Tanya!
% 2.40/0.74  % SZS status Theorem for theBenchmark
% 2.40/0.74  % SZS output start Proof for theBenchmark
% 2.40/0.74  fof(f2491,plain,(
% 2.40/0.74    $false),
% 2.40/0.74    inference(subsumption_resolution,[],[f2490,f51])).
% 2.40/0.74  fof(f51,plain,(
% 2.40/0.74    l1_pre_topc(sK0)),
% 2.40/0.74    inference(cnf_transformation,[],[f37])).
% 2.40/0.74  fof(f37,plain,(
% 2.40/0.74    ((~r1_tarski(sK1,k2_tops_1(sK0,sK1)) | ~v2_tops_1(sK1,sK0)) & (r1_tarski(sK1,k2_tops_1(sK0,sK1)) | v2_tops_1(sK1,sK0)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0)),
% 2.40/0.74    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f34,f36,f35])).
% 2.40/0.74  fof(f35,plain,(
% 2.40/0.74    ? [X0] : (? [X1] : ((~r1_tarski(X1,k2_tops_1(X0,X1)) | ~v2_tops_1(X1,X0)) & (r1_tarski(X1,k2_tops_1(X0,X1)) | v2_tops_1(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0)) => (? [X1] : ((~r1_tarski(X1,k2_tops_1(sK0,X1)) | ~v2_tops_1(X1,sK0)) & (r1_tarski(X1,k2_tops_1(sK0,X1)) | v2_tops_1(X1,sK0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0))),
% 2.40/0.74    introduced(choice_axiom,[])).
% 2.40/0.74  fof(f36,plain,(
% 2.40/0.74    ? [X1] : ((~r1_tarski(X1,k2_tops_1(sK0,X1)) | ~v2_tops_1(X1,sK0)) & (r1_tarski(X1,k2_tops_1(sK0,X1)) | v2_tops_1(X1,sK0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) => ((~r1_tarski(sK1,k2_tops_1(sK0,sK1)) | ~v2_tops_1(sK1,sK0)) & (r1_tarski(sK1,k2_tops_1(sK0,sK1)) | v2_tops_1(sK1,sK0)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))))),
% 2.40/0.74    introduced(choice_axiom,[])).
% 2.40/0.74  fof(f34,plain,(
% 2.40/0.74    ? [X0] : (? [X1] : ((~r1_tarski(X1,k2_tops_1(X0,X1)) | ~v2_tops_1(X1,X0)) & (r1_tarski(X1,k2_tops_1(X0,X1)) | v2_tops_1(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 2.40/0.74    inference(flattening,[],[f33])).
% 2.40/0.74  fof(f33,plain,(
% 2.40/0.74    ? [X0] : (? [X1] : (((~r1_tarski(X1,k2_tops_1(X0,X1)) | ~v2_tops_1(X1,X0)) & (r1_tarski(X1,k2_tops_1(X0,X1)) | v2_tops_1(X1,X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 2.40/0.74    inference(nnf_transformation,[],[f23])).
% 2.40/0.74  fof(f23,plain,(
% 2.40/0.74    ? [X0] : (? [X1] : ((v2_tops_1(X1,X0) <~> r1_tarski(X1,k2_tops_1(X0,X1))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 2.40/0.74    inference(ennf_transformation,[],[f22])).
% 2.40/0.74  fof(f22,negated_conjecture,(
% 2.40/0.74    ~! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v2_tops_1(X1,X0) <=> r1_tarski(X1,k2_tops_1(X0,X1)))))),
% 2.40/0.74    inference(negated_conjecture,[],[f21])).
% 2.40/0.74  fof(f21,conjecture,(
% 2.40/0.74    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v2_tops_1(X1,X0) <=> r1_tarski(X1,k2_tops_1(X0,X1)))))),
% 2.40/0.74    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t88_tops_1)).
% 2.40/0.74  fof(f2490,plain,(
% 2.40/0.74    ~l1_pre_topc(sK0)),
% 2.40/0.74    inference(subsumption_resolution,[],[f2489,f52])).
% 2.40/0.74  fof(f52,plain,(
% 2.40/0.74    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 2.40/0.74    inference(cnf_transformation,[],[f37])).
% 2.40/0.74  fof(f2489,plain,(
% 2.40/0.74    ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0)),
% 2.40/0.74    inference(subsumption_resolution,[],[f2488,f1710])).
% 2.40/0.74  fof(f1710,plain,(
% 2.40/0.74    ~v2_tops_1(sK1,sK0)),
% 2.40/0.74    inference(subsumption_resolution,[],[f1628,f90])).
% 2.40/0.74  fof(f90,plain,(
% 2.40/0.74    r1_tarski(sK1,k2_pre_topc(sK0,sK1))),
% 2.40/0.74    inference(subsumption_resolution,[],[f84,f51])).
% 2.40/0.74  fof(f84,plain,(
% 2.40/0.74    r1_tarski(sK1,k2_pre_topc(sK0,sK1)) | ~l1_pre_topc(sK0)),
% 2.40/0.74    inference(resolution,[],[f52,f58])).
% 2.40/0.74  fof(f58,plain,(
% 2.40/0.74    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | r1_tarski(X1,k2_pre_topc(X0,X1)) | ~l1_pre_topc(X0)) )),
% 2.40/0.74    inference(cnf_transformation,[],[f25])).
% 2.40/0.74  fof(f25,plain,(
% 2.40/0.74    ! [X0] : (! [X1] : (r1_tarski(X1,k2_pre_topc(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.40/0.74    inference(ennf_transformation,[],[f17])).
% 2.40/0.74  fof(f17,axiom,(
% 2.40/0.74    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => r1_tarski(X1,k2_pre_topc(X0,X1))))),
% 2.40/0.74    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_pre_topc)).
% 2.40/0.74  fof(f1628,plain,(
% 2.40/0.74    ~r1_tarski(sK1,k2_pre_topc(sK0,sK1)) | ~v2_tops_1(sK1,sK0)),
% 2.40/0.74    inference(backward_demodulation,[],[f54,f1626])).
% 2.40/0.74  fof(f1626,plain,(
% 2.40/0.74    k2_tops_1(sK0,sK1) = k2_pre_topc(sK0,sK1)),
% 2.40/0.74    inference(forward_demodulation,[],[f1255,f74])).
% 2.40/0.74  fof(f74,plain,(
% 2.40/0.74    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 2.40/0.74    inference(cnf_transformation,[],[f6])).
% 2.40/0.74  fof(f6,axiom,(
% 2.40/0.74    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 2.40/0.74    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).
% 2.40/0.74  fof(f1255,plain,(
% 2.40/0.74    k2_tops_1(sK0,sK1) = k4_xboole_0(k2_pre_topc(sK0,sK1),k1_xboole_0)),
% 2.40/0.74    inference(backward_demodulation,[],[f130,f1238])).
% 2.40/0.74  fof(f1238,plain,(
% 2.40/0.74    k1_xboole_0 = k1_tops_1(sK0,sK1)),
% 2.40/0.74    inference(subsumption_resolution,[],[f1237,f1177])).
% 2.40/0.74  fof(f1177,plain,(
% 2.40/0.74    r2_hidden(sK4(k1_xboole_0,k1_tops_1(sK0,sK1)),k1_xboole_0) | k1_xboole_0 = k1_tops_1(sK0,sK1)),
% 2.40/0.74    inference(duplicate_literal_removal,[],[f1174])).
% 2.40/0.74  fof(f1174,plain,(
% 2.40/0.74    k1_xboole_0 = k1_tops_1(sK0,sK1) | r2_hidden(sK4(k1_xboole_0,k1_tops_1(sK0,sK1)),k1_xboole_0) | k1_xboole_0 = k1_tops_1(sK0,sK1)),
% 2.40/0.74    inference(resolution,[],[f1149,f128])).
% 2.40/0.74  fof(f128,plain,(
% 2.40/0.74    ( ! [X5] : (~r2_hidden(sK4(X5,k1_tops_1(sK0,sK1)),k2_tops_1(sK0,sK1)) | r2_hidden(sK4(X5,k1_tops_1(sK0,sK1)),X5) | k1_tops_1(sK0,sK1) = X5) )),
% 2.40/0.74    inference(resolution,[],[f117,f72])).
% 2.40/0.74  fof(f72,plain,(
% 2.40/0.74    ( ! [X0,X1] : (r2_hidden(sK4(X0,X1),X1) | r2_hidden(sK4(X0,X1),X0) | X0 = X1) )),
% 2.40/0.74    inference(cnf_transformation,[],[f50])).
% 2.40/0.74  fof(f50,plain,(
% 2.40/0.74    ! [X0,X1] : (X0 = X1 | ((~r2_hidden(sK4(X0,X1),X1) | ~r2_hidden(sK4(X0,X1),X0)) & (r2_hidden(sK4(X0,X1),X1) | r2_hidden(sK4(X0,X1),X0))))),
% 2.40/0.74    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f48,f49])).
% 2.40/0.74  fof(f49,plain,(
% 2.40/0.74    ! [X1,X0] : (? [X2] : ((~r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) & (r2_hidden(X2,X1) | r2_hidden(X2,X0))) => ((~r2_hidden(sK4(X0,X1),X1) | ~r2_hidden(sK4(X0,X1),X0)) & (r2_hidden(sK4(X0,X1),X1) | r2_hidden(sK4(X0,X1),X0))))),
% 2.40/0.74    introduced(choice_axiom,[])).
% 2.40/0.74  fof(f48,plain,(
% 2.40/0.74    ! [X0,X1] : (X0 = X1 | ? [X2] : ((~r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) & (r2_hidden(X2,X1) | r2_hidden(X2,X0))))),
% 2.40/0.74    inference(nnf_transformation,[],[f32])).
% 2.40/0.74  fof(f32,plain,(
% 2.40/0.74    ! [X0,X1] : (X0 = X1 | ? [X2] : (r2_hidden(X2,X0) <~> r2_hidden(X2,X1)))),
% 2.40/0.74    inference(ennf_transformation,[],[f3])).
% 2.40/0.74  fof(f3,axiom,(
% 2.40/0.74    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) <=> r2_hidden(X2,X1)) => X0 = X1)),
% 2.40/0.74    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_tarski)).
% 2.40/0.74  fof(f117,plain,(
% 2.40/0.74    ( ! [X1] : (~r2_hidden(X1,k1_tops_1(sK0,sK1)) | ~r2_hidden(X1,k2_tops_1(sK0,sK1))) )),
% 2.40/0.74    inference(superposition,[],[f78,f114])).
% 2.40/0.74  fof(f114,plain,(
% 2.40/0.74    k1_tops_1(sK0,sK1) = k4_xboole_0(sK1,k2_tops_1(sK0,sK1))),
% 2.40/0.74    inference(superposition,[],[f88,f85])).
% 2.40/0.74  fof(f85,plain,(
% 2.40/0.74    ( ! [X0] : (k7_subset_1(u1_struct_0(sK0),sK1,X0) = k4_xboole_0(sK1,X0)) )),
% 2.40/0.74    inference(resolution,[],[f52,f64])).
% 2.40/0.74  fof(f64,plain,(
% 2.40/0.74    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)) )),
% 2.40/0.74    inference(cnf_transformation,[],[f29])).
% 2.40/0.74  fof(f29,plain,(
% 2.40/0.74    ! [X0,X1,X2] : (k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.40/0.74    inference(ennf_transformation,[],[f14])).
% 2.40/0.74  fof(f14,axiom,(
% 2.40/0.74    ! [X0,X1,X2] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2))),
% 2.40/0.74    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_subset_1)).
% 2.40/0.74  fof(f88,plain,(
% 2.40/0.74    k1_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1))),
% 2.40/0.74    inference(subsumption_resolution,[],[f82,f51])).
% 2.40/0.74  fof(f82,plain,(
% 2.40/0.74    k1_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) | ~l1_pre_topc(sK0)),
% 2.40/0.74    inference(resolution,[],[f52,f61])).
% 2.40/0.74  fof(f61,plain,(
% 2.40/0.74    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) | ~l1_pre_topc(X0)) )),
% 2.40/0.74    inference(cnf_transformation,[],[f27])).
% 2.40/0.74  fof(f27,plain,(
% 2.40/0.74    ! [X0] : (! [X1] : (k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.40/0.74    inference(ennf_transformation,[],[f19])).
% 2.40/0.74  fof(f19,axiom,(
% 2.40/0.74    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))))),
% 2.40/0.74    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_tops_1)).
% 2.40/0.74  fof(f78,plain,(
% 2.40/0.74    ( ! [X4,X0,X1] : (~r2_hidden(X4,k4_xboole_0(X0,X1)) | ~r2_hidden(X4,X1)) )),
% 2.40/0.74    inference(equality_resolution,[],[f67])).
% 2.40/0.74  fof(f67,plain,(
% 2.40/0.74    ( ! [X4,X2,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,X2) | k4_xboole_0(X0,X1) != X2) )),
% 2.40/0.74    inference(cnf_transformation,[],[f47])).
% 2.40/0.74  fof(f47,plain,(
% 2.40/0.74    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ((r2_hidden(sK3(X0,X1,X2),X1) | ~r2_hidden(sK3(X0,X1,X2),X0) | ~r2_hidden(sK3(X0,X1,X2),X2)) & ((~r2_hidden(sK3(X0,X1,X2),X1) & r2_hidden(sK3(X0,X1,X2),X0)) | r2_hidden(sK3(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 2.40/0.74    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f45,f46])).
% 2.40/0.74  fof(f46,plain,(
% 2.40/0.74    ! [X2,X1,X0] : (? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2))) => ((r2_hidden(sK3(X0,X1,X2),X1) | ~r2_hidden(sK3(X0,X1,X2),X0) | ~r2_hidden(sK3(X0,X1,X2),X2)) & ((~r2_hidden(sK3(X0,X1,X2),X1) & r2_hidden(sK3(X0,X1,X2),X0)) | r2_hidden(sK3(X0,X1,X2),X2))))),
% 2.40/0.74    introduced(choice_axiom,[])).
% 2.40/0.74  fof(f45,plain,(
% 2.40/0.74    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 2.40/0.74    inference(rectify,[],[f44])).
% 2.40/0.74  fof(f44,plain,(
% 2.40/0.74    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 2.40/0.74    inference(flattening,[],[f43])).
% 2.40/0.74  fof(f43,plain,(
% 2.40/0.74    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : (((r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 2.40/0.74    inference(nnf_transformation,[],[f2])).
% 2.40/0.74  fof(f2,axiom,(
% 2.40/0.74    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 2.40/0.74    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).
% 2.40/0.74  fof(f1149,plain,(
% 2.40/0.74    r2_hidden(sK4(k1_xboole_0,k1_tops_1(sK0,sK1)),k2_tops_1(sK0,sK1)) | k1_xboole_0 = k1_tops_1(sK0,sK1)),
% 2.40/0.74    inference(subsumption_resolution,[],[f1148,f498])).
% 2.40/0.74  fof(f498,plain,(
% 2.40/0.74    ( ! [X33,X34] : (k1_xboole_0 = k1_tops_1(sK0,sK1) | r2_hidden(sK4(X33,k1_tops_1(sK0,sK1)),X34) | r2_hidden(sK4(X33,k1_tops_1(sK0,sK1)),X33) | k1_tops_1(sK0,sK1) = X33) )),
% 2.40/0.74    inference(subsumption_resolution,[],[f488,f128])).
% 2.40/0.74  fof(f488,plain,(
% 2.40/0.74    ( ! [X33,X34] : (k1_xboole_0 = k1_tops_1(sK0,sK1) | r2_hidden(sK4(X33,k1_tops_1(sK0,sK1)),X34) | r2_hidden(sK4(X33,k1_tops_1(sK0,sK1)),k2_tops_1(sK0,sK1)) | r2_hidden(sK4(X33,k1_tops_1(sK0,sK1)),X33) | k1_tops_1(sK0,sK1) = X33) )),
% 2.40/0.74    inference(resolution,[],[f234,f123])).
% 2.40/0.74  fof(f123,plain,(
% 2.40/0.74    ( ! [X5] : (r2_hidden(sK4(X5,k1_tops_1(sK0,sK1)),sK1) | r2_hidden(sK4(X5,k1_tops_1(sK0,sK1)),X5) | k1_tops_1(sK0,sK1) = X5) )),
% 2.40/0.74    inference(resolution,[],[f116,f72])).
% 2.40/0.74  fof(f116,plain,(
% 2.40/0.74    ( ! [X0] : (~r2_hidden(X0,k1_tops_1(sK0,sK1)) | r2_hidden(X0,sK1)) )),
% 2.40/0.74    inference(superposition,[],[f79,f114])).
% 2.40/0.74  fof(f79,plain,(
% 2.40/0.74    ( ! [X4,X0,X1] : (~r2_hidden(X4,k4_xboole_0(X0,X1)) | r2_hidden(X4,X0)) )),
% 2.40/0.74    inference(equality_resolution,[],[f66])).
% 2.40/0.74  fof(f66,plain,(
% 2.40/0.74    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X0) | ~r2_hidden(X4,X2) | k4_xboole_0(X0,X1) != X2) )),
% 2.40/0.74    inference(cnf_transformation,[],[f47])).
% 2.40/0.74  fof(f234,plain,(
% 2.40/0.74    ( ! [X0,X1] : (~r2_hidden(X0,sK1) | k1_xboole_0 = k1_tops_1(sK0,sK1) | r2_hidden(X0,X1) | r2_hidden(X0,k2_tops_1(sK0,sK1))) )),
% 2.40/0.74    inference(resolution,[],[f218,f158])).
% 2.40/0.74  fof(f158,plain,(
% 2.40/0.74    ( ! [X2,X3] : (~r1_tarski(k1_tops_1(sK0,sK1),X3) | ~r2_hidden(X2,sK1) | r2_hidden(X2,X3) | r2_hidden(X2,k2_tops_1(sK0,sK1))) )),
% 2.40/0.74    inference(resolution,[],[f118,f55])).
% 2.40/0.74  fof(f55,plain,(
% 2.40/0.74    ( ! [X0,X3,X1] : (~r2_hidden(X3,X0) | r2_hidden(X3,X1) | ~r1_tarski(X0,X1)) )),
% 2.40/0.74    inference(cnf_transformation,[],[f41])).
% 2.40/0.74  fof(f41,plain,(
% 2.40/0.74    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK2(X0,X1),X1) & r2_hidden(sK2(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 2.40/0.74    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f39,f40])).
% 2.40/0.74  fof(f40,plain,(
% 2.40/0.74    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK2(X0,X1),X1) & r2_hidden(sK2(X0,X1),X0)))),
% 2.40/0.74    introduced(choice_axiom,[])).
% 2.40/0.74  fof(f39,plain,(
% 2.40/0.74    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 2.40/0.74    inference(rectify,[],[f38])).
% 2.40/0.74  fof(f38,plain,(
% 2.40/0.74    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 2.40/0.74    inference(nnf_transformation,[],[f24])).
% 2.40/0.74  fof(f24,plain,(
% 2.40/0.74    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 2.40/0.74    inference(ennf_transformation,[],[f1])).
% 2.40/0.74  fof(f1,axiom,(
% 2.40/0.74    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 2.40/0.74    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).
% 2.40/0.74  fof(f118,plain,(
% 2.40/0.74    ( ! [X2] : (r2_hidden(X2,k1_tops_1(sK0,sK1)) | r2_hidden(X2,k2_tops_1(sK0,sK1)) | ~r2_hidden(X2,sK1)) )),
% 2.40/0.74    inference(superposition,[],[f77,f114])).
% 2.40/0.74  fof(f77,plain,(
% 2.40/0.74    ( ! [X4,X0,X1] : (r2_hidden(X4,k4_xboole_0(X0,X1)) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) )),
% 2.40/0.74    inference(equality_resolution,[],[f68])).
% 2.40/0.74  fof(f68,plain,(
% 2.40/0.74    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0) | k4_xboole_0(X0,X1) != X2) )),
% 2.40/0.74    inference(cnf_transformation,[],[f47])).
% 2.40/0.74  fof(f218,plain,(
% 2.40/0.74    ( ! [X0] : (r1_tarski(k1_tops_1(sK0,sK1),X0) | k1_xboole_0 = k1_tops_1(sK0,sK1)) )),
% 2.40/0.74    inference(resolution,[],[f212,f102])).
% 2.40/0.74  fof(f102,plain,(
% 2.40/0.74    r1_tarski(sK1,k2_tops_1(sK0,sK1)) | k1_xboole_0 = k1_tops_1(sK0,sK1)),
% 2.40/0.74    inference(resolution,[],[f87,f53])).
% 2.40/0.74  fof(f53,plain,(
% 2.40/0.74    v2_tops_1(sK1,sK0) | r1_tarski(sK1,k2_tops_1(sK0,sK1))),
% 2.40/0.74    inference(cnf_transformation,[],[f37])).
% 2.40/0.74  fof(f87,plain,(
% 2.40/0.74    ~v2_tops_1(sK1,sK0) | k1_xboole_0 = k1_tops_1(sK0,sK1)),
% 2.40/0.74    inference(subsumption_resolution,[],[f81,f51])).
% 2.40/0.74  fof(f81,plain,(
% 2.40/0.74    ~v2_tops_1(sK1,sK0) | k1_xboole_0 = k1_tops_1(sK0,sK1) | ~l1_pre_topc(sK0)),
% 2.40/0.74    inference(resolution,[],[f52,f62])).
% 2.40/0.74  fof(f62,plain,(
% 2.40/0.74    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v2_tops_1(X1,X0) | k1_xboole_0 = k1_tops_1(X0,X1) | ~l1_pre_topc(X0)) )),
% 2.40/0.74    inference(cnf_transformation,[],[f42])).
% 2.40/0.74  fof(f42,plain,(
% 2.40/0.74    ! [X0] : (! [X1] : (((v2_tops_1(X1,X0) | k1_xboole_0 != k1_tops_1(X0,X1)) & (k1_xboole_0 = k1_tops_1(X0,X1) | ~v2_tops_1(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.40/0.74    inference(nnf_transformation,[],[f28])).
% 2.40/0.74  fof(f28,plain,(
% 2.40/0.74    ! [X0] : (! [X1] : ((v2_tops_1(X1,X0) <=> k1_xboole_0 = k1_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.40/0.74    inference(ennf_transformation,[],[f20])).
% 2.40/0.74  fof(f20,axiom,(
% 2.40/0.74    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v2_tops_1(X1,X0) <=> k1_xboole_0 = k1_tops_1(X0,X1))))),
% 2.40/0.74    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t84_tops_1)).
% 2.40/0.74  fof(f212,plain,(
% 2.40/0.74    ( ! [X11] : (~r1_tarski(sK1,k2_tops_1(sK0,sK1)) | r1_tarski(k1_tops_1(sK0,sK1),X11)) )),
% 2.40/0.74    inference(duplicate_literal_removal,[],[f206])).
% 2.40/0.74  fof(f206,plain,(
% 2.40/0.74    ( ! [X11] : (r1_tarski(k1_tops_1(sK0,sK1),X11) | ~r1_tarski(sK1,k2_tops_1(sK0,sK1)) | r1_tarski(k1_tops_1(sK0,sK1),X11)) )),
% 2.40/0.74    inference(resolution,[],[f154,f125])).
% 2.40/0.74  fof(f125,plain,(
% 2.40/0.74    ( ! [X0] : (~r2_hidden(sK2(k1_tops_1(sK0,sK1),X0),k2_tops_1(sK0,sK1)) | r1_tarski(k1_tops_1(sK0,sK1),X0)) )),
% 2.40/0.74    inference(resolution,[],[f117,f56])).
% 2.40/0.74  fof(f56,plain,(
% 2.40/0.74    ( ! [X0,X1] : (r2_hidden(sK2(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 2.40/0.74    inference(cnf_transformation,[],[f41])).
% 2.40/0.74  fof(f154,plain,(
% 2.40/0.74    ( ! [X0,X1] : (r2_hidden(sK2(k1_tops_1(sK0,sK1),X0),X1) | r1_tarski(k1_tops_1(sK0,sK1),X0) | ~r1_tarski(sK1,X1)) )),
% 2.40/0.74    inference(resolution,[],[f120,f55])).
% 2.40/0.74  fof(f120,plain,(
% 2.40/0.74    ( ! [X0] : (r2_hidden(sK2(k1_tops_1(sK0,sK1),X0),sK1) | r1_tarski(k1_tops_1(sK0,sK1),X0)) )),
% 2.40/0.74    inference(resolution,[],[f116,f56])).
% 2.40/0.74  fof(f1148,plain,(
% 2.40/0.74    k1_xboole_0 = k1_tops_1(sK0,sK1) | r2_hidden(sK4(k1_xboole_0,k1_tops_1(sK0,sK1)),k2_tops_1(sK0,sK1)) | ~r2_hidden(sK4(k1_xboole_0,k1_tops_1(sK0,sK1)),k1_xboole_0)),
% 2.40/0.74    inference(duplicate_literal_removal,[],[f1143])).
% 2.40/0.74  fof(f1143,plain,(
% 2.40/0.74    k1_xboole_0 = k1_tops_1(sK0,sK1) | r2_hidden(sK4(k1_xboole_0,k1_tops_1(sK0,sK1)),k2_tops_1(sK0,sK1)) | k1_xboole_0 = k1_tops_1(sK0,sK1) | ~r2_hidden(sK4(k1_xboole_0,k1_tops_1(sK0,sK1)),k1_xboole_0)),
% 2.40/0.74    inference(resolution,[],[f1100,f161])).
% 2.40/0.74  fof(f161,plain,(
% 2.40/0.74    ( ! [X7] : (~r2_hidden(sK4(X7,k1_tops_1(sK0,sK1)),sK1) | r2_hidden(sK4(X7,k1_tops_1(sK0,sK1)),k2_tops_1(sK0,sK1)) | k1_tops_1(sK0,sK1) = X7 | ~r2_hidden(sK4(X7,k1_tops_1(sK0,sK1)),X7)) )),
% 2.40/0.74    inference(resolution,[],[f118,f73])).
% 2.40/0.74  fof(f73,plain,(
% 2.40/0.74    ( ! [X0,X1] : (~r2_hidden(sK4(X0,X1),X1) | X0 = X1 | ~r2_hidden(sK4(X0,X1),X0)) )),
% 2.40/0.74    inference(cnf_transformation,[],[f50])).
% 2.40/0.74  fof(f1100,plain,(
% 2.40/0.74    r2_hidden(sK4(k1_xboole_0,k1_tops_1(sK0,sK1)),sK1) | k1_xboole_0 = k1_tops_1(sK0,sK1)),
% 2.40/0.74    inference(superposition,[],[f1093,f74])).
% 2.40/0.74  fof(f1093,plain,(
% 2.40/0.74    ( ! [X1] : (r2_hidden(sK4(k4_xboole_0(X1,X1),k1_tops_1(sK0,sK1)),sK1) | k1_tops_1(sK0,sK1) = k4_xboole_0(X1,X1)) )),
% 2.40/0.74    inference(duplicate_literal_removal,[],[f1070])).
% 2.40/0.74  fof(f1070,plain,(
% 2.40/0.74    ( ! [X1] : (k1_tops_1(sK0,sK1) = k4_xboole_0(X1,X1) | r2_hidden(sK4(k4_xboole_0(X1,X1),k1_tops_1(sK0,sK1)),sK1) | r2_hidden(sK4(k4_xboole_0(X1,X1),k1_tops_1(sK0,sK1)),sK1) | k1_tops_1(sK0,sK1) = k4_xboole_0(X1,X1)) )),
% 2.40/0.74    inference(resolution,[],[f223,f222])).
% 2.40/0.74  fof(f222,plain,(
% 2.40/0.74    ( ! [X2,X3] : (r2_hidden(sK4(k4_xboole_0(X2,X3),k1_tops_1(sK0,sK1)),sK1) | r2_hidden(sK4(k4_xboole_0(X2,X3),k1_tops_1(sK0,sK1)),X2) | k1_tops_1(sK0,sK1) = k4_xboole_0(X2,X3)) )),
% 2.40/0.74    inference(resolution,[],[f123,f79])).
% 2.40/0.74  fof(f223,plain,(
% 2.40/0.74    ( ! [X4,X5] : (~r2_hidden(sK4(k4_xboole_0(X4,X5),k1_tops_1(sK0,sK1)),X5) | k1_tops_1(sK0,sK1) = k4_xboole_0(X4,X5) | r2_hidden(sK4(k4_xboole_0(X4,X5),k1_tops_1(sK0,sK1)),sK1)) )),
% 2.40/0.74    inference(resolution,[],[f123,f78])).
% 2.40/0.74  fof(f1237,plain,(
% 2.40/0.74    k1_xboole_0 = k1_tops_1(sK0,sK1) | ~r2_hidden(sK4(k1_xboole_0,k1_tops_1(sK0,sK1)),k1_xboole_0)),
% 2.40/0.74    inference(duplicate_literal_removal,[],[f1216])).
% 2.40/0.74  fof(f1216,plain,(
% 2.40/0.74    k1_xboole_0 = k1_tops_1(sK0,sK1) | k1_xboole_0 = k1_tops_1(sK0,sK1) | ~r2_hidden(sK4(k1_xboole_0,k1_tops_1(sK0,sK1)),k1_xboole_0)),
% 2.40/0.74    inference(resolution,[],[f1189,f73])).
% 2.40/0.74  fof(f1189,plain,(
% 2.40/0.74    ( ! [X0] : (r2_hidden(sK4(k1_xboole_0,k1_tops_1(sK0,sK1)),X0) | k1_xboole_0 = k1_tops_1(sK0,sK1)) )),
% 2.40/0.74    inference(subsumption_resolution,[],[f1188,f59])).
% 2.40/0.74  fof(f59,plain,(
% 2.40/0.74    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 2.40/0.74    inference(cnf_transformation,[],[f5])).
% 2.40/0.74  fof(f5,axiom,(
% 2.40/0.74    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 2.40/0.74    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).
% 2.40/0.74  fof(f1188,plain,(
% 2.40/0.74    ( ! [X0] : (k1_xboole_0 = k1_tops_1(sK0,sK1) | r2_hidden(sK4(k1_xboole_0,k1_tops_1(sK0,sK1)),X0) | ~r1_tarski(k1_xboole_0,X0)) )),
% 2.40/0.74    inference(resolution,[],[f1177,f55])).
% 2.40/0.74  fof(f130,plain,(
% 2.40/0.74    k2_tops_1(sK0,sK1) = k4_xboole_0(k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1))),
% 2.40/0.74    inference(superposition,[],[f96,f89])).
% 2.40/0.74  fof(f89,plain,(
% 2.40/0.74    k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1))),
% 2.40/0.74    inference(subsumption_resolution,[],[f83,f51])).
% 2.40/0.74  fof(f83,plain,(
% 2.40/0.74    k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1)) | ~l1_pre_topc(sK0)),
% 2.40/0.74    inference(resolution,[],[f52,f60])).
% 2.40/0.74  fof(f60,plain,(
% 2.40/0.74    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) | ~l1_pre_topc(X0)) )),
% 2.40/0.74    inference(cnf_transformation,[],[f26])).
% 2.40/0.74  fof(f26,plain,(
% 2.40/0.74    ! [X0] : (! [X1] : (k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.40/0.74    inference(ennf_transformation,[],[f18])).
% 2.40/0.74  fof(f18,axiom,(
% 2.40/0.74    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1))))),
% 2.40/0.74    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l78_tops_1)).
% 2.40/0.74  fof(f96,plain,(
% 2.40/0.74    ( ! [X0] : (k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),X0) = k4_xboole_0(k2_pre_topc(sK0,sK1),X0)) )),
% 2.40/0.74    inference(resolution,[],[f86,f64])).
% 2.40/0.74  fof(f86,plain,(
% 2.40/0.74    m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))),
% 2.40/0.74    inference(subsumption_resolution,[],[f80,f51])).
% 2.40/0.74  fof(f80,plain,(
% 2.40/0.74    m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0)),
% 2.40/0.74    inference(resolution,[],[f52,f65])).
% 2.40/0.74  fof(f65,plain,(
% 2.40/0.74    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 2.40/0.74    inference(cnf_transformation,[],[f31])).
% 2.40/0.74  fof(f31,plain,(
% 2.40/0.74    ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 2.40/0.74    inference(flattening,[],[f30])).
% 2.40/0.74  fof(f30,plain,(
% 2.40/0.74    ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 2.40/0.74    inference(ennf_transformation,[],[f16])).
% 2.40/0.74  fof(f16,axiom,(
% 2.40/0.74    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 2.40/0.74    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_pre_topc)).
% 2.40/0.74  fof(f54,plain,(
% 2.40/0.74    ~r1_tarski(sK1,k2_tops_1(sK0,sK1)) | ~v2_tops_1(sK1,sK0)),
% 2.40/0.74    inference(cnf_transformation,[],[f37])).
% 2.40/0.74  fof(f2488,plain,(
% 2.40/0.74    v2_tops_1(sK1,sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0)),
% 2.40/0.74    inference(trivial_inequality_removal,[],[f2487])).
% 2.40/0.74  fof(f2487,plain,(
% 2.40/0.74    k1_xboole_0 != k1_xboole_0 | v2_tops_1(sK1,sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0)),
% 2.40/0.74    inference(superposition,[],[f63,f1238])).
% 2.40/0.74  fof(f63,plain,(
% 2.40/0.74    ( ! [X0,X1] : (k1_xboole_0 != k1_tops_1(X0,X1) | v2_tops_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 2.40/0.74    inference(cnf_transformation,[],[f42])).
% 2.40/0.74  % SZS output end Proof for theBenchmark
% 2.40/0.74  % (6192)------------------------------
% 2.40/0.74  % (6192)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.40/0.74  % (6192)Termination reason: Refutation
% 2.40/0.74  
% 2.40/0.74  % (6192)Memory used [KB]: 2942
% 2.40/0.74  % (6192)Time elapsed: 0.329 s
% 2.40/0.74  % (6192)------------------------------
% 2.40/0.74  % (6192)------------------------------
% 2.92/0.77  % (6172)Success in time 0.394 s
%------------------------------------------------------------------------------
