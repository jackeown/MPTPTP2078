%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:10:49 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 1.79s
% Verified   : 
% Statistics : Number of formulae       :  117 (3629 expanded)
%              Number of leaves         :   18 ( 950 expanded)
%              Depth                    :   31
%              Number of atoms          :  329 (21532 expanded)
%              Number of equality atoms :   63 (2242 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f866,plain,(
    $false ),
    inference(subsumption_resolution,[],[f865,f95])).

fof(f95,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0))) ),
    inference(backward_demodulation,[],[f49,f94])).

fof(f94,plain,(
    u1_struct_0(sK0) = k2_struct_0(sK0) ),
    inference(resolution,[],[f82,f61])).

fof(f61,plain,(
    ! [X0] :
      ( ~ l1_struct_0(X0)
      | k2_struct_0(X0) = u1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k2_struct_0(X0) = u1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).

fof(f82,plain,(
    l1_struct_0(sK0) ),
    inference(resolution,[],[f48,f62])).

fof(f62,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(f48,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,
    ( ( ~ v3_pre_topc(k3_subset_1(u1_struct_0(sK0),sK1),sK0)
      | ~ v4_pre_topc(sK1,sK0) )
    & ( v3_pre_topc(k3_subset_1(u1_struct_0(sK0),sK1),sK0)
      | v4_pre_topc(sK1,sK0) )
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f35,f37,f36])).

fof(f36,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ( ~ v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)
              | ~ v4_pre_topc(X1,X0) )
            & ( v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)
              | v4_pre_topc(X1,X0) )
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_pre_topc(X0) )
   => ( ? [X1] :
          ( ( ~ v3_pre_topc(k3_subset_1(u1_struct_0(sK0),X1),sK0)
            | ~ v4_pre_topc(X1,sK0) )
          & ( v3_pre_topc(k3_subset_1(u1_struct_0(sK0),X1),sK0)
            | v4_pre_topc(X1,sK0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
      & l1_pre_topc(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f37,plain,
    ( ? [X1] :
        ( ( ~ v3_pre_topc(k3_subset_1(u1_struct_0(sK0),X1),sK0)
          | ~ v4_pre_topc(X1,sK0) )
        & ( v3_pre_topc(k3_subset_1(u1_struct_0(sK0),X1),sK0)
          | v4_pre_topc(X1,sK0) )
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
   => ( ( ~ v3_pre_topc(k3_subset_1(u1_struct_0(sK0),sK1),sK0)
        | ~ v4_pre_topc(sK1,sK0) )
      & ( v3_pre_topc(k3_subset_1(u1_struct_0(sK0),sK1),sK0)
        | v4_pre_topc(sK1,sK0) )
      & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ~ v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)
            | ~ v4_pre_topc(X1,X0) )
          & ( v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)
            | v4_pre_topc(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(flattening,[],[f34])).

fof(f34,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ~ v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)
            | ~ v4_pre_topc(X1,X0) )
          & ( v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)
            | v4_pre_topc(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f23])).

fof(f23,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v4_pre_topc(X1,X0)
          <~> v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,negated_conjecture,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( v4_pre_topc(X1,X0)
            <=> v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) ) ) ) ),
    inference(negated_conjecture,[],[f21])).

fof(f21,conjecture,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v4_pre_topc(X1,X0)
          <=> v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_tops_1)).

fof(f49,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f38])).

fof(f865,plain,(
    ~ m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0))) ),
    inference(subsumption_resolution,[],[f864,f819])).

fof(f819,plain,(
    ~ v4_pre_topc(sK1,sK0) ),
    inference(resolution,[],[f815,f103])).

fof(f103,plain,
    ( ~ v3_pre_topc(k4_xboole_0(k2_struct_0(sK0),sK1),sK0)
    | ~ v4_pre_topc(sK1,sK0) ),
    inference(backward_demodulation,[],[f92,f94])).

fof(f92,plain,
    ( ~ v3_pre_topc(k4_xboole_0(u1_struct_0(sK0),sK1),sK0)
    | ~ v4_pre_topc(sK1,sK0) ),
    inference(backward_demodulation,[],[f51,f88])).

fof(f88,plain,(
    k3_subset_1(u1_struct_0(sK0),sK1) = k4_xboole_0(u1_struct_0(sK0),sK1) ),
    inference(resolution,[],[f49,f55])).

fof(f55,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

fof(f51,plain,
    ( ~ v3_pre_topc(k3_subset_1(u1_struct_0(sK0),sK1),sK0)
    | ~ v4_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f38])).

fof(f815,plain,(
    v3_pre_topc(k4_xboole_0(k2_struct_0(sK0),sK1),sK0) ),
    inference(subsumption_resolution,[],[f808,f102])).

fof(f102,plain,
    ( v3_pre_topc(k4_xboole_0(k2_struct_0(sK0),sK1),sK0)
    | v4_pre_topc(sK1,sK0) ),
    inference(backward_demodulation,[],[f91,f94])).

fof(f91,plain,
    ( v3_pre_topc(k4_xboole_0(u1_struct_0(sK0),sK1),sK0)
    | v4_pre_topc(sK1,sK0) ),
    inference(backward_demodulation,[],[f50,f88])).

fof(f50,plain,
    ( v3_pre_topc(k3_subset_1(u1_struct_0(sK0),sK1),sK0)
    | v4_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f38])).

fof(f808,plain,
    ( v3_pre_topc(k4_xboole_0(k2_struct_0(sK0),sK1),sK0)
    | ~ v4_pre_topc(sK1,sK0) ),
    inference(backward_demodulation,[],[f101,f807])).

fof(f807,plain,(
    k4_xboole_0(k2_struct_0(sK0),sK1) = k7_subset_1(k2_struct_0(sK0),k2_struct_0(sK0),sK1) ),
    inference(backward_demodulation,[],[f298,f806])).

fof(f806,plain,(
    ! [X2,X3] : k4_xboole_0(X2,X3) = k3_xboole_0(k4_xboole_0(X2,X3),X2) ),
    inference(forward_demodulation,[],[f793,f76])).

fof(f76,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

fof(f793,plain,(
    ! [X2,X3] : k3_xboole_0(k4_xboole_0(X2,X3),X2) = k4_xboole_0(k4_xboole_0(X2,X3),k1_xboole_0) ),
    inference(superposition,[],[f72,f782])).

fof(f782,plain,(
    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(X0,X1),X0) ),
    inference(duplicate_literal_removal,[],[f764])).

fof(f764,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(k4_xboole_0(X0,X1),X0)
      | k1_xboole_0 = k4_xboole_0(k4_xboole_0(X0,X1),X0) ) ),
    inference(resolution,[],[f368,f362])).

fof(f362,plain,(
    ! [X4,X3] :
      ( ~ r2_hidden(sK2(sK1,k2_struct_0(sK0),k4_xboole_0(X3,X4)),X4)
      | k1_xboole_0 = k4_xboole_0(X3,X4) ) ),
    inference(backward_demodulation,[],[f181,f358])).

fof(f358,plain,(
    k1_xboole_0 = k4_xboole_0(sK1,k2_struct_0(sK0)) ),
    inference(resolution,[],[f343,f153])).

fof(f153,plain,(
    ! [X1] :
      ( r2_hidden(sK2(sK1,k2_struct_0(sK0),X1),X1)
      | k4_xboole_0(sK1,k2_struct_0(sK0)) = X1 ) ),
    inference(duplicate_literal_removal,[],[f152])).

fof(f152,plain,(
    ! [X1] :
      ( k4_xboole_0(sK1,k2_struct_0(sK0)) = X1
      | r2_hidden(sK2(sK1,k2_struct_0(sK0),X1),X1)
      | r2_hidden(sK2(sK1,k2_struct_0(sK0),X1),X1)
      | k4_xboole_0(sK1,k2_struct_0(sK0)) = X1 ) ),
    inference(resolution,[],[f120,f66])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK2(X0,X1,X2),X2)
      | r2_hidden(sK2(X0,X1,X2),X0)
      | k4_xboole_0(X0,X1) = X2 ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ( ( r2_hidden(sK2(X0,X1,X2),X1)
            | ~ r2_hidden(sK2(X0,X1,X2),X0)
            | ~ r2_hidden(sK2(X0,X1,X2),X2) )
          & ( ( ~ r2_hidden(sK2(X0,X1,X2),X1)
              & r2_hidden(sK2(X0,X1,X2),X0) )
            | r2_hidden(sK2(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( ~ r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f43,f44])).

fof(f44,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X3,X2) )
          & ( ( ~ r2_hidden(X3,X1)
              & r2_hidden(X3,X0) )
            | r2_hidden(X3,X2) ) )
     => ( ( r2_hidden(sK2(X0,X1,X2),X1)
          | ~ r2_hidden(sK2(X0,X1,X2),X0)
          | ~ r2_hidden(sK2(X0,X1,X2),X2) )
        & ( ( ~ r2_hidden(sK2(X0,X1,X2),X1)
            & r2_hidden(sK2(X0,X1,X2),X0) )
          | r2_hidden(sK2(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

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
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( ~ r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f42])).

fof(f42,plain,(
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
    inference(flattening,[],[f41])).

fof(f41,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).

fof(f120,plain,(
    ! [X2,X3] :
      ( ~ r2_hidden(sK2(X2,k2_struct_0(sK0),X3),sK1)
      | k4_xboole_0(X2,k2_struct_0(sK0)) = X3
      | r2_hidden(sK2(X2,k2_struct_0(sK0),X3),X3) ) ),
    inference(resolution,[],[f97,f67])).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(sK2(X0,X1,X2),X1)
      | k4_xboole_0(X0,X1) = X2
      | r2_hidden(sK2(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f97,plain,(
    ! [X1] :
      ( r2_hidden(X1,k2_struct_0(sK0))
      | ~ r2_hidden(X1,sK1) ) ),
    inference(backward_demodulation,[],[f85,f94])).

fof(f85,plain,(
    ! [X1] :
      ( ~ r2_hidden(X1,sK1)
      | r2_hidden(X1,u1_struct_0(sK0)) ) ),
    inference(resolution,[],[f49,f60])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ r2_hidden(X2,X1)
      | r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
          | ~ r2_hidden(X2,X1) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( r2_hidden(X2,X1)
         => r2_hidden(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_subset_1)).

fof(f343,plain,(
    ! [X0] : ~ r2_hidden(X0,k1_xboole_0) ),
    inference(superposition,[],[f332,f76])).

fof(f332,plain,(
    ! [X0,X1] : ~ r2_hidden(X1,k4_xboole_0(X0,X0)) ),
    inference(superposition,[],[f286,f258])).

fof(f258,plain,(
    ! [X0] : k4_xboole_0(sK1,k2_struct_0(sK0)) = k4_xboole_0(X0,X0) ),
    inference(duplicate_literal_removal,[],[f252])).

fof(f252,plain,(
    ! [X0] :
      ( k4_xboole_0(sK1,k2_struct_0(sK0)) = k4_xboole_0(X0,X0)
      | k4_xboole_0(sK1,k2_struct_0(sK0)) = k4_xboole_0(X0,X0) ) ),
    inference(resolution,[],[f181,f180])).

fof(f180,plain,(
    ! [X2,X1] :
      ( r2_hidden(sK2(sK1,k2_struct_0(sK0),k4_xboole_0(X1,X2)),X1)
      | k4_xboole_0(X1,X2) = k4_xboole_0(sK1,k2_struct_0(sK0)) ) ),
    inference(resolution,[],[f153,f79])).

fof(f79,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,k4_xboole_0(X0,X1))
      | r2_hidden(X4,X0) ) ),
    inference(equality_resolution,[],[f63])).

fof(f63,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f45])).

fof(f286,plain,(
    ! [X7] : ~ r2_hidden(X7,k4_xboole_0(sK1,k2_struct_0(sK0))) ),
    inference(subsumption_resolution,[],[f282,f281])).

fof(f281,plain,(
    ! [X4,X5] :
      ( ~ r2_hidden(X5,k4_xboole_0(sK1,k2_struct_0(sK0)))
      | ~ r2_hidden(X5,X4) ) ),
    inference(superposition,[],[f78,f258])).

fof(f78,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,k4_xboole_0(X0,X1))
      | ~ r2_hidden(X4,X1) ) ),
    inference(equality_resolution,[],[f64])).

fof(f64,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f45])).

fof(f282,plain,(
    ! [X6,X7] :
      ( ~ r2_hidden(X7,k4_xboole_0(sK1,k2_struct_0(sK0)))
      | r2_hidden(X7,X6) ) ),
    inference(superposition,[],[f79,f258])).

fof(f181,plain,(
    ! [X4,X3] :
      ( ~ r2_hidden(sK2(sK1,k2_struct_0(sK0),k4_xboole_0(X3,X4)),X4)
      | k4_xboole_0(sK1,k2_struct_0(sK0)) = k4_xboole_0(X3,X4) ) ),
    inference(resolution,[],[f153,f78])).

fof(f368,plain,(
    ! [X4,X2,X3] :
      ( r2_hidden(sK2(sK1,k2_struct_0(sK0),k4_xboole_0(k4_xboole_0(X2,X3),X4)),X2)
      | k1_xboole_0 = k4_xboole_0(k4_xboole_0(X2,X3),X4) ) ),
    inference(backward_demodulation,[],[f224,f358])).

fof(f224,plain,(
    ! [X4,X2,X3] :
      ( k4_xboole_0(sK1,k2_struct_0(sK0)) = k4_xboole_0(k4_xboole_0(X2,X3),X4)
      | r2_hidden(sK2(sK1,k2_struct_0(sK0),k4_xboole_0(k4_xboole_0(X2,X3),X4)),X2) ) ),
    inference(resolution,[],[f180,f79])).

fof(f72,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f298,plain,(
    k7_subset_1(k2_struct_0(sK0),k2_struct_0(sK0),sK1) = k3_xboole_0(k4_xboole_0(k2_struct_0(sK0),sK1),k2_struct_0(sK0)) ),
    inference(superposition,[],[f214,f76])).

fof(f214,plain,(
    ! [X1] : k3_xboole_0(k4_xboole_0(k2_struct_0(sK0),sK1),k4_xboole_0(k2_struct_0(sK0),X1)) = k7_subset_1(k2_struct_0(sK0),k4_xboole_0(k2_struct_0(sK0),X1),sK1) ),
    inference(superposition,[],[f148,f73])).

fof(f73,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f148,plain,(
    ! [X0] : k7_subset_1(k2_struct_0(sK0),k4_xboole_0(k2_struct_0(sK0),X0),sK1) = k3_xboole_0(k4_xboole_0(k2_struct_0(sK0),X0),k4_xboole_0(k2_struct_0(sK0),sK1)) ),
    inference(resolution,[],[f133,f75])).

fof(f75,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

fof(f133,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,k2_struct_0(sK0))
      | k7_subset_1(k2_struct_0(sK0),X0,sK1) = k3_xboole_0(X0,k4_xboole_0(k2_struct_0(sK0),sK1)) ) ),
    inference(resolution,[],[f129,f59])).

fof(f59,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f129,plain,(
    ! [X3] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_struct_0(sK0)))
      | k7_subset_1(k2_struct_0(sK0),X3,sK1) = k3_xboole_0(X3,k4_xboole_0(k2_struct_0(sK0),sK1)) ) ),
    inference(backward_demodulation,[],[f105,f123])).

fof(f123,plain,(
    ! [X0] : k9_subset_1(k2_struct_0(sK0),X0,k4_xboole_0(k2_struct_0(sK0),sK1)) = k3_xboole_0(X0,k4_xboole_0(k2_struct_0(sK0),sK1)) ),
    inference(resolution,[],[f122,f74])).

fof(f74,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

fof(f122,plain,(
    m1_subset_1(k4_xboole_0(k2_struct_0(sK0),sK1),k1_zfmisc_1(k2_struct_0(sK0))) ),
    inference(subsumption_resolution,[],[f121,f95])).

fof(f121,plain,
    ( m1_subset_1(k4_xboole_0(k2_struct_0(sK0),sK1),k1_zfmisc_1(k2_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0))) ),
    inference(superposition,[],[f56,f100])).

fof(f100,plain,(
    k3_subset_1(k2_struct_0(sK0),sK1) = k4_xboole_0(k2_struct_0(sK0),sK1) ),
    inference(backward_demodulation,[],[f88,f94])).

fof(f56,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_subset_1)).

fof(f105,plain,(
    ! [X3] :
      ( k7_subset_1(k2_struct_0(sK0),X3,sK1) = k9_subset_1(k2_struct_0(sK0),X3,k4_xboole_0(k2_struct_0(sK0),sK1))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_struct_0(sK0))) ) ),
    inference(forward_demodulation,[],[f104,f94])).

fof(f104,plain,(
    ! [X3] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_struct_0(sK0)))
      | k7_subset_1(u1_struct_0(sK0),X3,sK1) = k9_subset_1(u1_struct_0(sK0),X3,k4_xboole_0(u1_struct_0(sK0),sK1)) ) ),
    inference(backward_demodulation,[],[f93,f94])).

fof(f93,plain,(
    ! [X3] :
      ( k7_subset_1(u1_struct_0(sK0),X3,sK1) = k9_subset_1(u1_struct_0(sK0),X3,k4_xboole_0(u1_struct_0(sK0),sK1))
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(forward_demodulation,[],[f89,f88])).

fof(f89,plain,(
    ! [X3] :
      ( k7_subset_1(u1_struct_0(sK0),X3,sK1) = k9_subset_1(u1_struct_0(sK0),X3,k3_subset_1(u1_struct_0(sK0),sK1))
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(resolution,[],[f49,f54])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | k7_subset_1(X0,X1,X2) = k9_subset_1(X0,X1,k3_subset_1(X0,X2))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k7_subset_1(X0,X1,X2) = k9_subset_1(X0,X1,k3_subset_1(X0,X2))
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X0))
         => k7_subset_1(X0,X1,X2) = k9_subset_1(X0,X1,k3_subset_1(X0,X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t32_subset_1)).

fof(f101,plain,
    ( v3_pre_topc(k7_subset_1(k2_struct_0(sK0),k2_struct_0(sK0),sK1),sK0)
    | ~ v4_pre_topc(sK1,sK0) ),
    inference(backward_demodulation,[],[f90,f94])).

fof(f90,plain,
    ( ~ v4_pre_topc(sK1,sK0)
    | v3_pre_topc(k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1),sK0) ),
    inference(subsumption_resolution,[],[f83,f48])).

fof(f83,plain,
    ( ~ v4_pre_topc(sK1,sK0)
    | v3_pre_topc(k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1),sK0)
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f49,f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v4_pre_topc(X1,X0)
      | v3_pre_topc(k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1),X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_pre_topc(X1,X0)
              | ~ v3_pre_topc(k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1),X0) )
            & ( v3_pre_topc(k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1),X0)
              | ~ v4_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v4_pre_topc(X1,X0)
          <=> v3_pre_topc(k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1),X0) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v4_pre_topc(X1,X0)
          <=> v3_pre_topc(k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1),X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d6_pre_topc)).

fof(f864,plain,
    ( v4_pre_topc(sK1,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0))) ),
    inference(subsumption_resolution,[],[f862,f815])).

fof(f862,plain,
    ( ~ v3_pre_topc(k4_xboole_0(k2_struct_0(sK0),sK1),sK0)
    | v4_pre_topc(sK1,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0))) ),
    inference(superposition,[],[f117,f807])).

fof(f117,plain,(
    ! [X1] :
      ( ~ v3_pre_topc(k7_subset_1(k2_struct_0(sK0),k2_struct_0(sK0),X1),sK0)
      | v4_pre_topc(X1,sK0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK0))) ) ),
    inference(subsumption_resolution,[],[f115,f48])).

fof(f115,plain,(
    ! [X1] :
      ( ~ v3_pre_topc(k7_subset_1(k2_struct_0(sK0),k2_struct_0(sK0),X1),sK0)
      | v4_pre_topc(X1,sK0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK0)))
      | ~ l1_pre_topc(sK0) ) ),
    inference(superposition,[],[f53,f94])).

fof(f53,plain,(
    ! [X0,X1] :
      ( ~ v3_pre_topc(k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1),X0)
      | v4_pre_topc(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f39])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 17:11:26 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.22/0.51  % (11756)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.22/0.51  % (11779)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.22/0.51  % (11761)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.22/0.51  % (11771)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.22/0.52  % (11762)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.52  % (11757)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.22/0.52  % (11769)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.22/0.52  % (11763)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.22/0.53  % (11780)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 0.22/0.53  % (11760)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.22/0.53  % (11768)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.22/0.53  % (11758)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.22/0.53  % (11777)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 0.22/0.53  % (11770)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.22/0.53  % (11781)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 0.22/0.53  % (11759)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.22/0.54  % (11775)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 0.22/0.54  % (11782)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 0.22/0.54  % (11764)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.22/0.54  % (11776)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 0.22/0.54  % (11772)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 0.22/0.54  % (11773)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 0.22/0.54  % (11774)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 0.22/0.54  % (11785)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.22/0.54  % (11785)Refutation not found, incomplete strategy% (11785)------------------------------
% 0.22/0.54  % (11785)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.54  % (11785)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.54  
% 0.22/0.54  % (11785)Memory used [KB]: 1663
% 0.22/0.54  % (11785)Time elapsed: 0.001 s
% 0.22/0.54  % (11785)------------------------------
% 0.22/0.54  % (11785)------------------------------
% 0.22/0.54  % (11772)Refutation not found, incomplete strategy% (11772)------------------------------
% 0.22/0.54  % (11772)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.54  % (11772)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.54  
% 0.22/0.54  % (11772)Memory used [KB]: 10618
% 0.22/0.54  % (11772)Time elapsed: 0.139 s
% 0.22/0.54  % (11772)------------------------------
% 0.22/0.54  % (11772)------------------------------
% 0.22/0.54  % (11784)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 0.22/0.55  % (11784)Refutation not found, incomplete strategy% (11784)------------------------------
% 0.22/0.55  % (11784)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.55  % (11784)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.55  
% 0.22/0.55  % (11784)Memory used [KB]: 10746
% 0.22/0.55  % (11784)Time elapsed: 0.140 s
% 0.22/0.55  % (11784)------------------------------
% 0.22/0.55  % (11784)------------------------------
% 0.22/0.55  % (11778)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.22/0.55  % (11783)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 0.22/0.55  % (11766)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.22/0.55  % (11767)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.22/0.55  % (11765)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.22/0.55  % (11766)Refutation not found, incomplete strategy% (11766)------------------------------
% 0.22/0.55  % (11766)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.55  % (11766)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.55  
% 0.22/0.55  % (11766)Memory used [KB]: 10746
% 0.22/0.55  % (11766)Time elapsed: 0.152 s
% 0.22/0.55  % (11766)------------------------------
% 0.22/0.55  % (11766)------------------------------
% 0.22/0.59  % (11770)Refutation found. Thanks to Tanya!
% 0.22/0.59  % SZS status Theorem for theBenchmark
% 1.79/0.60  % SZS output start Proof for theBenchmark
% 1.79/0.60  fof(f866,plain,(
% 1.79/0.60    $false),
% 1.79/0.60    inference(subsumption_resolution,[],[f865,f95])).
% 1.79/0.60  fof(f95,plain,(
% 1.79/0.60    m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0)))),
% 1.79/0.60    inference(backward_demodulation,[],[f49,f94])).
% 1.79/0.60  fof(f94,plain,(
% 1.79/0.60    u1_struct_0(sK0) = k2_struct_0(sK0)),
% 1.79/0.60    inference(resolution,[],[f82,f61])).
% 1.79/0.60  fof(f61,plain,(
% 1.79/0.60    ( ! [X0] : (~l1_struct_0(X0) | k2_struct_0(X0) = u1_struct_0(X0)) )),
% 1.79/0.60    inference(cnf_transformation,[],[f31])).
% 1.79/0.60  fof(f31,plain,(
% 1.79/0.60    ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0))),
% 1.79/0.60    inference(ennf_transformation,[],[f18])).
% 1.79/0.60  fof(f18,axiom,(
% 1.79/0.60    ! [X0] : (l1_struct_0(X0) => k2_struct_0(X0) = u1_struct_0(X0))),
% 1.79/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).
% 1.79/0.60  fof(f82,plain,(
% 1.79/0.60    l1_struct_0(sK0)),
% 1.79/0.60    inference(resolution,[],[f48,f62])).
% 1.79/0.60  fof(f62,plain,(
% 1.79/0.60    ( ! [X0] : (~l1_pre_topc(X0) | l1_struct_0(X0)) )),
% 1.79/0.60    inference(cnf_transformation,[],[f32])).
% 1.79/0.60  fof(f32,plain,(
% 1.79/0.60    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 1.79/0.60    inference(ennf_transformation,[],[f20])).
% 1.79/0.60  fof(f20,axiom,(
% 1.79/0.60    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 1.79/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).
% 1.79/0.60  fof(f48,plain,(
% 1.79/0.60    l1_pre_topc(sK0)),
% 1.79/0.60    inference(cnf_transformation,[],[f38])).
% 1.79/0.60  fof(f38,plain,(
% 1.79/0.60    ((~v3_pre_topc(k3_subset_1(u1_struct_0(sK0),sK1),sK0) | ~v4_pre_topc(sK1,sK0)) & (v3_pre_topc(k3_subset_1(u1_struct_0(sK0),sK1),sK0) | v4_pre_topc(sK1,sK0)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0)),
% 1.79/0.60    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f35,f37,f36])).
% 1.79/0.60  fof(f36,plain,(
% 1.79/0.60    ? [X0] : (? [X1] : ((~v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) | ~v4_pre_topc(X1,X0)) & (v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) | v4_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0)) => (? [X1] : ((~v3_pre_topc(k3_subset_1(u1_struct_0(sK0),X1),sK0) | ~v4_pre_topc(X1,sK0)) & (v3_pre_topc(k3_subset_1(u1_struct_0(sK0),X1),sK0) | v4_pre_topc(X1,sK0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0))),
% 1.79/0.60    introduced(choice_axiom,[])).
% 1.79/0.60  fof(f37,plain,(
% 1.79/0.60    ? [X1] : ((~v3_pre_topc(k3_subset_1(u1_struct_0(sK0),X1),sK0) | ~v4_pre_topc(X1,sK0)) & (v3_pre_topc(k3_subset_1(u1_struct_0(sK0),X1),sK0) | v4_pre_topc(X1,sK0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) => ((~v3_pre_topc(k3_subset_1(u1_struct_0(sK0),sK1),sK0) | ~v4_pre_topc(sK1,sK0)) & (v3_pre_topc(k3_subset_1(u1_struct_0(sK0),sK1),sK0) | v4_pre_topc(sK1,sK0)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))))),
% 1.79/0.60    introduced(choice_axiom,[])).
% 1.79/0.60  fof(f35,plain,(
% 1.79/0.60    ? [X0] : (? [X1] : ((~v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) | ~v4_pre_topc(X1,X0)) & (v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) | v4_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 1.79/0.60    inference(flattening,[],[f34])).
% 1.79/0.60  fof(f34,plain,(
% 1.79/0.60    ? [X0] : (? [X1] : (((~v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) | ~v4_pre_topc(X1,X0)) & (v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) | v4_pre_topc(X1,X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 1.79/0.60    inference(nnf_transformation,[],[f23])).
% 1.79/0.60  fof(f23,plain,(
% 1.79/0.60    ? [X0] : (? [X1] : ((v4_pre_topc(X1,X0) <~> v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 1.79/0.60    inference(ennf_transformation,[],[f22])).
% 1.79/0.60  fof(f22,negated_conjecture,(
% 1.79/0.60    ~! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_pre_topc(X1,X0) <=> v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0))))),
% 1.79/0.60    inference(negated_conjecture,[],[f21])).
% 1.79/0.60  fof(f21,conjecture,(
% 1.79/0.60    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_pre_topc(X1,X0) <=> v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0))))),
% 1.79/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_tops_1)).
% 1.79/0.60  fof(f49,plain,(
% 1.79/0.60    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.79/0.60    inference(cnf_transformation,[],[f38])).
% 1.79/0.60  fof(f865,plain,(
% 1.79/0.60    ~m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0)))),
% 1.79/0.60    inference(subsumption_resolution,[],[f864,f819])).
% 1.79/0.60  fof(f819,plain,(
% 1.79/0.60    ~v4_pre_topc(sK1,sK0)),
% 1.79/0.60    inference(resolution,[],[f815,f103])).
% 1.79/0.60  fof(f103,plain,(
% 1.79/0.60    ~v3_pre_topc(k4_xboole_0(k2_struct_0(sK0),sK1),sK0) | ~v4_pre_topc(sK1,sK0)),
% 1.79/0.60    inference(backward_demodulation,[],[f92,f94])).
% 1.79/0.60  fof(f92,plain,(
% 1.79/0.60    ~v3_pre_topc(k4_xboole_0(u1_struct_0(sK0),sK1),sK0) | ~v4_pre_topc(sK1,sK0)),
% 1.79/0.60    inference(backward_demodulation,[],[f51,f88])).
% 1.79/0.60  fof(f88,plain,(
% 1.79/0.60    k3_subset_1(u1_struct_0(sK0),sK1) = k4_xboole_0(u1_struct_0(sK0),sK1)),
% 1.79/0.60    inference(resolution,[],[f49,f55])).
% 1.79/0.60  fof(f55,plain,(
% 1.79/0.60    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)) )),
% 1.79/0.60    inference(cnf_transformation,[],[f26])).
% 1.79/0.60  fof(f26,plain,(
% 1.79/0.60    ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.79/0.60    inference(ennf_transformation,[],[f9])).
% 1.79/0.60  fof(f9,axiom,(
% 1.79/0.60    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1))),
% 1.79/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).
% 1.79/0.60  fof(f51,plain,(
% 1.79/0.60    ~v3_pre_topc(k3_subset_1(u1_struct_0(sK0),sK1),sK0) | ~v4_pre_topc(sK1,sK0)),
% 1.79/0.60    inference(cnf_transformation,[],[f38])).
% 1.79/0.60  fof(f815,plain,(
% 1.79/0.60    v3_pre_topc(k4_xboole_0(k2_struct_0(sK0),sK1),sK0)),
% 1.79/0.60    inference(subsumption_resolution,[],[f808,f102])).
% 1.79/0.60  fof(f102,plain,(
% 1.79/0.60    v3_pre_topc(k4_xboole_0(k2_struct_0(sK0),sK1),sK0) | v4_pre_topc(sK1,sK0)),
% 1.79/0.60    inference(backward_demodulation,[],[f91,f94])).
% 1.79/0.60  fof(f91,plain,(
% 1.79/0.60    v3_pre_topc(k4_xboole_0(u1_struct_0(sK0),sK1),sK0) | v4_pre_topc(sK1,sK0)),
% 1.79/0.60    inference(backward_demodulation,[],[f50,f88])).
% 1.79/0.60  fof(f50,plain,(
% 1.79/0.60    v3_pre_topc(k3_subset_1(u1_struct_0(sK0),sK1),sK0) | v4_pre_topc(sK1,sK0)),
% 1.79/0.60    inference(cnf_transformation,[],[f38])).
% 1.79/0.60  fof(f808,plain,(
% 1.79/0.60    v3_pre_topc(k4_xboole_0(k2_struct_0(sK0),sK1),sK0) | ~v4_pre_topc(sK1,sK0)),
% 1.79/0.60    inference(backward_demodulation,[],[f101,f807])).
% 1.79/0.60  fof(f807,plain,(
% 1.79/0.60    k4_xboole_0(k2_struct_0(sK0),sK1) = k7_subset_1(k2_struct_0(sK0),k2_struct_0(sK0),sK1)),
% 1.79/0.60    inference(backward_demodulation,[],[f298,f806])).
% 1.79/0.60  fof(f806,plain,(
% 1.79/0.60    ( ! [X2,X3] : (k4_xboole_0(X2,X3) = k3_xboole_0(k4_xboole_0(X2,X3),X2)) )),
% 1.79/0.60    inference(forward_demodulation,[],[f793,f76])).
% 1.79/0.60  fof(f76,plain,(
% 1.79/0.60    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 1.79/0.60    inference(cnf_transformation,[],[f6])).
% 1.79/0.60  fof(f6,axiom,(
% 1.79/0.60    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 1.79/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).
% 1.79/0.60  fof(f793,plain,(
% 1.79/0.60    ( ! [X2,X3] : (k3_xboole_0(k4_xboole_0(X2,X3),X2) = k4_xboole_0(k4_xboole_0(X2,X3),k1_xboole_0)) )),
% 1.79/0.60    inference(superposition,[],[f72,f782])).
% 1.79/0.60  fof(f782,plain,(
% 1.79/0.60    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(k4_xboole_0(X0,X1),X0)) )),
% 1.79/0.60    inference(duplicate_literal_removal,[],[f764])).
% 1.79/0.60  fof(f764,plain,(
% 1.79/0.60    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(k4_xboole_0(X0,X1),X0) | k1_xboole_0 = k4_xboole_0(k4_xboole_0(X0,X1),X0)) )),
% 1.79/0.60    inference(resolution,[],[f368,f362])).
% 1.79/0.60  fof(f362,plain,(
% 1.79/0.60    ( ! [X4,X3] : (~r2_hidden(sK2(sK1,k2_struct_0(sK0),k4_xboole_0(X3,X4)),X4) | k1_xboole_0 = k4_xboole_0(X3,X4)) )),
% 1.79/0.60    inference(backward_demodulation,[],[f181,f358])).
% 1.79/0.60  fof(f358,plain,(
% 1.79/0.60    k1_xboole_0 = k4_xboole_0(sK1,k2_struct_0(sK0))),
% 1.79/0.60    inference(resolution,[],[f343,f153])).
% 1.79/0.60  fof(f153,plain,(
% 1.79/0.60    ( ! [X1] : (r2_hidden(sK2(sK1,k2_struct_0(sK0),X1),X1) | k4_xboole_0(sK1,k2_struct_0(sK0)) = X1) )),
% 1.79/0.60    inference(duplicate_literal_removal,[],[f152])).
% 1.79/0.60  fof(f152,plain,(
% 1.79/0.60    ( ! [X1] : (k4_xboole_0(sK1,k2_struct_0(sK0)) = X1 | r2_hidden(sK2(sK1,k2_struct_0(sK0),X1),X1) | r2_hidden(sK2(sK1,k2_struct_0(sK0),X1),X1) | k4_xboole_0(sK1,k2_struct_0(sK0)) = X1) )),
% 1.79/0.60    inference(resolution,[],[f120,f66])).
% 1.79/0.60  fof(f66,plain,(
% 1.79/0.60    ( ! [X2,X0,X1] : (r2_hidden(sK2(X0,X1,X2),X2) | r2_hidden(sK2(X0,X1,X2),X0) | k4_xboole_0(X0,X1) = X2) )),
% 1.79/0.60    inference(cnf_transformation,[],[f45])).
% 1.79/0.60  fof(f45,plain,(
% 1.79/0.60    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ((r2_hidden(sK2(X0,X1,X2),X1) | ~r2_hidden(sK2(X0,X1,X2),X0) | ~r2_hidden(sK2(X0,X1,X2),X2)) & ((~r2_hidden(sK2(X0,X1,X2),X1) & r2_hidden(sK2(X0,X1,X2),X0)) | r2_hidden(sK2(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 1.79/0.60    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f43,f44])).
% 1.79/0.60  fof(f44,plain,(
% 1.79/0.60    ! [X2,X1,X0] : (? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2))) => ((r2_hidden(sK2(X0,X1,X2),X1) | ~r2_hidden(sK2(X0,X1,X2),X0) | ~r2_hidden(sK2(X0,X1,X2),X2)) & ((~r2_hidden(sK2(X0,X1,X2),X1) & r2_hidden(sK2(X0,X1,X2),X0)) | r2_hidden(sK2(X0,X1,X2),X2))))),
% 1.79/0.60    introduced(choice_axiom,[])).
% 1.79/0.60  fof(f43,plain,(
% 1.79/0.60    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 1.79/0.60    inference(rectify,[],[f42])).
% 1.79/0.60  fof(f42,plain,(
% 1.79/0.60    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 1.79/0.60    inference(flattening,[],[f41])).
% 1.79/0.60  fof(f41,plain,(
% 1.79/0.60    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : (((r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 1.79/0.60    inference(nnf_transformation,[],[f2])).
% 1.79/0.60  fof(f2,axiom,(
% 1.79/0.60    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 1.79/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).
% 1.79/0.60  fof(f120,plain,(
% 1.79/0.60    ( ! [X2,X3] : (~r2_hidden(sK2(X2,k2_struct_0(sK0),X3),sK1) | k4_xboole_0(X2,k2_struct_0(sK0)) = X3 | r2_hidden(sK2(X2,k2_struct_0(sK0),X3),X3)) )),
% 1.79/0.60    inference(resolution,[],[f97,f67])).
% 1.79/0.60  fof(f67,plain,(
% 1.79/0.60    ( ! [X2,X0,X1] : (~r2_hidden(sK2(X0,X1,X2),X1) | k4_xboole_0(X0,X1) = X2 | r2_hidden(sK2(X0,X1,X2),X2)) )),
% 1.79/0.60    inference(cnf_transformation,[],[f45])).
% 1.79/0.60  fof(f97,plain,(
% 1.79/0.60    ( ! [X1] : (r2_hidden(X1,k2_struct_0(sK0)) | ~r2_hidden(X1,sK1)) )),
% 1.79/0.60    inference(backward_demodulation,[],[f85,f94])).
% 1.79/0.60  fof(f85,plain,(
% 1.79/0.60    ( ! [X1] : (~r2_hidden(X1,sK1) | r2_hidden(X1,u1_struct_0(sK0))) )),
% 1.79/0.60    inference(resolution,[],[f49,f60])).
% 1.79/0.60  fof(f60,plain,(
% 1.79/0.60    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~r2_hidden(X2,X1) | r2_hidden(X2,X0)) )),
% 1.79/0.60    inference(cnf_transformation,[],[f30])).
% 1.79/0.60  fof(f30,plain,(
% 1.79/0.60    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) | ~r2_hidden(X2,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.79/0.60    inference(ennf_transformation,[],[f12])).
% 1.79/0.60  fof(f12,axiom,(
% 1.79/0.60    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (r2_hidden(X2,X1) => r2_hidden(X2,X0)))),
% 1.79/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_subset_1)).
% 1.79/0.60  fof(f343,plain,(
% 1.79/0.60    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0)) )),
% 1.79/0.60    inference(superposition,[],[f332,f76])).
% 1.79/0.60  fof(f332,plain,(
% 1.79/0.60    ( ! [X0,X1] : (~r2_hidden(X1,k4_xboole_0(X0,X0))) )),
% 1.79/0.60    inference(superposition,[],[f286,f258])).
% 1.79/0.60  fof(f258,plain,(
% 1.79/0.60    ( ! [X0] : (k4_xboole_0(sK1,k2_struct_0(sK0)) = k4_xboole_0(X0,X0)) )),
% 1.79/0.60    inference(duplicate_literal_removal,[],[f252])).
% 1.79/0.60  fof(f252,plain,(
% 1.79/0.60    ( ! [X0] : (k4_xboole_0(sK1,k2_struct_0(sK0)) = k4_xboole_0(X0,X0) | k4_xboole_0(sK1,k2_struct_0(sK0)) = k4_xboole_0(X0,X0)) )),
% 1.79/0.60    inference(resolution,[],[f181,f180])).
% 1.79/0.60  fof(f180,plain,(
% 1.79/0.60    ( ! [X2,X1] : (r2_hidden(sK2(sK1,k2_struct_0(sK0),k4_xboole_0(X1,X2)),X1) | k4_xboole_0(X1,X2) = k4_xboole_0(sK1,k2_struct_0(sK0))) )),
% 1.79/0.60    inference(resolution,[],[f153,f79])).
% 1.79/0.60  fof(f79,plain,(
% 1.79/0.60    ( ! [X4,X0,X1] : (~r2_hidden(X4,k4_xboole_0(X0,X1)) | r2_hidden(X4,X0)) )),
% 1.79/0.60    inference(equality_resolution,[],[f63])).
% 1.79/0.60  fof(f63,plain,(
% 1.79/0.60    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X0) | ~r2_hidden(X4,X2) | k4_xboole_0(X0,X1) != X2) )),
% 1.79/0.60    inference(cnf_transformation,[],[f45])).
% 1.79/0.60  fof(f286,plain,(
% 1.79/0.60    ( ! [X7] : (~r2_hidden(X7,k4_xboole_0(sK1,k2_struct_0(sK0)))) )),
% 1.79/0.60    inference(subsumption_resolution,[],[f282,f281])).
% 1.79/0.60  fof(f281,plain,(
% 1.79/0.60    ( ! [X4,X5] : (~r2_hidden(X5,k4_xboole_0(sK1,k2_struct_0(sK0))) | ~r2_hidden(X5,X4)) )),
% 1.79/0.60    inference(superposition,[],[f78,f258])).
% 1.79/0.60  fof(f78,plain,(
% 1.79/0.60    ( ! [X4,X0,X1] : (~r2_hidden(X4,k4_xboole_0(X0,X1)) | ~r2_hidden(X4,X1)) )),
% 1.79/0.60    inference(equality_resolution,[],[f64])).
% 1.79/0.60  fof(f64,plain,(
% 1.79/0.60    ( ! [X4,X2,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,X2) | k4_xboole_0(X0,X1) != X2) )),
% 1.79/0.60    inference(cnf_transformation,[],[f45])).
% 1.79/0.60  fof(f282,plain,(
% 1.79/0.60    ( ! [X6,X7] : (~r2_hidden(X7,k4_xboole_0(sK1,k2_struct_0(sK0))) | r2_hidden(X7,X6)) )),
% 1.79/0.60    inference(superposition,[],[f79,f258])).
% 1.79/0.60  fof(f181,plain,(
% 1.79/0.60    ( ! [X4,X3] : (~r2_hidden(sK2(sK1,k2_struct_0(sK0),k4_xboole_0(X3,X4)),X4) | k4_xboole_0(sK1,k2_struct_0(sK0)) = k4_xboole_0(X3,X4)) )),
% 1.79/0.60    inference(resolution,[],[f153,f78])).
% 1.79/0.60  fof(f368,plain,(
% 1.79/0.60    ( ! [X4,X2,X3] : (r2_hidden(sK2(sK1,k2_struct_0(sK0),k4_xboole_0(k4_xboole_0(X2,X3),X4)),X2) | k1_xboole_0 = k4_xboole_0(k4_xboole_0(X2,X3),X4)) )),
% 1.79/0.60    inference(backward_demodulation,[],[f224,f358])).
% 1.79/0.60  fof(f224,plain,(
% 1.79/0.60    ( ! [X4,X2,X3] : (k4_xboole_0(sK1,k2_struct_0(sK0)) = k4_xboole_0(k4_xboole_0(X2,X3),X4) | r2_hidden(sK2(sK1,k2_struct_0(sK0),k4_xboole_0(k4_xboole_0(X2,X3),X4)),X2)) )),
% 1.79/0.60    inference(resolution,[],[f180,f79])).
% 1.79/0.60  fof(f72,plain,(
% 1.79/0.60    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 1.79/0.60    inference(cnf_transformation,[],[f7])).
% 1.79/0.60  fof(f7,axiom,(
% 1.79/0.60    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 1.79/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).
% 1.79/0.60  fof(f298,plain,(
% 1.79/0.60    k7_subset_1(k2_struct_0(sK0),k2_struct_0(sK0),sK1) = k3_xboole_0(k4_xboole_0(k2_struct_0(sK0),sK1),k2_struct_0(sK0))),
% 1.79/0.60    inference(superposition,[],[f214,f76])).
% 1.79/0.60  fof(f214,plain,(
% 1.79/0.60    ( ! [X1] : (k3_xboole_0(k4_xboole_0(k2_struct_0(sK0),sK1),k4_xboole_0(k2_struct_0(sK0),X1)) = k7_subset_1(k2_struct_0(sK0),k4_xboole_0(k2_struct_0(sK0),X1),sK1)) )),
% 1.79/0.60    inference(superposition,[],[f148,f73])).
% 1.79/0.60  fof(f73,plain,(
% 1.79/0.60    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 1.79/0.60    inference(cnf_transformation,[],[f1])).
% 1.79/0.60  fof(f1,axiom,(
% 1.79/0.60    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 1.79/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 1.79/0.60  fof(f148,plain,(
% 1.79/0.60    ( ! [X0] : (k7_subset_1(k2_struct_0(sK0),k4_xboole_0(k2_struct_0(sK0),X0),sK1) = k3_xboole_0(k4_xboole_0(k2_struct_0(sK0),X0),k4_xboole_0(k2_struct_0(sK0),sK1))) )),
% 1.79/0.60    inference(resolution,[],[f133,f75])).
% 1.79/0.60  fof(f75,plain,(
% 1.79/0.60    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 1.79/0.60    inference(cnf_transformation,[],[f5])).
% 1.79/0.60  fof(f5,axiom,(
% 1.79/0.60    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 1.79/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).
% 1.79/0.60  fof(f133,plain,(
% 1.79/0.60    ( ! [X0] : (~r1_tarski(X0,k2_struct_0(sK0)) | k7_subset_1(k2_struct_0(sK0),X0,sK1) = k3_xboole_0(X0,k4_xboole_0(k2_struct_0(sK0),sK1))) )),
% 1.79/0.60    inference(resolution,[],[f129,f59])).
% 1.79/0.60  fof(f59,plain,(
% 1.79/0.60    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 1.79/0.60    inference(cnf_transformation,[],[f40])).
% 1.79/0.60  fof(f40,plain,(
% 1.79/0.60    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 1.79/0.60    inference(nnf_transformation,[],[f16])).
% 1.79/0.60  fof(f16,axiom,(
% 1.79/0.60    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 1.79/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).
% 1.79/0.60  fof(f129,plain,(
% 1.79/0.60    ( ! [X3] : (~m1_subset_1(X3,k1_zfmisc_1(k2_struct_0(sK0))) | k7_subset_1(k2_struct_0(sK0),X3,sK1) = k3_xboole_0(X3,k4_xboole_0(k2_struct_0(sK0),sK1))) )),
% 1.79/0.60    inference(backward_demodulation,[],[f105,f123])).
% 1.79/0.60  fof(f123,plain,(
% 1.79/0.60    ( ! [X0] : (k9_subset_1(k2_struct_0(sK0),X0,k4_xboole_0(k2_struct_0(sK0),sK1)) = k3_xboole_0(X0,k4_xboole_0(k2_struct_0(sK0),sK1))) )),
% 1.79/0.60    inference(resolution,[],[f122,f74])).
% 1.79/0.61  fof(f74,plain,(
% 1.79/0.61    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(X0)) | k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)) )),
% 1.79/0.61    inference(cnf_transformation,[],[f33])).
% 1.79/0.61  fof(f33,plain,(
% 1.79/0.61    ! [X0,X1,X2] : (k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 1.79/0.61    inference(ennf_transformation,[],[f13])).
% 1.79/0.61  fof(f13,axiom,(
% 1.79/0.61    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2))),
% 1.79/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k9_subset_1)).
% 1.79/0.61  fof(f122,plain,(
% 1.79/0.61    m1_subset_1(k4_xboole_0(k2_struct_0(sK0),sK1),k1_zfmisc_1(k2_struct_0(sK0)))),
% 1.79/0.61    inference(subsumption_resolution,[],[f121,f95])).
% 1.79/0.61  fof(f121,plain,(
% 1.79/0.61    m1_subset_1(k4_xboole_0(k2_struct_0(sK0),sK1),k1_zfmisc_1(k2_struct_0(sK0))) | ~m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0)))),
% 1.79/0.61    inference(superposition,[],[f56,f100])).
% 1.79/0.61  fof(f100,plain,(
% 1.79/0.61    k3_subset_1(k2_struct_0(sK0),sK1) = k4_xboole_0(k2_struct_0(sK0),sK1)),
% 1.79/0.61    inference(backward_demodulation,[],[f88,f94])).
% 1.79/0.61  fof(f56,plain,(
% 1.79/0.61    ( ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 1.79/0.61    inference(cnf_transformation,[],[f27])).
% 1.79/0.61  fof(f27,plain,(
% 1.79/0.61    ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.79/0.61    inference(ennf_transformation,[],[f11])).
% 1.79/0.61  fof(f11,axiom,(
% 1.79/0.61    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)))),
% 1.79/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_subset_1)).
% 1.79/0.61  fof(f105,plain,(
% 1.79/0.61    ( ! [X3] : (k7_subset_1(k2_struct_0(sK0),X3,sK1) = k9_subset_1(k2_struct_0(sK0),X3,k4_xboole_0(k2_struct_0(sK0),sK1)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_struct_0(sK0)))) )),
% 1.79/0.61    inference(forward_demodulation,[],[f104,f94])).
% 1.79/0.61  fof(f104,plain,(
% 1.79/0.61    ( ! [X3] : (~m1_subset_1(X3,k1_zfmisc_1(k2_struct_0(sK0))) | k7_subset_1(u1_struct_0(sK0),X3,sK1) = k9_subset_1(u1_struct_0(sK0),X3,k4_xboole_0(u1_struct_0(sK0),sK1))) )),
% 1.79/0.61    inference(backward_demodulation,[],[f93,f94])).
% 1.79/0.61  fof(f93,plain,(
% 1.79/0.61    ( ! [X3] : (k7_subset_1(u1_struct_0(sK0),X3,sK1) = k9_subset_1(u1_struct_0(sK0),X3,k4_xboole_0(u1_struct_0(sK0),sK1)) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))) )),
% 1.79/0.61    inference(forward_demodulation,[],[f89,f88])).
% 1.79/0.61  fof(f89,plain,(
% 1.79/0.61    ( ! [X3] : (k7_subset_1(u1_struct_0(sK0),X3,sK1) = k9_subset_1(u1_struct_0(sK0),X3,k3_subset_1(u1_struct_0(sK0),sK1)) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))) )),
% 1.79/0.61    inference(resolution,[],[f49,f54])).
% 1.79/0.61  fof(f54,plain,(
% 1.79/0.61    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(X0)) | k7_subset_1(X0,X1,X2) = k9_subset_1(X0,X1,k3_subset_1(X0,X2)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 1.79/0.61    inference(cnf_transformation,[],[f25])).
% 1.79/0.61  fof(f25,plain,(
% 1.79/0.61    ! [X0,X1] : (! [X2] : (k7_subset_1(X0,X1,X2) = k9_subset_1(X0,X1,k3_subset_1(X0,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.79/0.61    inference(ennf_transformation,[],[f14])).
% 1.79/0.61  fof(f14,axiom,(
% 1.79/0.61    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => k7_subset_1(X0,X1,X2) = k9_subset_1(X0,X1,k3_subset_1(X0,X2))))),
% 1.79/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t32_subset_1)).
% 1.79/0.61  fof(f101,plain,(
% 1.79/0.61    v3_pre_topc(k7_subset_1(k2_struct_0(sK0),k2_struct_0(sK0),sK1),sK0) | ~v4_pre_topc(sK1,sK0)),
% 1.79/0.61    inference(backward_demodulation,[],[f90,f94])).
% 1.79/0.61  fof(f90,plain,(
% 1.79/0.61    ~v4_pre_topc(sK1,sK0) | v3_pre_topc(k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1),sK0)),
% 1.79/0.61    inference(subsumption_resolution,[],[f83,f48])).
% 1.79/0.61  fof(f83,plain,(
% 1.79/0.61    ~v4_pre_topc(sK1,sK0) | v3_pre_topc(k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1),sK0) | ~l1_pre_topc(sK0)),
% 1.79/0.61    inference(resolution,[],[f49,f52])).
% 1.79/0.61  fof(f52,plain,(
% 1.79/0.61    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v4_pre_topc(X1,X0) | v3_pre_topc(k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1),X0) | ~l1_pre_topc(X0)) )),
% 1.79/0.61    inference(cnf_transformation,[],[f39])).
% 1.79/0.61  fof(f39,plain,(
% 1.79/0.61    ! [X0] : (! [X1] : (((v4_pre_topc(X1,X0) | ~v3_pre_topc(k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1),X0)) & (v3_pre_topc(k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1),X0) | ~v4_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.79/0.61    inference(nnf_transformation,[],[f24])).
% 1.79/0.61  fof(f24,plain,(
% 1.79/0.61    ! [X0] : (! [X1] : ((v4_pre_topc(X1,X0) <=> v3_pre_topc(k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1),X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.79/0.61    inference(ennf_transformation,[],[f19])).
% 1.79/0.61  fof(f19,axiom,(
% 1.79/0.61    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_pre_topc(X1,X0) <=> v3_pre_topc(k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1),X0))))),
% 1.79/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d6_pre_topc)).
% 1.79/0.61  fof(f864,plain,(
% 1.79/0.61    v4_pre_topc(sK1,sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0)))),
% 1.79/0.61    inference(subsumption_resolution,[],[f862,f815])).
% 1.79/0.61  fof(f862,plain,(
% 1.79/0.61    ~v3_pre_topc(k4_xboole_0(k2_struct_0(sK0),sK1),sK0) | v4_pre_topc(sK1,sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0)))),
% 1.79/0.61    inference(superposition,[],[f117,f807])).
% 1.79/0.61  fof(f117,plain,(
% 1.79/0.61    ( ! [X1] : (~v3_pre_topc(k7_subset_1(k2_struct_0(sK0),k2_struct_0(sK0),X1),sK0) | v4_pre_topc(X1,sK0) | ~m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK0)))) )),
% 1.79/0.61    inference(subsumption_resolution,[],[f115,f48])).
% 1.79/0.61  fof(f115,plain,(
% 1.79/0.61    ( ! [X1] : (~v3_pre_topc(k7_subset_1(k2_struct_0(sK0),k2_struct_0(sK0),X1),sK0) | v4_pre_topc(X1,sK0) | ~m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK0))) | ~l1_pre_topc(sK0)) )),
% 1.79/0.61    inference(superposition,[],[f53,f94])).
% 1.79/0.61  fof(f53,plain,(
% 1.79/0.61    ( ! [X0,X1] : (~v3_pre_topc(k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1),X0) | v4_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 1.79/0.61    inference(cnf_transformation,[],[f39])).
% 1.79/0.61  % SZS output end Proof for theBenchmark
% 1.79/0.61  % (11770)------------------------------
% 1.79/0.61  % (11770)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.79/0.61  % (11770)Termination reason: Refutation
% 1.79/0.61  
% 1.79/0.61  % (11770)Memory used [KB]: 2174
% 1.79/0.61  % (11770)Time elapsed: 0.194 s
% 1.79/0.61  % (11770)------------------------------
% 1.79/0.61  % (11770)------------------------------
% 1.95/0.61  % (11755)Success in time 0.251 s
%------------------------------------------------------------------------------
