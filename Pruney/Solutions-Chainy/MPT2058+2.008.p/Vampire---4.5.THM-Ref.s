%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:23:31 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  200 (5534 expanded)
%              Number of leaves         :   23 (1716 expanded)
%              Depth                    :   59
%              Number of atoms          : 1045 (51501 expanded)
%              Number of equality atoms :   41 ( 880 expanded)
%              Maximal formula depth    :   14 (   6 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f325,plain,(
    $false ),
    inference(subsumption_resolution,[],[f324,f58])).

fof(f58,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f48])).

fof(f48,plain,
    ( ( ~ r1_waybel_7(sK0,sK1,sK2)
      | ~ r3_waybel_9(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK2) )
    & ( r1_waybel_7(sK0,sK1,sK2)
      | r3_waybel_9(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK2) )
    & m1_subset_1(sK2,u1_struct_0(sK0))
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))))
    & v13_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0)))
    & v2_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0)))
    & v1_subset_1(sK1,u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))
    & ~ v1_xboole_0(sK1)
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f44,f47,f46,f45])).

fof(f45,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ( ~ r1_waybel_7(X0,X1,X2)
                  | ~ r3_waybel_9(X0,k3_yellow19(X0,k2_struct_0(X0),X1),X2) )
                & ( r1_waybel_7(X0,X1,X2)
                  | r3_waybel_9(X0,k3_yellow19(X0,k2_struct_0(X0),X1),X2) )
                & m1_subset_1(X2,u1_struct_0(X0)) )
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
            & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
            & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
            & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0))))
            & ~ v1_xboole_0(X1) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ( ~ r1_waybel_7(sK0,X1,X2)
                | ~ r3_waybel_9(sK0,k3_yellow19(sK0,k2_struct_0(sK0),X1),X2) )
              & ( r1_waybel_7(sK0,X1,X2)
                | r3_waybel_9(sK0,k3_yellow19(sK0,k2_struct_0(sK0),X1),X2) )
              & m1_subset_1(X2,u1_struct_0(sK0)) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))))
          & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(sK0)))
          & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(sK0)))
          & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))
          & ~ v1_xboole_0(X1) )
      & l1_pre_topc(sK0)
      & v2_pre_topc(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f46,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ( ~ r1_waybel_7(sK0,X1,X2)
              | ~ r3_waybel_9(sK0,k3_yellow19(sK0,k2_struct_0(sK0),X1),X2) )
            & ( r1_waybel_7(sK0,X1,X2)
              | r3_waybel_9(sK0,k3_yellow19(sK0,k2_struct_0(sK0),X1),X2) )
            & m1_subset_1(X2,u1_struct_0(sK0)) )
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))))
        & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(sK0)))
        & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(sK0)))
        & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))
        & ~ v1_xboole_0(X1) )
   => ( ? [X2] :
          ( ( ~ r1_waybel_7(sK0,sK1,X2)
            | ~ r3_waybel_9(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1),X2) )
          & ( r1_waybel_7(sK0,sK1,X2)
            | r3_waybel_9(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1),X2) )
          & m1_subset_1(X2,u1_struct_0(sK0)) )
      & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))))
      & v13_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0)))
      & v2_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0)))
      & v1_subset_1(sK1,u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))
      & ~ v1_xboole_0(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f47,plain,
    ( ? [X2] :
        ( ( ~ r1_waybel_7(sK0,sK1,X2)
          | ~ r3_waybel_9(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1),X2) )
        & ( r1_waybel_7(sK0,sK1,X2)
          | r3_waybel_9(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1),X2) )
        & m1_subset_1(X2,u1_struct_0(sK0)) )
   => ( ( ~ r1_waybel_7(sK0,sK1,sK2)
        | ~ r3_waybel_9(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK2) )
      & ( r1_waybel_7(sK0,sK1,sK2)
        | r3_waybel_9(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK2) )
      & m1_subset_1(sK2,u1_struct_0(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f44,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ~ r1_waybel_7(X0,X1,X2)
                | ~ r3_waybel_9(X0,k3_yellow19(X0,k2_struct_0(X0),X1),X2) )
              & ( r1_waybel_7(X0,X1,X2)
                | r3_waybel_9(X0,k3_yellow19(X0,k2_struct_0(X0),X1),X2) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
          & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
          & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
          & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0))))
          & ~ v1_xboole_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f43])).

fof(f43,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ~ r1_waybel_7(X0,X1,X2)
                | ~ r3_waybel_9(X0,k3_yellow19(X0,k2_struct_0(X0),X1),X2) )
              & ( r1_waybel_7(X0,X1,X2)
                | r3_waybel_9(X0,k3_yellow19(X0,k2_struct_0(X0),X1),X2) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
          & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
          & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
          & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0))))
          & ~ v1_xboole_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f21])).

fof(f21,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( r3_waybel_9(X0,k3_yellow19(X0,k2_struct_0(X0),X1),X2)
              <~> r1_waybel_7(X0,X1,X2) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
          & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
          & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
          & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0))))
          & ~ v1_xboole_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( r3_waybel_9(X0,k3_yellow19(X0,k2_struct_0(X0),X1),X2)
              <~> r1_waybel_7(X0,X1,X2) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
          & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
          & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
          & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0))))
          & ~ v1_xboole_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
              & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
              & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
              & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0))))
              & ~ v1_xboole_0(X1) )
           => ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => ( r3_waybel_9(X0,k3_yellow19(X0,k2_struct_0(X0),X1),X2)
                <=> r1_waybel_7(X0,X1,X2) ) ) ) ) ),
    inference(negated_conjecture,[],[f18])).

fof(f18,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
            & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
            & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
            & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0))))
            & ~ v1_xboole_0(X1) )
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( r3_waybel_9(X0,k3_yellow19(X0,k2_struct_0(X0),X1),X2)
              <=> r1_waybel_7(X0,X1,X2) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_yellow19)).

fof(f324,plain,(
    v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f323,f59])).

fof(f59,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f48])).

fof(f323,plain,
    ( ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f322,f60])).

fof(f60,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f48])).

fof(f322,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f321,f83])).

fof(f83,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(sK3(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f53,plain,(
    ! [X0] :
      ( ( v4_pre_topc(sK3(X0),X0)
        & ~ v1_xboole_0(sK3(X0))
        & m1_subset_1(sK3(X0),k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f31,f52])).

fof(f52,plain,(
    ! [X0] :
      ( ? [X1] :
          ( v4_pre_topc(X1,X0)
          & ~ v1_xboole_0(X1)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( v4_pre_topc(sK3(X0),X0)
        & ~ v1_xboole_0(sK3(X0))
        & m1_subset_1(sK3(X0),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,(
    ! [X0] :
      ( ? [X1] :
          ( v4_pre_topc(X1,X0)
          & ~ v1_xboole_0(X1)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ? [X1] :
          ( v4_pre_topc(X1,X0)
          & ~ v1_xboole_0(X1)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ? [X1] :
          ( v4_pre_topc(X1,X0)
          & ~ v1_xboole_0(X1)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',rc7_pre_topc)).

fof(f321,plain,(
    v1_xboole_0(sK3(sK0)) ),
    inference(resolution,[],[f320,f171])).

fof(f171,plain,
    ( ~ v1_xboole_0(k2_struct_0(sK0))
    | v1_xboole_0(sK3(sK0)) ),
    inference(backward_demodulation,[],[f141,f164])).

fof(f164,plain,(
    k2_struct_0(sK0) = u1_struct_0(sK0) ),
    inference(forward_demodulation,[],[f163,f138])).

fof(f138,plain,(
    k2_struct_0(sK0) = k2_pre_topc(sK0,k2_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f137,f60])).

fof(f137,plain,
    ( k2_struct_0(sK0) = k2_pre_topc(sK0,k2_struct_0(sK0))
    | ~ l1_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f134,f121])).

fof(f121,plain,(
    v4_pre_topc(k2_struct_0(sK0),sK0) ),
    inference(subsumption_resolution,[],[f120,f60])).

fof(f120,plain,
    ( ~ l1_pre_topc(sK0)
    | v4_pre_topc(k2_struct_0(sK0),sK0) ),
    inference(resolution,[],[f86,f59])).

fof(f86,plain,(
    ! [X0] :
      ( ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v4_pre_topc(k2_struct_0(X0),X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0] :
      ( v4_pre_topc(k2_struct_0(X0),X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f34])).

fof(f34,plain,(
    ! [X0] :
      ( v4_pre_topc(k2_struct_0(X0),X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => v4_pre_topc(k2_struct_0(X0),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc4_pre_topc)).

fof(f134,plain,
    ( ~ v4_pre_topc(k2_struct_0(sK0),sK0)
    | k2_struct_0(sK0) = k2_pre_topc(sK0,k2_struct_0(sK0))
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f74,f119])).

fof(f119,plain,(
    m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(resolution,[],[f72,f116])).

fof(f116,plain,(
    l1_struct_0(sK0) ),
    inference(resolution,[],[f73,f60])).

fof(f73,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(f72,plain,(
    ! [X0] :
      ( ~ l1_struct_0(X0)
      | m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_struct_0)).

fof(f74,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v4_pre_topc(X1,X0)
      | k2_pre_topc(X0,X1) = X1
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_pre_topc(X1,X0)
              | k2_pre_topc(X0,X1) != X1
              | ~ v2_pre_topc(X0) )
            & ( k2_pre_topc(X0,X1) = X1
              | ~ v4_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_pre_topc(X1,X0)
              | k2_pre_topc(X0,X1) != X1
              | ~ v2_pre_topc(X0) )
            & ( k2_pre_topc(X0,X1) = X1
              | ~ v4_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( ( ( k2_pre_topc(X0,X1) = X1
                & v2_pre_topc(X0) )
             => v4_pre_topc(X1,X0) )
            & ( v4_pre_topc(X1,X0)
             => k2_pre_topc(X0,X1) = X1 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_pre_topc)).

fof(f163,plain,(
    u1_struct_0(sK0) = k2_pre_topc(sK0,k2_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f162,f60])).

fof(f162,plain,
    ( u1_struct_0(sK0) = k2_pre_topc(sK0,k2_struct_0(sK0))
    | ~ l1_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f159,f153])).

fof(f153,plain,(
    v1_tops_1(k2_struct_0(sK0),sK0) ),
    inference(subsumption_resolution,[],[f152,f60])).

fof(f152,plain,
    ( v1_tops_1(k2_struct_0(sK0),sK0)
    | ~ l1_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f149,f138])).

fof(f149,plain,
    ( k2_struct_0(sK0) != k2_pre_topc(sK0,k2_struct_0(sK0))
    | v1_tops_1(k2_struct_0(sK0),sK0)
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f77,f119])).

fof(f77,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | k2_struct_0(X0) != k2_pre_topc(X0,X1)
      | v1_tops_1(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f49,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v1_tops_1(X1,X0)
              | k2_struct_0(X0) != k2_pre_topc(X0,X1) )
            & ( k2_struct_0(X0) = k2_pre_topc(X0,X1)
              | ~ v1_tops_1(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v1_tops_1(X1,X0)
          <=> k2_struct_0(X0) = k2_pre_topc(X0,X1) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v1_tops_1(X1,X0)
          <=> k2_struct_0(X0) = k2_pre_topc(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tops_1)).

fof(f159,plain,
    ( ~ v1_tops_1(k2_struct_0(sK0),sK0)
    | u1_struct_0(sK0) = k2_pre_topc(sK0,k2_struct_0(sK0))
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f78,f119])).

fof(f78,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v1_tops_1(X1,X0)
      | u1_struct_0(X0) = k2_pre_topc(X0,X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f50,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v1_tops_1(X1,X0)
              | u1_struct_0(X0) != k2_pre_topc(X0,X1) )
            & ( u1_struct_0(X0) = k2_pre_topc(X0,X1)
              | ~ v1_tops_1(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v1_tops_1(X1,X0)
          <=> u1_struct_0(X0) = k2_pre_topc(X0,X1) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v1_tops_1(X1,X0)
          <=> u1_struct_0(X0) = k2_pre_topc(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_tops_3)).

fof(f141,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK0))
    | v1_xboole_0(sK3(sK0)) ),
    inference(resolution,[],[f132,f88])).

fof(f88,plain,(
    ! [X0] :
      ( r2_hidden(sK4(X0),X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f57,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | r2_hidden(sK4(X0),X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f55,f56])).

fof(f56,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK4(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f55,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(rectify,[],[f54])).

fof(f54,plain,(
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

fof(f132,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK3(sK0))
      | ~ v1_xboole_0(u1_struct_0(sK0)) ) ),
    inference(resolution,[],[f131,f99])).

fof(f99,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ v1_xboole_0(X2)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).

fof(f131,plain,(
    m1_subset_1(sK3(sK0),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(subsumption_resolution,[],[f130,f58])).

fof(f130,plain,
    ( m1_subset_1(sK3(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f129,f60])).

fof(f129,plain,
    ( ~ l1_pre_topc(sK0)
    | m1_subset_1(sK3(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f82,f59])).

fof(f82,plain,(
    ! [X0] :
      ( ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | m1_subset_1(sK3(X0),k1_zfmisc_1(u1_struct_0(X0)))
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f320,plain,(
    v1_xboole_0(k2_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f319,f115])).

fof(f115,plain,(
    ! [X0] : m1_subset_1(X0,k1_zfmisc_1(X0)) ),
    inference(forward_demodulation,[],[f70,f69])).

fof(f69,plain,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).

fof(f70,plain,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_subset_1)).

fof(f319,plain,
    ( ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0)))
    | v1_xboole_0(k2_struct_0(sK0)) ),
    inference(forward_demodulation,[],[f318,f164])).

fof(f318,plain,
    ( v1_xboole_0(k2_struct_0(sK0))
    | ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(subsumption_resolution,[],[f317,f58])).

fof(f317,plain,
    ( v1_xboole_0(k2_struct_0(sK0))
    | ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f316,f116])).

fof(f316,plain,
    ( v1_xboole_0(k2_struct_0(sK0))
    | ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_struct_0(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f315,f61])).

fof(f61,plain,(
    ~ v1_xboole_0(sK1) ),
    inference(cnf_transformation,[],[f48])).

fof(f315,plain,
    ( v1_xboole_0(k2_struct_0(sK0))
    | v1_xboole_0(sK1)
    | ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_struct_0(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f314,f102])).

fof(f102,plain,(
    v2_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) ),
    inference(definition_unfolding,[],[f63,f71])).

fof(f71,plain,(
    ! [X0] : k3_yellow_1(X0) = k3_lattice3(k1_lattice3(X0)) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] : k3_yellow_1(X0) = k3_lattice3(k1_lattice3(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_yellow_1)).

fof(f63,plain,(
    v2_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f48])).

fof(f314,plain,
    ( v1_xboole_0(k2_struct_0(sK0))
    | ~ v2_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(sK0))))
    | v1_xboole_0(sK1)
    | ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_struct_0(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f313,f101])).

fof(f101,plain,(
    v13_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) ),
    inference(definition_unfolding,[],[f64,f71])).

fof(f64,plain,(
    v13_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f48])).

fof(f313,plain,
    ( v1_xboole_0(k2_struct_0(sK0))
    | ~ v13_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(sK0))))
    | ~ v2_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(sK0))))
    | v1_xboole_0(sK1)
    | ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_struct_0(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f312,f100])).

fof(f100,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))))) ),
    inference(definition_unfolding,[],[f65,f71])).

fof(f65,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))) ),
    inference(cnf_transformation,[],[f48])).

fof(f312,plain,
    ( v1_xboole_0(k2_struct_0(sK0))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0))))))
    | ~ v13_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(sK0))))
    | ~ v2_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(sK0))))
    | v1_xboole_0(sK1)
    | ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_struct_0(sK0)
    | v2_struct_0(sK0) ),
    inference(duplicate_literal_removal,[],[f311])).

fof(f311,plain,
    ( v1_xboole_0(k2_struct_0(sK0))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0))))))
    | ~ v13_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(sK0))))
    | ~ v2_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(sK0))))
    | v1_xboole_0(sK1)
    | ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | v1_xboole_0(k2_struct_0(sK0))
    | ~ l1_struct_0(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f310,f108])).

fof(f108,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_struct_0(k3_yellow19(X0,X1,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
      | ~ v13_waybel_0(X2,k3_lattice3(k1_lattice3(X1)))
      | ~ v2_waybel_0(X2,k3_lattice3(k1_lattice3(X1)))
      | v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(definition_unfolding,[],[f89,f71,f71,f71])).

fof(f89,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_struct_0(k3_yellow19(X0,X1,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1))))
      | ~ v13_waybel_0(X2,k3_yellow_1(X1))
      | ~ v2_waybel_0(X2,k3_yellow_1(X1))
      | v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( ( v6_waybel_0(k3_yellow19(X0,X1,X2),X0)
        & v4_orders_2(k3_yellow19(X0,X1,X2))
        & v3_orders_2(k3_yellow19(X0,X1,X2))
        & ~ v2_struct_0(k3_yellow19(X0,X1,X2)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1))))
      | ~ v13_waybel_0(X2,k3_yellow_1(X1))
      | ~ v2_waybel_0(X2,k3_yellow_1(X1))
      | v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f36])).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( ( v6_waybel_0(k3_yellow19(X0,X1,X2),X0)
        & v4_orders_2(k3_yellow19(X0,X1,X2))
        & v3_orders_2(k3_yellow19(X0,X1,X2))
        & ~ v2_struct_0(k3_yellow19(X0,X1,X2)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1))))
      | ~ v13_waybel_0(X2,k3_yellow_1(X1))
      | ~ v2_waybel_0(X2,k3_yellow_1(X1))
      | v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f14])).

% (5398)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1))))
        & v13_waybel_0(X2,k3_yellow_1(X1))
        & v2_waybel_0(X2,k3_yellow_1(X1))
        & ~ v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & ~ v1_xboole_0(X1)
        & l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ( v6_waybel_0(k3_yellow19(X0,X1,X2),X0)
        & v4_orders_2(k3_yellow19(X0,X1,X2))
        & v3_orders_2(k3_yellow19(X0,X1,X2))
        & ~ v2_struct_0(k3_yellow19(X0,X1,X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc4_yellow19)).

fof(f310,plain,
    ( v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
    | v1_xboole_0(k2_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f307,f285])).

fof(f285,plain,
    ( v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
    | v1_xboole_0(k2_struct_0(sK0))
    | r1_waybel_7(sK0,sK1,sK2) ),
    inference(duplicate_literal_removal,[],[f280])).

fof(f280,plain,
    ( r1_waybel_7(sK0,sK1,sK2)
    | v1_xboole_0(k2_struct_0(sK0))
    | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
    | r1_waybel_7(sK0,sK1,sK2) ),
    inference(backward_demodulation,[],[f269,f279])).

fof(f279,plain,(
    sK1 = k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)) ),
    inference(subsumption_resolution,[],[f278,f58])).

fof(f278,plain,
    ( sK1 = k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1))
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f277,f116])).

fof(f277,plain,
    ( sK1 = k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1))
    | ~ l1_struct_0(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f276,f61])).

fof(f276,plain,
    ( sK1 = k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1))
    | v1_xboole_0(sK1)
    | ~ l1_struct_0(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f275,f103])).

fof(f103,plain,(
    v1_subset_1(sK1,u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0))))) ),
    inference(definition_unfolding,[],[f62,f71])).

fof(f62,plain,(
    v1_subset_1(sK1,u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))) ),
    inference(cnf_transformation,[],[f48])).

fof(f275,plain,
    ( sK1 = k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1))
    | ~ v1_subset_1(sK1,u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))))
    | v1_xboole_0(sK1)
    | ~ l1_struct_0(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f274,f102])).

fof(f274,plain,
    ( sK1 = k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1))
    | ~ v2_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(sK0))))
    | ~ v1_subset_1(sK1,u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))))
    | v1_xboole_0(sK1)
    | ~ l1_struct_0(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f273,f101])).

fof(f273,plain,
    ( sK1 = k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1))
    | ~ v13_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(sK0))))
    | ~ v2_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(sK0))))
    | ~ v1_subset_1(sK1,u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))))
    | v1_xboole_0(sK1)
    | ~ l1_struct_0(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f104,f100])).

fof(f104,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X0))))))
      | k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) = X1
      | ~ v13_waybel_0(X1,k3_lattice3(k1_lattice3(k2_struct_0(X0))))
      | ~ v2_waybel_0(X1,k3_lattice3(k1_lattice3(k2_struct_0(X0))))
      | ~ v1_subset_1(X1,u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X0)))))
      | v1_xboole_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(definition_unfolding,[],[f85,f71,f71,f71,f71])).

fof(f85,plain,(
    ! [X0,X1] :
      ( k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
      | ~ v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
      | ~ v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
      | ~ v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0))))
      | v1_xboole_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) = X1
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
          | ~ v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
          | ~ v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
          | ~ v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0))))
          | v1_xboole_0(X1) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) = X1
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
          | ~ v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
          | ~ v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
          | ~ v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0))))
          | v1_xboole_0(X1) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
            & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
            & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
            & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0))))
            & ~ v1_xboole_0(X1) )
         => k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t15_yellow19)).

fof(f269,plain,
    ( r1_waybel_7(sK0,k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),sK2)
    | v1_xboole_0(k2_struct_0(sK0))
    | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
    | r1_waybel_7(sK0,sK1,sK2) ),
    inference(duplicate_literal_removal,[],[f268])).

fof(f268,plain,
    ( v1_xboole_0(k2_struct_0(sK0))
    | r1_waybel_7(sK0,k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),sK2)
    | v1_xboole_0(k2_struct_0(sK0))
    | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
    | r1_waybel_7(sK0,sK1,sK2) ),
    inference(resolution,[],[f267,f257])).

fof(f257,plain,
    ( ~ v7_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
    | r1_waybel_7(sK0,k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),sK2)
    | v1_xboole_0(k2_struct_0(sK0))
    | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
    | r1_waybel_7(sK0,sK1,sK2) ),
    inference(subsumption_resolution,[],[f256,f228])).

fof(f228,plain,
    ( v4_orders_2(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
    | v1_xboole_0(k2_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f227,f58])).

fof(f227,plain,
    ( v4_orders_2(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
    | v1_xboole_0(k2_struct_0(sK0))
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f226,f116])).

fof(f226,plain,
    ( v4_orders_2(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
    | v1_xboole_0(k2_struct_0(sK0))
    | ~ l1_struct_0(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f225,f115])).

fof(f225,plain,
    ( ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0)))
    | v4_orders_2(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
    | v1_xboole_0(k2_struct_0(sK0))
    | ~ l1_struct_0(sK0)
    | v2_struct_0(sK0) ),
    inference(superposition,[],[f224,f164])).

fof(f224,plain,(
    ! [X2] :
      ( ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(X2)))
      | v4_orders_2(k3_yellow19(X2,k2_struct_0(sK0),sK1))
      | v1_xboole_0(k2_struct_0(sK0))
      | ~ l1_struct_0(X2)
      | v2_struct_0(X2) ) ),
    inference(subsumption_resolution,[],[f223,f61])).

fof(f223,plain,(
    ! [X2] :
      ( v4_orders_2(k3_yellow19(X2,k2_struct_0(sK0),sK1))
      | v1_xboole_0(sK1)
      | ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(X2)))
      | v1_xboole_0(k2_struct_0(sK0))
      | ~ l1_struct_0(X2)
      | v2_struct_0(X2) ) ),
    inference(subsumption_resolution,[],[f222,f102])).

fof(f222,plain,(
    ! [X2] :
      ( v4_orders_2(k3_yellow19(X2,k2_struct_0(sK0),sK1))
      | ~ v2_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(sK0))))
      | v1_xboole_0(sK1)
      | ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(X2)))
      | v1_xboole_0(k2_struct_0(sK0))
      | ~ l1_struct_0(X2)
      | v2_struct_0(X2) ) ),
    inference(subsumption_resolution,[],[f221,f101])).

fof(f221,plain,(
    ! [X2] :
      ( v4_orders_2(k3_yellow19(X2,k2_struct_0(sK0),sK1))
      | ~ v13_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(sK0))))
      | ~ v2_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(sK0))))
      | v1_xboole_0(sK1)
      | ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(X2)))
      | v1_xboole_0(k2_struct_0(sK0))
      | ~ l1_struct_0(X2)
      | v2_struct_0(X2) ) ),
    inference(resolution,[],[f106,f100])).

fof(f106,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
      | v4_orders_2(k3_yellow19(X0,X1,X2))
      | ~ v13_waybel_0(X2,k3_lattice3(k1_lattice3(X1)))
      | ~ v2_waybel_0(X2,k3_lattice3(k1_lattice3(X1)))
      | v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(definition_unfolding,[],[f91,f71,f71,f71])).

fof(f91,plain,(
    ! [X2,X0,X1] :
      ( v4_orders_2(k3_yellow19(X0,X1,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1))))
      | ~ v13_waybel_0(X2,k3_yellow_1(X1))
      | ~ v2_waybel_0(X2,k3_yellow_1(X1))
      | v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f256,plain,
    ( v1_xboole_0(k2_struct_0(sK0))
    | r1_waybel_7(sK0,k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),sK2)
    | ~ v7_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
    | ~ v4_orders_2(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
    | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
    | r1_waybel_7(sK0,sK1,sK2) ),
    inference(resolution,[],[f255,f219])).

fof(f219,plain,
    ( ~ l1_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK0)
    | r1_waybel_7(sK0,k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),sK2)
    | ~ v7_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
    | ~ v4_orders_2(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
    | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
    | r1_waybel_7(sK0,sK1,sK2) ),
    inference(subsumption_resolution,[],[f218,f165])).

fof(f165,plain,(
    m1_subset_1(sK2,k2_struct_0(sK0)) ),
    inference(backward_demodulation,[],[f66,f164])).

fof(f66,plain,(
    m1_subset_1(sK2,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f48])).

fof(f218,plain,
    ( ~ m1_subset_1(sK2,k2_struct_0(sK0))
    | r1_waybel_7(sK0,k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),sK2)
    | ~ l1_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK0)
    | ~ v7_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
    | ~ v4_orders_2(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
    | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
    | r1_waybel_7(sK0,sK1,sK2) ),
    inference(forward_demodulation,[],[f217,f164])).

fof(f217,plain,
    ( r1_waybel_7(sK0,k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),sK2)
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ l1_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK0)
    | ~ v7_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
    | ~ v4_orders_2(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
    | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
    | r1_waybel_7(sK0,sK1,sK2) ),
    inference(subsumption_resolution,[],[f216,f58])).

fof(f216,plain,
    ( r1_waybel_7(sK0,k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),sK2)
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ l1_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK0)
    | ~ v7_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
    | ~ v4_orders_2(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
    | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
    | v2_struct_0(sK0)
    | r1_waybel_7(sK0,sK1,sK2) ),
    inference(subsumption_resolution,[],[f215,f59])).

fof(f215,plain,
    ( r1_waybel_7(sK0,k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),sK2)
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ l1_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK0)
    | ~ v7_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
    | ~ v4_orders_2(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
    | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | r1_waybel_7(sK0,sK1,sK2) ),
    inference(subsumption_resolution,[],[f214,f60])).

fof(f214,plain,
    ( r1_waybel_7(sK0,k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),sK2)
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ l1_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK0)
    | ~ v7_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
    | ~ v4_orders_2(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
    | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | r1_waybel_7(sK0,sK1,sK2) ),
    inference(resolution,[],[f80,f67])).

fof(f67,plain,
    ( r3_waybel_9(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK2)
    | r1_waybel_7(sK0,sK1,sK2) ),
    inference(cnf_transformation,[],[f48])).

fof(f80,plain,(
    ! [X2,X0,X1] :
      ( ~ r3_waybel_9(X0,X1,X2)
      | r1_waybel_7(X0,k2_yellow19(X0,X1),X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f51,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( r3_waybel_9(X0,X1,X2)
                  | ~ r1_waybel_7(X0,k2_yellow19(X0,X1),X2) )
                & ( r1_waybel_7(X0,k2_yellow19(X0,X1),X2)
                  | ~ r3_waybel_9(X0,X1,X2) ) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ l1_waybel_0(X1,X0)
          | ~ v7_waybel_0(X1)
          | ~ v4_orders_2(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r3_waybel_9(X0,X1,X2)
              <=> r1_waybel_7(X0,k2_yellow19(X0,X1),X2) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ l1_waybel_0(X1,X0)
          | ~ v7_waybel_0(X1)
          | ~ v4_orders_2(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r3_waybel_9(X0,X1,X2)
              <=> r1_waybel_7(X0,k2_yellow19(X0,X1),X2) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ l1_waybel_0(X1,X0)
          | ~ v7_waybel_0(X1)
          | ~ v4_orders_2(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( l1_waybel_0(X1,X0)
            & v7_waybel_0(X1)
            & v4_orders_2(X1)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( r3_waybel_9(X0,X1,X2)
              <=> r1_waybel_7(X0,k2_yellow19(X0,X1),X2) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_yellow19)).

fof(f255,plain,
    ( l1_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK0)
    | v1_xboole_0(k2_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f254,f58])).

fof(f254,plain,
    ( l1_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK0)
    | v1_xboole_0(k2_struct_0(sK0))
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f253,f116])).

fof(f253,plain,
    ( l1_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK0)
    | v1_xboole_0(k2_struct_0(sK0))
    | ~ l1_struct_0(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f252,f115])).

fof(f252,plain,
    ( ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0)))
    | l1_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK0)
    | v1_xboole_0(k2_struct_0(sK0))
    | ~ l1_struct_0(sK0)
    | v2_struct_0(sK0) ),
    inference(superposition,[],[f251,f164])).

fof(f251,plain,(
    ! [X2] :
      ( ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(X2)))
      | l1_waybel_0(k3_yellow19(X2,k2_struct_0(sK0),sK1),X2)
      | v1_xboole_0(k2_struct_0(sK0))
      | ~ l1_struct_0(X2)
      | v2_struct_0(X2) ) ),
    inference(subsumption_resolution,[],[f250,f61])).

fof(f250,plain,(
    ! [X2] :
      ( l1_waybel_0(k3_yellow19(X2,k2_struct_0(sK0),sK1),X2)
      | v1_xboole_0(sK1)
      | ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(X2)))
      | v1_xboole_0(k2_struct_0(sK0))
      | ~ l1_struct_0(X2)
      | v2_struct_0(X2) ) ),
    inference(subsumption_resolution,[],[f249,f102])).

fof(f249,plain,(
    ! [X2] :
      ( l1_waybel_0(k3_yellow19(X2,k2_struct_0(sK0),sK1),X2)
      | ~ v2_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(sK0))))
      | v1_xboole_0(sK1)
      | ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(X2)))
      | v1_xboole_0(k2_struct_0(sK0))
      | ~ l1_struct_0(X2)
      | v2_struct_0(X2) ) ),
    inference(subsumption_resolution,[],[f248,f101])).

fof(f248,plain,(
    ! [X2] :
      ( l1_waybel_0(k3_yellow19(X2,k2_struct_0(sK0),sK1),X2)
      | ~ v13_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(sK0))))
      | ~ v2_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(sK0))))
      | v1_xboole_0(sK1)
      | ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(X2)))
      | v1_xboole_0(k2_struct_0(sK0))
      | ~ l1_struct_0(X2)
      | v2_struct_0(X2) ) ),
    inference(resolution,[],[f109,f100])).

fof(f109,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
      | l1_waybel_0(k3_yellow19(X0,X1,X2),X0)
      | ~ v13_waybel_0(X2,k3_lattice3(k1_lattice3(X1)))
      | ~ v2_waybel_0(X2,k3_lattice3(k1_lattice3(X1)))
      | v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(definition_unfolding,[],[f95,f71,f71,f71])).

fof(f95,plain,(
    ! [X2,X0,X1] :
      ( l1_waybel_0(k3_yellow19(X0,X1,X2),X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1))))
      | ~ v13_waybel_0(X2,k3_yellow_1(X1))
      | ~ v2_waybel_0(X2,k3_yellow_1(X1))
      | v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1,X2] :
      ( ( l1_waybel_0(k3_yellow19(X0,X1,X2),X0)
        & v6_waybel_0(k3_yellow19(X0,X1,X2),X0)
        & ~ v2_struct_0(k3_yellow19(X0,X1,X2)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1))))
      | ~ v13_waybel_0(X2,k3_yellow_1(X1))
      | ~ v2_waybel_0(X2,k3_yellow_1(X1))
      | v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f38])).

fof(f38,plain,(
    ! [X0,X1,X2] :
      ( ( l1_waybel_0(k3_yellow19(X0,X1,X2),X0)
        & v6_waybel_0(k3_yellow19(X0,X1,X2),X0)
        & ~ v2_struct_0(k3_yellow19(X0,X1,X2)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1))))
      | ~ v13_waybel_0(X2,k3_yellow_1(X1))
      | ~ v2_waybel_0(X2,k3_yellow_1(X1))
      | v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1))))
        & v13_waybel_0(X2,k3_yellow_1(X1))
        & v2_waybel_0(X2,k3_yellow_1(X1))
        & ~ v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & ~ v1_xboole_0(X1)
        & l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ( l1_waybel_0(k3_yellow19(X0,X1,X2),X0)
        & v6_waybel_0(k3_yellow19(X0,X1,X2),X0)
        & ~ v2_struct_0(k3_yellow19(X0,X1,X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_yellow19)).

fof(f267,plain,
    ( v7_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
    | v1_xboole_0(k2_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f266,f58])).

fof(f266,plain,
    ( v7_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
    | v1_xboole_0(k2_struct_0(sK0))
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f265,f116])).

fof(f265,plain,
    ( v7_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
    | v1_xboole_0(k2_struct_0(sK0))
    | ~ l1_struct_0(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f264,f115])).

fof(f264,plain,
    ( ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0)))
    | v7_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
    | v1_xboole_0(k2_struct_0(sK0))
    | ~ l1_struct_0(sK0)
    | v2_struct_0(sK0) ),
    inference(superposition,[],[f263,f164])).

fof(f263,plain,(
    ! [X2] :
      ( ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(X2)))
      | v7_waybel_0(k3_yellow19(X2,k2_struct_0(sK0),sK1))
      | v1_xboole_0(k2_struct_0(sK0))
      | ~ l1_struct_0(X2)
      | v2_struct_0(X2) ) ),
    inference(subsumption_resolution,[],[f262,f61])).

fof(f262,plain,(
    ! [X2] :
      ( v7_waybel_0(k3_yellow19(X2,k2_struct_0(sK0),sK1))
      | v1_xboole_0(sK1)
      | ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(X2)))
      | v1_xboole_0(k2_struct_0(sK0))
      | ~ l1_struct_0(X2)
      | v2_struct_0(X2) ) ),
    inference(subsumption_resolution,[],[f261,f103])).

fof(f261,plain,(
    ! [X2] :
      ( v7_waybel_0(k3_yellow19(X2,k2_struct_0(sK0),sK1))
      | ~ v1_subset_1(sK1,u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))))
      | v1_xboole_0(sK1)
      | ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(X2)))
      | v1_xboole_0(k2_struct_0(sK0))
      | ~ l1_struct_0(X2)
      | v2_struct_0(X2) ) ),
    inference(subsumption_resolution,[],[f260,f102])).

fof(f260,plain,(
    ! [X2] :
      ( v7_waybel_0(k3_yellow19(X2,k2_struct_0(sK0),sK1))
      | ~ v2_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(sK0))))
      | ~ v1_subset_1(sK1,u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))))
      | v1_xboole_0(sK1)
      | ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(X2)))
      | v1_xboole_0(k2_struct_0(sK0))
      | ~ l1_struct_0(X2)
      | v2_struct_0(X2) ) ),
    inference(subsumption_resolution,[],[f259,f101])).

fof(f259,plain,(
    ! [X2] :
      ( v7_waybel_0(k3_yellow19(X2,k2_struct_0(sK0),sK1))
      | ~ v13_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(sK0))))
      | ~ v2_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(sK0))))
      | ~ v1_subset_1(sK1,u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))))
      | v1_xboole_0(sK1)
      | ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(X2)))
      | v1_xboole_0(k2_struct_0(sK0))
      | ~ l1_struct_0(X2)
      | v2_struct_0(X2) ) ),
    inference(resolution,[],[f112,f100])).

fof(f112,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
      | v7_waybel_0(k3_yellow19(X0,X1,X2))
      | ~ v13_waybel_0(X2,k3_lattice3(k1_lattice3(X1)))
      | ~ v2_waybel_0(X2,k3_lattice3(k1_lattice3(X1)))
      | ~ v1_subset_1(X2,u1_struct_0(k3_lattice3(k1_lattice3(X1))))
      | v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(definition_unfolding,[],[f98,f71,f71,f71,f71])).

fof(f98,plain,(
    ! [X2,X0,X1] :
      ( v7_waybel_0(k3_yellow19(X0,X1,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1))))
      | ~ v13_waybel_0(X2,k3_yellow_1(X1))
      | ~ v2_waybel_0(X2,k3_yellow_1(X1))
      | ~ v1_subset_1(X2,u1_struct_0(k3_yellow_1(X1)))
      | v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1,X2] :
      ( ( v7_waybel_0(k3_yellow19(X0,X1,X2))
        & v6_waybel_0(k3_yellow19(X0,X1,X2),X0)
        & ~ v2_struct_0(k3_yellow19(X0,X1,X2)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1))))
      | ~ v13_waybel_0(X2,k3_yellow_1(X1))
      | ~ v2_waybel_0(X2,k3_yellow_1(X1))
      | ~ v1_subset_1(X2,u1_struct_0(k3_yellow_1(X1)))
      | v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f40])).

fof(f40,plain,(
    ! [X0,X1,X2] :
      ( ( v7_waybel_0(k3_yellow19(X0,X1,X2))
        & v6_waybel_0(k3_yellow19(X0,X1,X2),X0)
        & ~ v2_struct_0(k3_yellow19(X0,X1,X2)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1))))
      | ~ v13_waybel_0(X2,k3_yellow_1(X1))
      | ~ v2_waybel_0(X2,k3_yellow_1(X1))
      | ~ v1_subset_1(X2,u1_struct_0(k3_yellow_1(X1)))
      | v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1))))
        & v13_waybel_0(X2,k3_yellow_1(X1))
        & v2_waybel_0(X2,k3_yellow_1(X1))
        & v1_subset_1(X2,u1_struct_0(k3_yellow_1(X1)))
        & ~ v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & ~ v1_xboole_0(X1)
        & l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ( v7_waybel_0(k3_yellow19(X0,X1,X2))
        & v6_waybel_0(k3_yellow19(X0,X1,X2),X0)
        & ~ v2_struct_0(k3_yellow19(X0,X1,X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc5_yellow19)).

fof(f307,plain,
    ( v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
    | v1_xboole_0(k2_struct_0(sK0))
    | ~ r1_waybel_7(sK0,sK1,sK2) ),
    inference(resolution,[],[f306,f68])).

fof(f68,plain,
    ( ~ r3_waybel_9(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK2)
    | ~ r1_waybel_7(sK0,sK1,sK2) ),
    inference(cnf_transformation,[],[f48])).

fof(f306,plain,
    ( r3_waybel_9(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK2)
    | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
    | v1_xboole_0(k2_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f305,f228])).

fof(f305,plain,
    ( r3_waybel_9(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK2)
    | ~ v4_orders_2(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
    | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
    | v1_xboole_0(k2_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f304,f267])).

fof(f304,plain,
    ( r3_waybel_9(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK2)
    | ~ v7_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
    | ~ v4_orders_2(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
    | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
    | v1_xboole_0(k2_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f303,f255])).

fof(f303,plain,
    ( r3_waybel_9(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK2)
    | ~ l1_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK0)
    | ~ v7_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
    | ~ v4_orders_2(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
    | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
    | v1_xboole_0(k2_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f302,f165])).

fof(f302,plain,
    ( ~ m1_subset_1(sK2,k2_struct_0(sK0))
    | r3_waybel_9(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK2)
    | ~ l1_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK0)
    | ~ v7_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
    | ~ v4_orders_2(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
    | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
    | v1_xboole_0(k2_struct_0(sK0)) ),
    inference(resolution,[],[f290,f300])).

fof(f300,plain,
    ( r1_waybel_7(sK0,sK1,sK2)
    | v1_xboole_0(k2_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f299,f115])).

fof(f299,plain,
    ( ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0)))
    | v1_xboole_0(k2_struct_0(sK0))
    | r1_waybel_7(sK0,sK1,sK2) ),
    inference(forward_demodulation,[],[f298,f164])).

fof(f298,plain,
    ( v1_xboole_0(k2_struct_0(sK0))
    | r1_waybel_7(sK0,sK1,sK2)
    | ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(subsumption_resolution,[],[f297,f58])).

fof(f297,plain,
    ( v1_xboole_0(k2_struct_0(sK0))
    | r1_waybel_7(sK0,sK1,sK2)
    | ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f296,f116])).

fof(f296,plain,
    ( v1_xboole_0(k2_struct_0(sK0))
    | r1_waybel_7(sK0,sK1,sK2)
    | ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_struct_0(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f295,f61])).

fof(f295,plain,
    ( v1_xboole_0(k2_struct_0(sK0))
    | r1_waybel_7(sK0,sK1,sK2)
    | v1_xboole_0(sK1)
    | ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_struct_0(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f294,f102])).

fof(f294,plain,
    ( v1_xboole_0(k2_struct_0(sK0))
    | r1_waybel_7(sK0,sK1,sK2)
    | ~ v2_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(sK0))))
    | v1_xboole_0(sK1)
    | ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_struct_0(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f293,f101])).

fof(f293,plain,
    ( v1_xboole_0(k2_struct_0(sK0))
    | r1_waybel_7(sK0,sK1,sK2)
    | ~ v13_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(sK0))))
    | ~ v2_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(sK0))))
    | v1_xboole_0(sK1)
    | ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_struct_0(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f292,f100])).

fof(f292,plain,
    ( v1_xboole_0(k2_struct_0(sK0))
    | r1_waybel_7(sK0,sK1,sK2)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0))))))
    | ~ v13_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(sK0))))
    | ~ v2_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(sK0))))
    | v1_xboole_0(sK1)
    | ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_struct_0(sK0)
    | v2_struct_0(sK0) ),
    inference(duplicate_literal_removal,[],[f291])).

fof(f291,plain,
    ( v1_xboole_0(k2_struct_0(sK0))
    | r1_waybel_7(sK0,sK1,sK2)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0))))))
    | ~ v13_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(sK0))))
    | ~ v2_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(sK0))))
    | v1_xboole_0(sK1)
    | ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | v1_xboole_0(k2_struct_0(sK0))
    | ~ l1_struct_0(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f285,f108])).

fof(f290,plain,(
    ! [X0] :
      ( ~ r1_waybel_7(sK0,sK1,X0)
      | ~ m1_subset_1(X0,k2_struct_0(sK0))
      | r3_waybel_9(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1),X0)
      | ~ l1_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK0)
      | ~ v7_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
      | ~ v4_orders_2(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
      | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1)) ) ),
    inference(forward_demodulation,[],[f289,f164])).

fof(f289,plain,(
    ! [X0] :
      ( ~ r1_waybel_7(sK0,sK1,X0)
      | r3_waybel_9(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1),X0)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ l1_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK0)
      | ~ v7_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
      | ~ v4_orders_2(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
      | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1)) ) ),
    inference(subsumption_resolution,[],[f288,f58])).

fof(f288,plain,(
    ! [X0] :
      ( ~ r1_waybel_7(sK0,sK1,X0)
      | r3_waybel_9(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1),X0)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ l1_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK0)
      | ~ v7_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
      | ~ v4_orders_2(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
      | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f287,f59])).

fof(f287,plain,(
    ! [X0] :
      ( ~ r1_waybel_7(sK0,sK1,X0)
      | r3_waybel_9(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1),X0)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ l1_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK0)
      | ~ v7_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
      | ~ v4_orders_2(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
      | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f286,f60])).

fof(f286,plain,(
    ! [X0] :
      ( ~ r1_waybel_7(sK0,sK1,X0)
      | r3_waybel_9(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1),X0)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ l1_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK0)
      | ~ v7_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
      | ~ v4_orders_2(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
      | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(superposition,[],[f81,f279])).

fof(f81,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_waybel_7(X0,k2_yellow19(X0,X1),X2)
      | r3_waybel_9(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f51])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n018.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 18:01:12 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.42  % (5400)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.21/0.46  % (5408)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.21/0.47  % (5408)Refutation found. Thanks to Tanya!
% 0.21/0.47  % SZS status Theorem for theBenchmark
% 0.21/0.47  % (5401)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.21/0.47  % (5405)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.21/0.47  % (5409)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.21/0.48  % (5395)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.21/0.48  % (5402)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.21/0.48  % (5407)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.21/0.48  % (5399)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.21/0.48  % (5396)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.21/0.48  % (5410)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.21/0.48  % SZS output start Proof for theBenchmark
% 0.21/0.48  fof(f325,plain,(
% 0.21/0.48    $false),
% 0.21/0.48    inference(subsumption_resolution,[],[f324,f58])).
% 0.21/0.48  fof(f58,plain,(
% 0.21/0.48    ~v2_struct_0(sK0)),
% 0.21/0.48    inference(cnf_transformation,[],[f48])).
% 0.21/0.48  fof(f48,plain,(
% 0.21/0.48    (((~r1_waybel_7(sK0,sK1,sK2) | ~r3_waybel_9(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK2)) & (r1_waybel_7(sK0,sK1,sK2) | r3_waybel_9(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK2)) & m1_subset_1(sK2,u1_struct_0(sK0))) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))) & v13_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0))) & v2_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0))) & v1_subset_1(sK1,u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))) & ~v1_xboole_0(sK1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0)),
% 0.21/0.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f44,f47,f46,f45])).
% 0.21/0.48  fof(f45,plain,(
% 0.21/0.48    ? [X0] : (? [X1] : (? [X2] : ((~r1_waybel_7(X0,X1,X2) | ~r3_waybel_9(X0,k3_yellow19(X0,k2_struct_0(X0),X1),X2)) & (r1_waybel_7(X0,X1,X2) | r3_waybel_9(X0,k3_yellow19(X0,k2_struct_0(X0),X1),X2)) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) & ~v1_xboole_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : ((~r1_waybel_7(sK0,X1,X2) | ~r3_waybel_9(sK0,k3_yellow19(sK0,k2_struct_0(sK0),X1),X2)) & (r1_waybel_7(sK0,X1,X2) | r3_waybel_9(sK0,k3_yellow19(sK0,k2_struct_0(sK0),X1),X2)) & m1_subset_1(X2,u1_struct_0(sK0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))) & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(sK0))) & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(sK0))) & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))) & ~v1_xboole_0(X1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0))),
% 0.21/0.48    introduced(choice_axiom,[])).
% 0.21/0.48  fof(f46,plain,(
% 0.21/0.48    ? [X1] : (? [X2] : ((~r1_waybel_7(sK0,X1,X2) | ~r3_waybel_9(sK0,k3_yellow19(sK0,k2_struct_0(sK0),X1),X2)) & (r1_waybel_7(sK0,X1,X2) | r3_waybel_9(sK0,k3_yellow19(sK0,k2_struct_0(sK0),X1),X2)) & m1_subset_1(X2,u1_struct_0(sK0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))) & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(sK0))) & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(sK0))) & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))) & ~v1_xboole_0(X1)) => (? [X2] : ((~r1_waybel_7(sK0,sK1,X2) | ~r3_waybel_9(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1),X2)) & (r1_waybel_7(sK0,sK1,X2) | r3_waybel_9(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1),X2)) & m1_subset_1(X2,u1_struct_0(sK0))) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))) & v13_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0))) & v2_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0))) & v1_subset_1(sK1,u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))) & ~v1_xboole_0(sK1))),
% 0.21/0.48    introduced(choice_axiom,[])).
% 0.21/0.48  fof(f47,plain,(
% 0.21/0.48    ? [X2] : ((~r1_waybel_7(sK0,sK1,X2) | ~r3_waybel_9(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1),X2)) & (r1_waybel_7(sK0,sK1,X2) | r3_waybel_9(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1),X2)) & m1_subset_1(X2,u1_struct_0(sK0))) => ((~r1_waybel_7(sK0,sK1,sK2) | ~r3_waybel_9(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK2)) & (r1_waybel_7(sK0,sK1,sK2) | r3_waybel_9(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK2)) & m1_subset_1(sK2,u1_struct_0(sK0)))),
% 0.21/0.48    introduced(choice_axiom,[])).
% 0.21/0.48  fof(f44,plain,(
% 0.21/0.48    ? [X0] : (? [X1] : (? [X2] : ((~r1_waybel_7(X0,X1,X2) | ~r3_waybel_9(X0,k3_yellow19(X0,k2_struct_0(X0),X1),X2)) & (r1_waybel_7(X0,X1,X2) | r3_waybel_9(X0,k3_yellow19(X0,k2_struct_0(X0),X1),X2)) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) & ~v1_xboole_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.21/0.48    inference(flattening,[],[f43])).
% 0.21/0.48  fof(f43,plain,(
% 0.21/0.48    ? [X0] : (? [X1] : (? [X2] : (((~r1_waybel_7(X0,X1,X2) | ~r3_waybel_9(X0,k3_yellow19(X0,k2_struct_0(X0),X1),X2)) & (r1_waybel_7(X0,X1,X2) | r3_waybel_9(X0,k3_yellow19(X0,k2_struct_0(X0),X1),X2))) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) & ~v1_xboole_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.21/0.48    inference(nnf_transformation,[],[f21])).
% 0.21/0.48  fof(f21,plain,(
% 0.21/0.48    ? [X0] : (? [X1] : (? [X2] : ((r3_waybel_9(X0,k3_yellow19(X0,k2_struct_0(X0),X1),X2) <~> r1_waybel_7(X0,X1,X2)) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) & ~v1_xboole_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.21/0.48    inference(flattening,[],[f20])).
% 0.21/0.48  fof(f20,plain,(
% 0.21/0.48    ? [X0] : (? [X1] : (? [X2] : ((r3_waybel_9(X0,k3_yellow19(X0,k2_struct_0(X0),X1),X2) <~> r1_waybel_7(X0,X1,X2)) & m1_subset_1(X2,u1_struct_0(X0))) & (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) & ~v1_xboole_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 0.21/0.48    inference(ennf_transformation,[],[f19])).
% 0.21/0.48  fof(f19,negated_conjecture,(
% 0.21/0.48    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) & ~v1_xboole_0(X1)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r3_waybel_9(X0,k3_yellow19(X0,k2_struct_0(X0),X1),X2) <=> r1_waybel_7(X0,X1,X2)))))),
% 0.21/0.48    inference(negated_conjecture,[],[f18])).
% 0.21/0.48  fof(f18,conjecture,(
% 0.21/0.48    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) & ~v1_xboole_0(X1)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r3_waybel_9(X0,k3_yellow19(X0,k2_struct_0(X0),X1),X2) <=> r1_waybel_7(X0,X1,X2)))))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_yellow19)).
% 0.21/0.48  fof(f324,plain,(
% 0.21/0.48    v2_struct_0(sK0)),
% 0.21/0.48    inference(subsumption_resolution,[],[f323,f59])).
% 0.21/0.48  fof(f59,plain,(
% 0.21/0.48    v2_pre_topc(sK0)),
% 0.21/0.48    inference(cnf_transformation,[],[f48])).
% 0.21/0.48  fof(f323,plain,(
% 0.21/0.48    ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 0.21/0.48    inference(subsumption_resolution,[],[f322,f60])).
% 0.21/0.48  fof(f60,plain,(
% 0.21/0.48    l1_pre_topc(sK0)),
% 0.21/0.48    inference(cnf_transformation,[],[f48])).
% 0.21/0.48  fof(f322,plain,(
% 0.21/0.48    ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 0.21/0.48    inference(resolution,[],[f321,f83])).
% 0.21/0.48  fof(f83,plain,(
% 0.21/0.48    ( ! [X0] : (~v1_xboole_0(sK3(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f53])).
% 0.21/0.48  fof(f53,plain,(
% 0.21/0.48    ! [X0] : ((v4_pre_topc(sK3(X0),X0) & ~v1_xboole_0(sK3(X0)) & m1_subset_1(sK3(X0),k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f31,f52])).
% 0.21/0.48  fof(f52,plain,(
% 0.21/0.48    ! [X0] : (? [X1] : (v4_pre_topc(X1,X0) & ~v1_xboole_0(X1) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) => (v4_pre_topc(sK3(X0),X0) & ~v1_xboole_0(sK3(X0)) & m1_subset_1(sK3(X0),k1_zfmisc_1(u1_struct_0(X0)))))),
% 0.21/0.48    introduced(choice_axiom,[])).
% 0.21/0.48  fof(f31,plain,(
% 0.21/0.48    ! [X0] : (? [X1] : (v4_pre_topc(X1,X0) & ~v1_xboole_0(X1) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.48    inference(flattening,[],[f30])).
% 0.21/0.48  fof(f30,plain,(
% 0.21/0.48    ! [X0] : (? [X1] : (v4_pre_topc(X1,X0) & ~v1_xboole_0(X1) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.21/0.48    inference(ennf_transformation,[],[f8])).
% 0.21/0.48  fof(f8,axiom,(
% 0.21/0.48    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ? [X1] : (v4_pre_topc(X1,X0) & ~v1_xboole_0(X1) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',rc7_pre_topc)).
% 0.21/0.48  fof(f321,plain,(
% 0.21/0.48    v1_xboole_0(sK3(sK0))),
% 0.21/0.48    inference(resolution,[],[f320,f171])).
% 0.21/0.48  fof(f171,plain,(
% 0.21/0.48    ~v1_xboole_0(k2_struct_0(sK0)) | v1_xboole_0(sK3(sK0))),
% 0.21/0.48    inference(backward_demodulation,[],[f141,f164])).
% 0.21/0.48  fof(f164,plain,(
% 0.21/0.48    k2_struct_0(sK0) = u1_struct_0(sK0)),
% 0.21/0.48    inference(forward_demodulation,[],[f163,f138])).
% 0.21/0.48  fof(f138,plain,(
% 0.21/0.48    k2_struct_0(sK0) = k2_pre_topc(sK0,k2_struct_0(sK0))),
% 0.21/0.48    inference(subsumption_resolution,[],[f137,f60])).
% 0.21/0.48  fof(f137,plain,(
% 0.21/0.48    k2_struct_0(sK0) = k2_pre_topc(sK0,k2_struct_0(sK0)) | ~l1_pre_topc(sK0)),
% 0.21/0.48    inference(subsumption_resolution,[],[f134,f121])).
% 0.21/0.48  fof(f121,plain,(
% 0.21/0.48    v4_pre_topc(k2_struct_0(sK0),sK0)),
% 0.21/0.48    inference(subsumption_resolution,[],[f120,f60])).
% 0.21/0.48  fof(f120,plain,(
% 0.21/0.48    ~l1_pre_topc(sK0) | v4_pre_topc(k2_struct_0(sK0),sK0)),
% 0.21/0.48    inference(resolution,[],[f86,f59])).
% 0.21/0.48  fof(f86,plain,(
% 0.21/0.48    ( ! [X0] : (~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v4_pre_topc(k2_struct_0(X0),X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f35])).
% 0.21/0.48  fof(f35,plain,(
% 0.21/0.48    ! [X0] : (v4_pre_topc(k2_struct_0(X0),X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.21/0.48    inference(flattening,[],[f34])).
% 0.21/0.48  fof(f34,plain,(
% 0.21/0.48    ! [X0] : (v4_pre_topc(k2_struct_0(X0),X0) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 0.21/0.48    inference(ennf_transformation,[],[f7])).
% 0.21/0.48  fof(f7,axiom,(
% 0.21/0.48    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => v4_pre_topc(k2_struct_0(X0),X0))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc4_pre_topc)).
% 0.21/0.48  fof(f134,plain,(
% 0.21/0.48    ~v4_pre_topc(k2_struct_0(sK0),sK0) | k2_struct_0(sK0) = k2_pre_topc(sK0,k2_struct_0(sK0)) | ~l1_pre_topc(sK0)),
% 0.21/0.48    inference(resolution,[],[f74,f119])).
% 0.21/0.48  fof(f119,plain,(
% 0.21/0.48    m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.21/0.48    inference(resolution,[],[f72,f116])).
% 0.21/0.48  fof(f116,plain,(
% 0.21/0.48    l1_struct_0(sK0)),
% 0.21/0.48    inference(resolution,[],[f73,f60])).
% 0.21/0.48  fof(f73,plain,(
% 0.21/0.48    ( ! [X0] : (~l1_pre_topc(X0) | l1_struct_0(X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f23])).
% 0.21/0.48  fof(f23,plain,(
% 0.21/0.48    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 0.21/0.48    inference(ennf_transformation,[],[f6])).
% 0.21/0.48  fof(f6,axiom,(
% 0.21/0.48    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).
% 0.21/0.48  fof(f72,plain,(
% 0.21/0.48    ( ! [X0] : (~l1_struct_0(X0) | m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0)))) )),
% 0.21/0.48    inference(cnf_transformation,[],[f22])).
% 0.21/0.48  fof(f22,plain,(
% 0.21/0.48    ! [X0] : (m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0))) | ~l1_struct_0(X0))),
% 0.21/0.48    inference(ennf_transformation,[],[f5])).
% 0.21/0.48  fof(f5,axiom,(
% 0.21/0.48    ! [X0] : (l1_struct_0(X0) => m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0))))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_struct_0)).
% 0.21/0.48  fof(f74,plain,(
% 0.21/0.48    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v4_pre_topc(X1,X0) | k2_pre_topc(X0,X1) = X1 | ~l1_pre_topc(X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f25])).
% 0.21/0.48  fof(f25,plain,(
% 0.21/0.48    ! [X0] : (! [X1] : (((v4_pre_topc(X1,X0) | k2_pre_topc(X0,X1) != X1 | ~v2_pre_topc(X0)) & (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.21/0.48    inference(flattening,[],[f24])).
% 0.21/0.48  fof(f24,plain,(
% 0.21/0.48    ! [X0] : (! [X1] : (((v4_pre_topc(X1,X0) | (k2_pre_topc(X0,X1) != X1 | ~v2_pre_topc(X0))) & (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.21/0.48    inference(ennf_transformation,[],[f9])).
% 0.21/0.48  fof(f9,axiom,(
% 0.21/0.48    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (((k2_pre_topc(X0,X1) = X1 & v2_pre_topc(X0)) => v4_pre_topc(X1,X0)) & (v4_pre_topc(X1,X0) => k2_pre_topc(X0,X1) = X1))))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_pre_topc)).
% 0.21/0.48  fof(f163,plain,(
% 0.21/0.48    u1_struct_0(sK0) = k2_pre_topc(sK0,k2_struct_0(sK0))),
% 0.21/0.48    inference(subsumption_resolution,[],[f162,f60])).
% 0.21/0.48  fof(f162,plain,(
% 0.21/0.48    u1_struct_0(sK0) = k2_pre_topc(sK0,k2_struct_0(sK0)) | ~l1_pre_topc(sK0)),
% 0.21/0.48    inference(subsumption_resolution,[],[f159,f153])).
% 0.21/0.48  fof(f153,plain,(
% 0.21/0.48    v1_tops_1(k2_struct_0(sK0),sK0)),
% 0.21/0.48    inference(subsumption_resolution,[],[f152,f60])).
% 0.21/0.48  fof(f152,plain,(
% 0.21/0.48    v1_tops_1(k2_struct_0(sK0),sK0) | ~l1_pre_topc(sK0)),
% 0.21/0.48    inference(subsumption_resolution,[],[f149,f138])).
% 0.21/0.48  fof(f149,plain,(
% 0.21/0.48    k2_struct_0(sK0) != k2_pre_topc(sK0,k2_struct_0(sK0)) | v1_tops_1(k2_struct_0(sK0),sK0) | ~l1_pre_topc(sK0)),
% 0.21/0.48    inference(resolution,[],[f77,f119])).
% 0.21/0.48  fof(f77,plain,(
% 0.21/0.48    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | k2_struct_0(X0) != k2_pre_topc(X0,X1) | v1_tops_1(X1,X0) | ~l1_pre_topc(X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f49])).
% 0.21/0.48  fof(f49,plain,(
% 0.21/0.48    ! [X0] : (! [X1] : (((v1_tops_1(X1,X0) | k2_struct_0(X0) != k2_pre_topc(X0,X1)) & (k2_struct_0(X0) = k2_pre_topc(X0,X1) | ~v1_tops_1(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.21/0.48    inference(nnf_transformation,[],[f26])).
% 0.21/0.48  fof(f26,plain,(
% 0.21/0.48    ! [X0] : (! [X1] : ((v1_tops_1(X1,X0) <=> k2_struct_0(X0) = k2_pre_topc(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.21/0.48    inference(ennf_transformation,[],[f10])).
% 0.21/0.48  fof(f10,axiom,(
% 0.21/0.48    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v1_tops_1(X1,X0) <=> k2_struct_0(X0) = k2_pre_topc(X0,X1))))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tops_1)).
% 0.21/0.48  fof(f159,plain,(
% 0.21/0.48    ~v1_tops_1(k2_struct_0(sK0),sK0) | u1_struct_0(sK0) = k2_pre_topc(sK0,k2_struct_0(sK0)) | ~l1_pre_topc(sK0)),
% 0.21/0.48    inference(resolution,[],[f78,f119])).
% 0.21/0.49  fof(f78,plain,(
% 0.21/0.49    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v1_tops_1(X1,X0) | u1_struct_0(X0) = k2_pre_topc(X0,X1) | ~l1_pre_topc(X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f50])).
% 0.21/0.49  fof(f50,plain,(
% 0.21/0.49    ! [X0] : (! [X1] : (((v1_tops_1(X1,X0) | u1_struct_0(X0) != k2_pre_topc(X0,X1)) & (u1_struct_0(X0) = k2_pre_topc(X0,X1) | ~v1_tops_1(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.21/0.49    inference(nnf_transformation,[],[f27])).
% 0.21/0.49  fof(f27,plain,(
% 0.21/0.49    ! [X0] : (! [X1] : ((v1_tops_1(X1,X0) <=> u1_struct_0(X0) = k2_pre_topc(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.21/0.49    inference(ennf_transformation,[],[f12])).
% 0.21/0.49  fof(f12,axiom,(
% 0.21/0.49    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v1_tops_1(X1,X0) <=> u1_struct_0(X0) = k2_pre_topc(X0,X1))))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_tops_3)).
% 0.21/0.49  fof(f141,plain,(
% 0.21/0.49    ~v1_xboole_0(u1_struct_0(sK0)) | v1_xboole_0(sK3(sK0))),
% 0.21/0.49    inference(resolution,[],[f132,f88])).
% 0.21/0.49  fof(f88,plain,(
% 0.21/0.49    ( ! [X0] : (r2_hidden(sK4(X0),X0) | v1_xboole_0(X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f57])).
% 0.21/0.49  fof(f57,plain,(
% 0.21/0.49    ! [X0] : ((v1_xboole_0(X0) | r2_hidden(sK4(X0),X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 0.21/0.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f55,f56])).
% 0.21/0.49  fof(f56,plain,(
% 0.21/0.49    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK4(X0),X0))),
% 0.21/0.49    introduced(choice_axiom,[])).
% 0.21/0.49  fof(f55,plain,(
% 0.21/0.49    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 0.21/0.49    inference(rectify,[],[f54])).
% 0.21/0.49  fof(f54,plain,(
% 0.21/0.49    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0)))),
% 0.21/0.49    inference(nnf_transformation,[],[f1])).
% 0.21/0.49  fof(f1,axiom,(
% 0.21/0.49    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).
% 0.21/0.49  fof(f132,plain,(
% 0.21/0.49    ( ! [X0] : (~r2_hidden(X0,sK3(sK0)) | ~v1_xboole_0(u1_struct_0(sK0))) )),
% 0.21/0.49    inference(resolution,[],[f131,f99])).
% 0.21/0.49  fof(f99,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~v1_xboole_0(X2) | ~r2_hidden(X0,X1)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f42])).
% 0.21/0.49  fof(f42,plain,(
% 0.21/0.49    ! [X0,X1,X2] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 0.21/0.49    inference(ennf_transformation,[],[f4])).
% 0.21/0.49  fof(f4,axiom,(
% 0.21/0.49    ! [X0,X1,X2] : ~(v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).
% 0.21/0.49  fof(f131,plain,(
% 0.21/0.49    m1_subset_1(sK3(sK0),k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.21/0.49    inference(subsumption_resolution,[],[f130,f58])).
% 0.21/0.49  fof(f130,plain,(
% 0.21/0.49    m1_subset_1(sK3(sK0),k1_zfmisc_1(u1_struct_0(sK0))) | v2_struct_0(sK0)),
% 0.21/0.49    inference(subsumption_resolution,[],[f129,f60])).
% 0.21/0.49  fof(f129,plain,(
% 0.21/0.49    ~l1_pre_topc(sK0) | m1_subset_1(sK3(sK0),k1_zfmisc_1(u1_struct_0(sK0))) | v2_struct_0(sK0)),
% 0.21/0.49    inference(resolution,[],[f82,f59])).
% 0.21/0.49  fof(f82,plain,(
% 0.21/0.49    ( ! [X0] : (~v2_pre_topc(X0) | ~l1_pre_topc(X0) | m1_subset_1(sK3(X0),k1_zfmisc_1(u1_struct_0(X0))) | v2_struct_0(X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f53])).
% 0.21/0.49  fof(f320,plain,(
% 0.21/0.49    v1_xboole_0(k2_struct_0(sK0))),
% 0.21/0.49    inference(subsumption_resolution,[],[f319,f115])).
% 0.21/0.49  fof(f115,plain,(
% 0.21/0.49    ( ! [X0] : (m1_subset_1(X0,k1_zfmisc_1(X0))) )),
% 0.21/0.49    inference(forward_demodulation,[],[f70,f69])).
% 0.21/0.49  fof(f69,plain,(
% 0.21/0.49    ( ! [X0] : (k2_subset_1(X0) = X0) )),
% 0.21/0.49    inference(cnf_transformation,[],[f2])).
% 0.21/0.49  fof(f2,axiom,(
% 0.21/0.49    ! [X0] : k2_subset_1(X0) = X0),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).
% 0.21/0.49  fof(f70,plain,(
% 0.21/0.49    ( ! [X0] : (m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))) )),
% 0.21/0.49    inference(cnf_transformation,[],[f3])).
% 0.21/0.49  fof(f3,axiom,(
% 0.21/0.49    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_subset_1)).
% 0.21/0.49  fof(f319,plain,(
% 0.21/0.49    ~m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0))) | v1_xboole_0(k2_struct_0(sK0))),
% 0.21/0.49    inference(forward_demodulation,[],[f318,f164])).
% 0.21/0.49  fof(f318,plain,(
% 0.21/0.49    v1_xboole_0(k2_struct_0(sK0)) | ~m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.21/0.49    inference(subsumption_resolution,[],[f317,f58])).
% 0.21/0.49  fof(f317,plain,(
% 0.21/0.49    v1_xboole_0(k2_struct_0(sK0)) | ~m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) | v2_struct_0(sK0)),
% 0.21/0.49    inference(subsumption_resolution,[],[f316,f116])).
% 0.21/0.49  fof(f316,plain,(
% 0.21/0.49    v1_xboole_0(k2_struct_0(sK0)) | ~m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_struct_0(sK0) | v2_struct_0(sK0)),
% 0.21/0.49    inference(subsumption_resolution,[],[f315,f61])).
% 0.21/0.49  fof(f61,plain,(
% 0.21/0.49    ~v1_xboole_0(sK1)),
% 0.21/0.49    inference(cnf_transformation,[],[f48])).
% 0.21/0.49  fof(f315,plain,(
% 0.21/0.49    v1_xboole_0(k2_struct_0(sK0)) | v1_xboole_0(sK1) | ~m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_struct_0(sK0) | v2_struct_0(sK0)),
% 0.21/0.49    inference(subsumption_resolution,[],[f314,f102])).
% 0.21/0.49  fof(f102,plain,(
% 0.21/0.49    v2_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(sK0))))),
% 0.21/0.49    inference(definition_unfolding,[],[f63,f71])).
% 0.21/0.49  fof(f71,plain,(
% 0.21/0.49    ( ! [X0] : (k3_yellow_1(X0) = k3_lattice3(k1_lattice3(X0))) )),
% 0.21/0.49    inference(cnf_transformation,[],[f11])).
% 0.21/0.49  fof(f11,axiom,(
% 0.21/0.49    ! [X0] : k3_yellow_1(X0) = k3_lattice3(k1_lattice3(X0))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_yellow_1)).
% 0.21/0.49  fof(f63,plain,(
% 0.21/0.49    v2_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0)))),
% 0.21/0.49    inference(cnf_transformation,[],[f48])).
% 0.21/0.49  fof(f314,plain,(
% 0.21/0.49    v1_xboole_0(k2_struct_0(sK0)) | ~v2_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) | v1_xboole_0(sK1) | ~m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_struct_0(sK0) | v2_struct_0(sK0)),
% 0.21/0.49    inference(subsumption_resolution,[],[f313,f101])).
% 0.21/0.49  fof(f101,plain,(
% 0.21/0.49    v13_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(sK0))))),
% 0.21/0.49    inference(definition_unfolding,[],[f64,f71])).
% 0.21/0.49  fof(f64,plain,(
% 0.21/0.49    v13_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0)))),
% 0.21/0.49    inference(cnf_transformation,[],[f48])).
% 0.21/0.49  fof(f313,plain,(
% 0.21/0.49    v1_xboole_0(k2_struct_0(sK0)) | ~v13_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) | ~v2_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) | v1_xboole_0(sK1) | ~m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_struct_0(sK0) | v2_struct_0(sK0)),
% 0.21/0.49    inference(subsumption_resolution,[],[f312,f100])).
% 0.21/0.49  fof(f100,plain,(
% 0.21/0.49    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0))))))),
% 0.21/0.49    inference(definition_unfolding,[],[f65,f71])).
% 0.21/0.49  fof(f65,plain,(
% 0.21/0.49    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))))),
% 0.21/0.49    inference(cnf_transformation,[],[f48])).
% 0.21/0.49  fof(f312,plain,(
% 0.21/0.49    v1_xboole_0(k2_struct_0(sK0)) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))))) | ~v13_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) | ~v2_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) | v1_xboole_0(sK1) | ~m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_struct_0(sK0) | v2_struct_0(sK0)),
% 0.21/0.49    inference(duplicate_literal_removal,[],[f311])).
% 0.21/0.49  fof(f311,plain,(
% 0.21/0.49    v1_xboole_0(k2_struct_0(sK0)) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))))) | ~v13_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) | ~v2_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) | v1_xboole_0(sK1) | ~m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) | v1_xboole_0(k2_struct_0(sK0)) | ~l1_struct_0(sK0) | v2_struct_0(sK0)),
% 0.21/0.49    inference(resolution,[],[f310,f108])).
% 0.21/0.49  fof(f108,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (~v2_struct_0(k3_yellow19(X0,X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1))))) | ~v13_waybel_0(X2,k3_lattice3(k1_lattice3(X1))) | ~v2_waybel_0(X2,k3_lattice3(k1_lattice3(X1))) | v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 0.21/0.49    inference(definition_unfolding,[],[f89,f71,f71,f71])).
% 0.21/0.49  fof(f89,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (~v2_struct_0(k3_yellow19(X0,X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1)))) | ~v13_waybel_0(X2,k3_yellow_1(X1)) | ~v2_waybel_0(X2,k3_yellow_1(X1)) | v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f37])).
% 0.21/0.49  fof(f37,plain,(
% 0.21/0.49    ! [X0,X1,X2] : ((v6_waybel_0(k3_yellow19(X0,X1,X2),X0) & v4_orders_2(k3_yellow19(X0,X1,X2)) & v3_orders_2(k3_yellow19(X0,X1,X2)) & ~v2_struct_0(k3_yellow19(X0,X1,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1)))) | ~v13_waybel_0(X2,k3_yellow_1(X1)) | ~v2_waybel_0(X2,k3_yellow_1(X1)) | v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 0.21/0.49    inference(flattening,[],[f36])).
% 0.21/0.49  fof(f36,plain,(
% 0.21/0.49    ! [X0,X1,X2] : ((v6_waybel_0(k3_yellow19(X0,X1,X2),X0) & v4_orders_2(k3_yellow19(X0,X1,X2)) & v3_orders_2(k3_yellow19(X0,X1,X2)) & ~v2_struct_0(k3_yellow19(X0,X1,X2))) | (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1)))) | ~v13_waybel_0(X2,k3_yellow_1(X1)) | ~v2_waybel_0(X2,k3_yellow_1(X1)) | v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)))),
% 0.21/0.49    inference(ennf_transformation,[],[f14])).
% 0.21/0.49  % (5398)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.21/0.49  fof(f14,axiom,(
% 0.21/0.49    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1)))) & v13_waybel_0(X2,k3_yellow_1(X1)) & v2_waybel_0(X2,k3_yellow_1(X1)) & ~v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1) & l1_struct_0(X0) & ~v2_struct_0(X0)) => (v6_waybel_0(k3_yellow19(X0,X1,X2),X0) & v4_orders_2(k3_yellow19(X0,X1,X2)) & v3_orders_2(k3_yellow19(X0,X1,X2)) & ~v2_struct_0(k3_yellow19(X0,X1,X2))))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc4_yellow19)).
% 0.21/0.49  fof(f310,plain,(
% 0.21/0.49    v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1)) | v1_xboole_0(k2_struct_0(sK0))),
% 0.21/0.49    inference(subsumption_resolution,[],[f307,f285])).
% 0.21/0.49  fof(f285,plain,(
% 0.21/0.49    v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1)) | v1_xboole_0(k2_struct_0(sK0)) | r1_waybel_7(sK0,sK1,sK2)),
% 0.21/0.49    inference(duplicate_literal_removal,[],[f280])).
% 0.21/0.49  fof(f280,plain,(
% 0.21/0.49    r1_waybel_7(sK0,sK1,sK2) | v1_xboole_0(k2_struct_0(sK0)) | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1)) | r1_waybel_7(sK0,sK1,sK2)),
% 0.21/0.49    inference(backward_demodulation,[],[f269,f279])).
% 0.21/0.49  fof(f279,plain,(
% 0.21/0.49    sK1 = k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1))),
% 0.21/0.49    inference(subsumption_resolution,[],[f278,f58])).
% 0.21/0.49  fof(f278,plain,(
% 0.21/0.49    sK1 = k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)) | v2_struct_0(sK0)),
% 0.21/0.49    inference(subsumption_resolution,[],[f277,f116])).
% 0.21/0.49  fof(f277,plain,(
% 0.21/0.49    sK1 = k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)) | ~l1_struct_0(sK0) | v2_struct_0(sK0)),
% 0.21/0.49    inference(subsumption_resolution,[],[f276,f61])).
% 0.21/0.49  fof(f276,plain,(
% 0.21/0.49    sK1 = k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)) | v1_xboole_0(sK1) | ~l1_struct_0(sK0) | v2_struct_0(sK0)),
% 0.21/0.49    inference(subsumption_resolution,[],[f275,f103])).
% 0.21/0.49  fof(f103,plain,(
% 0.21/0.49    v1_subset_1(sK1,u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))))),
% 0.21/0.49    inference(definition_unfolding,[],[f62,f71])).
% 0.21/0.49  fof(f62,plain,(
% 0.21/0.49    v1_subset_1(sK1,u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))),
% 0.21/0.49    inference(cnf_transformation,[],[f48])).
% 0.21/0.49  fof(f275,plain,(
% 0.21/0.49    sK1 = k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)) | ~v1_subset_1(sK1,u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0))))) | v1_xboole_0(sK1) | ~l1_struct_0(sK0) | v2_struct_0(sK0)),
% 0.21/0.49    inference(subsumption_resolution,[],[f274,f102])).
% 0.21/0.49  fof(f274,plain,(
% 0.21/0.49    sK1 = k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)) | ~v2_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) | ~v1_subset_1(sK1,u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0))))) | v1_xboole_0(sK1) | ~l1_struct_0(sK0) | v2_struct_0(sK0)),
% 0.21/0.49    inference(subsumption_resolution,[],[f273,f101])).
% 0.21/0.49  fof(f273,plain,(
% 0.21/0.49    sK1 = k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)) | ~v13_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) | ~v2_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) | ~v1_subset_1(sK1,u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0))))) | v1_xboole_0(sK1) | ~l1_struct_0(sK0) | v2_struct_0(sK0)),
% 0.21/0.49    inference(resolution,[],[f104,f100])).
% 0.21/0.49  fof(f104,plain,(
% 0.21/0.49    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X0)))))) | k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) = X1 | ~v13_waybel_0(X1,k3_lattice3(k1_lattice3(k2_struct_0(X0)))) | ~v2_waybel_0(X1,k3_lattice3(k1_lattice3(k2_struct_0(X0)))) | ~v1_subset_1(X1,u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X0))))) | v1_xboole_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 0.21/0.49    inference(definition_unfolding,[],[f85,f71,f71,f71,f71])).
% 0.21/0.49  fof(f85,plain,(
% 0.21/0.49    ( ! [X0,X1] : (k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) | ~v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) | ~v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) | ~v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) | v1_xboole_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f33])).
% 0.21/0.49  fof(f33,plain,(
% 0.21/0.49    ! [X0] : (! [X1] : (k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) | ~v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) | ~v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) | ~v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) | v1_xboole_0(X1)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 0.21/0.49    inference(flattening,[],[f32])).
% 0.21/0.49  fof(f32,plain,(
% 0.21/0.49    ! [X0] : (! [X1] : (k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) = X1 | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) | ~v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) | ~v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) | ~v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) | v1_xboole_0(X1))) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 0.21/0.49    inference(ennf_transformation,[],[f17])).
% 0.21/0.49  fof(f17,axiom,(
% 0.21/0.49    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) & ~v1_xboole_0(X1)) => k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) = X1))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t15_yellow19)).
% 0.21/0.49  fof(f269,plain,(
% 0.21/0.49    r1_waybel_7(sK0,k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),sK2) | v1_xboole_0(k2_struct_0(sK0)) | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1)) | r1_waybel_7(sK0,sK1,sK2)),
% 0.21/0.49    inference(duplicate_literal_removal,[],[f268])).
% 0.21/0.49  fof(f268,plain,(
% 0.21/0.49    v1_xboole_0(k2_struct_0(sK0)) | r1_waybel_7(sK0,k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),sK2) | v1_xboole_0(k2_struct_0(sK0)) | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1)) | r1_waybel_7(sK0,sK1,sK2)),
% 0.21/0.49    inference(resolution,[],[f267,f257])).
% 0.21/0.49  fof(f257,plain,(
% 0.21/0.49    ~v7_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1)) | r1_waybel_7(sK0,k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),sK2) | v1_xboole_0(k2_struct_0(sK0)) | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1)) | r1_waybel_7(sK0,sK1,sK2)),
% 0.21/0.49    inference(subsumption_resolution,[],[f256,f228])).
% 0.21/0.49  fof(f228,plain,(
% 0.21/0.49    v4_orders_2(k3_yellow19(sK0,k2_struct_0(sK0),sK1)) | v1_xboole_0(k2_struct_0(sK0))),
% 0.21/0.49    inference(subsumption_resolution,[],[f227,f58])).
% 0.21/0.49  fof(f227,plain,(
% 0.21/0.49    v4_orders_2(k3_yellow19(sK0,k2_struct_0(sK0),sK1)) | v1_xboole_0(k2_struct_0(sK0)) | v2_struct_0(sK0)),
% 0.21/0.49    inference(subsumption_resolution,[],[f226,f116])).
% 0.21/0.49  fof(f226,plain,(
% 0.21/0.49    v4_orders_2(k3_yellow19(sK0,k2_struct_0(sK0),sK1)) | v1_xboole_0(k2_struct_0(sK0)) | ~l1_struct_0(sK0) | v2_struct_0(sK0)),
% 0.21/0.49    inference(subsumption_resolution,[],[f225,f115])).
% 0.21/0.49  fof(f225,plain,(
% 0.21/0.49    ~m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0))) | v4_orders_2(k3_yellow19(sK0,k2_struct_0(sK0),sK1)) | v1_xboole_0(k2_struct_0(sK0)) | ~l1_struct_0(sK0) | v2_struct_0(sK0)),
% 0.21/0.49    inference(superposition,[],[f224,f164])).
% 0.21/0.49  fof(f224,plain,(
% 0.21/0.49    ( ! [X2] : (~m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(X2))) | v4_orders_2(k3_yellow19(X2,k2_struct_0(sK0),sK1)) | v1_xboole_0(k2_struct_0(sK0)) | ~l1_struct_0(X2) | v2_struct_0(X2)) )),
% 0.21/0.49    inference(subsumption_resolution,[],[f223,f61])).
% 0.21/0.49  fof(f223,plain,(
% 0.21/0.49    ( ! [X2] : (v4_orders_2(k3_yellow19(X2,k2_struct_0(sK0),sK1)) | v1_xboole_0(sK1) | ~m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(X2))) | v1_xboole_0(k2_struct_0(sK0)) | ~l1_struct_0(X2) | v2_struct_0(X2)) )),
% 0.21/0.49    inference(subsumption_resolution,[],[f222,f102])).
% 0.21/0.49  fof(f222,plain,(
% 0.21/0.49    ( ! [X2] : (v4_orders_2(k3_yellow19(X2,k2_struct_0(sK0),sK1)) | ~v2_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) | v1_xboole_0(sK1) | ~m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(X2))) | v1_xboole_0(k2_struct_0(sK0)) | ~l1_struct_0(X2) | v2_struct_0(X2)) )),
% 0.21/0.49    inference(subsumption_resolution,[],[f221,f101])).
% 0.21/0.49  fof(f221,plain,(
% 0.21/0.49    ( ! [X2] : (v4_orders_2(k3_yellow19(X2,k2_struct_0(sK0),sK1)) | ~v13_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) | ~v2_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) | v1_xboole_0(sK1) | ~m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(X2))) | v1_xboole_0(k2_struct_0(sK0)) | ~l1_struct_0(X2) | v2_struct_0(X2)) )),
% 0.21/0.49    inference(resolution,[],[f106,f100])).
% 0.21/0.49  fof(f106,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1))))) | v4_orders_2(k3_yellow19(X0,X1,X2)) | ~v13_waybel_0(X2,k3_lattice3(k1_lattice3(X1))) | ~v2_waybel_0(X2,k3_lattice3(k1_lattice3(X1))) | v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 0.21/0.49    inference(definition_unfolding,[],[f91,f71,f71,f71])).
% 0.21/0.49  fof(f91,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (v4_orders_2(k3_yellow19(X0,X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1)))) | ~v13_waybel_0(X2,k3_yellow_1(X1)) | ~v2_waybel_0(X2,k3_yellow_1(X1)) | v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f37])).
% 0.21/0.49  fof(f256,plain,(
% 0.21/0.49    v1_xboole_0(k2_struct_0(sK0)) | r1_waybel_7(sK0,k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),sK2) | ~v7_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1)) | ~v4_orders_2(k3_yellow19(sK0,k2_struct_0(sK0),sK1)) | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1)) | r1_waybel_7(sK0,sK1,sK2)),
% 0.21/0.49    inference(resolution,[],[f255,f219])).
% 0.21/0.49  fof(f219,plain,(
% 0.21/0.49    ~l1_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK0) | r1_waybel_7(sK0,k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),sK2) | ~v7_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1)) | ~v4_orders_2(k3_yellow19(sK0,k2_struct_0(sK0),sK1)) | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1)) | r1_waybel_7(sK0,sK1,sK2)),
% 0.21/0.49    inference(subsumption_resolution,[],[f218,f165])).
% 0.21/0.49  fof(f165,plain,(
% 0.21/0.49    m1_subset_1(sK2,k2_struct_0(sK0))),
% 0.21/0.49    inference(backward_demodulation,[],[f66,f164])).
% 0.21/0.49  fof(f66,plain,(
% 0.21/0.49    m1_subset_1(sK2,u1_struct_0(sK0))),
% 0.21/0.49    inference(cnf_transformation,[],[f48])).
% 0.21/0.49  fof(f218,plain,(
% 0.21/0.49    ~m1_subset_1(sK2,k2_struct_0(sK0)) | r1_waybel_7(sK0,k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),sK2) | ~l1_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK0) | ~v7_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1)) | ~v4_orders_2(k3_yellow19(sK0,k2_struct_0(sK0),sK1)) | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1)) | r1_waybel_7(sK0,sK1,sK2)),
% 0.21/0.49    inference(forward_demodulation,[],[f217,f164])).
% 0.21/0.49  fof(f217,plain,(
% 0.21/0.49    r1_waybel_7(sK0,k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),sK2) | ~m1_subset_1(sK2,u1_struct_0(sK0)) | ~l1_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK0) | ~v7_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1)) | ~v4_orders_2(k3_yellow19(sK0,k2_struct_0(sK0),sK1)) | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1)) | r1_waybel_7(sK0,sK1,sK2)),
% 0.21/0.49    inference(subsumption_resolution,[],[f216,f58])).
% 0.21/0.49  fof(f216,plain,(
% 0.21/0.49    r1_waybel_7(sK0,k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),sK2) | ~m1_subset_1(sK2,u1_struct_0(sK0)) | ~l1_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK0) | ~v7_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1)) | ~v4_orders_2(k3_yellow19(sK0,k2_struct_0(sK0),sK1)) | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1)) | v2_struct_0(sK0) | r1_waybel_7(sK0,sK1,sK2)),
% 0.21/0.49    inference(subsumption_resolution,[],[f215,f59])).
% 0.21/0.49  fof(f215,plain,(
% 0.21/0.49    r1_waybel_7(sK0,k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),sK2) | ~m1_subset_1(sK2,u1_struct_0(sK0)) | ~l1_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK0) | ~v7_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1)) | ~v4_orders_2(k3_yellow19(sK0,k2_struct_0(sK0),sK1)) | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1)) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | r1_waybel_7(sK0,sK1,sK2)),
% 0.21/0.49    inference(subsumption_resolution,[],[f214,f60])).
% 0.21/0.49  fof(f214,plain,(
% 0.21/0.49    r1_waybel_7(sK0,k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),sK2) | ~m1_subset_1(sK2,u1_struct_0(sK0)) | ~l1_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK0) | ~v7_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1)) | ~v4_orders_2(k3_yellow19(sK0,k2_struct_0(sK0),sK1)) | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1)) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | r1_waybel_7(sK0,sK1,sK2)),
% 0.21/0.49    inference(resolution,[],[f80,f67])).
% 0.21/0.49  fof(f67,plain,(
% 0.21/0.49    r3_waybel_9(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK2) | r1_waybel_7(sK0,sK1,sK2)),
% 0.21/0.49    inference(cnf_transformation,[],[f48])).
% 0.21/0.49  fof(f80,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (~r3_waybel_9(X0,X1,X2) | r1_waybel_7(X0,k2_yellow19(X0,X1),X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f51])).
% 0.21/0.49  fof(f51,plain,(
% 0.21/0.49    ! [X0] : (! [X1] : (! [X2] : (((r3_waybel_9(X0,X1,X2) | ~r1_waybel_7(X0,k2_yellow19(X0,X1),X2)) & (r1_waybel_7(X0,k2_yellow19(X0,X1),X2) | ~r3_waybel_9(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.49    inference(nnf_transformation,[],[f29])).
% 0.21/0.49  fof(f29,plain,(
% 0.21/0.49    ! [X0] : (! [X1] : (! [X2] : ((r3_waybel_9(X0,X1,X2) <=> r1_waybel_7(X0,k2_yellow19(X0,X1),X2)) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.49    inference(flattening,[],[f28])).
% 0.21/0.49  fof(f28,plain,(
% 0.21/0.49    ! [X0] : (! [X1] : (! [X2] : ((r3_waybel_9(X0,X1,X2) <=> r1_waybel_7(X0,k2_yellow19(X0,X1),X2)) | ~m1_subset_1(X2,u1_struct_0(X0))) | (~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.21/0.49    inference(ennf_transformation,[],[f16])).
% 0.21/0.49  fof(f16,axiom,(
% 0.21/0.49    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r3_waybel_9(X0,X1,X2) <=> r1_waybel_7(X0,k2_yellow19(X0,X1),X2)))))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_yellow19)).
% 0.21/0.49  fof(f255,plain,(
% 0.21/0.49    l1_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK0) | v1_xboole_0(k2_struct_0(sK0))),
% 0.21/0.49    inference(subsumption_resolution,[],[f254,f58])).
% 0.21/0.49  fof(f254,plain,(
% 0.21/0.49    l1_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK0) | v1_xboole_0(k2_struct_0(sK0)) | v2_struct_0(sK0)),
% 0.21/0.49    inference(subsumption_resolution,[],[f253,f116])).
% 0.21/0.49  fof(f253,plain,(
% 0.21/0.49    l1_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK0) | v1_xboole_0(k2_struct_0(sK0)) | ~l1_struct_0(sK0) | v2_struct_0(sK0)),
% 0.21/0.49    inference(subsumption_resolution,[],[f252,f115])).
% 0.21/0.49  fof(f252,plain,(
% 0.21/0.49    ~m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0))) | l1_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK0) | v1_xboole_0(k2_struct_0(sK0)) | ~l1_struct_0(sK0) | v2_struct_0(sK0)),
% 0.21/0.49    inference(superposition,[],[f251,f164])).
% 0.21/0.49  fof(f251,plain,(
% 0.21/0.49    ( ! [X2] : (~m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(X2))) | l1_waybel_0(k3_yellow19(X2,k2_struct_0(sK0),sK1),X2) | v1_xboole_0(k2_struct_0(sK0)) | ~l1_struct_0(X2) | v2_struct_0(X2)) )),
% 0.21/0.49    inference(subsumption_resolution,[],[f250,f61])).
% 0.21/0.49  fof(f250,plain,(
% 0.21/0.49    ( ! [X2] : (l1_waybel_0(k3_yellow19(X2,k2_struct_0(sK0),sK1),X2) | v1_xboole_0(sK1) | ~m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(X2))) | v1_xboole_0(k2_struct_0(sK0)) | ~l1_struct_0(X2) | v2_struct_0(X2)) )),
% 0.21/0.49    inference(subsumption_resolution,[],[f249,f102])).
% 0.21/0.49  fof(f249,plain,(
% 0.21/0.49    ( ! [X2] : (l1_waybel_0(k3_yellow19(X2,k2_struct_0(sK0),sK1),X2) | ~v2_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) | v1_xboole_0(sK1) | ~m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(X2))) | v1_xboole_0(k2_struct_0(sK0)) | ~l1_struct_0(X2) | v2_struct_0(X2)) )),
% 0.21/0.49    inference(subsumption_resolution,[],[f248,f101])).
% 0.21/0.49  fof(f248,plain,(
% 0.21/0.49    ( ! [X2] : (l1_waybel_0(k3_yellow19(X2,k2_struct_0(sK0),sK1),X2) | ~v13_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) | ~v2_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) | v1_xboole_0(sK1) | ~m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(X2))) | v1_xboole_0(k2_struct_0(sK0)) | ~l1_struct_0(X2) | v2_struct_0(X2)) )),
% 0.21/0.49    inference(resolution,[],[f109,f100])).
% 0.21/0.49  fof(f109,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1))))) | l1_waybel_0(k3_yellow19(X0,X1,X2),X0) | ~v13_waybel_0(X2,k3_lattice3(k1_lattice3(X1))) | ~v2_waybel_0(X2,k3_lattice3(k1_lattice3(X1))) | v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 0.21/0.49    inference(definition_unfolding,[],[f95,f71,f71,f71])).
% 0.21/0.49  fof(f95,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (l1_waybel_0(k3_yellow19(X0,X1,X2),X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1)))) | ~v13_waybel_0(X2,k3_yellow_1(X1)) | ~v2_waybel_0(X2,k3_yellow_1(X1)) | v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f39])).
% 0.21/0.49  fof(f39,plain,(
% 0.21/0.49    ! [X0,X1,X2] : ((l1_waybel_0(k3_yellow19(X0,X1,X2),X0) & v6_waybel_0(k3_yellow19(X0,X1,X2),X0) & ~v2_struct_0(k3_yellow19(X0,X1,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1)))) | ~v13_waybel_0(X2,k3_yellow_1(X1)) | ~v2_waybel_0(X2,k3_yellow_1(X1)) | v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 0.21/0.49    inference(flattening,[],[f38])).
% 0.21/0.49  fof(f38,plain,(
% 0.21/0.49    ! [X0,X1,X2] : ((l1_waybel_0(k3_yellow19(X0,X1,X2),X0) & v6_waybel_0(k3_yellow19(X0,X1,X2),X0) & ~v2_struct_0(k3_yellow19(X0,X1,X2))) | (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1)))) | ~v13_waybel_0(X2,k3_yellow_1(X1)) | ~v2_waybel_0(X2,k3_yellow_1(X1)) | v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)))),
% 0.21/0.49    inference(ennf_transformation,[],[f13])).
% 0.21/0.49  fof(f13,axiom,(
% 0.21/0.49    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1)))) & v13_waybel_0(X2,k3_yellow_1(X1)) & v2_waybel_0(X2,k3_yellow_1(X1)) & ~v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1) & l1_struct_0(X0) & ~v2_struct_0(X0)) => (l1_waybel_0(k3_yellow19(X0,X1,X2),X0) & v6_waybel_0(k3_yellow19(X0,X1,X2),X0) & ~v2_struct_0(k3_yellow19(X0,X1,X2))))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_yellow19)).
% 0.21/0.49  fof(f267,plain,(
% 0.21/0.49    v7_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1)) | v1_xboole_0(k2_struct_0(sK0))),
% 0.21/0.49    inference(subsumption_resolution,[],[f266,f58])).
% 0.21/0.49  fof(f266,plain,(
% 0.21/0.49    v7_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1)) | v1_xboole_0(k2_struct_0(sK0)) | v2_struct_0(sK0)),
% 0.21/0.49    inference(subsumption_resolution,[],[f265,f116])).
% 0.21/0.49  fof(f265,plain,(
% 0.21/0.49    v7_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1)) | v1_xboole_0(k2_struct_0(sK0)) | ~l1_struct_0(sK0) | v2_struct_0(sK0)),
% 0.21/0.49    inference(subsumption_resolution,[],[f264,f115])).
% 0.21/0.49  fof(f264,plain,(
% 0.21/0.49    ~m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0))) | v7_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1)) | v1_xboole_0(k2_struct_0(sK0)) | ~l1_struct_0(sK0) | v2_struct_0(sK0)),
% 0.21/0.49    inference(superposition,[],[f263,f164])).
% 0.21/0.49  fof(f263,plain,(
% 0.21/0.49    ( ! [X2] : (~m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(X2))) | v7_waybel_0(k3_yellow19(X2,k2_struct_0(sK0),sK1)) | v1_xboole_0(k2_struct_0(sK0)) | ~l1_struct_0(X2) | v2_struct_0(X2)) )),
% 0.21/0.49    inference(subsumption_resolution,[],[f262,f61])).
% 0.21/0.49  fof(f262,plain,(
% 0.21/0.49    ( ! [X2] : (v7_waybel_0(k3_yellow19(X2,k2_struct_0(sK0),sK1)) | v1_xboole_0(sK1) | ~m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(X2))) | v1_xboole_0(k2_struct_0(sK0)) | ~l1_struct_0(X2) | v2_struct_0(X2)) )),
% 0.21/0.49    inference(subsumption_resolution,[],[f261,f103])).
% 0.21/0.49  fof(f261,plain,(
% 0.21/0.49    ( ! [X2] : (v7_waybel_0(k3_yellow19(X2,k2_struct_0(sK0),sK1)) | ~v1_subset_1(sK1,u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0))))) | v1_xboole_0(sK1) | ~m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(X2))) | v1_xboole_0(k2_struct_0(sK0)) | ~l1_struct_0(X2) | v2_struct_0(X2)) )),
% 0.21/0.49    inference(subsumption_resolution,[],[f260,f102])).
% 0.21/0.49  fof(f260,plain,(
% 0.21/0.49    ( ! [X2] : (v7_waybel_0(k3_yellow19(X2,k2_struct_0(sK0),sK1)) | ~v2_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) | ~v1_subset_1(sK1,u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0))))) | v1_xboole_0(sK1) | ~m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(X2))) | v1_xboole_0(k2_struct_0(sK0)) | ~l1_struct_0(X2) | v2_struct_0(X2)) )),
% 0.21/0.49    inference(subsumption_resolution,[],[f259,f101])).
% 0.21/0.49  fof(f259,plain,(
% 0.21/0.49    ( ! [X2] : (v7_waybel_0(k3_yellow19(X2,k2_struct_0(sK0),sK1)) | ~v13_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) | ~v2_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) | ~v1_subset_1(sK1,u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0))))) | v1_xboole_0(sK1) | ~m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(X2))) | v1_xboole_0(k2_struct_0(sK0)) | ~l1_struct_0(X2) | v2_struct_0(X2)) )),
% 0.21/0.49    inference(resolution,[],[f112,f100])).
% 0.21/0.49  fof(f112,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1))))) | v7_waybel_0(k3_yellow19(X0,X1,X2)) | ~v13_waybel_0(X2,k3_lattice3(k1_lattice3(X1))) | ~v2_waybel_0(X2,k3_lattice3(k1_lattice3(X1))) | ~v1_subset_1(X2,u1_struct_0(k3_lattice3(k1_lattice3(X1)))) | v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 0.21/0.49    inference(definition_unfolding,[],[f98,f71,f71,f71,f71])).
% 0.21/0.49  fof(f98,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (v7_waybel_0(k3_yellow19(X0,X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1)))) | ~v13_waybel_0(X2,k3_yellow_1(X1)) | ~v2_waybel_0(X2,k3_yellow_1(X1)) | ~v1_subset_1(X2,u1_struct_0(k3_yellow_1(X1))) | v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f41])).
% 0.21/0.49  fof(f41,plain,(
% 0.21/0.49    ! [X0,X1,X2] : ((v7_waybel_0(k3_yellow19(X0,X1,X2)) & v6_waybel_0(k3_yellow19(X0,X1,X2),X0) & ~v2_struct_0(k3_yellow19(X0,X1,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1)))) | ~v13_waybel_0(X2,k3_yellow_1(X1)) | ~v2_waybel_0(X2,k3_yellow_1(X1)) | ~v1_subset_1(X2,u1_struct_0(k3_yellow_1(X1))) | v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 0.21/0.49    inference(flattening,[],[f40])).
% 0.21/0.49  fof(f40,plain,(
% 0.21/0.49    ! [X0,X1,X2] : ((v7_waybel_0(k3_yellow19(X0,X1,X2)) & v6_waybel_0(k3_yellow19(X0,X1,X2),X0) & ~v2_struct_0(k3_yellow19(X0,X1,X2))) | (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1)))) | ~v13_waybel_0(X2,k3_yellow_1(X1)) | ~v2_waybel_0(X2,k3_yellow_1(X1)) | ~v1_subset_1(X2,u1_struct_0(k3_yellow_1(X1))) | v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)))),
% 0.21/0.49    inference(ennf_transformation,[],[f15])).
% 0.21/0.49  fof(f15,axiom,(
% 0.21/0.49    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1)))) & v13_waybel_0(X2,k3_yellow_1(X1)) & v2_waybel_0(X2,k3_yellow_1(X1)) & v1_subset_1(X2,u1_struct_0(k3_yellow_1(X1))) & ~v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1) & l1_struct_0(X0) & ~v2_struct_0(X0)) => (v7_waybel_0(k3_yellow19(X0,X1,X2)) & v6_waybel_0(k3_yellow19(X0,X1,X2),X0) & ~v2_struct_0(k3_yellow19(X0,X1,X2))))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc5_yellow19)).
% 0.21/0.49  fof(f307,plain,(
% 0.21/0.49    v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1)) | v1_xboole_0(k2_struct_0(sK0)) | ~r1_waybel_7(sK0,sK1,sK2)),
% 0.21/0.49    inference(resolution,[],[f306,f68])).
% 0.21/0.49  fof(f68,plain,(
% 0.21/0.49    ~r3_waybel_9(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK2) | ~r1_waybel_7(sK0,sK1,sK2)),
% 0.21/0.49    inference(cnf_transformation,[],[f48])).
% 0.21/0.49  fof(f306,plain,(
% 0.21/0.49    r3_waybel_9(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK2) | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1)) | v1_xboole_0(k2_struct_0(sK0))),
% 0.21/0.49    inference(subsumption_resolution,[],[f305,f228])).
% 0.21/0.49  fof(f305,plain,(
% 0.21/0.49    r3_waybel_9(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK2) | ~v4_orders_2(k3_yellow19(sK0,k2_struct_0(sK0),sK1)) | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1)) | v1_xboole_0(k2_struct_0(sK0))),
% 0.21/0.49    inference(subsumption_resolution,[],[f304,f267])).
% 0.21/0.49  fof(f304,plain,(
% 0.21/0.49    r3_waybel_9(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK2) | ~v7_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1)) | ~v4_orders_2(k3_yellow19(sK0,k2_struct_0(sK0),sK1)) | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1)) | v1_xboole_0(k2_struct_0(sK0))),
% 0.21/0.49    inference(subsumption_resolution,[],[f303,f255])).
% 0.21/0.49  fof(f303,plain,(
% 0.21/0.49    r3_waybel_9(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK2) | ~l1_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK0) | ~v7_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1)) | ~v4_orders_2(k3_yellow19(sK0,k2_struct_0(sK0),sK1)) | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1)) | v1_xboole_0(k2_struct_0(sK0))),
% 0.21/0.49    inference(subsumption_resolution,[],[f302,f165])).
% 0.21/0.49  fof(f302,plain,(
% 0.21/0.49    ~m1_subset_1(sK2,k2_struct_0(sK0)) | r3_waybel_9(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK2) | ~l1_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK0) | ~v7_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1)) | ~v4_orders_2(k3_yellow19(sK0,k2_struct_0(sK0),sK1)) | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1)) | v1_xboole_0(k2_struct_0(sK0))),
% 0.21/0.49    inference(resolution,[],[f290,f300])).
% 0.21/0.49  fof(f300,plain,(
% 0.21/0.49    r1_waybel_7(sK0,sK1,sK2) | v1_xboole_0(k2_struct_0(sK0))),
% 0.21/0.49    inference(subsumption_resolution,[],[f299,f115])).
% 0.21/0.49  fof(f299,plain,(
% 0.21/0.49    ~m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0))) | v1_xboole_0(k2_struct_0(sK0)) | r1_waybel_7(sK0,sK1,sK2)),
% 0.21/0.49    inference(forward_demodulation,[],[f298,f164])).
% 0.21/0.49  fof(f298,plain,(
% 0.21/0.49    v1_xboole_0(k2_struct_0(sK0)) | r1_waybel_7(sK0,sK1,sK2) | ~m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.21/0.49    inference(subsumption_resolution,[],[f297,f58])).
% 0.21/0.49  fof(f297,plain,(
% 0.21/0.49    v1_xboole_0(k2_struct_0(sK0)) | r1_waybel_7(sK0,sK1,sK2) | ~m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) | v2_struct_0(sK0)),
% 0.21/0.49    inference(subsumption_resolution,[],[f296,f116])).
% 0.21/0.49  fof(f296,plain,(
% 0.21/0.49    v1_xboole_0(k2_struct_0(sK0)) | r1_waybel_7(sK0,sK1,sK2) | ~m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_struct_0(sK0) | v2_struct_0(sK0)),
% 0.21/0.49    inference(subsumption_resolution,[],[f295,f61])).
% 0.21/0.49  fof(f295,plain,(
% 0.21/0.49    v1_xboole_0(k2_struct_0(sK0)) | r1_waybel_7(sK0,sK1,sK2) | v1_xboole_0(sK1) | ~m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_struct_0(sK0) | v2_struct_0(sK0)),
% 0.21/0.49    inference(subsumption_resolution,[],[f294,f102])).
% 0.21/0.49  fof(f294,plain,(
% 0.21/0.49    v1_xboole_0(k2_struct_0(sK0)) | r1_waybel_7(sK0,sK1,sK2) | ~v2_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) | v1_xboole_0(sK1) | ~m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_struct_0(sK0) | v2_struct_0(sK0)),
% 0.21/0.49    inference(subsumption_resolution,[],[f293,f101])).
% 0.21/0.49  fof(f293,plain,(
% 0.21/0.49    v1_xboole_0(k2_struct_0(sK0)) | r1_waybel_7(sK0,sK1,sK2) | ~v13_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) | ~v2_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) | v1_xboole_0(sK1) | ~m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_struct_0(sK0) | v2_struct_0(sK0)),
% 0.21/0.49    inference(subsumption_resolution,[],[f292,f100])).
% 0.21/0.49  fof(f292,plain,(
% 0.21/0.49    v1_xboole_0(k2_struct_0(sK0)) | r1_waybel_7(sK0,sK1,sK2) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))))) | ~v13_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) | ~v2_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) | v1_xboole_0(sK1) | ~m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_struct_0(sK0) | v2_struct_0(sK0)),
% 0.21/0.49    inference(duplicate_literal_removal,[],[f291])).
% 0.21/0.49  fof(f291,plain,(
% 0.21/0.49    v1_xboole_0(k2_struct_0(sK0)) | r1_waybel_7(sK0,sK1,sK2) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))))) | ~v13_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) | ~v2_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) | v1_xboole_0(sK1) | ~m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) | v1_xboole_0(k2_struct_0(sK0)) | ~l1_struct_0(sK0) | v2_struct_0(sK0)),
% 0.21/0.49    inference(resolution,[],[f285,f108])).
% 0.21/0.49  fof(f290,plain,(
% 0.21/0.49    ( ! [X0] : (~r1_waybel_7(sK0,sK1,X0) | ~m1_subset_1(X0,k2_struct_0(sK0)) | r3_waybel_9(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1),X0) | ~l1_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK0) | ~v7_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1)) | ~v4_orders_2(k3_yellow19(sK0,k2_struct_0(sK0),sK1)) | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))) )),
% 0.21/0.49    inference(forward_demodulation,[],[f289,f164])).
% 0.21/0.49  fof(f289,plain,(
% 0.21/0.49    ( ! [X0] : (~r1_waybel_7(sK0,sK1,X0) | r3_waybel_9(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1),X0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~l1_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK0) | ~v7_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1)) | ~v4_orders_2(k3_yellow19(sK0,k2_struct_0(sK0),sK1)) | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))) )),
% 0.21/0.49    inference(subsumption_resolution,[],[f288,f58])).
% 0.21/0.49  fof(f288,plain,(
% 0.21/0.49    ( ! [X0] : (~r1_waybel_7(sK0,sK1,X0) | r3_waybel_9(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1),X0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~l1_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK0) | ~v7_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1)) | ~v4_orders_2(k3_yellow19(sK0,k2_struct_0(sK0),sK1)) | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1)) | v2_struct_0(sK0)) )),
% 0.21/0.49    inference(subsumption_resolution,[],[f287,f59])).
% 0.21/0.49  fof(f287,plain,(
% 0.21/0.49    ( ! [X0] : (~r1_waybel_7(sK0,sK1,X0) | r3_waybel_9(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1),X0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~l1_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK0) | ~v7_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1)) | ~v4_orders_2(k3_yellow19(sK0,k2_struct_0(sK0),sK1)) | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1)) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 0.21/0.49    inference(subsumption_resolution,[],[f286,f60])).
% 0.21/0.49  fof(f286,plain,(
% 0.21/0.49    ( ! [X0] : (~r1_waybel_7(sK0,sK1,X0) | r3_waybel_9(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1),X0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~l1_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK0) | ~v7_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1)) | ~v4_orders_2(k3_yellow19(sK0,k2_struct_0(sK0),sK1)) | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1)) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 0.21/0.49    inference(superposition,[],[f81,f279])).
% 0.21/0.49  fof(f81,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (~r1_waybel_7(X0,k2_yellow19(X0,X1),X2) | r3_waybel_9(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f51])).
% 0.21/0.49  % SZS output end Proof for theBenchmark
% 0.21/0.49  % (5408)------------------------------
% 0.21/0.49  % (5408)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.49  % (5408)Termination reason: Refutation
% 0.21/0.49  
% 0.21/0.49  % (5408)Memory used [KB]: 1791
% 0.21/0.49  % (5408)Time elapsed: 0.061 s
% 0.21/0.49  % (5408)------------------------------
% 0.21/0.49  % (5408)------------------------------
% 0.21/0.49  % (5394)Success in time 0.129 s
%------------------------------------------------------------------------------
