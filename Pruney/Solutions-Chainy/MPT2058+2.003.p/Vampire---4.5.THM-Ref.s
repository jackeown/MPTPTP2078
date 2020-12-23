%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:23:30 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 1.56s
% Verified   : 
% Statistics : Number of formulae       :  303 (285388 expanded)
%              Number of leaves         :   27 (92215 expanded)
%              Depth                    :  137
%              Number of atoms          : 1793 (2724844 expanded)
%              Number of equality atoms :   75 (45395 expanded)
%              Maximal formula depth    :   20 (   7 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f657,plain,(
    $false ),
    inference(unit_resulting_resolution,[],[f73,f653,f85])).

fof(f85,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(f653,plain,(
    ~ l1_struct_0(sK0) ),
    inference(trivial_inequality_removal,[],[f651])).

fof(f651,plain,
    ( sK2 != sK2
    | ~ l1_struct_0(sK0) ),
    inference(backward_demodulation,[],[f608,f629])).

fof(f629,plain,(
    sK2 = sK3(sK0) ),
    inference(resolution,[],[f624,f593])).

fof(f593,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,sK2)
      | sK2 = X0 ) ),
    inference(backward_demodulation,[],[f559,f566])).

fof(f566,plain,(
    sK2 = sK4(sK0) ),
    inference(resolution,[],[f560,f347])).

fof(f347,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | sK2 = X0 ) ),
    inference(backward_demodulation,[],[f288,f303])).

fof(f303,plain,(
    k2_struct_0(sK0) = sK2 ),
    inference(resolution,[],[f299,f288])).

fof(f299,plain,(
    v1_xboole_0(sK2) ),
    inference(resolution,[],[f290,f138])).

fof(f138,plain,(
    m1_subset_1(sK2,k2_struct_0(sK0)) ),
    inference(backward_demodulation,[],[f79,f137])).

fof(f137,plain,(
    k2_struct_0(sK0) = u1_struct_0(sK0) ),
    inference(resolution,[],[f136,f73])).

fof(f136,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | k2_struct_0(X0) = u1_struct_0(X0) ) ),
    inference(resolution,[],[f86,f85])).

fof(f86,plain,(
    ! [X0] :
      ( ~ l1_struct_0(X0)
      | k2_struct_0(X0) = u1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k2_struct_0(X0) = u1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).

fof(f79,plain,(
    m1_subset_1(sK2,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f54])).

fof(f54,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f50,f53,f52,f51])).

fof(f51,plain,
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

fof(f52,plain,
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

fof(f53,plain,
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

fof(f50,plain,(
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
    inference(flattening,[],[f49])).

fof(f49,plain,(
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
    inference(nnf_transformation,[],[f23])).

fof(f23,plain,(
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
    inference(flattening,[],[f22])).

fof(f22,plain,(
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
    inference(ennf_transformation,[],[f21])).

fof(f21,negated_conjecture,(
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
    inference(negated_conjecture,[],[f20])).

fof(f20,conjecture,(
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

fof(f290,plain,(
    ! [X2] :
      ( ~ m1_subset_1(X2,k2_struct_0(sK0))
      | v1_xboole_0(X2) ) ),
    inference(resolution,[],[f287,f105])).

fof(f105,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X0)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f70])).

fof(f70,plain,(
    ! [X0,X1] :
      ( ( ( ( m1_subset_1(X1,X0)
            | ~ v1_xboole_0(X1) )
          & ( v1_xboole_0(X1)
            | ~ m1_subset_1(X1,X0) ) )
        | ~ v1_xboole_0(X0) )
      & ( ( ( m1_subset_1(X1,X0)
            | ~ r2_hidden(X1,X0) )
          & ( r2_hidden(X1,X0)
            | ~ m1_subset_1(X1,X0) ) )
        | v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ( ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) )
        | ~ v1_xboole_0(X0) )
      & ( ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) )
        | v1_xboole_0(X0) ) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( ( v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) ) )
      & ( ~ v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).

fof(f287,plain,(
    v1_xboole_0(k2_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f286,f73])).

fof(f286,plain,
    ( v1_xboole_0(k2_struct_0(sK0))
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f285,f85])).

fof(f285,plain,
    ( ~ l1_struct_0(sK0)
    | v1_xboole_0(k2_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f284,f238])).

fof(f238,plain,
    ( ~ r1_waybel_7(sK0,sK1,sK2)
    | v1_xboole_0(k2_struct_0(sK0)) ),
    inference(resolution,[],[f237,f81])).

fof(f81,plain,
    ( ~ r3_waybel_9(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK2)
    | ~ r1_waybel_7(sK0,sK1,sK2) ),
    inference(cnf_transformation,[],[f54])).

% (2314)Refutation not found, incomplete strategy% (2314)------------------------------
% (2314)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
fof(f237,plain,
    ( r3_waybel_9(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK2)
    | v1_xboole_0(k2_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f236,f138])).

fof(f236,plain,
    ( r3_waybel_9(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK2)
    | ~ m1_subset_1(sK2,k2_struct_0(sK0))
    | v1_xboole_0(k2_struct_0(sK0)) ),
    inference(duplicate_literal_removal,[],[f235])).

fof(f235,plain,
    ( r3_waybel_9(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK2)
    | ~ m1_subset_1(sK2,k2_struct_0(sK0))
    | v1_xboole_0(k2_struct_0(sK0))
    | r3_waybel_9(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK2) ),
    inference(resolution,[],[f234,f80])).

fof(f80,plain,
    ( r1_waybel_7(sK0,sK1,sK2)
    | r3_waybel_9(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK2) ),
    inference(cnf_transformation,[],[f54])).

fof(f234,plain,(
    ! [X0] :
      ( ~ r1_waybel_7(sK0,sK1,X0)
      | r3_waybel_9(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1),X0)
      | ~ m1_subset_1(X0,k2_struct_0(sK0))
      | v1_xboole_0(k2_struct_0(sK0)) ) ),
    inference(subsumption_resolution,[],[f233,f73])).

fof(f233,plain,(
    ! [X0] :
      ( v1_xboole_0(k2_struct_0(sK0))
      | r3_waybel_9(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1),X0)
      | ~ m1_subset_1(X0,k2_struct_0(sK0))
      | ~ r1_waybel_7(sK0,sK1,X0)
      | ~ l1_pre_topc(sK0) ) ),
    inference(resolution,[],[f232,f85])).

fof(f232,plain,(
    ! [X0] :
      ( ~ l1_struct_0(sK0)
      | v1_xboole_0(k2_struct_0(sK0))
      | r3_waybel_9(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1),X0)
      | ~ m1_subset_1(X0,k2_struct_0(sK0))
      | ~ r1_waybel_7(sK0,sK1,X0) ) ),
    inference(subsumption_resolution,[],[f231,f71])).

fof(f71,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f54])).

fof(f231,plain,(
    ! [X0] :
      ( ~ r1_waybel_7(sK0,sK1,X0)
      | v1_xboole_0(k2_struct_0(sK0))
      | r3_waybel_9(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1),X0)
      | ~ m1_subset_1(X0,k2_struct_0(sK0))
      | ~ l1_struct_0(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f230,f74])).

fof(f74,plain,(
    ~ v1_xboole_0(sK1) ),
    inference(cnf_transformation,[],[f54])).

fof(f230,plain,(
    ! [X0] :
      ( ~ r1_waybel_7(sK0,sK1,X0)
      | v1_xboole_0(k2_struct_0(sK0))
      | r3_waybel_9(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1),X0)
      | ~ m1_subset_1(X0,k2_struct_0(sK0))
      | v1_xboole_0(sK1)
      | ~ l1_struct_0(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f229,f122])).

fof(f122,plain,(
    v1_subset_1(sK1,u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0))))) ),
    inference(definition_unfolding,[],[f75,f84])).

fof(f84,plain,(
    ! [X0] : k3_yellow_1(X0) = k3_lattice3(k1_lattice3(X0)) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] : k3_yellow_1(X0) = k3_lattice3(k1_lattice3(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_yellow_1)).

fof(f75,plain,(
    v1_subset_1(sK1,u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))) ),
    inference(cnf_transformation,[],[f54])).

fof(f229,plain,(
    ! [X0] :
      ( ~ r1_waybel_7(sK0,sK1,X0)
      | v1_xboole_0(k2_struct_0(sK0))
      | r3_waybel_9(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1),X0)
      | ~ m1_subset_1(X0,k2_struct_0(sK0))
      | ~ v1_subset_1(sK1,u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))))
      | v1_xboole_0(sK1)
      | ~ l1_struct_0(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f228,f121])).

fof(f121,plain,(
    v2_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) ),
    inference(definition_unfolding,[],[f76,f84])).

fof(f76,plain,(
    v2_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f54])).

fof(f228,plain,(
    ! [X0] :
      ( ~ r1_waybel_7(sK0,sK1,X0)
      | v1_xboole_0(k2_struct_0(sK0))
      | r3_waybel_9(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1),X0)
      | ~ m1_subset_1(X0,k2_struct_0(sK0))
      | ~ v2_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(sK0))))
      | ~ v1_subset_1(sK1,u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))))
      | v1_xboole_0(sK1)
      | ~ l1_struct_0(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f227,f120])).

fof(f120,plain,(
    v13_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) ),
    inference(definition_unfolding,[],[f77,f84])).

fof(f77,plain,(
    v13_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f54])).

fof(f227,plain,(
    ! [X0] :
      ( ~ r1_waybel_7(sK0,sK1,X0)
      | v1_xboole_0(k2_struct_0(sK0))
      | r3_waybel_9(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1),X0)
      | ~ m1_subset_1(X0,k2_struct_0(sK0))
      | ~ v13_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(sK0))))
      | ~ v2_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(sK0))))
      | ~ v1_subset_1(sK1,u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))))
      | v1_xboole_0(sK1)
      | ~ l1_struct_0(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f226,f119])).

fof(f119,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))))) ),
    inference(definition_unfolding,[],[f78,f84])).

fof(f78,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))) ),
    inference(cnf_transformation,[],[f54])).

fof(f226,plain,(
    ! [X0] :
      ( ~ r1_waybel_7(sK0,sK1,X0)
      | v1_xboole_0(k2_struct_0(sK0))
      | r3_waybel_9(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1),X0)
      | ~ m1_subset_1(X0,k2_struct_0(sK0))
      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0))))))
      | ~ v13_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(sK0))))
      | ~ v2_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(sK0))))
      | ~ v1_subset_1(sK1,u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))))
      | v1_xboole_0(sK1)
      | ~ l1_struct_0(sK0)
      | v2_struct_0(sK0) ) ),
    inference(superposition,[],[f225,f123])).

fof(f123,plain,(
    ! [X0,X1] :
      ( k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X0))))))
      | ~ v13_waybel_0(X1,k3_lattice3(k1_lattice3(k2_struct_0(X0))))
      | ~ v2_waybel_0(X1,k3_lattice3(k1_lattice3(k2_struct_0(X0))))
      | ~ v1_subset_1(X1,u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X0)))))
      | v1_xboole_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(definition_unfolding,[],[f100,f84,f84,f84,f84])).

fof(f100,plain,(
    ! [X0,X1] :
      ( k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
      | ~ v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
      | ~ v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
      | ~ v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0))))
      | v1_xboole_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
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
    inference(flattening,[],[f37])).

fof(f37,plain,(
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
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
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

fof(f225,plain,(
    ! [X0] :
      ( ~ r1_waybel_7(sK0,k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),X0)
      | v1_xboole_0(k2_struct_0(sK0))
      | r3_waybel_9(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1),X0)
      | ~ m1_subset_1(X0,k2_struct_0(sK0)) ) ),
    inference(subsumption_resolution,[],[f224,f73])).

fof(f224,plain,(
    ! [X0] :
      ( r3_waybel_9(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1),X0)
      | v1_xboole_0(k2_struct_0(sK0))
      | ~ r1_waybel_7(sK0,k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),X0)
      | ~ m1_subset_1(X0,k2_struct_0(sK0))
      | ~ l1_pre_topc(sK0) ) ),
    inference(resolution,[],[f223,f85])).

fof(f223,plain,(
    ! [X0] :
      ( ~ l1_struct_0(sK0)
      | r3_waybel_9(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1),X0)
      | v1_xboole_0(k2_struct_0(sK0))
      | ~ r1_waybel_7(sK0,k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),X0)
      | ~ m1_subset_1(X0,k2_struct_0(sK0)) ) ),
    inference(subsumption_resolution,[],[f222,f134])).

fof(f134,plain,(
    ! [X0] : m1_subset_1(X0,k1_zfmisc_1(X0)) ),
    inference(forward_demodulation,[],[f83,f82])).

fof(f82,plain,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).

fof(f83,plain,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_subset_1)).

fof(f222,plain,(
    ! [X0] :
      ( ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0)))
      | ~ m1_subset_1(X0,k2_struct_0(sK0))
      | r3_waybel_9(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1),X0)
      | v1_xboole_0(k2_struct_0(sK0))
      | ~ r1_waybel_7(sK0,k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),X0)
      | ~ l1_struct_0(sK0) ) ),
    inference(forward_demodulation,[],[f221,f137])).

fof(f221,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k2_struct_0(sK0))
      | r3_waybel_9(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1),X0)
      | v1_xboole_0(k2_struct_0(sK0))
      | ~ r1_waybel_7(sK0,k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),X0)
      | ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ l1_struct_0(sK0) ) ),
    inference(forward_demodulation,[],[f220,f137])).

fof(f220,plain,(
    ! [X0] :
      ( r3_waybel_9(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1),X0)
      | v1_xboole_0(k2_struct_0(sK0))
      | ~ r1_waybel_7(sK0,k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),X0)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ l1_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f219,f74])).

fof(f219,plain,(
    ! [X0] :
      ( r3_waybel_9(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1),X0)
      | v1_xboole_0(k2_struct_0(sK0))
      | ~ r1_waybel_7(sK0,k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),X0)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | v1_xboole_0(sK1)
      | ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ l1_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f218,f121])).

fof(f218,plain,(
    ! [X0] :
      ( r3_waybel_9(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1),X0)
      | v1_xboole_0(k2_struct_0(sK0))
      | ~ r1_waybel_7(sK0,k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),X0)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ v2_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(sK0))))
      | v1_xboole_0(sK1)
      | ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ l1_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f217,f120])).

fof(f217,plain,(
    ! [X0] :
      ( r3_waybel_9(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1),X0)
      | v1_xboole_0(k2_struct_0(sK0))
      | ~ r1_waybel_7(sK0,k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),X0)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ v13_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(sK0))))
      | ~ v2_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(sK0))))
      | v1_xboole_0(sK1)
      | ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ l1_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f216,f119])).

fof(f216,plain,(
    ! [X0] :
      ( r3_waybel_9(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1),X0)
      | v1_xboole_0(k2_struct_0(sK0))
      | ~ r1_waybel_7(sK0,k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),X0)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0))))))
      | ~ v13_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(sK0))))
      | ~ v2_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(sK0))))
      | v1_xboole_0(sK1)
      | ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ l1_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f215,f71])).

fof(f215,plain,(
    ! [X0] :
      ( r3_waybel_9(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1),X0)
      | v1_xboole_0(k2_struct_0(sK0))
      | ~ r1_waybel_7(sK0,k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),X0)
      | v2_struct_0(sK0)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0))))))
      | ~ v13_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(sK0))))
      | ~ v2_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(sK0))))
      | v1_xboole_0(sK1)
      | ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ l1_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f214,f72])).

fof(f72,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f54])).

fof(f214,plain,(
    ! [X0] :
      ( r3_waybel_9(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1),X0)
      | v1_xboole_0(k2_struct_0(sK0))
      | ~ r1_waybel_7(sK0,k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),X0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0))))))
      | ~ v13_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(sK0))))
      | ~ v2_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(sK0))))
      | v1_xboole_0(sK1)
      | ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ l1_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f213,f73])).

fof(f213,plain,(
    ! [X0] :
      ( r3_waybel_9(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1),X0)
      | v1_xboole_0(k2_struct_0(sK0))
      | ~ r1_waybel_7(sK0,k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),X0)
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0))))))
      | ~ v13_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(sK0))))
      | ~ v2_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(sK0))))
      | v1_xboole_0(sK1)
      | ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ l1_struct_0(sK0) ) ),
    inference(duplicate_literal_removal,[],[f212])).

fof(f212,plain,(
    ! [X0] :
      ( r3_waybel_9(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1),X0)
      | v1_xboole_0(k2_struct_0(sK0))
      | ~ r1_waybel_7(sK0,k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),X0)
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0))))))
      | ~ v13_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(sK0))))
      | ~ v2_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(sK0))))
      | v1_xboole_0(sK1)
      | ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
      | v1_xboole_0(k2_struct_0(sK0))
      | ~ l1_struct_0(sK0)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f211,f128])).

fof(f128,plain,(
    ! [X2,X0,X1] :
      ( l1_waybel_0(k3_yellow19(X0,X1,X2),X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
      | ~ v13_waybel_0(X2,k3_lattice3(k1_lattice3(X1)))
      | ~ v2_waybel_0(X2,k3_lattice3(k1_lattice3(X1)))
      | v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(definition_unfolding,[],[f115,f84,f84,f84])).

fof(f115,plain,(
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
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
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
    inference(flattening,[],[f45])).

fof(f45,plain,(
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
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
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

fof(f211,plain,(
    ! [X0,X1] :
      ( ~ l1_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1),X0)
      | r3_waybel_9(X0,k3_yellow19(sK0,k2_struct_0(sK0),sK1),X1)
      | v1_xboole_0(k2_struct_0(sK0))
      | ~ r1_waybel_7(X0,k2_yellow19(X0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0)) ) ),
    inference(subsumption_resolution,[],[f210,f73])).

fof(f210,plain,(
    ! [X0,X1] :
      ( ~ l1_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1),X0)
      | r3_waybel_9(X0,k3_yellow19(sK0,k2_struct_0(sK0),sK1),X1)
      | v1_xboole_0(k2_struct_0(sK0))
      | ~ r1_waybel_7(X0,k2_yellow19(X0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(sK0) ) ),
    inference(resolution,[],[f209,f85])).

% (2328)Refutation not found, incomplete strategy% (2328)------------------------------
% (2328)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
fof(f209,plain,(
    ! [X0,X1] :
      ( ~ l1_struct_0(sK0)
      | ~ l1_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1),X1)
      | r3_waybel_9(X1,k3_yellow19(sK0,k2_struct_0(sK0),sK1),X0)
      | v1_xboole_0(k2_struct_0(sK0))
      | ~ r1_waybel_7(X1,k2_yellow19(X1,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),X0)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ m1_subset_1(X0,u1_struct_0(X1)) ) ),
    inference(subsumption_resolution,[],[f208,f134])).

fof(f208,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0)))
      | ~ m1_subset_1(X0,u1_struct_0(X1))
      | ~ l1_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1),X1)
      | r3_waybel_9(X1,k3_yellow19(sK0,k2_struct_0(sK0),sK1),X0)
      | v1_xboole_0(k2_struct_0(sK0))
      | ~ r1_waybel_7(X1,k2_yellow19(X1,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),X0)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_struct_0(sK0) ) ),
    inference(forward_demodulation,[],[f207,f137])).

fof(f207,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,u1_struct_0(X1))
      | ~ l1_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1),X1)
      | r3_waybel_9(X1,k3_yellow19(sK0,k2_struct_0(sK0),sK1),X0)
      | v1_xboole_0(k2_struct_0(sK0))
      | ~ r1_waybel_7(X1,k2_yellow19(X1,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),X0)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_struct_0(sK0)
      | ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(subsumption_resolution,[],[f206,f71])).

fof(f206,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,u1_struct_0(X1))
      | ~ l1_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1),X1)
      | r3_waybel_9(X1,k3_yellow19(sK0,k2_struct_0(sK0),sK1),X0)
      | v1_xboole_0(k2_struct_0(sK0))
      | ~ r1_waybel_7(X1,k2_yellow19(X1,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),X0)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_struct_0(sK0)
      | ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f205,f74])).

fof(f205,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,u1_struct_0(X1))
      | ~ l1_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1),X1)
      | r3_waybel_9(X1,k3_yellow19(sK0,k2_struct_0(sK0),sK1),X0)
      | v1_xboole_0(k2_struct_0(sK0))
      | ~ r1_waybel_7(X1,k2_yellow19(X1,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),X0)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_struct_0(sK0)
      | v1_xboole_0(sK1)
      | ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f204,f121])).

fof(f204,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,u1_struct_0(X1))
      | ~ l1_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1),X1)
      | r3_waybel_9(X1,k3_yellow19(sK0,k2_struct_0(sK0),sK1),X0)
      | v1_xboole_0(k2_struct_0(sK0))
      | ~ r1_waybel_7(X1,k2_yellow19(X1,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),X0)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_struct_0(sK0)
      | ~ v2_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(sK0))))
      | v1_xboole_0(sK1)
      | ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f203,f120])).

fof(f203,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,u1_struct_0(X1))
      | ~ l1_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1),X1)
      | r3_waybel_9(X1,k3_yellow19(sK0,k2_struct_0(sK0),sK1),X0)
      | v1_xboole_0(k2_struct_0(sK0))
      | ~ r1_waybel_7(X1,k2_yellow19(X1,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),X0)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_struct_0(sK0)
      | ~ v13_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(sK0))))
      | ~ v2_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(sK0))))
      | v1_xboole_0(sK1)
      | ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f202,f119])).

fof(f202,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,u1_struct_0(X1))
      | ~ l1_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1),X1)
      | r3_waybel_9(X1,k3_yellow19(sK0,k2_struct_0(sK0),sK1),X0)
      | v1_xboole_0(k2_struct_0(sK0))
      | ~ r1_waybel_7(X1,k2_yellow19(X1,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),X0)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_struct_0(sK0)
      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0))))))
      | ~ v13_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(sK0))))
      | ~ v2_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(sK0))))
      | v1_xboole_0(sK1)
      | ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
      | v2_struct_0(sK0) ) ),
    inference(duplicate_literal_removal,[],[f200])).

% (2315)Termination reason: Refutation not found, incomplete strategy

% (2315)Memory used [KB]: 10746
% (2315)Time elapsed: 0.154 s
% (2315)------------------------------
% (2315)------------------------------
fof(f200,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,u1_struct_0(X1))
      | ~ l1_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1),X1)
      | r3_waybel_9(X1,k3_yellow19(sK0,k2_struct_0(sK0),sK1),X0)
      | v1_xboole_0(k2_struct_0(sK0))
      | ~ r1_waybel_7(X1,k2_yellow19(X1,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),X0)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_struct_0(sK0)
      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0))))))
      | ~ v13_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(sK0))))
      | ~ v2_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(sK0))))
      | v1_xboole_0(sK1)
      | ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
      | v1_xboole_0(k2_struct_0(sK0))
      | ~ l1_struct_0(sK0)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f199,f127])).

fof(f127,plain,(
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
    inference(definition_unfolding,[],[f109,f84,f84,f84])).

fof(f109,plain,(
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
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
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
    inference(flattening,[],[f43])).

fof(f43,plain,(
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
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
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

fof(f199,plain,(
    ! [X0,X1] :
      ( v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1),X0)
      | r3_waybel_9(X0,k3_yellow19(sK0,k2_struct_0(sK0),sK1),X1)
      | v1_xboole_0(k2_struct_0(sK0))
      | ~ r1_waybel_7(X0,k2_yellow19(X0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ l1_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f198,f134])).

fof(f198,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0)))
      | ~ r1_waybel_7(X0,k2_yellow19(X0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),X1)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1),X0)
      | r3_waybel_9(X0,k3_yellow19(sK0,k2_struct_0(sK0),sK1),X1)
      | v1_xboole_0(k2_struct_0(sK0))
      | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ l1_struct_0(sK0) ) ),
    inference(forward_demodulation,[],[f197,f137])).

fof(f197,plain,(
    ! [X0,X1] :
      ( ~ r1_waybel_7(X0,k2_yellow19(X0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),X1)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1),X0)
      | r3_waybel_9(X0,k3_yellow19(sK0,k2_struct_0(sK0),sK1),X1)
      | v1_xboole_0(k2_struct_0(sK0))
      | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ l1_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f196,f71])).

fof(f196,plain,(
    ! [X0,X1] :
      ( ~ r1_waybel_7(X0,k2_yellow19(X0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),X1)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1),X0)
      | r3_waybel_9(X0,k3_yellow19(sK0,k2_struct_0(sK0),sK1),X1)
      | v1_xboole_0(k2_struct_0(sK0))
      | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ l1_struct_0(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f195,f74])).

fof(f195,plain,(
    ! [X0,X1] :
      ( ~ r1_waybel_7(X0,k2_yellow19(X0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),X1)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1),X0)
      | r3_waybel_9(X0,k3_yellow19(sK0,k2_struct_0(sK0),sK1),X1)
      | v1_xboole_0(k2_struct_0(sK0))
      | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | v1_xboole_0(sK1)
      | ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ l1_struct_0(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f194,f121])).

fof(f194,plain,(
    ! [X0,X1] :
      ( ~ r1_waybel_7(X0,k2_yellow19(X0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),X1)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1),X0)
      | r3_waybel_9(X0,k3_yellow19(sK0,k2_struct_0(sK0),sK1),X1)
      | v1_xboole_0(k2_struct_0(sK0))
      | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ v2_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(sK0))))
      | v1_xboole_0(sK1)
      | ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ l1_struct_0(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f193,f120])).

fof(f193,plain,(
    ! [X0,X1] :
      ( ~ r1_waybel_7(X0,k2_yellow19(X0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),X1)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1),X0)
      | r3_waybel_9(X0,k3_yellow19(sK0,k2_struct_0(sK0),sK1),X1)
      | v1_xboole_0(k2_struct_0(sK0))
      | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ v13_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(sK0))))
      | ~ v2_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(sK0))))
      | v1_xboole_0(sK1)
      | ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ l1_struct_0(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f192,f119])).

fof(f192,plain,(
    ! [X0,X1] :
      ( ~ r1_waybel_7(X0,k2_yellow19(X0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),X1)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1),X0)
      | r3_waybel_9(X0,k3_yellow19(sK0,k2_struct_0(sK0),sK1),X1)
      | v1_xboole_0(k2_struct_0(sK0))
      | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0))))))
      | ~ v13_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(sK0))))
      | ~ v2_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(sK0))))
      | v1_xboole_0(sK1)
      | ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ l1_struct_0(sK0)
      | v2_struct_0(sK0) ) ),
    inference(duplicate_literal_removal,[],[f191])).

fof(f191,plain,(
    ! [X0,X1] :
      ( ~ r1_waybel_7(X0,k2_yellow19(X0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),X1)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1),X0)
      | r3_waybel_9(X0,k3_yellow19(sK0,k2_struct_0(sK0),sK1),X1)
      | v1_xboole_0(k2_struct_0(sK0))
      | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0))))))
      | ~ v13_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(sK0))))
      | ~ v2_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(sK0))))
      | v1_xboole_0(sK1)
      | ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
      | v1_xboole_0(k2_struct_0(sK0))
      | ~ l1_struct_0(sK0)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f188,f125])).

fof(f125,plain,(
    ! [X2,X0,X1] :
      ( v4_orders_2(k3_yellow19(X0,X1,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
      | ~ v13_waybel_0(X2,k3_lattice3(k1_lattice3(X1)))
      | ~ v2_waybel_0(X2,k3_lattice3(k1_lattice3(X1)))
      | v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(definition_unfolding,[],[f111,f84,f84,f84])).

fof(f111,plain,(
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
    inference(cnf_transformation,[],[f44])).

fof(f188,plain,(
    ! [X0,X1] :
      ( ~ v4_orders_2(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
      | ~ r1_waybel_7(X0,k2_yellow19(X0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),X1)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1),X0)
      | r3_waybel_9(X0,k3_yellow19(sK0,k2_struct_0(sK0),sK1),X1)
      | v1_xboole_0(k2_struct_0(sK0))
      | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(resolution,[],[f187,f96])).

fof(f96,plain,(
    ! [X2,X0,X1] :
      ( ~ v7_waybel_0(X1)
      | ~ r1_waybel_7(X0,k2_yellow19(X0,X1),X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_waybel_0(X1,X0)
      | r3_waybel_9(X0,X1,X2)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f61])).

fof(f61,plain,(
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
    inference(nnf_transformation,[],[f34])).

fof(f34,plain,(
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
    inference(flattening,[],[f33])).

fof(f33,plain,(
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
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
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

fof(f187,plain,
    ( v7_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
    | v1_xboole_0(k2_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f186,f119])).

fof(f186,plain,
    ( v1_xboole_0(k2_struct_0(sK0))
    | v7_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))))) ),
    inference(subsumption_resolution,[],[f185,f74])).

fof(f185,plain,
    ( v1_xboole_0(sK1)
    | v1_xboole_0(k2_struct_0(sK0))
    | v7_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))))) ),
    inference(subsumption_resolution,[],[f184,f134])).

fof(f184,plain,
    ( ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0)))
    | v1_xboole_0(sK1)
    | v1_xboole_0(k2_struct_0(sK0))
    | v7_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))))) ),
    inference(subsumption_resolution,[],[f183,f121])).

fof(f183,plain,
    ( ~ v2_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(sK0))))
    | ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0)))
    | v1_xboole_0(sK1)
    | v1_xboole_0(k2_struct_0(sK0))
    | v7_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))))) ),
    inference(subsumption_resolution,[],[f182,f120])).

fof(f182,plain,
    ( ~ v13_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(sK0))))
    | ~ v2_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(sK0))))
    | ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0)))
    | v1_xboole_0(sK1)
    | v1_xboole_0(k2_struct_0(sK0))
    | v7_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))))) ),
    inference(resolution,[],[f181,f122])).

fof(f181,plain,(
    ! [X0,X1] :
      ( ~ v1_subset_1(X0,u1_struct_0(k3_lattice3(k1_lattice3(X1))))
      | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
      | ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK0)))
      | v1_xboole_0(X0)
      | v1_xboole_0(X1)
      | v7_waybel_0(k3_yellow19(sK0,X1,X0))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1))))) ) ),
    inference(forward_demodulation,[],[f180,f137])).

fof(f180,plain,(
    ! [X0,X1] :
      ( ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
      | ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
      | ~ v1_subset_1(X0,u1_struct_0(k3_lattice3(k1_lattice3(X1))))
      | v1_xboole_0(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | v1_xboole_0(X1)
      | v7_waybel_0(k3_yellow19(sK0,X1,X0))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1))))) ) ),
    inference(subsumption_resolution,[],[f179,f71])).

fof(f179,plain,(
    ! [X0,X1] :
      ( ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
      | ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
      | ~ v1_subset_1(X0,u1_struct_0(k3_lattice3(k1_lattice3(X1))))
      | v1_xboole_0(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | v1_xboole_0(X1)
      | v7_waybel_0(k3_yellow19(sK0,X1,X0))
      | v2_struct_0(sK0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1))))) ) ),
    inference(resolution,[],[f178,f73])).

fof(f178,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_pre_topc(X2)
      | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
      | ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
      | ~ v1_subset_1(X0,u1_struct_0(k3_lattice3(k1_lattice3(X1))))
      | v1_xboole_0(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
      | v1_xboole_0(X1)
      | v7_waybel_0(k3_yellow19(X2,X1,X0))
      | v2_struct_0(X2)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1))))) ) ),
    inference(resolution,[],[f131,f85])).

fof(f131,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_struct_0(X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
      | ~ v13_waybel_0(X2,k3_lattice3(k1_lattice3(X1)))
      | ~ v2_waybel_0(X2,k3_lattice3(k1_lattice3(X1)))
      | ~ v1_subset_1(X2,u1_struct_0(k3_lattice3(k1_lattice3(X1))))
      | v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(X1)
      | v7_waybel_0(k3_yellow19(X0,X1,X2))
      | v2_struct_0(X0) ) ),
    inference(definition_unfolding,[],[f118,f84,f84,f84,f84])).

fof(f118,plain,(
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
    inference(cnf_transformation,[],[f48])).

fof(f48,plain,(
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
    inference(flattening,[],[f47])).

fof(f47,plain,(
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
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
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

fof(f284,plain,
    ( r1_waybel_7(sK0,sK1,sK2)
    | v1_xboole_0(k2_struct_0(sK0))
    | ~ l1_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f283,f71])).

fof(f283,plain,
    ( r1_waybel_7(sK0,sK1,sK2)
    | v1_xboole_0(k2_struct_0(sK0))
    | ~ l1_struct_0(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f282,f74])).

fof(f282,plain,
    ( r1_waybel_7(sK0,sK1,sK2)
    | v1_xboole_0(k2_struct_0(sK0))
    | v1_xboole_0(sK1)
    | ~ l1_struct_0(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f281,f122])).

fof(f281,plain,
    ( r1_waybel_7(sK0,sK1,sK2)
    | v1_xboole_0(k2_struct_0(sK0))
    | ~ v1_subset_1(sK1,u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))))
    | v1_xboole_0(sK1)
    | ~ l1_struct_0(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f280,f121])).

fof(f280,plain,
    ( r1_waybel_7(sK0,sK1,sK2)
    | v1_xboole_0(k2_struct_0(sK0))
    | ~ v2_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(sK0))))
    | ~ v1_subset_1(sK1,u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))))
    | v1_xboole_0(sK1)
    | ~ l1_struct_0(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f279,f120])).

fof(f279,plain,
    ( r1_waybel_7(sK0,sK1,sK2)
    | v1_xboole_0(k2_struct_0(sK0))
    | ~ v13_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(sK0))))
    | ~ v2_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(sK0))))
    | ~ v1_subset_1(sK1,u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))))
    | v1_xboole_0(sK1)
    | ~ l1_struct_0(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f277,f119])).

fof(f277,plain,
    ( r1_waybel_7(sK0,sK1,sK2)
    | v1_xboole_0(k2_struct_0(sK0))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0))))))
    | ~ v13_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(sK0))))
    | ~ v2_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(sK0))))
    | ~ v1_subset_1(sK1,u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))))
    | v1_xboole_0(sK1)
    | ~ l1_struct_0(sK0)
    | v2_struct_0(sK0) ),
    inference(superposition,[],[f275,f123])).

fof(f275,plain,
    ( r1_waybel_7(sK0,k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),sK2)
    | v1_xboole_0(k2_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f274,f73])).

fof(f274,plain,
    ( r1_waybel_7(sK0,k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),sK2)
    | v1_xboole_0(k2_struct_0(sK0))
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f273,f85])).

fof(f273,plain,
    ( ~ l1_struct_0(sK0)
    | r1_waybel_7(sK0,k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),sK2)
    | v1_xboole_0(k2_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f272,f134])).

fof(f272,plain,
    ( ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0)))
    | v1_xboole_0(k2_struct_0(sK0))
    | r1_waybel_7(sK0,k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),sK2)
    | ~ l1_struct_0(sK0) ),
    inference(forward_demodulation,[],[f271,f137])).

fof(f271,plain,
    ( v1_xboole_0(k2_struct_0(sK0))
    | r1_waybel_7(sK0,k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),sK2)
    | ~ l1_struct_0(sK0)
    | ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(subsumption_resolution,[],[f270,f71])).

fof(f270,plain,
    ( v1_xboole_0(k2_struct_0(sK0))
    | r1_waybel_7(sK0,k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),sK2)
    | ~ l1_struct_0(sK0)
    | ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f269,f74])).

fof(f269,plain,
    ( v1_xboole_0(k2_struct_0(sK0))
    | r1_waybel_7(sK0,k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),sK2)
    | ~ l1_struct_0(sK0)
    | v1_xboole_0(sK1)
    | ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f268,f121])).

fof(f268,plain,
    ( v1_xboole_0(k2_struct_0(sK0))
    | r1_waybel_7(sK0,k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),sK2)
    | ~ l1_struct_0(sK0)
    | ~ v2_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(sK0))))
    | v1_xboole_0(sK1)
    | ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f267,f120])).

fof(f267,plain,
    ( v1_xboole_0(k2_struct_0(sK0))
    | r1_waybel_7(sK0,k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),sK2)
    | ~ l1_struct_0(sK0)
    | ~ v13_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(sK0))))
    | ~ v2_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(sK0))))
    | v1_xboole_0(sK1)
    | ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f266,f119])).

fof(f266,plain,
    ( v1_xboole_0(k2_struct_0(sK0))
    | r1_waybel_7(sK0,k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),sK2)
    | ~ l1_struct_0(sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0))))))
    | ~ v13_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(sK0))))
    | ~ v2_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(sK0))))
    | v1_xboole_0(sK1)
    | ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | v2_struct_0(sK0) ),
    inference(duplicate_literal_removal,[],[f265])).

fof(f265,plain,
    ( v1_xboole_0(k2_struct_0(sK0))
    | r1_waybel_7(sK0,k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),sK2)
    | ~ l1_struct_0(sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0))))))
    | ~ v13_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(sK0))))
    | ~ v2_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(sK0))))
    | v1_xboole_0(sK1)
    | ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | v1_xboole_0(k2_struct_0(sK0))
    | ~ l1_struct_0(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f264,f127])).

fof(f264,plain,
    ( v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
    | v1_xboole_0(k2_struct_0(sK0))
    | r1_waybel_7(sK0,k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),sK2)
    | ~ l1_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f263,f134])).

fof(f263,plain,
    ( ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0)))
    | r1_waybel_7(sK0,k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),sK2)
    | v1_xboole_0(k2_struct_0(sK0))
    | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
    | ~ l1_struct_0(sK0) ),
    inference(forward_demodulation,[],[f262,f137])).

fof(f262,plain,
    ( r1_waybel_7(sK0,k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),sK2)
    | v1_xboole_0(k2_struct_0(sK0))
    | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
    | ~ l1_struct_0(sK0)
    | ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(subsumption_resolution,[],[f261,f71])).

fof(f261,plain,
    ( r1_waybel_7(sK0,k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),sK2)
    | v1_xboole_0(k2_struct_0(sK0))
    | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
    | ~ l1_struct_0(sK0)
    | ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f260,f74])).

fof(f260,plain,
    ( r1_waybel_7(sK0,k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),sK2)
    | v1_xboole_0(k2_struct_0(sK0))
    | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
    | ~ l1_struct_0(sK0)
    | v1_xboole_0(sK1)
    | ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f259,f121])).

fof(f259,plain,
    ( r1_waybel_7(sK0,k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),sK2)
    | v1_xboole_0(k2_struct_0(sK0))
    | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
    | ~ l1_struct_0(sK0)
    | ~ v2_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(sK0))))
    | v1_xboole_0(sK1)
    | ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f258,f120])).

fof(f258,plain,
    ( r1_waybel_7(sK0,k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),sK2)
    | v1_xboole_0(k2_struct_0(sK0))
    | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
    | ~ l1_struct_0(sK0)
    | ~ v13_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(sK0))))
    | ~ v2_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(sK0))))
    | v1_xboole_0(sK1)
    | ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f257,f119])).

fof(f257,plain,
    ( r1_waybel_7(sK0,k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),sK2)
    | v1_xboole_0(k2_struct_0(sK0))
    | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
    | ~ l1_struct_0(sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0))))))
    | ~ v13_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(sK0))))
    | ~ v2_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(sK0))))
    | v1_xboole_0(sK1)
    | ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | v2_struct_0(sK0) ),
    inference(duplicate_literal_removal,[],[f256])).

fof(f256,plain,
    ( r1_waybel_7(sK0,k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),sK2)
    | v1_xboole_0(k2_struct_0(sK0))
    | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
    | ~ l1_struct_0(sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0))))))
    | ~ v13_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(sK0))))
    | ~ v2_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(sK0))))
    | v1_xboole_0(sK1)
    | ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | v1_xboole_0(k2_struct_0(sK0))
    | ~ l1_struct_0(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f255,f128])).

fof(f255,plain,
    ( ~ l1_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK0)
    | r1_waybel_7(sK0,k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),sK2)
    | v1_xboole_0(k2_struct_0(sK0))
    | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
    | ~ l1_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f254,f134])).

fof(f254,plain,
    ( ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0)))
    | ~ l1_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK0)
    | r1_waybel_7(sK0,k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),sK2)
    | v1_xboole_0(k2_struct_0(sK0))
    | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
    | ~ l1_struct_0(sK0) ),
    inference(forward_demodulation,[],[f253,f137])).

fof(f253,plain,
    ( ~ l1_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK0)
    | r1_waybel_7(sK0,k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),sK2)
    | v1_xboole_0(k2_struct_0(sK0))
    | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
    | ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f252,f71])).

fof(f252,plain,
    ( ~ l1_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK0)
    | r1_waybel_7(sK0,k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),sK2)
    | v1_xboole_0(k2_struct_0(sK0))
    | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
    | ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_struct_0(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f251,f74])).

fof(f251,plain,
    ( ~ l1_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK0)
    | r1_waybel_7(sK0,k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),sK2)
    | v1_xboole_0(k2_struct_0(sK0))
    | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
    | v1_xboole_0(sK1)
    | ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_struct_0(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f250,f121])).

fof(f250,plain,
    ( ~ l1_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK0)
    | r1_waybel_7(sK0,k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),sK2)
    | v1_xboole_0(k2_struct_0(sK0))
    | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
    | ~ v2_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(sK0))))
    | v1_xboole_0(sK1)
    | ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_struct_0(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f249,f120])).

fof(f249,plain,
    ( ~ l1_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK0)
    | r1_waybel_7(sK0,k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),sK2)
    | v1_xboole_0(k2_struct_0(sK0))
    | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
    | ~ v13_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(sK0))))
    | ~ v2_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(sK0))))
    | v1_xboole_0(sK1)
    | ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_struct_0(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f248,f119])).

fof(f248,plain,
    ( ~ l1_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK0)
    | r1_waybel_7(sK0,k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),sK2)
    | v1_xboole_0(k2_struct_0(sK0))
    | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0))))))
    | ~ v13_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(sK0))))
    | ~ v2_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(sK0))))
    | v1_xboole_0(sK1)
    | ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_struct_0(sK0)
    | v2_struct_0(sK0) ),
    inference(duplicate_literal_removal,[],[f247])).

fof(f247,plain,
    ( ~ l1_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK0)
    | r1_waybel_7(sK0,k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),sK2)
    | v1_xboole_0(k2_struct_0(sK0))
    | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0))))))
    | ~ v13_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(sK0))))
    | ~ v2_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(sK0))))
    | v1_xboole_0(sK1)
    | ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | v1_xboole_0(k2_struct_0(sK0))
    | ~ l1_struct_0(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f245,f125])).

fof(f245,plain,
    ( ~ v4_orders_2(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
    | ~ l1_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK0)
    | r1_waybel_7(sK0,k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),sK2)
    | v1_xboole_0(k2_struct_0(sK0))
    | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1)) ),
    inference(subsumption_resolution,[],[f244,f138])).

fof(f244,plain,
    ( ~ m1_subset_1(sK2,k2_struct_0(sK0))
    | v1_xboole_0(k2_struct_0(sK0))
    | ~ l1_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK0)
    | r1_waybel_7(sK0,k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),sK2)
    | ~ v4_orders_2(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
    | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1)) ),
    inference(forward_demodulation,[],[f243,f137])).

fof(f243,plain,
    ( v1_xboole_0(k2_struct_0(sK0))
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ l1_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK0)
    | r1_waybel_7(sK0,k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),sK2)
    | ~ v4_orders_2(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
    | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1)) ),
    inference(subsumption_resolution,[],[f242,f71])).

fof(f242,plain,
    ( v1_xboole_0(k2_struct_0(sK0))
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ l1_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK0)
    | r1_waybel_7(sK0,k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),sK2)
    | ~ v4_orders_2(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
    | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f241,f72])).

fof(f241,plain,
    ( v1_xboole_0(k2_struct_0(sK0))
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ l1_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK0)
    | r1_waybel_7(sK0,k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),sK2)
    | ~ v4_orders_2(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
    | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f240,f73])).

fof(f240,plain,
    ( v1_xboole_0(k2_struct_0(sK0))
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ l1_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK0)
    | r1_waybel_7(sK0,k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),sK2)
    | ~ v4_orders_2(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
    | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(duplicate_literal_removal,[],[f239])).

fof(f239,plain,
    ( v1_xboole_0(k2_struct_0(sK0))
    | v1_xboole_0(k2_struct_0(sK0))
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ l1_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK0)
    | r1_waybel_7(sK0,k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),sK2)
    | ~ v4_orders_2(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
    | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f237,f189])).

fof(f189,plain,(
    ! [X2,X3] :
      ( ~ r3_waybel_9(X2,k3_yellow19(sK0,k2_struct_0(sK0),sK1),X3)
      | v1_xboole_0(k2_struct_0(sK0))
      | ~ m1_subset_1(X3,u1_struct_0(X2))
      | ~ l1_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1),X2)
      | r1_waybel_7(X2,k2_yellow19(X2,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),X3)
      | ~ v4_orders_2(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
      | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
      | ~ l1_pre_topc(X2)
      | ~ v2_pre_topc(X2)
      | v2_struct_0(X2) ) ),
    inference(resolution,[],[f187,f95])).

fof(f95,plain,(
    ! [X2,X0,X1] :
      ( ~ v7_waybel_0(X1)
      | ~ r3_waybel_9(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_waybel_0(X1,X0)
      | r1_waybel_7(X0,k2_yellow19(X0,X1),X2)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f61])).

fof(f288,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k2_struct_0(sK0) = X0 ) ),
    inference(resolution,[],[f287,f108])).

fof(f108,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | X0 = X1
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | X0 = X1
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ~ ( v1_xboole_0(X1)
        & X0 != X1
        & v1_xboole_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_boole)).

fof(f560,plain,(
    v1_xboole_0(sK4(sK0)) ),
    inference(resolution,[],[f548,f349])).

fof(f349,plain,(
    ! [X2] :
      ( ~ m1_subset_1(X2,sK2)
      | v1_xboole_0(X2) ) ),
    inference(backward_demodulation,[],[f290,f303])).

fof(f548,plain,(
    m1_subset_1(sK4(sK0),sK2) ),
    inference(subsumption_resolution,[],[f547,f73])).

fof(f547,plain,
    ( m1_subset_1(sK4(sK0),sK2)
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f541,f85])).

fof(f541,plain,
    ( ~ l1_struct_0(sK0)
    | m1_subset_1(sK4(sK0),sK2) ),
    inference(forward_demodulation,[],[f539,f314])).

fof(f314,plain,(
    u1_struct_0(sK0) = sK2 ),
    inference(backward_demodulation,[],[f137,f303])).

fof(f539,plain,
    ( m1_subset_1(sK4(sK0),u1_struct_0(sK0))
    | ~ l1_struct_0(sK0) ),
    inference(resolution,[],[f537,f89])).

fof(f89,plain,(
    ! [X0] :
      ( v7_struct_0(X0)
      | m1_subset_1(sK4(X0),u1_struct_0(X0))
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f59])).

fof(f59,plain,(
    ! [X0] :
      ( ( ( v7_struct_0(X0)
          | ( sK3(X0) != sK4(X0)
            & m1_subset_1(sK4(X0),u1_struct_0(X0))
            & m1_subset_1(sK3(X0),u1_struct_0(X0)) ) )
        & ( ! [X3] :
              ( ! [X4] :
                  ( X3 = X4
                  | ~ m1_subset_1(X4,u1_struct_0(X0)) )
              | ~ m1_subset_1(X3,u1_struct_0(X0)) )
          | ~ v7_struct_0(X0) ) )
      | ~ l1_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f56,f58,f57])).

fof(f57,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( X1 != X2
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
     => ( ? [X2] :
            ( sK3(X0) != X2
            & m1_subset_1(X2,u1_struct_0(X0)) )
        & m1_subset_1(sK3(X0),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f58,plain,(
    ! [X0] :
      ( ? [X2] :
          ( sK3(X0) != X2
          & m1_subset_1(X2,u1_struct_0(X0)) )
     => ( sK3(X0) != sK4(X0)
        & m1_subset_1(sK4(X0),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f56,plain,(
    ! [X0] :
      ( ( ( v7_struct_0(X0)
          | ? [X1] :
              ( ? [X2] :
                  ( X1 != X2
                  & m1_subset_1(X2,u1_struct_0(X0)) )
              & m1_subset_1(X1,u1_struct_0(X0)) ) )
        & ( ! [X3] :
              ( ! [X4] :
                  ( X3 = X4
                  | ~ m1_subset_1(X4,u1_struct_0(X0)) )
              | ~ m1_subset_1(X3,u1_struct_0(X0)) )
          | ~ v7_struct_0(X0) ) )
      | ~ l1_struct_0(X0) ) ),
    inference(rectify,[],[f55])).

fof(f55,plain,(
    ! [X0] :
      ( ( ( v7_struct_0(X0)
          | ? [X1] :
              ( ? [X2] :
                  ( X1 != X2
                  & m1_subset_1(X2,u1_struct_0(X0)) )
              & m1_subset_1(X1,u1_struct_0(X0)) ) )
        & ( ! [X1] :
              ( ! [X2] :
                  ( X1 = X2
                  | ~ m1_subset_1(X2,u1_struct_0(X0)) )
              | ~ m1_subset_1(X1,u1_struct_0(X0)) )
          | ~ v7_struct_0(X0) ) )
      | ~ l1_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ( v7_struct_0(X0)
      <=> ! [X1] :
            ( ! [X2] :
                ( X1 = X2
                | ~ m1_subset_1(X2,u1_struct_0(X0)) )
            | ~ m1_subset_1(X1,u1_struct_0(X0)) ) )
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => ( v7_struct_0(X0)
      <=> ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => X1 = X2 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_struct_0)).

fof(f537,plain,(
    ~ v7_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f534,f134])).

fof(f534,plain,
    ( ~ v7_struct_0(sK0)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(sK2)) ),
    inference(resolution,[],[f532,f392])).

fof(f392,plain,(
    ! [X1] :
      ( m2_connsp_2(sK2,sK0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(sK2)) ) ),
    inference(forward_demodulation,[],[f391,f314])).

fof(f391,plain,(
    ! [X1] :
      ( m2_connsp_2(sK2,sK0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(subsumption_resolution,[],[f390,f71])).

fof(f390,plain,(
    ! [X1] :
      ( m2_connsp_2(sK2,sK0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f389,f72])).

fof(f389,plain,(
    ! [X1] :
      ( m2_connsp_2(sK2,sK0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f387,f73])).

fof(f387,plain,(
    ! [X1] :
      ( m2_connsp_2(sK2,sK0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(superposition,[],[f93,f303])).

fof(f93,plain,(
    ! [X0,X1] :
      ( m2_connsp_2(k2_struct_0(X0),X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( m2_connsp_2(k2_struct_0(X0),X0,X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( m2_connsp_2(k2_struct_0(X0),X0,X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => m2_connsp_2(k2_struct_0(X0),X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_connsp_2)).

fof(f532,plain,
    ( ~ m2_connsp_2(sK2,sK0,sK2)
    | ~ v7_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f531,f73])).

fof(f531,plain,
    ( ~ v7_struct_0(sK0)
    | ~ m2_connsp_2(sK2,sK0,sK2)
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f529,f85])).

fof(f529,plain,
    ( ~ l1_struct_0(sK0)
    | ~ v7_struct_0(sK0)
    | ~ m2_connsp_2(sK2,sK0,sK2) ),
    inference(subsumption_resolution,[],[f527,f404])).

fof(f404,plain,
    ( m1_subset_1(sK5(sK0),sK2)
    | ~ v7_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f403,f73])).

fof(f403,plain,
    ( ~ v7_struct_0(sK0)
    | m1_subset_1(sK5(sK0),sK2)
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f316,f85])).

fof(f316,plain,
    ( ~ l1_struct_0(sK0)
    | ~ v7_struct_0(sK0)
    | m1_subset_1(sK5(sK0),sK2) ),
    inference(backward_demodulation,[],[f140,f303])).

fof(f140,plain,
    ( m1_subset_1(sK5(sK0),k2_struct_0(sK0))
    | ~ v7_struct_0(sK0)
    | ~ l1_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f139,f71])).

fof(f139,plain,
    ( m1_subset_1(sK5(sK0),k2_struct_0(sK0))
    | ~ v7_struct_0(sK0)
    | ~ l1_struct_0(sK0)
    | v2_struct_0(sK0) ),
    inference(superposition,[],[f97,f137])).

fof(f97,plain,(
    ! [X0] :
      ( m1_subset_1(sK5(X0),u1_struct_0(X0))
      | ~ v7_struct_0(X0)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f65])).

fof(f65,plain,(
    ! [X0] :
      ( ( ( v7_struct_0(X0)
          | ! [X1] :
              ( u1_struct_0(X0) != k6_domain_1(u1_struct_0(X0),X1)
              | ~ m1_subset_1(X1,u1_struct_0(X0)) ) )
        & ( ( u1_struct_0(X0) = k6_domain_1(u1_struct_0(X0),sK5(X0))
            & m1_subset_1(sK5(X0),u1_struct_0(X0)) )
          | ~ v7_struct_0(X0) ) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f63,f64])).

fof(f64,plain,(
    ! [X0] :
      ( ? [X2] :
          ( u1_struct_0(X0) = k6_domain_1(u1_struct_0(X0),X2)
          & m1_subset_1(X2,u1_struct_0(X0)) )
     => ( u1_struct_0(X0) = k6_domain_1(u1_struct_0(X0),sK5(X0))
        & m1_subset_1(sK5(X0),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f63,plain,(
    ! [X0] :
      ( ( ( v7_struct_0(X0)
          | ! [X1] :
              ( u1_struct_0(X0) != k6_domain_1(u1_struct_0(X0),X1)
              | ~ m1_subset_1(X1,u1_struct_0(X0)) ) )
        & ( ? [X2] :
              ( u1_struct_0(X0) = k6_domain_1(u1_struct_0(X0),X2)
              & m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ v7_struct_0(X0) ) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(rectify,[],[f62])).

% (2328)Termination reason: Refutation not found, incomplete strategy
fof(f62,plain,(
    ! [X0] :
      ( ( ( v7_struct_0(X0)
          | ! [X1] :
              ( u1_struct_0(X0) != k6_domain_1(u1_struct_0(X0),X1)
              | ~ m1_subset_1(X1,u1_struct_0(X0)) ) )
        & ( ? [X1] :
              ( u1_struct_0(X0) = k6_domain_1(u1_struct_0(X0),X1)
              & m1_subset_1(X1,u1_struct_0(X0)) )
          | ~ v7_struct_0(X0) ) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f36])).

% (2328)Memory used [KB]: 6524
% (2328)Time elapsed: 0.170 s
% (2328)------------------------------
% (2328)------------------------------
fof(f36,plain,(
    ! [X0] :
      ( ( v7_struct_0(X0)
      <=> ? [X1] :
            ( u1_struct_0(X0) = k6_domain_1(u1_struct_0(X0),X1)
            & m1_subset_1(X1,u1_struct_0(X0)) ) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f35])).

% (2314)Termination reason: Refutation not found, incomplete strategy

% (2314)Memory used [KB]: 6652
% (2314)Time elapsed: 0.164 s
% (2314)------------------------------
% (2314)------------------------------
fof(f35,plain,(
    ! [X0] :
      ( ( v7_struct_0(X0)
      <=> ? [X1] :
            ( u1_struct_0(X0) = k6_domain_1(u1_struct_0(X0),X1)
            & m1_subset_1(X1,u1_struct_0(X0)) ) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ( v7_struct_0(X0)
      <=> ? [X1] :
            ( u1_struct_0(X0) = k6_domain_1(u1_struct_0(X0),X1)
            & m1_subset_1(X1,u1_struct_0(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tex_1)).

fof(f527,plain,
    ( ~ m2_connsp_2(sK2,sK0,sK2)
    | ~ m1_subset_1(sK5(sK0),sK2)
    | ~ v7_struct_0(sK0)
    | ~ l1_struct_0(sK0) ),
    inference(superposition,[],[f524,f317])).

fof(f317,plain,
    ( sK2 = k6_domain_1(sK2,sK5(sK0))
    | ~ v7_struct_0(sK0)
    | ~ l1_struct_0(sK0) ),
    inference(backward_demodulation,[],[f142,f303])).

fof(f142,plain,
    ( k2_struct_0(sK0) = k6_domain_1(k2_struct_0(sK0),sK5(sK0))
    | ~ v7_struct_0(sK0)
    | ~ l1_struct_0(sK0) ),
    inference(forward_demodulation,[],[f141,f137])).

fof(f141,plain,
    ( ~ v7_struct_0(sK0)
    | ~ l1_struct_0(sK0)
    | u1_struct_0(sK0) = k6_domain_1(u1_struct_0(sK0),sK5(sK0)) ),
    inference(resolution,[],[f98,f71])).

fof(f98,plain,(
    ! [X0] :
      ( v2_struct_0(X0)
      | ~ v7_struct_0(X0)
      | ~ l1_struct_0(X0)
      | u1_struct_0(X0) = k6_domain_1(u1_struct_0(X0),sK5(X0)) ) ),
    inference(cnf_transformation,[],[f65])).

fof(f524,plain,(
    ! [X0] :
      ( ~ m2_connsp_2(sK2,sK0,k6_domain_1(sK2,X0))
      | ~ m1_subset_1(X0,sK2) ) ),
    inference(subsumption_resolution,[],[f523,f134])).

fof(f523,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,sK2)
      | ~ m1_subset_1(sK2,k1_zfmisc_1(sK2))
      | ~ m2_connsp_2(sK2,sK0,k6_domain_1(sK2,X0)) ) ),
    inference(duplicate_literal_removal,[],[f522])).

fof(f522,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,sK2)
      | ~ m1_subset_1(sK2,k1_zfmisc_1(sK2))
      | ~ m1_subset_1(X0,sK2)
      | ~ m2_connsp_2(sK2,sK0,k6_domain_1(sK2,X0)) ) ),
    inference(resolution,[],[f521,f367])).

fof(f367,plain,(
    ! [X0,X1] :
      ( m1_connsp_2(X0,sK0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(sK2))
      | ~ m1_subset_1(X1,sK2)
      | ~ m2_connsp_2(X0,sK0,k6_domain_1(sK2,X1)) ) ),
    inference(forward_demodulation,[],[f366,f303])).

fof(f366,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(sK2))
      | ~ m1_subset_1(X1,sK2)
      | m1_connsp_2(X0,sK0,X1)
      | ~ m2_connsp_2(X0,sK0,k6_domain_1(k2_struct_0(sK0),X1)) ) ),
    inference(forward_demodulation,[],[f324,f303])).

fof(f324,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,sK2)
      | m1_connsp_2(X0,sK0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))
      | ~ m2_connsp_2(X0,sK0,k6_domain_1(k2_struct_0(sK0),X1)) ) ),
    inference(backward_demodulation,[],[f161,f303])).

fof(f161,plain,(
    ! [X0,X1] :
      ( m1_connsp_2(X0,sK0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))
      | ~ m2_connsp_2(X0,sK0,k6_domain_1(k2_struct_0(sK0),X1))
      | ~ m1_subset_1(X1,k2_struct_0(sK0)) ) ),
    inference(forward_demodulation,[],[f160,f137])).

fof(f160,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))
      | ~ m2_connsp_2(X0,sK0,k6_domain_1(k2_struct_0(sK0),X1))
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | m1_connsp_2(X0,sK0,X1) ) ),
    inference(forward_demodulation,[],[f159,f137])).

fof(f159,plain,(
    ! [X0,X1] :
      ( ~ m2_connsp_2(X0,sK0,k6_domain_1(k2_struct_0(sK0),X1))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | m1_connsp_2(X0,sK0,X1) ) ),
    inference(forward_demodulation,[],[f158,f137])).

fof(f158,plain,(
    ! [X0,X1] :
      ( ~ m2_connsp_2(X0,sK0,k6_domain_1(u1_struct_0(sK0),X1))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | m1_connsp_2(X0,sK0,X1) ) ),
    inference(subsumption_resolution,[],[f157,f71])).

fof(f157,plain,(
    ! [X0,X1] :
      ( ~ m2_connsp_2(X0,sK0,k6_domain_1(u1_struct_0(sK0),X1))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | m1_connsp_2(X0,sK0,X1)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f156,f73])).

fof(f156,plain,(
    ! [X0,X1] :
      ( ~ m2_connsp_2(X0,sK0,k6_domain_1(u1_struct_0(sK0),X1))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ l1_pre_topc(sK0)
      | m1_connsp_2(X0,sK0,X1)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f91,f72])).

fof(f91,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_pre_topc(X0)
      | ~ m2_connsp_2(X2,X0,k6_domain_1(u1_struct_0(X0),X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | m1_connsp_2(X2,X0,X1)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f60])).

fof(f60,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( m2_connsp_2(X2,X0,k6_domain_1(u1_struct_0(X0),X1))
                  | ~ m1_connsp_2(X2,X0,X1) )
                & ( m1_connsp_2(X2,X0,X1)
                  | ~ m2_connsp_2(X2,X0,k6_domain_1(u1_struct_0(X0),X1)) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( m2_connsp_2(X2,X0,k6_domain_1(u1_struct_0(X0),X1))
              <=> m1_connsp_2(X2,X0,X1) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( m2_connsp_2(X2,X0,k6_domain_1(u1_struct_0(X0),X1))
              <=> m1_connsp_2(X2,X0,X1) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( m2_connsp_2(X2,X0,k6_domain_1(u1_struct_0(X0),X1))
              <=> m1_connsp_2(X2,X0,X1) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_connsp_2)).

fof(f521,plain,(
    ! [X0] :
      ( ~ m1_connsp_2(sK2,sK0,X0)
      | ~ m1_subset_1(X0,sK2) ) ),
    inference(forward_demodulation,[],[f520,f314])).

fof(f520,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ m1_connsp_2(sK2,sK0,X0) ) ),
    inference(subsumption_resolution,[],[f519,f71])).

fof(f519,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ m1_connsp_2(sK2,sK0,X0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f518,f73])).

fof(f518,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ l1_pre_topc(sK0)
      | ~ m1_connsp_2(sK2,sK0,X0)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f351,f72])).

fof(f351,plain,(
    ! [X0,X1] :
      ( ~ v2_pre_topc(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ m1_connsp_2(sK2,X0,X1)
      | v2_struct_0(X0) ) ),
    inference(backward_demodulation,[],[f295,f303])).

fof(f295,plain,(
    ! [X0,X1] :
      ( ~ m1_connsp_2(k2_struct_0(sK0),X0,X1)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f293,f107])).

fof(f107,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_connsp_2(X2,X0,X1)
      | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_connsp_2(X2,X0,X1) )
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_connsp_2(X2,X0,X1) )
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,u1_struct_0(X0))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X2] :
          ( m1_connsp_2(X2,X0,X1)
         => m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_connsp_2)).

fof(f293,plain,(
    ! [X0,X1] :
      ( ~ m1_connsp_2(k2_struct_0(sK0),X0,X1)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(resolution,[],[f291,f94])).

fof(f94,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X2,X1)
      | ~ m1_connsp_2(X1,X0,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r2_hidden(X2,X1)
              | ~ m1_connsp_2(X1,X0,X2)
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r2_hidden(X2,X1)
              | ~ m1_connsp_2(X1,X0,X2)
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( m1_connsp_2(X1,X0,X2)
               => r2_hidden(X2,X1) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_connsp_2)).

fof(f291,plain,(
    ! [X3] : ~ r2_hidden(X3,k2_struct_0(sK0)) ),
    inference(resolution,[],[f287,f101])).

fof(f101,plain,(
    ! [X2,X0] :
      ( ~ v1_xboole_0(X0)
      | ~ r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f69])).

fof(f69,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | r2_hidden(sK6(X0),X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f67,f68])).

fof(f68,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK6(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f67,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(rectify,[],[f66])).

fof(f66,plain,(
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

fof(f559,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,sK2)
      | sK4(sK0) = X0 ) ),
    inference(global_subsumption,[],[f347,f349,f558])).

fof(f558,plain,(
    ! [X0] :
      ( sK2 != X0
      | ~ m1_subset_1(X0,sK2)
      | sK4(sK0) = X0 ) ),
    inference(subsumption_resolution,[],[f554,f548])).

fof(f554,plain,(
    ! [X0] :
      ( sK2 != X0
      | ~ m1_subset_1(X0,sK2)
      | ~ m1_subset_1(sK4(sK0),sK2)
      | sK4(sK0) = X0 ) ),
    inference(equality_factoring,[],[f503])).

fof(f503,plain,(
    ! [X12,X13] :
      ( sK2 = sK4(sK0)
      | ~ m1_subset_1(X13,sK2)
      | ~ m1_subset_1(X12,sK2)
      | X12 = X13 ) ),
    inference(resolution,[],[f481,f347])).

fof(f481,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(sK4(sK0))
      | X0 = X1
      | ~ m1_subset_1(X1,sK2)
      | ~ m1_subset_1(X0,sK2) ) ),
    inference(resolution,[],[f459,f349])).

fof(f459,plain,(
    ! [X0,X1] :
      ( m1_subset_1(sK4(sK0),sK2)
      | ~ m1_subset_1(X0,sK2)
      | X0 = X1
      | ~ m1_subset_1(X1,sK2) ) ),
    inference(subsumption_resolution,[],[f458,f73])).

fof(f458,plain,(
    ! [X0,X1] :
      ( m1_subset_1(sK4(sK0),sK2)
      | ~ m1_subset_1(X0,sK2)
      | X0 = X1
      | ~ m1_subset_1(X1,sK2)
      | ~ l1_pre_topc(sK0) ) ),
    inference(resolution,[],[f356,f85])).

fof(f356,plain,(
    ! [X0,X1] :
      ( ~ l1_struct_0(sK0)
      | m1_subset_1(sK4(sK0),sK2)
      | ~ m1_subset_1(X0,sK2)
      | X0 = X1
      | ~ m1_subset_1(X1,sK2) ) ),
    inference(forward_demodulation,[],[f355,f303])).

fof(f355,plain,(
    ! [X0,X1] :
      ( m1_subset_1(sK4(sK0),sK2)
      | ~ m1_subset_1(X0,sK2)
      | ~ m1_subset_1(X1,k2_struct_0(sK0))
      | X0 = X1
      | ~ l1_struct_0(sK0) ) ),
    inference(forward_demodulation,[],[f319,f303])).

fof(f319,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,sK2)
      | m1_subset_1(sK4(sK0),k2_struct_0(sK0))
      | ~ m1_subset_1(X1,k2_struct_0(sK0))
      | X0 = X1
      | ~ l1_struct_0(sK0) ) ),
    inference(backward_demodulation,[],[f149,f303])).

fof(f149,plain,(
    ! [X0,X1] :
      ( m1_subset_1(sK4(sK0),k2_struct_0(sK0))
      | ~ m1_subset_1(X0,k2_struct_0(sK0))
      | ~ m1_subset_1(X1,k2_struct_0(sK0))
      | X0 = X1
      | ~ l1_struct_0(sK0) ) ),
    inference(forward_demodulation,[],[f147,f137])).

fof(f147,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k2_struct_0(sK0))
      | ~ m1_subset_1(X1,k2_struct_0(sK0))
      | X0 = X1
      | m1_subset_1(sK4(sK0),u1_struct_0(sK0))
      | ~ l1_struct_0(sK0) ) ),
    inference(resolution,[],[f146,f89])).

fof(f146,plain,(
    ! [X0,X1] :
      ( ~ v7_struct_0(sK0)
      | ~ m1_subset_1(X0,k2_struct_0(sK0))
      | ~ m1_subset_1(X1,k2_struct_0(sK0))
      | X0 = X1 ) ),
    inference(forward_demodulation,[],[f145,f137])).

fof(f145,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k2_struct_0(sK0))
      | ~ v7_struct_0(sK0)
      | X0 = X1
      | ~ m1_subset_1(X1,u1_struct_0(sK0)) ) ),
    inference(forward_demodulation,[],[f144,f137])).

fof(f144,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ v7_struct_0(sK0)
      | X0 = X1
      | ~ m1_subset_1(X1,u1_struct_0(sK0)) ) ),
    inference(resolution,[],[f143,f73])).

fof(f143,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_pre_topc(X1)
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ v7_struct_0(X1)
      | X0 = X2
      | ~ m1_subset_1(X0,u1_struct_0(X1)) ) ),
    inference(resolution,[],[f87,f85])).

fof(f87,plain,(
    ! [X4,X0,X3] :
      ( ~ l1_struct_0(X0)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ v7_struct_0(X0)
      | X3 = X4 ) ),
    inference(cnf_transformation,[],[f59])).

fof(f624,plain,(
    m1_subset_1(sK3(sK0),sK2) ),
    inference(subsumption_resolution,[],[f623,f73])).

fof(f623,plain,
    ( m1_subset_1(sK3(sK0),sK2)
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f542,f85])).

fof(f542,plain,
    ( ~ l1_struct_0(sK0)
    | m1_subset_1(sK3(sK0),sK2) ),
    inference(forward_demodulation,[],[f540,f314])).

fof(f540,plain,
    ( m1_subset_1(sK3(sK0),u1_struct_0(sK0))
    | ~ l1_struct_0(sK0) ),
    inference(resolution,[],[f537,f88])).

fof(f88,plain,(
    ! [X0] :
      ( v7_struct_0(X0)
      | m1_subset_1(sK3(X0),u1_struct_0(X0))
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f59])).

fof(f608,plain,
    ( sK2 != sK3(sK0)
    | ~ l1_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f607,f537])).

fof(f607,plain,
    ( sK2 != sK3(sK0)
    | v7_struct_0(sK0)
    | ~ l1_struct_0(sK0) ),
    inference(superposition,[],[f90,f566])).

fof(f90,plain,(
    ! [X0] :
      ( sK3(X0) != sK4(X0)
      | v7_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f59])).

fof(f73,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f54])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n020.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 11:51:22 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.51  % (2313)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.22/0.52  % (2304)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.22/0.52  % (2320)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 0.22/0.52  % (2311)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.22/0.52  % (2332)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.22/0.52  % (2332)Refutation not found, incomplete strategy% (2332)------------------------------
% 0.22/0.52  % (2332)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.52  % (2332)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.52  
% 0.22/0.52  % (2332)Memory used [KB]: 1663
% 0.22/0.52  % (2332)Time elapsed: 0.097 s
% 0.22/0.52  % (2332)------------------------------
% 0.22/0.52  % (2332)------------------------------
% 0.22/0.53  % (2329)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 0.22/0.53  % (2325)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.22/0.53  % (2312)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.22/0.53  % (2327)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 0.22/0.53  % (2314)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.22/0.53  % (2310)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.22/0.53  % (2305)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.22/0.53  % (2313)Refutation not found, incomplete strategy% (2313)------------------------------
% 0.22/0.53  % (2313)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.53  % (2313)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.53  
% 0.22/0.53  % (2313)Memory used [KB]: 11001
% 0.22/0.53  % (2313)Time elapsed: 0.104 s
% 0.22/0.53  % (2313)------------------------------
% 0.22/0.53  % (2313)------------------------------
% 0.22/0.53  % (2326)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.22/0.53  % (2304)Refutation not found, incomplete strategy% (2304)------------------------------
% 0.22/0.53  % (2304)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.53  % (2307)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.22/0.53  % (2304)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.53  
% 0.22/0.53  % (2304)Memory used [KB]: 1791
% 0.22/0.53  % (2304)Time elapsed: 0.107 s
% 0.22/0.53  % (2304)------------------------------
% 0.22/0.53  % (2304)------------------------------
% 0.22/0.53  % (2322)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 0.22/0.54  % (2319)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 0.22/0.54  % (2318)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.22/0.54  % (2306)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.22/0.54  % (2329)Refutation not found, incomplete strategy% (2329)------------------------------
% 0.22/0.54  % (2329)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.54  % (2329)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.54  
% 0.22/0.54  % (2329)Memory used [KB]: 6396
% 0.22/0.54  % (2329)Time elapsed: 0.120 s
% 0.22/0.54  % (2329)------------------------------
% 0.22/0.54  % (2329)------------------------------
% 0.22/0.54  % (2319)Refutation not found, incomplete strategy% (2319)------------------------------
% 0.22/0.54  % (2319)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.54  % (2319)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.54  
% 0.22/0.54  % (2319)Memory used [KB]: 10746
% 0.22/0.54  % (2319)Time elapsed: 0.113 s
% 0.22/0.54  % (2319)------------------------------
% 0.22/0.54  % (2319)------------------------------
% 0.22/0.54  % (2321)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 0.22/0.54  % (2320)Refutation not found, incomplete strategy% (2320)------------------------------
% 0.22/0.54  % (2320)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.54  % (2320)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.54  
% 0.22/0.54  % (2320)Memory used [KB]: 1918
% 0.22/0.54  % (2320)Time elapsed: 0.122 s
% 0.22/0.54  % (2320)------------------------------
% 0.22/0.54  % (2320)------------------------------
% 0.22/0.54  % (2309)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.54  % (2328)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 0.22/0.54  % (2331)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 0.22/0.54  % (2308)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.22/0.54  % (2324)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 0.22/0.54  % (2317)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.22/0.54  % (2323)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 0.22/0.55  % (2330)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 0.22/0.55  % (2322)Refutation not found, incomplete strategy% (2322)------------------------------
% 0.22/0.55  % (2322)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.55  % (2322)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.55  
% 0.22/0.55  % (2322)Memory used [KB]: 1791
% 0.22/0.55  % (2322)Time elapsed: 0.123 s
% 0.22/0.55  % (2322)------------------------------
% 0.22/0.55  % (2322)------------------------------
% 0.22/0.55  % (2330)Refutation not found, incomplete strategy% (2330)------------------------------
% 0.22/0.55  % (2330)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.55  % (2330)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.55  
% 0.22/0.55  % (2330)Memory used [KB]: 6396
% 0.22/0.55  % (2330)Time elapsed: 0.134 s
% 0.22/0.55  % (2330)------------------------------
% 0.22/0.55  % (2330)------------------------------
% 0.22/0.55  % (2327)Refutation not found, incomplete strategy% (2327)------------------------------
% 0.22/0.55  % (2327)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.55  % (2327)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.55  
% 0.22/0.55  % (2327)Memory used [KB]: 10874
% 0.22/0.55  % (2327)Time elapsed: 0.118 s
% 0.22/0.55  % (2327)------------------------------
% 0.22/0.55  % (2327)------------------------------
% 0.22/0.55  % (2331)Refutation not found, incomplete strategy% (2331)------------------------------
% 0.22/0.55  % (2331)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.55  % (2331)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.55  
% 0.22/0.55  % (2331)Memory used [KB]: 11001
% 0.22/0.55  % (2331)Time elapsed: 0.144 s
% 0.22/0.55  % (2331)------------------------------
% 0.22/0.55  % (2331)------------------------------
% 0.22/0.55  % (2316)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.22/0.56  % (2303)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.22/0.56  % (2315)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.22/0.57  % (2315)Refutation not found, incomplete strategy% (2315)------------------------------
% 0.22/0.57  % (2315)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.57  % (2325)Refutation found. Thanks to Tanya!
% 0.22/0.57  % SZS status Theorem for theBenchmark
% 0.22/0.57  % SZS output start Proof for theBenchmark
% 0.22/0.57  fof(f657,plain,(
% 0.22/0.57    $false),
% 0.22/0.57    inference(unit_resulting_resolution,[],[f73,f653,f85])).
% 0.22/0.57  fof(f85,plain,(
% 0.22/0.57    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 0.22/0.57    inference(cnf_transformation,[],[f24])).
% 0.22/0.57  fof(f24,plain,(
% 0.22/0.57    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 0.22/0.57    inference(ennf_transformation,[],[f7])).
% 0.22/0.57  fof(f7,axiom,(
% 0.22/0.57    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 0.22/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).
% 0.22/0.57  fof(f653,plain,(
% 0.22/0.57    ~l1_struct_0(sK0)),
% 0.22/0.57    inference(trivial_inequality_removal,[],[f651])).
% 0.22/0.57  fof(f651,plain,(
% 0.22/0.57    sK2 != sK2 | ~l1_struct_0(sK0)),
% 0.22/0.57    inference(backward_demodulation,[],[f608,f629])).
% 0.22/0.57  fof(f629,plain,(
% 0.22/0.57    sK2 = sK3(sK0)),
% 0.22/0.57    inference(resolution,[],[f624,f593])).
% 0.22/0.57  fof(f593,plain,(
% 0.22/0.57    ( ! [X0] : (~m1_subset_1(X0,sK2) | sK2 = X0) )),
% 0.22/0.57    inference(backward_demodulation,[],[f559,f566])).
% 0.22/0.57  fof(f566,plain,(
% 0.22/0.57    sK2 = sK4(sK0)),
% 0.22/0.57    inference(resolution,[],[f560,f347])).
% 0.22/0.57  fof(f347,plain,(
% 0.22/0.57    ( ! [X0] : (~v1_xboole_0(X0) | sK2 = X0) )),
% 0.22/0.57    inference(backward_demodulation,[],[f288,f303])).
% 0.22/0.57  fof(f303,plain,(
% 0.22/0.57    k2_struct_0(sK0) = sK2),
% 0.22/0.57    inference(resolution,[],[f299,f288])).
% 0.22/0.57  fof(f299,plain,(
% 0.22/0.57    v1_xboole_0(sK2)),
% 0.22/0.57    inference(resolution,[],[f290,f138])).
% 0.22/0.57  fof(f138,plain,(
% 0.22/0.57    m1_subset_1(sK2,k2_struct_0(sK0))),
% 0.22/0.57    inference(backward_demodulation,[],[f79,f137])).
% 0.22/0.57  fof(f137,plain,(
% 0.22/0.57    k2_struct_0(sK0) = u1_struct_0(sK0)),
% 0.22/0.57    inference(resolution,[],[f136,f73])).
% 0.22/0.57  fof(f136,plain,(
% 0.22/0.57    ( ! [X0] : (~l1_pre_topc(X0) | k2_struct_0(X0) = u1_struct_0(X0)) )),
% 0.22/0.57    inference(resolution,[],[f86,f85])).
% 0.22/0.57  fof(f86,plain,(
% 0.22/0.57    ( ! [X0] : (~l1_struct_0(X0) | k2_struct_0(X0) = u1_struct_0(X0)) )),
% 0.22/0.57    inference(cnf_transformation,[],[f25])).
% 0.22/0.57  fof(f25,plain,(
% 0.22/0.57    ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0))),
% 0.22/0.57    inference(ennf_transformation,[],[f6])).
% 0.22/0.57  fof(f6,axiom,(
% 0.22/0.57    ! [X0] : (l1_struct_0(X0) => k2_struct_0(X0) = u1_struct_0(X0))),
% 0.22/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).
% 0.22/0.57  fof(f79,plain,(
% 0.22/0.57    m1_subset_1(sK2,u1_struct_0(sK0))),
% 0.22/0.57    inference(cnf_transformation,[],[f54])).
% 0.22/0.57  fof(f54,plain,(
% 0.22/0.57    (((~r1_waybel_7(sK0,sK1,sK2) | ~r3_waybel_9(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK2)) & (r1_waybel_7(sK0,sK1,sK2) | r3_waybel_9(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK2)) & m1_subset_1(sK2,u1_struct_0(sK0))) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))) & v13_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0))) & v2_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0))) & v1_subset_1(sK1,u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))) & ~v1_xboole_0(sK1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0)),
% 0.22/0.57    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f50,f53,f52,f51])).
% 0.22/0.57  fof(f51,plain,(
% 0.22/0.57    ? [X0] : (? [X1] : (? [X2] : ((~r1_waybel_7(X0,X1,X2) | ~r3_waybel_9(X0,k3_yellow19(X0,k2_struct_0(X0),X1),X2)) & (r1_waybel_7(X0,X1,X2) | r3_waybel_9(X0,k3_yellow19(X0,k2_struct_0(X0),X1),X2)) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) & ~v1_xboole_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : ((~r1_waybel_7(sK0,X1,X2) | ~r3_waybel_9(sK0,k3_yellow19(sK0,k2_struct_0(sK0),X1),X2)) & (r1_waybel_7(sK0,X1,X2) | r3_waybel_9(sK0,k3_yellow19(sK0,k2_struct_0(sK0),X1),X2)) & m1_subset_1(X2,u1_struct_0(sK0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))) & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(sK0))) & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(sK0))) & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))) & ~v1_xboole_0(X1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0))),
% 0.22/0.57    introduced(choice_axiom,[])).
% 0.22/0.57  fof(f52,plain,(
% 0.22/0.57    ? [X1] : (? [X2] : ((~r1_waybel_7(sK0,X1,X2) | ~r3_waybel_9(sK0,k3_yellow19(sK0,k2_struct_0(sK0),X1),X2)) & (r1_waybel_7(sK0,X1,X2) | r3_waybel_9(sK0,k3_yellow19(sK0,k2_struct_0(sK0),X1),X2)) & m1_subset_1(X2,u1_struct_0(sK0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))) & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(sK0))) & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(sK0))) & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))) & ~v1_xboole_0(X1)) => (? [X2] : ((~r1_waybel_7(sK0,sK1,X2) | ~r3_waybel_9(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1),X2)) & (r1_waybel_7(sK0,sK1,X2) | r3_waybel_9(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1),X2)) & m1_subset_1(X2,u1_struct_0(sK0))) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))) & v13_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0))) & v2_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0))) & v1_subset_1(sK1,u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))) & ~v1_xboole_0(sK1))),
% 0.22/0.57    introduced(choice_axiom,[])).
% 0.22/0.57  fof(f53,plain,(
% 0.22/0.57    ? [X2] : ((~r1_waybel_7(sK0,sK1,X2) | ~r3_waybel_9(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1),X2)) & (r1_waybel_7(sK0,sK1,X2) | r3_waybel_9(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1),X2)) & m1_subset_1(X2,u1_struct_0(sK0))) => ((~r1_waybel_7(sK0,sK1,sK2) | ~r3_waybel_9(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK2)) & (r1_waybel_7(sK0,sK1,sK2) | r3_waybel_9(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK2)) & m1_subset_1(sK2,u1_struct_0(sK0)))),
% 0.22/0.57    introduced(choice_axiom,[])).
% 0.22/0.57  fof(f50,plain,(
% 0.22/0.57    ? [X0] : (? [X1] : (? [X2] : ((~r1_waybel_7(X0,X1,X2) | ~r3_waybel_9(X0,k3_yellow19(X0,k2_struct_0(X0),X1),X2)) & (r1_waybel_7(X0,X1,X2) | r3_waybel_9(X0,k3_yellow19(X0,k2_struct_0(X0),X1),X2)) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) & ~v1_xboole_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.22/0.57    inference(flattening,[],[f49])).
% 0.22/0.57  fof(f49,plain,(
% 0.22/0.57    ? [X0] : (? [X1] : (? [X2] : (((~r1_waybel_7(X0,X1,X2) | ~r3_waybel_9(X0,k3_yellow19(X0,k2_struct_0(X0),X1),X2)) & (r1_waybel_7(X0,X1,X2) | r3_waybel_9(X0,k3_yellow19(X0,k2_struct_0(X0),X1),X2))) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) & ~v1_xboole_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.22/0.57    inference(nnf_transformation,[],[f23])).
% 0.22/0.57  fof(f23,plain,(
% 0.22/0.57    ? [X0] : (? [X1] : (? [X2] : ((r3_waybel_9(X0,k3_yellow19(X0,k2_struct_0(X0),X1),X2) <~> r1_waybel_7(X0,X1,X2)) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) & ~v1_xboole_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.22/0.57    inference(flattening,[],[f22])).
% 0.22/0.57  fof(f22,plain,(
% 0.22/0.57    ? [X0] : (? [X1] : (? [X2] : ((r3_waybel_9(X0,k3_yellow19(X0,k2_struct_0(X0),X1),X2) <~> r1_waybel_7(X0,X1,X2)) & m1_subset_1(X2,u1_struct_0(X0))) & (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) & ~v1_xboole_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 0.22/0.57    inference(ennf_transformation,[],[f21])).
% 0.22/0.57  fof(f21,negated_conjecture,(
% 0.22/0.57    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) & ~v1_xboole_0(X1)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r3_waybel_9(X0,k3_yellow19(X0,k2_struct_0(X0),X1),X2) <=> r1_waybel_7(X0,X1,X2)))))),
% 0.22/0.57    inference(negated_conjecture,[],[f20])).
% 0.22/0.57  fof(f20,conjecture,(
% 0.22/0.57    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) & ~v1_xboole_0(X1)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r3_waybel_9(X0,k3_yellow19(X0,k2_struct_0(X0),X1),X2) <=> r1_waybel_7(X0,X1,X2)))))),
% 0.22/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_yellow19)).
% 0.22/0.57  fof(f290,plain,(
% 0.22/0.57    ( ! [X2] : (~m1_subset_1(X2,k2_struct_0(sK0)) | v1_xboole_0(X2)) )),
% 0.22/0.57    inference(resolution,[],[f287,f105])).
% 0.22/0.57  fof(f105,plain,(
% 0.22/0.57    ( ! [X0,X1] : (~v1_xboole_0(X0) | ~m1_subset_1(X1,X0) | v1_xboole_0(X1)) )),
% 0.22/0.57    inference(cnf_transformation,[],[f70])).
% 0.22/0.57  fof(f70,plain,(
% 0.22/0.57    ! [X0,X1] : ((((m1_subset_1(X1,X0) | ~v1_xboole_0(X1)) & (v1_xboole_0(X1) | ~m1_subset_1(X1,X0))) | ~v1_xboole_0(X0)) & (((m1_subset_1(X1,X0) | ~r2_hidden(X1,X0)) & (r2_hidden(X1,X0) | ~m1_subset_1(X1,X0))) | v1_xboole_0(X0)))),
% 0.22/0.57    inference(nnf_transformation,[],[f39])).
% 0.22/0.57  fof(f39,plain,(
% 0.22/0.57    ! [X0,X1] : (((m1_subset_1(X1,X0) <=> v1_xboole_0(X1)) | ~v1_xboole_0(X0)) & ((m1_subset_1(X1,X0) <=> r2_hidden(X1,X0)) | v1_xboole_0(X0)))),
% 0.22/0.57    inference(ennf_transformation,[],[f3])).
% 0.22/0.57  fof(f3,axiom,(
% 0.22/0.57    ! [X0,X1] : ((v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> v1_xboole_0(X1))) & (~v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> r2_hidden(X1,X0))))),
% 0.22/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).
% 0.22/0.57  fof(f287,plain,(
% 0.22/0.57    v1_xboole_0(k2_struct_0(sK0))),
% 0.22/0.57    inference(subsumption_resolution,[],[f286,f73])).
% 0.22/0.57  fof(f286,plain,(
% 0.22/0.57    v1_xboole_0(k2_struct_0(sK0)) | ~l1_pre_topc(sK0)),
% 0.22/0.57    inference(resolution,[],[f285,f85])).
% 0.22/0.57  fof(f285,plain,(
% 0.22/0.57    ~l1_struct_0(sK0) | v1_xboole_0(k2_struct_0(sK0))),
% 0.22/0.57    inference(subsumption_resolution,[],[f284,f238])).
% 0.22/0.57  fof(f238,plain,(
% 0.22/0.57    ~r1_waybel_7(sK0,sK1,sK2) | v1_xboole_0(k2_struct_0(sK0))),
% 0.22/0.57    inference(resolution,[],[f237,f81])).
% 0.22/0.57  fof(f81,plain,(
% 0.22/0.57    ~r3_waybel_9(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK2) | ~r1_waybel_7(sK0,sK1,sK2)),
% 0.22/0.57    inference(cnf_transformation,[],[f54])).
% 1.56/0.58  % (2314)Refutation not found, incomplete strategy% (2314)------------------------------
% 1.56/0.58  % (2314)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.56/0.58  fof(f237,plain,(
% 1.56/0.58    r3_waybel_9(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK2) | v1_xboole_0(k2_struct_0(sK0))),
% 1.56/0.58    inference(subsumption_resolution,[],[f236,f138])).
% 1.56/0.58  fof(f236,plain,(
% 1.56/0.58    r3_waybel_9(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK2) | ~m1_subset_1(sK2,k2_struct_0(sK0)) | v1_xboole_0(k2_struct_0(sK0))),
% 1.56/0.58    inference(duplicate_literal_removal,[],[f235])).
% 1.56/0.58  fof(f235,plain,(
% 1.56/0.58    r3_waybel_9(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK2) | ~m1_subset_1(sK2,k2_struct_0(sK0)) | v1_xboole_0(k2_struct_0(sK0)) | r3_waybel_9(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK2)),
% 1.56/0.58    inference(resolution,[],[f234,f80])).
% 1.56/0.58  fof(f80,plain,(
% 1.56/0.58    r1_waybel_7(sK0,sK1,sK2) | r3_waybel_9(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK2)),
% 1.56/0.58    inference(cnf_transformation,[],[f54])).
% 1.56/0.58  fof(f234,plain,(
% 1.56/0.58    ( ! [X0] : (~r1_waybel_7(sK0,sK1,X0) | r3_waybel_9(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1),X0) | ~m1_subset_1(X0,k2_struct_0(sK0)) | v1_xboole_0(k2_struct_0(sK0))) )),
% 1.56/0.58    inference(subsumption_resolution,[],[f233,f73])).
% 1.56/0.58  fof(f233,plain,(
% 1.56/0.58    ( ! [X0] : (v1_xboole_0(k2_struct_0(sK0)) | r3_waybel_9(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1),X0) | ~m1_subset_1(X0,k2_struct_0(sK0)) | ~r1_waybel_7(sK0,sK1,X0) | ~l1_pre_topc(sK0)) )),
% 1.56/0.58    inference(resolution,[],[f232,f85])).
% 1.56/0.58  fof(f232,plain,(
% 1.56/0.58    ( ! [X0] : (~l1_struct_0(sK0) | v1_xboole_0(k2_struct_0(sK0)) | r3_waybel_9(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1),X0) | ~m1_subset_1(X0,k2_struct_0(sK0)) | ~r1_waybel_7(sK0,sK1,X0)) )),
% 1.56/0.58    inference(subsumption_resolution,[],[f231,f71])).
% 1.56/0.58  fof(f71,plain,(
% 1.56/0.58    ~v2_struct_0(sK0)),
% 1.56/0.58    inference(cnf_transformation,[],[f54])).
% 1.56/0.58  fof(f231,plain,(
% 1.56/0.58    ( ! [X0] : (~r1_waybel_7(sK0,sK1,X0) | v1_xboole_0(k2_struct_0(sK0)) | r3_waybel_9(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1),X0) | ~m1_subset_1(X0,k2_struct_0(sK0)) | ~l1_struct_0(sK0) | v2_struct_0(sK0)) )),
% 1.56/0.58    inference(subsumption_resolution,[],[f230,f74])).
% 1.56/0.58  fof(f74,plain,(
% 1.56/0.58    ~v1_xboole_0(sK1)),
% 1.56/0.58    inference(cnf_transformation,[],[f54])).
% 1.56/0.58  fof(f230,plain,(
% 1.56/0.58    ( ! [X0] : (~r1_waybel_7(sK0,sK1,X0) | v1_xboole_0(k2_struct_0(sK0)) | r3_waybel_9(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1),X0) | ~m1_subset_1(X0,k2_struct_0(sK0)) | v1_xboole_0(sK1) | ~l1_struct_0(sK0) | v2_struct_0(sK0)) )),
% 1.56/0.58    inference(subsumption_resolution,[],[f229,f122])).
% 1.56/0.58  fof(f122,plain,(
% 1.56/0.58    v1_subset_1(sK1,u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))))),
% 1.56/0.58    inference(definition_unfolding,[],[f75,f84])).
% 1.56/0.58  fof(f84,plain,(
% 1.56/0.58    ( ! [X0] : (k3_yellow_1(X0) = k3_lattice3(k1_lattice3(X0))) )),
% 1.56/0.58    inference(cnf_transformation,[],[f12])).
% 1.56/0.58  fof(f12,axiom,(
% 1.56/0.58    ! [X0] : k3_yellow_1(X0) = k3_lattice3(k1_lattice3(X0))),
% 1.56/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_yellow_1)).
% 1.56/0.58  fof(f75,plain,(
% 1.56/0.58    v1_subset_1(sK1,u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))),
% 1.56/0.58    inference(cnf_transformation,[],[f54])).
% 1.56/0.58  fof(f229,plain,(
% 1.56/0.58    ( ! [X0] : (~r1_waybel_7(sK0,sK1,X0) | v1_xboole_0(k2_struct_0(sK0)) | r3_waybel_9(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1),X0) | ~m1_subset_1(X0,k2_struct_0(sK0)) | ~v1_subset_1(sK1,u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0))))) | v1_xboole_0(sK1) | ~l1_struct_0(sK0) | v2_struct_0(sK0)) )),
% 1.56/0.58    inference(subsumption_resolution,[],[f228,f121])).
% 1.56/0.58  fof(f121,plain,(
% 1.56/0.58    v2_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(sK0))))),
% 1.56/0.58    inference(definition_unfolding,[],[f76,f84])).
% 1.56/0.58  fof(f76,plain,(
% 1.56/0.58    v2_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0)))),
% 1.56/0.58    inference(cnf_transformation,[],[f54])).
% 1.56/0.58  fof(f228,plain,(
% 1.56/0.58    ( ! [X0] : (~r1_waybel_7(sK0,sK1,X0) | v1_xboole_0(k2_struct_0(sK0)) | r3_waybel_9(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1),X0) | ~m1_subset_1(X0,k2_struct_0(sK0)) | ~v2_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) | ~v1_subset_1(sK1,u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0))))) | v1_xboole_0(sK1) | ~l1_struct_0(sK0) | v2_struct_0(sK0)) )),
% 1.56/0.58    inference(subsumption_resolution,[],[f227,f120])).
% 1.56/0.58  fof(f120,plain,(
% 1.56/0.58    v13_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(sK0))))),
% 1.56/0.58    inference(definition_unfolding,[],[f77,f84])).
% 1.56/0.58  fof(f77,plain,(
% 1.56/0.58    v13_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0)))),
% 1.56/0.58    inference(cnf_transformation,[],[f54])).
% 1.56/0.58  fof(f227,plain,(
% 1.56/0.58    ( ! [X0] : (~r1_waybel_7(sK0,sK1,X0) | v1_xboole_0(k2_struct_0(sK0)) | r3_waybel_9(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1),X0) | ~m1_subset_1(X0,k2_struct_0(sK0)) | ~v13_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) | ~v2_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) | ~v1_subset_1(sK1,u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0))))) | v1_xboole_0(sK1) | ~l1_struct_0(sK0) | v2_struct_0(sK0)) )),
% 1.56/0.58    inference(subsumption_resolution,[],[f226,f119])).
% 1.56/0.58  fof(f119,plain,(
% 1.56/0.58    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0))))))),
% 1.56/0.58    inference(definition_unfolding,[],[f78,f84])).
% 1.56/0.58  fof(f78,plain,(
% 1.56/0.58    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))))),
% 1.56/0.58    inference(cnf_transformation,[],[f54])).
% 1.56/0.58  fof(f226,plain,(
% 1.56/0.58    ( ! [X0] : (~r1_waybel_7(sK0,sK1,X0) | v1_xboole_0(k2_struct_0(sK0)) | r3_waybel_9(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1),X0) | ~m1_subset_1(X0,k2_struct_0(sK0)) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))))) | ~v13_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) | ~v2_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) | ~v1_subset_1(sK1,u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0))))) | v1_xboole_0(sK1) | ~l1_struct_0(sK0) | v2_struct_0(sK0)) )),
% 1.56/0.58    inference(superposition,[],[f225,f123])).
% 1.56/0.58  fof(f123,plain,(
% 1.56/0.58    ( ! [X0,X1] : (k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X0)))))) | ~v13_waybel_0(X1,k3_lattice3(k1_lattice3(k2_struct_0(X0)))) | ~v2_waybel_0(X1,k3_lattice3(k1_lattice3(k2_struct_0(X0)))) | ~v1_subset_1(X1,u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X0))))) | v1_xboole_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 1.56/0.58    inference(definition_unfolding,[],[f100,f84,f84,f84,f84])).
% 1.56/0.58  fof(f100,plain,(
% 1.56/0.58    ( ! [X0,X1] : (k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) | ~v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) | ~v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) | ~v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) | v1_xboole_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 1.56/0.58    inference(cnf_transformation,[],[f38])).
% 1.56/0.58  fof(f38,plain,(
% 1.56/0.58    ! [X0] : (! [X1] : (k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) | ~v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) | ~v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) | ~v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) | v1_xboole_0(X1)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 1.56/0.58    inference(flattening,[],[f37])).
% 1.56/0.58  fof(f37,plain,(
% 1.56/0.58    ! [X0] : (! [X1] : (k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) = X1 | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) | ~v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) | ~v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) | ~v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) | v1_xboole_0(X1))) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 1.56/0.58    inference(ennf_transformation,[],[f19])).
% 1.56/0.58  fof(f19,axiom,(
% 1.56/0.58    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) & ~v1_xboole_0(X1)) => k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) = X1))),
% 1.56/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t15_yellow19)).
% 1.56/0.58  fof(f225,plain,(
% 1.56/0.58    ( ! [X0] : (~r1_waybel_7(sK0,k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),X0) | v1_xboole_0(k2_struct_0(sK0)) | r3_waybel_9(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1),X0) | ~m1_subset_1(X0,k2_struct_0(sK0))) )),
% 1.56/0.58    inference(subsumption_resolution,[],[f224,f73])).
% 1.56/0.58  fof(f224,plain,(
% 1.56/0.58    ( ! [X0] : (r3_waybel_9(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1),X0) | v1_xboole_0(k2_struct_0(sK0)) | ~r1_waybel_7(sK0,k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),X0) | ~m1_subset_1(X0,k2_struct_0(sK0)) | ~l1_pre_topc(sK0)) )),
% 1.56/0.58    inference(resolution,[],[f223,f85])).
% 1.56/0.58  fof(f223,plain,(
% 1.56/0.58    ( ! [X0] : (~l1_struct_0(sK0) | r3_waybel_9(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1),X0) | v1_xboole_0(k2_struct_0(sK0)) | ~r1_waybel_7(sK0,k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),X0) | ~m1_subset_1(X0,k2_struct_0(sK0))) )),
% 1.56/0.58    inference(subsumption_resolution,[],[f222,f134])).
% 1.56/0.58  fof(f134,plain,(
% 1.56/0.58    ( ! [X0] : (m1_subset_1(X0,k1_zfmisc_1(X0))) )),
% 1.56/0.58    inference(forward_demodulation,[],[f83,f82])).
% 1.56/0.58  fof(f82,plain,(
% 1.56/0.58    ( ! [X0] : (k2_subset_1(X0) = X0) )),
% 1.56/0.58    inference(cnf_transformation,[],[f4])).
% 1.56/0.58  fof(f4,axiom,(
% 1.56/0.58    ! [X0] : k2_subset_1(X0) = X0),
% 1.56/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).
% 1.56/0.58  fof(f83,plain,(
% 1.56/0.58    ( ! [X0] : (m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))) )),
% 1.56/0.58    inference(cnf_transformation,[],[f5])).
% 1.56/0.58  fof(f5,axiom,(
% 1.56/0.58    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))),
% 1.56/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_subset_1)).
% 1.56/0.58  fof(f222,plain,(
% 1.56/0.58    ( ! [X0] : (~m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0))) | ~m1_subset_1(X0,k2_struct_0(sK0)) | r3_waybel_9(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1),X0) | v1_xboole_0(k2_struct_0(sK0)) | ~r1_waybel_7(sK0,k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),X0) | ~l1_struct_0(sK0)) )),
% 1.56/0.58    inference(forward_demodulation,[],[f221,f137])).
% 1.56/0.58  fof(f221,plain,(
% 1.56/0.58    ( ! [X0] : (~m1_subset_1(X0,k2_struct_0(sK0)) | r3_waybel_9(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1),X0) | v1_xboole_0(k2_struct_0(sK0)) | ~r1_waybel_7(sK0,k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),X0) | ~m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_struct_0(sK0)) )),
% 1.56/0.58    inference(forward_demodulation,[],[f220,f137])).
% 1.56/0.58  fof(f220,plain,(
% 1.56/0.58    ( ! [X0] : (r3_waybel_9(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1),X0) | v1_xboole_0(k2_struct_0(sK0)) | ~r1_waybel_7(sK0,k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),X0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_struct_0(sK0)) )),
% 1.56/0.58    inference(subsumption_resolution,[],[f219,f74])).
% 1.56/0.58  fof(f219,plain,(
% 1.56/0.58    ( ! [X0] : (r3_waybel_9(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1),X0) | v1_xboole_0(k2_struct_0(sK0)) | ~r1_waybel_7(sK0,k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),X0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | v1_xboole_0(sK1) | ~m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_struct_0(sK0)) )),
% 1.56/0.58    inference(subsumption_resolution,[],[f218,f121])).
% 1.56/0.58  fof(f218,plain,(
% 1.56/0.58    ( ! [X0] : (r3_waybel_9(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1),X0) | v1_xboole_0(k2_struct_0(sK0)) | ~r1_waybel_7(sK0,k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),X0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~v2_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) | v1_xboole_0(sK1) | ~m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_struct_0(sK0)) )),
% 1.56/0.58    inference(subsumption_resolution,[],[f217,f120])).
% 1.56/0.58  fof(f217,plain,(
% 1.56/0.58    ( ! [X0] : (r3_waybel_9(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1),X0) | v1_xboole_0(k2_struct_0(sK0)) | ~r1_waybel_7(sK0,k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),X0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~v13_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) | ~v2_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) | v1_xboole_0(sK1) | ~m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_struct_0(sK0)) )),
% 1.56/0.58    inference(subsumption_resolution,[],[f216,f119])).
% 1.56/0.58  fof(f216,plain,(
% 1.56/0.58    ( ! [X0] : (r3_waybel_9(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1),X0) | v1_xboole_0(k2_struct_0(sK0)) | ~r1_waybel_7(sK0,k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),X0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))))) | ~v13_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) | ~v2_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) | v1_xboole_0(sK1) | ~m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_struct_0(sK0)) )),
% 1.56/0.58    inference(subsumption_resolution,[],[f215,f71])).
% 1.56/0.58  fof(f215,plain,(
% 1.56/0.58    ( ! [X0] : (r3_waybel_9(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1),X0) | v1_xboole_0(k2_struct_0(sK0)) | ~r1_waybel_7(sK0,k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),X0) | v2_struct_0(sK0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))))) | ~v13_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) | ~v2_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) | v1_xboole_0(sK1) | ~m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_struct_0(sK0)) )),
% 1.56/0.58    inference(subsumption_resolution,[],[f214,f72])).
% 1.56/0.58  fof(f72,plain,(
% 1.56/0.58    v2_pre_topc(sK0)),
% 1.56/0.58    inference(cnf_transformation,[],[f54])).
% 1.56/0.58  fof(f214,plain,(
% 1.56/0.58    ( ! [X0] : (r3_waybel_9(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1),X0) | v1_xboole_0(k2_struct_0(sK0)) | ~r1_waybel_7(sK0,k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),X0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))))) | ~v13_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) | ~v2_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) | v1_xboole_0(sK1) | ~m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_struct_0(sK0)) )),
% 1.56/0.58    inference(subsumption_resolution,[],[f213,f73])).
% 1.56/0.58  fof(f213,plain,(
% 1.56/0.58    ( ! [X0] : (r3_waybel_9(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1),X0) | v1_xboole_0(k2_struct_0(sK0)) | ~r1_waybel_7(sK0,k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),X0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))))) | ~v13_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) | ~v2_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) | v1_xboole_0(sK1) | ~m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_struct_0(sK0)) )),
% 1.56/0.58    inference(duplicate_literal_removal,[],[f212])).
% 1.56/0.58  fof(f212,plain,(
% 1.56/0.58    ( ! [X0] : (r3_waybel_9(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1),X0) | v1_xboole_0(k2_struct_0(sK0)) | ~r1_waybel_7(sK0,k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),X0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))))) | ~v13_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) | ~v2_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) | v1_xboole_0(sK1) | ~m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) | v1_xboole_0(k2_struct_0(sK0)) | ~l1_struct_0(sK0) | v2_struct_0(sK0)) )),
% 1.56/0.58    inference(resolution,[],[f211,f128])).
% 1.56/0.58  fof(f128,plain,(
% 1.56/0.58    ( ! [X2,X0,X1] : (l1_waybel_0(k3_yellow19(X0,X1,X2),X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1))))) | ~v13_waybel_0(X2,k3_lattice3(k1_lattice3(X1))) | ~v2_waybel_0(X2,k3_lattice3(k1_lattice3(X1))) | v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 1.56/0.58    inference(definition_unfolding,[],[f115,f84,f84,f84])).
% 1.56/0.58  fof(f115,plain,(
% 1.56/0.58    ( ! [X2,X0,X1] : (l1_waybel_0(k3_yellow19(X0,X1,X2),X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1)))) | ~v13_waybel_0(X2,k3_yellow_1(X1)) | ~v2_waybel_0(X2,k3_yellow_1(X1)) | v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 1.56/0.58    inference(cnf_transformation,[],[f46])).
% 1.56/0.58  fof(f46,plain,(
% 1.56/0.58    ! [X0,X1,X2] : ((l1_waybel_0(k3_yellow19(X0,X1,X2),X0) & v6_waybel_0(k3_yellow19(X0,X1,X2),X0) & ~v2_struct_0(k3_yellow19(X0,X1,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1)))) | ~v13_waybel_0(X2,k3_yellow_1(X1)) | ~v2_waybel_0(X2,k3_yellow_1(X1)) | v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 1.56/0.58    inference(flattening,[],[f45])).
% 1.56/0.58  fof(f45,plain,(
% 1.56/0.58    ! [X0,X1,X2] : ((l1_waybel_0(k3_yellow19(X0,X1,X2),X0) & v6_waybel_0(k3_yellow19(X0,X1,X2),X0) & ~v2_struct_0(k3_yellow19(X0,X1,X2))) | (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1)))) | ~v13_waybel_0(X2,k3_yellow_1(X1)) | ~v2_waybel_0(X2,k3_yellow_1(X1)) | v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)))),
% 1.56/0.58    inference(ennf_transformation,[],[f15])).
% 1.56/0.58  fof(f15,axiom,(
% 1.56/0.58    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1)))) & v13_waybel_0(X2,k3_yellow_1(X1)) & v2_waybel_0(X2,k3_yellow_1(X1)) & ~v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1) & l1_struct_0(X0) & ~v2_struct_0(X0)) => (l1_waybel_0(k3_yellow19(X0,X1,X2),X0) & v6_waybel_0(k3_yellow19(X0,X1,X2),X0) & ~v2_struct_0(k3_yellow19(X0,X1,X2))))),
% 1.56/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_yellow19)).
% 1.56/0.58  fof(f211,plain,(
% 1.56/0.58    ( ! [X0,X1] : (~l1_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1),X0) | r3_waybel_9(X0,k3_yellow19(sK0,k2_struct_0(sK0),sK1),X1) | v1_xboole_0(k2_struct_0(sK0)) | ~r1_waybel_7(X0,k2_yellow19(X0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0) | ~m1_subset_1(X1,u1_struct_0(X0))) )),
% 1.56/0.58    inference(subsumption_resolution,[],[f210,f73])).
% 1.56/0.58  fof(f210,plain,(
% 1.56/0.58    ( ! [X0,X1] : (~l1_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1),X0) | r3_waybel_9(X0,k3_yellow19(sK0,k2_struct_0(sK0),sK1),X1) | v1_xboole_0(k2_struct_0(sK0)) | ~r1_waybel_7(X0,k2_yellow19(X0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(sK0)) )),
% 1.56/0.58    inference(resolution,[],[f209,f85])).
% 1.56/0.58  % (2328)Refutation not found, incomplete strategy% (2328)------------------------------
% 1.56/0.58  % (2328)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.56/0.58  fof(f209,plain,(
% 1.56/0.58    ( ! [X0,X1] : (~l1_struct_0(sK0) | ~l1_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1),X1) | r3_waybel_9(X1,k3_yellow19(sK0,k2_struct_0(sK0),sK1),X0) | v1_xboole_0(k2_struct_0(sK0)) | ~r1_waybel_7(X1,k2_yellow19(X1,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),X0) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~m1_subset_1(X0,u1_struct_0(X1))) )),
% 1.56/0.58    inference(subsumption_resolution,[],[f208,f134])).
% 1.56/0.58  fof(f208,plain,(
% 1.56/0.58    ( ! [X0,X1] : (~m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0))) | ~m1_subset_1(X0,u1_struct_0(X1)) | ~l1_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1),X1) | r3_waybel_9(X1,k3_yellow19(sK0,k2_struct_0(sK0),sK1),X0) | v1_xboole_0(k2_struct_0(sK0)) | ~r1_waybel_7(X1,k2_yellow19(X1,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),X0) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_struct_0(sK0)) )),
% 1.56/0.58    inference(forward_demodulation,[],[f207,f137])).
% 1.56/0.58  fof(f207,plain,(
% 1.56/0.58    ( ! [X0,X1] : (~m1_subset_1(X0,u1_struct_0(X1)) | ~l1_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1),X1) | r3_waybel_9(X1,k3_yellow19(sK0,k2_struct_0(sK0),sK1),X0) | v1_xboole_0(k2_struct_0(sK0)) | ~r1_waybel_7(X1,k2_yellow19(X1,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),X0) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_struct_0(sK0) | ~m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))) )),
% 1.56/0.58    inference(subsumption_resolution,[],[f206,f71])).
% 1.56/0.58  fof(f206,plain,(
% 1.56/0.58    ( ! [X0,X1] : (~m1_subset_1(X0,u1_struct_0(X1)) | ~l1_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1),X1) | r3_waybel_9(X1,k3_yellow19(sK0,k2_struct_0(sK0),sK1),X0) | v1_xboole_0(k2_struct_0(sK0)) | ~r1_waybel_7(X1,k2_yellow19(X1,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),X0) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_struct_0(sK0) | ~m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) | v2_struct_0(sK0)) )),
% 1.56/0.58    inference(subsumption_resolution,[],[f205,f74])).
% 1.56/0.58  fof(f205,plain,(
% 1.56/0.58    ( ! [X0,X1] : (~m1_subset_1(X0,u1_struct_0(X1)) | ~l1_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1),X1) | r3_waybel_9(X1,k3_yellow19(sK0,k2_struct_0(sK0),sK1),X0) | v1_xboole_0(k2_struct_0(sK0)) | ~r1_waybel_7(X1,k2_yellow19(X1,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),X0) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_struct_0(sK0) | v1_xboole_0(sK1) | ~m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) | v2_struct_0(sK0)) )),
% 1.56/0.58    inference(subsumption_resolution,[],[f204,f121])).
% 1.56/0.58  fof(f204,plain,(
% 1.56/0.58    ( ! [X0,X1] : (~m1_subset_1(X0,u1_struct_0(X1)) | ~l1_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1),X1) | r3_waybel_9(X1,k3_yellow19(sK0,k2_struct_0(sK0),sK1),X0) | v1_xboole_0(k2_struct_0(sK0)) | ~r1_waybel_7(X1,k2_yellow19(X1,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),X0) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_struct_0(sK0) | ~v2_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) | v1_xboole_0(sK1) | ~m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) | v2_struct_0(sK0)) )),
% 1.56/0.58    inference(subsumption_resolution,[],[f203,f120])).
% 1.56/0.58  fof(f203,plain,(
% 1.56/0.58    ( ! [X0,X1] : (~m1_subset_1(X0,u1_struct_0(X1)) | ~l1_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1),X1) | r3_waybel_9(X1,k3_yellow19(sK0,k2_struct_0(sK0),sK1),X0) | v1_xboole_0(k2_struct_0(sK0)) | ~r1_waybel_7(X1,k2_yellow19(X1,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),X0) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_struct_0(sK0) | ~v13_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) | ~v2_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) | v1_xboole_0(sK1) | ~m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) | v2_struct_0(sK0)) )),
% 1.56/0.58    inference(subsumption_resolution,[],[f202,f119])).
% 1.56/0.58  fof(f202,plain,(
% 1.56/0.58    ( ! [X0,X1] : (~m1_subset_1(X0,u1_struct_0(X1)) | ~l1_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1),X1) | r3_waybel_9(X1,k3_yellow19(sK0,k2_struct_0(sK0),sK1),X0) | v1_xboole_0(k2_struct_0(sK0)) | ~r1_waybel_7(X1,k2_yellow19(X1,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),X0) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_struct_0(sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))))) | ~v13_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) | ~v2_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) | v1_xboole_0(sK1) | ~m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) | v2_struct_0(sK0)) )),
% 1.56/0.58    inference(duplicate_literal_removal,[],[f200])).
% 1.56/0.58  % (2315)Termination reason: Refutation not found, incomplete strategy
% 1.56/0.58  
% 1.56/0.58  % (2315)Memory used [KB]: 10746
% 1.56/0.58  % (2315)Time elapsed: 0.154 s
% 1.56/0.58  % (2315)------------------------------
% 1.56/0.58  % (2315)------------------------------
% 1.56/0.58  fof(f200,plain,(
% 1.56/0.58    ( ! [X0,X1] : (~m1_subset_1(X0,u1_struct_0(X1)) | ~l1_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1),X1) | r3_waybel_9(X1,k3_yellow19(sK0,k2_struct_0(sK0),sK1),X0) | v1_xboole_0(k2_struct_0(sK0)) | ~r1_waybel_7(X1,k2_yellow19(X1,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),X0) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_struct_0(sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))))) | ~v13_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) | ~v2_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) | v1_xboole_0(sK1) | ~m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) | v1_xboole_0(k2_struct_0(sK0)) | ~l1_struct_0(sK0) | v2_struct_0(sK0)) )),
% 1.56/0.58    inference(resolution,[],[f199,f127])).
% 1.56/0.58  fof(f127,plain,(
% 1.56/0.58    ( ! [X2,X0,X1] : (~v2_struct_0(k3_yellow19(X0,X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1))))) | ~v13_waybel_0(X2,k3_lattice3(k1_lattice3(X1))) | ~v2_waybel_0(X2,k3_lattice3(k1_lattice3(X1))) | v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 1.56/0.58    inference(definition_unfolding,[],[f109,f84,f84,f84])).
% 1.56/0.58  fof(f109,plain,(
% 1.56/0.58    ( ! [X2,X0,X1] : (~v2_struct_0(k3_yellow19(X0,X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1)))) | ~v13_waybel_0(X2,k3_yellow_1(X1)) | ~v2_waybel_0(X2,k3_yellow_1(X1)) | v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 1.56/0.58    inference(cnf_transformation,[],[f44])).
% 1.56/0.58  fof(f44,plain,(
% 1.56/0.58    ! [X0,X1,X2] : ((v6_waybel_0(k3_yellow19(X0,X1,X2),X0) & v4_orders_2(k3_yellow19(X0,X1,X2)) & v3_orders_2(k3_yellow19(X0,X1,X2)) & ~v2_struct_0(k3_yellow19(X0,X1,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1)))) | ~v13_waybel_0(X2,k3_yellow_1(X1)) | ~v2_waybel_0(X2,k3_yellow_1(X1)) | v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 1.56/0.58    inference(flattening,[],[f43])).
% 1.56/0.58  fof(f43,plain,(
% 1.56/0.58    ! [X0,X1,X2] : ((v6_waybel_0(k3_yellow19(X0,X1,X2),X0) & v4_orders_2(k3_yellow19(X0,X1,X2)) & v3_orders_2(k3_yellow19(X0,X1,X2)) & ~v2_struct_0(k3_yellow19(X0,X1,X2))) | (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1)))) | ~v13_waybel_0(X2,k3_yellow_1(X1)) | ~v2_waybel_0(X2,k3_yellow_1(X1)) | v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)))),
% 1.56/0.58    inference(ennf_transformation,[],[f16])).
% 1.56/0.58  fof(f16,axiom,(
% 1.56/0.58    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1)))) & v13_waybel_0(X2,k3_yellow_1(X1)) & v2_waybel_0(X2,k3_yellow_1(X1)) & ~v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1) & l1_struct_0(X0) & ~v2_struct_0(X0)) => (v6_waybel_0(k3_yellow19(X0,X1,X2),X0) & v4_orders_2(k3_yellow19(X0,X1,X2)) & v3_orders_2(k3_yellow19(X0,X1,X2)) & ~v2_struct_0(k3_yellow19(X0,X1,X2))))),
% 1.56/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc4_yellow19)).
% 1.56/0.58  fof(f199,plain,(
% 1.56/0.58    ( ! [X0,X1] : (v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1),X0) | r3_waybel_9(X0,k3_yellow19(sK0,k2_struct_0(sK0),sK1),X1) | v1_xboole_0(k2_struct_0(sK0)) | ~r1_waybel_7(X0,k2_yellow19(X0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0) | ~l1_struct_0(sK0)) )),
% 1.56/0.58    inference(subsumption_resolution,[],[f198,f134])).
% 1.56/0.58  fof(f198,plain,(
% 1.56/0.58    ( ! [X0,X1] : (~m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0))) | ~r1_waybel_7(X0,k2_yellow19(X0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),X1) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1),X0) | r3_waybel_9(X0,k3_yellow19(sK0,k2_struct_0(sK0),sK1),X1) | v1_xboole_0(k2_struct_0(sK0)) | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0) | ~l1_struct_0(sK0)) )),
% 1.56/0.58    inference(forward_demodulation,[],[f197,f137])).
% 1.56/0.58  fof(f197,plain,(
% 1.56/0.58    ( ! [X0,X1] : (~r1_waybel_7(X0,k2_yellow19(X0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),X1) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1),X0) | r3_waybel_9(X0,k3_yellow19(sK0,k2_struct_0(sK0),sK1),X1) | v1_xboole_0(k2_struct_0(sK0)) | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0) | ~m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_struct_0(sK0)) )),
% 1.56/0.58    inference(subsumption_resolution,[],[f196,f71])).
% 1.56/0.58  fof(f196,plain,(
% 1.56/0.58    ( ! [X0,X1] : (~r1_waybel_7(X0,k2_yellow19(X0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),X1) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1),X0) | r3_waybel_9(X0,k3_yellow19(sK0,k2_struct_0(sK0),sK1),X1) | v1_xboole_0(k2_struct_0(sK0)) | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0) | ~m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_struct_0(sK0) | v2_struct_0(sK0)) )),
% 1.56/0.58    inference(subsumption_resolution,[],[f195,f74])).
% 1.56/0.58  fof(f195,plain,(
% 1.56/0.58    ( ! [X0,X1] : (~r1_waybel_7(X0,k2_yellow19(X0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),X1) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1),X0) | r3_waybel_9(X0,k3_yellow19(sK0,k2_struct_0(sK0),sK1),X1) | v1_xboole_0(k2_struct_0(sK0)) | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0) | v1_xboole_0(sK1) | ~m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_struct_0(sK0) | v2_struct_0(sK0)) )),
% 1.56/0.58    inference(subsumption_resolution,[],[f194,f121])).
% 1.56/0.58  fof(f194,plain,(
% 1.56/0.58    ( ! [X0,X1] : (~r1_waybel_7(X0,k2_yellow19(X0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),X1) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1),X0) | r3_waybel_9(X0,k3_yellow19(sK0,k2_struct_0(sK0),sK1),X1) | v1_xboole_0(k2_struct_0(sK0)) | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0) | ~v2_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) | v1_xboole_0(sK1) | ~m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_struct_0(sK0) | v2_struct_0(sK0)) )),
% 1.56/0.58    inference(subsumption_resolution,[],[f193,f120])).
% 1.56/0.58  fof(f193,plain,(
% 1.56/0.58    ( ! [X0,X1] : (~r1_waybel_7(X0,k2_yellow19(X0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),X1) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1),X0) | r3_waybel_9(X0,k3_yellow19(sK0,k2_struct_0(sK0),sK1),X1) | v1_xboole_0(k2_struct_0(sK0)) | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0) | ~v13_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) | ~v2_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) | v1_xboole_0(sK1) | ~m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_struct_0(sK0) | v2_struct_0(sK0)) )),
% 1.56/0.58    inference(subsumption_resolution,[],[f192,f119])).
% 1.56/0.58  fof(f192,plain,(
% 1.56/0.58    ( ! [X0,X1] : (~r1_waybel_7(X0,k2_yellow19(X0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),X1) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1),X0) | r3_waybel_9(X0,k3_yellow19(sK0,k2_struct_0(sK0),sK1),X1) | v1_xboole_0(k2_struct_0(sK0)) | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))))) | ~v13_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) | ~v2_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) | v1_xboole_0(sK1) | ~m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_struct_0(sK0) | v2_struct_0(sK0)) )),
% 1.56/0.58    inference(duplicate_literal_removal,[],[f191])).
% 1.56/0.58  fof(f191,plain,(
% 1.56/0.58    ( ! [X0,X1] : (~r1_waybel_7(X0,k2_yellow19(X0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),X1) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1),X0) | r3_waybel_9(X0,k3_yellow19(sK0,k2_struct_0(sK0),sK1),X1) | v1_xboole_0(k2_struct_0(sK0)) | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))))) | ~v13_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) | ~v2_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) | v1_xboole_0(sK1) | ~m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) | v1_xboole_0(k2_struct_0(sK0)) | ~l1_struct_0(sK0) | v2_struct_0(sK0)) )),
% 1.56/0.58    inference(resolution,[],[f188,f125])).
% 1.56/0.58  fof(f125,plain,(
% 1.56/0.58    ( ! [X2,X0,X1] : (v4_orders_2(k3_yellow19(X0,X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1))))) | ~v13_waybel_0(X2,k3_lattice3(k1_lattice3(X1))) | ~v2_waybel_0(X2,k3_lattice3(k1_lattice3(X1))) | v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 1.56/0.58    inference(definition_unfolding,[],[f111,f84,f84,f84])).
% 1.56/0.58  fof(f111,plain,(
% 1.56/0.58    ( ! [X2,X0,X1] : (v4_orders_2(k3_yellow19(X0,X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1)))) | ~v13_waybel_0(X2,k3_yellow_1(X1)) | ~v2_waybel_0(X2,k3_yellow_1(X1)) | v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 1.56/0.58    inference(cnf_transformation,[],[f44])).
% 1.56/0.58  fof(f188,plain,(
% 1.56/0.58    ( ! [X0,X1] : (~v4_orders_2(k3_yellow19(sK0,k2_struct_0(sK0),sK1)) | ~r1_waybel_7(X0,k2_yellow19(X0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),X1) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1),X0) | r3_waybel_9(X0,k3_yellow19(sK0,k2_struct_0(sK0),sK1),X1) | v1_xboole_0(k2_struct_0(sK0)) | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.56/0.58    inference(resolution,[],[f187,f96])).
% 1.56/0.58  fof(f96,plain,(
% 1.56/0.58    ( ! [X2,X0,X1] : (~v7_waybel_0(X1) | ~r1_waybel_7(X0,k2_yellow19(X0,X1),X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_waybel_0(X1,X0) | r3_waybel_9(X0,X1,X2) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.56/0.58    inference(cnf_transformation,[],[f61])).
% 1.56/0.58  fof(f61,plain,(
% 1.56/0.58    ! [X0] : (! [X1] : (! [X2] : (((r3_waybel_9(X0,X1,X2) | ~r1_waybel_7(X0,k2_yellow19(X0,X1),X2)) & (r1_waybel_7(X0,k2_yellow19(X0,X1),X2) | ~r3_waybel_9(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.56/0.58    inference(nnf_transformation,[],[f34])).
% 1.56/0.58  fof(f34,plain,(
% 1.56/0.58    ! [X0] : (! [X1] : (! [X2] : ((r3_waybel_9(X0,X1,X2) <=> r1_waybel_7(X0,k2_yellow19(X0,X1),X2)) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.56/0.58    inference(flattening,[],[f33])).
% 1.56/0.58  fof(f33,plain,(
% 1.56/0.58    ! [X0] : (! [X1] : (! [X2] : ((r3_waybel_9(X0,X1,X2) <=> r1_waybel_7(X0,k2_yellow19(X0,X1),X2)) | ~m1_subset_1(X2,u1_struct_0(X0))) | (~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 1.56/0.58    inference(ennf_transformation,[],[f18])).
% 1.56/0.58  fof(f18,axiom,(
% 1.56/0.58    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r3_waybel_9(X0,X1,X2) <=> r1_waybel_7(X0,k2_yellow19(X0,X1),X2)))))),
% 1.56/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_yellow19)).
% 1.56/0.58  fof(f187,plain,(
% 1.56/0.58    v7_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1)) | v1_xboole_0(k2_struct_0(sK0))),
% 1.56/0.58    inference(subsumption_resolution,[],[f186,f119])).
% 1.56/0.58  fof(f186,plain,(
% 1.56/0.58    v1_xboole_0(k2_struct_0(sK0)) | v7_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1)) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0))))))),
% 1.56/0.58    inference(subsumption_resolution,[],[f185,f74])).
% 1.56/0.58  fof(f185,plain,(
% 1.56/0.58    v1_xboole_0(sK1) | v1_xboole_0(k2_struct_0(sK0)) | v7_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1)) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0))))))),
% 1.56/0.58    inference(subsumption_resolution,[],[f184,f134])).
% 1.56/0.58  fof(f184,plain,(
% 1.56/0.58    ~m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0))) | v1_xboole_0(sK1) | v1_xboole_0(k2_struct_0(sK0)) | v7_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1)) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0))))))),
% 1.56/0.58    inference(subsumption_resolution,[],[f183,f121])).
% 1.56/0.58  fof(f183,plain,(
% 1.56/0.58    ~v2_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) | ~m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0))) | v1_xboole_0(sK1) | v1_xboole_0(k2_struct_0(sK0)) | v7_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1)) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0))))))),
% 1.56/0.58    inference(subsumption_resolution,[],[f182,f120])).
% 1.56/0.58  fof(f182,plain,(
% 1.56/0.58    ~v13_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) | ~v2_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) | ~m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0))) | v1_xboole_0(sK1) | v1_xboole_0(k2_struct_0(sK0)) | v7_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1)) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0))))))),
% 1.56/0.58    inference(resolution,[],[f181,f122])).
% 1.56/0.58  fof(f181,plain,(
% 1.56/0.58    ( ! [X0,X1] : (~v1_subset_1(X0,u1_struct_0(k3_lattice3(k1_lattice3(X1)))) | ~v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1))) | ~v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1))) | ~m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK0))) | v1_xboole_0(X0) | v1_xboole_0(X1) | v7_waybel_0(k3_yellow19(sK0,X1,X0)) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))) )),
% 1.56/0.58    inference(forward_demodulation,[],[f180,f137])).
% 1.56/0.58  fof(f180,plain,(
% 1.56/0.58    ( ! [X0,X1] : (~v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1))) | ~v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1))) | ~v1_subset_1(X0,u1_struct_0(k3_lattice3(k1_lattice3(X1)))) | v1_xboole_0(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | v1_xboole_0(X1) | v7_waybel_0(k3_yellow19(sK0,X1,X0)) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))) )),
% 1.56/0.58    inference(subsumption_resolution,[],[f179,f71])).
% 1.56/0.58  fof(f179,plain,(
% 1.56/0.58    ( ! [X0,X1] : (~v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1))) | ~v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1))) | ~v1_subset_1(X0,u1_struct_0(k3_lattice3(k1_lattice3(X1)))) | v1_xboole_0(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | v1_xboole_0(X1) | v7_waybel_0(k3_yellow19(sK0,X1,X0)) | v2_struct_0(sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))) )),
% 1.56/0.58    inference(resolution,[],[f178,f73])).
% 1.56/0.58  fof(f178,plain,(
% 1.56/0.58    ( ! [X2,X0,X1] : (~l1_pre_topc(X2) | ~v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1))) | ~v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1))) | ~v1_subset_1(X0,u1_struct_0(k3_lattice3(k1_lattice3(X1)))) | v1_xboole_0(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2))) | v1_xboole_0(X1) | v7_waybel_0(k3_yellow19(X2,X1,X0)) | v2_struct_0(X2) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))) )),
% 1.56/0.58    inference(resolution,[],[f131,f85])).
% 1.56/0.58  fof(f131,plain,(
% 1.56/0.58    ( ! [X2,X0,X1] : (~l1_struct_0(X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1))))) | ~v13_waybel_0(X2,k3_lattice3(k1_lattice3(X1))) | ~v2_waybel_0(X2,k3_lattice3(k1_lattice3(X1))) | ~v1_subset_1(X2,u1_struct_0(k3_lattice3(k1_lattice3(X1)))) | v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | v7_waybel_0(k3_yellow19(X0,X1,X2)) | v2_struct_0(X0)) )),
% 1.56/0.58    inference(definition_unfolding,[],[f118,f84,f84,f84,f84])).
% 1.56/0.58  fof(f118,plain,(
% 1.56/0.58    ( ! [X2,X0,X1] : (v7_waybel_0(k3_yellow19(X0,X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1)))) | ~v13_waybel_0(X2,k3_yellow_1(X1)) | ~v2_waybel_0(X2,k3_yellow_1(X1)) | ~v1_subset_1(X2,u1_struct_0(k3_yellow_1(X1))) | v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 1.56/0.58    inference(cnf_transformation,[],[f48])).
% 1.56/0.58  fof(f48,plain,(
% 1.56/0.58    ! [X0,X1,X2] : ((v7_waybel_0(k3_yellow19(X0,X1,X2)) & v6_waybel_0(k3_yellow19(X0,X1,X2),X0) & ~v2_struct_0(k3_yellow19(X0,X1,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1)))) | ~v13_waybel_0(X2,k3_yellow_1(X1)) | ~v2_waybel_0(X2,k3_yellow_1(X1)) | ~v1_subset_1(X2,u1_struct_0(k3_yellow_1(X1))) | v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 1.56/0.58    inference(flattening,[],[f47])).
% 1.56/0.58  fof(f47,plain,(
% 1.56/0.58    ! [X0,X1,X2] : ((v7_waybel_0(k3_yellow19(X0,X1,X2)) & v6_waybel_0(k3_yellow19(X0,X1,X2),X0) & ~v2_struct_0(k3_yellow19(X0,X1,X2))) | (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1)))) | ~v13_waybel_0(X2,k3_yellow_1(X1)) | ~v2_waybel_0(X2,k3_yellow_1(X1)) | ~v1_subset_1(X2,u1_struct_0(k3_yellow_1(X1))) | v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)))),
% 1.56/0.58    inference(ennf_transformation,[],[f17])).
% 1.56/0.58  fof(f17,axiom,(
% 1.56/0.58    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1)))) & v13_waybel_0(X2,k3_yellow_1(X1)) & v2_waybel_0(X2,k3_yellow_1(X1)) & v1_subset_1(X2,u1_struct_0(k3_yellow_1(X1))) & ~v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1) & l1_struct_0(X0) & ~v2_struct_0(X0)) => (v7_waybel_0(k3_yellow19(X0,X1,X2)) & v6_waybel_0(k3_yellow19(X0,X1,X2),X0) & ~v2_struct_0(k3_yellow19(X0,X1,X2))))),
% 1.56/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc5_yellow19)).
% 1.56/0.58  fof(f284,plain,(
% 1.56/0.58    r1_waybel_7(sK0,sK1,sK2) | v1_xboole_0(k2_struct_0(sK0)) | ~l1_struct_0(sK0)),
% 1.56/0.58    inference(subsumption_resolution,[],[f283,f71])).
% 1.56/0.58  fof(f283,plain,(
% 1.56/0.58    r1_waybel_7(sK0,sK1,sK2) | v1_xboole_0(k2_struct_0(sK0)) | ~l1_struct_0(sK0) | v2_struct_0(sK0)),
% 1.56/0.58    inference(subsumption_resolution,[],[f282,f74])).
% 1.56/0.58  fof(f282,plain,(
% 1.56/0.58    r1_waybel_7(sK0,sK1,sK2) | v1_xboole_0(k2_struct_0(sK0)) | v1_xboole_0(sK1) | ~l1_struct_0(sK0) | v2_struct_0(sK0)),
% 1.56/0.58    inference(subsumption_resolution,[],[f281,f122])).
% 1.56/0.58  fof(f281,plain,(
% 1.56/0.58    r1_waybel_7(sK0,sK1,sK2) | v1_xboole_0(k2_struct_0(sK0)) | ~v1_subset_1(sK1,u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0))))) | v1_xboole_0(sK1) | ~l1_struct_0(sK0) | v2_struct_0(sK0)),
% 1.56/0.58    inference(subsumption_resolution,[],[f280,f121])).
% 1.56/0.58  fof(f280,plain,(
% 1.56/0.58    r1_waybel_7(sK0,sK1,sK2) | v1_xboole_0(k2_struct_0(sK0)) | ~v2_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) | ~v1_subset_1(sK1,u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0))))) | v1_xboole_0(sK1) | ~l1_struct_0(sK0) | v2_struct_0(sK0)),
% 1.56/0.58    inference(subsumption_resolution,[],[f279,f120])).
% 1.56/0.58  fof(f279,plain,(
% 1.56/0.58    r1_waybel_7(sK0,sK1,sK2) | v1_xboole_0(k2_struct_0(sK0)) | ~v13_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) | ~v2_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) | ~v1_subset_1(sK1,u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0))))) | v1_xboole_0(sK1) | ~l1_struct_0(sK0) | v2_struct_0(sK0)),
% 1.56/0.58    inference(subsumption_resolution,[],[f277,f119])).
% 1.56/0.58  fof(f277,plain,(
% 1.56/0.58    r1_waybel_7(sK0,sK1,sK2) | v1_xboole_0(k2_struct_0(sK0)) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))))) | ~v13_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) | ~v2_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) | ~v1_subset_1(sK1,u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0))))) | v1_xboole_0(sK1) | ~l1_struct_0(sK0) | v2_struct_0(sK0)),
% 1.56/0.58    inference(superposition,[],[f275,f123])).
% 1.56/0.58  fof(f275,plain,(
% 1.56/0.58    r1_waybel_7(sK0,k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),sK2) | v1_xboole_0(k2_struct_0(sK0))),
% 1.56/0.58    inference(subsumption_resolution,[],[f274,f73])).
% 1.56/0.58  fof(f274,plain,(
% 1.56/0.58    r1_waybel_7(sK0,k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),sK2) | v1_xboole_0(k2_struct_0(sK0)) | ~l1_pre_topc(sK0)),
% 1.56/0.58    inference(resolution,[],[f273,f85])).
% 1.56/0.58  fof(f273,plain,(
% 1.56/0.58    ~l1_struct_0(sK0) | r1_waybel_7(sK0,k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),sK2) | v1_xboole_0(k2_struct_0(sK0))),
% 1.56/0.58    inference(subsumption_resolution,[],[f272,f134])).
% 1.56/0.58  fof(f272,plain,(
% 1.56/0.58    ~m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0))) | v1_xboole_0(k2_struct_0(sK0)) | r1_waybel_7(sK0,k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),sK2) | ~l1_struct_0(sK0)),
% 1.56/0.58    inference(forward_demodulation,[],[f271,f137])).
% 1.56/0.58  fof(f271,plain,(
% 1.56/0.58    v1_xboole_0(k2_struct_0(sK0)) | r1_waybel_7(sK0,k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),sK2) | ~l1_struct_0(sK0) | ~m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.56/0.58    inference(subsumption_resolution,[],[f270,f71])).
% 1.56/0.58  fof(f270,plain,(
% 1.56/0.58    v1_xboole_0(k2_struct_0(sK0)) | r1_waybel_7(sK0,k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),sK2) | ~l1_struct_0(sK0) | ~m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) | v2_struct_0(sK0)),
% 1.56/0.58    inference(subsumption_resolution,[],[f269,f74])).
% 1.56/0.58  fof(f269,plain,(
% 1.56/0.58    v1_xboole_0(k2_struct_0(sK0)) | r1_waybel_7(sK0,k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),sK2) | ~l1_struct_0(sK0) | v1_xboole_0(sK1) | ~m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) | v2_struct_0(sK0)),
% 1.56/0.58    inference(subsumption_resolution,[],[f268,f121])).
% 1.56/0.58  fof(f268,plain,(
% 1.56/0.58    v1_xboole_0(k2_struct_0(sK0)) | r1_waybel_7(sK0,k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),sK2) | ~l1_struct_0(sK0) | ~v2_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) | v1_xboole_0(sK1) | ~m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) | v2_struct_0(sK0)),
% 1.56/0.58    inference(subsumption_resolution,[],[f267,f120])).
% 1.56/0.58  fof(f267,plain,(
% 1.56/0.58    v1_xboole_0(k2_struct_0(sK0)) | r1_waybel_7(sK0,k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),sK2) | ~l1_struct_0(sK0) | ~v13_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) | ~v2_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) | v1_xboole_0(sK1) | ~m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) | v2_struct_0(sK0)),
% 1.56/0.58    inference(subsumption_resolution,[],[f266,f119])).
% 1.56/0.58  fof(f266,plain,(
% 1.56/0.58    v1_xboole_0(k2_struct_0(sK0)) | r1_waybel_7(sK0,k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),sK2) | ~l1_struct_0(sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))))) | ~v13_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) | ~v2_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) | v1_xboole_0(sK1) | ~m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) | v2_struct_0(sK0)),
% 1.56/0.58    inference(duplicate_literal_removal,[],[f265])).
% 1.56/0.58  fof(f265,plain,(
% 1.56/0.58    v1_xboole_0(k2_struct_0(sK0)) | r1_waybel_7(sK0,k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),sK2) | ~l1_struct_0(sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))))) | ~v13_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) | ~v2_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) | v1_xboole_0(sK1) | ~m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) | v1_xboole_0(k2_struct_0(sK0)) | ~l1_struct_0(sK0) | v2_struct_0(sK0)),
% 1.56/0.58    inference(resolution,[],[f264,f127])).
% 1.56/0.58  fof(f264,plain,(
% 1.56/0.58    v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1)) | v1_xboole_0(k2_struct_0(sK0)) | r1_waybel_7(sK0,k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),sK2) | ~l1_struct_0(sK0)),
% 1.56/0.58    inference(subsumption_resolution,[],[f263,f134])).
% 1.56/0.58  fof(f263,plain,(
% 1.56/0.58    ~m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0))) | r1_waybel_7(sK0,k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),sK2) | v1_xboole_0(k2_struct_0(sK0)) | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1)) | ~l1_struct_0(sK0)),
% 1.56/0.58    inference(forward_demodulation,[],[f262,f137])).
% 1.56/0.58  fof(f262,plain,(
% 1.56/0.58    r1_waybel_7(sK0,k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),sK2) | v1_xboole_0(k2_struct_0(sK0)) | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1)) | ~l1_struct_0(sK0) | ~m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.56/0.58    inference(subsumption_resolution,[],[f261,f71])).
% 1.56/0.58  fof(f261,plain,(
% 1.56/0.58    r1_waybel_7(sK0,k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),sK2) | v1_xboole_0(k2_struct_0(sK0)) | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1)) | ~l1_struct_0(sK0) | ~m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) | v2_struct_0(sK0)),
% 1.56/0.58    inference(subsumption_resolution,[],[f260,f74])).
% 1.56/0.58  fof(f260,plain,(
% 1.56/0.58    r1_waybel_7(sK0,k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),sK2) | v1_xboole_0(k2_struct_0(sK0)) | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1)) | ~l1_struct_0(sK0) | v1_xboole_0(sK1) | ~m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) | v2_struct_0(sK0)),
% 1.56/0.58    inference(subsumption_resolution,[],[f259,f121])).
% 1.56/0.58  fof(f259,plain,(
% 1.56/0.58    r1_waybel_7(sK0,k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),sK2) | v1_xboole_0(k2_struct_0(sK0)) | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1)) | ~l1_struct_0(sK0) | ~v2_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) | v1_xboole_0(sK1) | ~m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) | v2_struct_0(sK0)),
% 1.56/0.58    inference(subsumption_resolution,[],[f258,f120])).
% 1.56/0.58  fof(f258,plain,(
% 1.56/0.58    r1_waybel_7(sK0,k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),sK2) | v1_xboole_0(k2_struct_0(sK0)) | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1)) | ~l1_struct_0(sK0) | ~v13_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) | ~v2_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) | v1_xboole_0(sK1) | ~m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) | v2_struct_0(sK0)),
% 1.56/0.58    inference(subsumption_resolution,[],[f257,f119])).
% 1.56/0.58  fof(f257,plain,(
% 1.56/0.58    r1_waybel_7(sK0,k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),sK2) | v1_xboole_0(k2_struct_0(sK0)) | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1)) | ~l1_struct_0(sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))))) | ~v13_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) | ~v2_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) | v1_xboole_0(sK1) | ~m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) | v2_struct_0(sK0)),
% 1.56/0.58    inference(duplicate_literal_removal,[],[f256])).
% 1.56/0.58  fof(f256,plain,(
% 1.56/0.58    r1_waybel_7(sK0,k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),sK2) | v1_xboole_0(k2_struct_0(sK0)) | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1)) | ~l1_struct_0(sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))))) | ~v13_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) | ~v2_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) | v1_xboole_0(sK1) | ~m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) | v1_xboole_0(k2_struct_0(sK0)) | ~l1_struct_0(sK0) | v2_struct_0(sK0)),
% 1.56/0.58    inference(resolution,[],[f255,f128])).
% 1.56/0.58  fof(f255,plain,(
% 1.56/0.58    ~l1_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK0) | r1_waybel_7(sK0,k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),sK2) | v1_xboole_0(k2_struct_0(sK0)) | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1)) | ~l1_struct_0(sK0)),
% 1.56/0.58    inference(subsumption_resolution,[],[f254,f134])).
% 1.56/0.58  fof(f254,plain,(
% 1.56/0.58    ~m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0))) | ~l1_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK0) | r1_waybel_7(sK0,k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),sK2) | v1_xboole_0(k2_struct_0(sK0)) | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1)) | ~l1_struct_0(sK0)),
% 1.56/0.58    inference(forward_demodulation,[],[f253,f137])).
% 1.56/0.58  fof(f253,plain,(
% 1.56/0.58    ~l1_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK0) | r1_waybel_7(sK0,k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),sK2) | v1_xboole_0(k2_struct_0(sK0)) | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1)) | ~m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_struct_0(sK0)),
% 1.56/0.58    inference(subsumption_resolution,[],[f252,f71])).
% 1.56/0.58  fof(f252,plain,(
% 1.56/0.58    ~l1_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK0) | r1_waybel_7(sK0,k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),sK2) | v1_xboole_0(k2_struct_0(sK0)) | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1)) | ~m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_struct_0(sK0) | v2_struct_0(sK0)),
% 1.56/0.58    inference(subsumption_resolution,[],[f251,f74])).
% 1.56/0.58  fof(f251,plain,(
% 1.56/0.58    ~l1_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK0) | r1_waybel_7(sK0,k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),sK2) | v1_xboole_0(k2_struct_0(sK0)) | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1)) | v1_xboole_0(sK1) | ~m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_struct_0(sK0) | v2_struct_0(sK0)),
% 1.56/0.58    inference(subsumption_resolution,[],[f250,f121])).
% 1.56/0.58  fof(f250,plain,(
% 1.56/0.58    ~l1_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK0) | r1_waybel_7(sK0,k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),sK2) | v1_xboole_0(k2_struct_0(sK0)) | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1)) | ~v2_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) | v1_xboole_0(sK1) | ~m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_struct_0(sK0) | v2_struct_0(sK0)),
% 1.56/0.58    inference(subsumption_resolution,[],[f249,f120])).
% 1.56/0.58  fof(f249,plain,(
% 1.56/0.58    ~l1_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK0) | r1_waybel_7(sK0,k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),sK2) | v1_xboole_0(k2_struct_0(sK0)) | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1)) | ~v13_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) | ~v2_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) | v1_xboole_0(sK1) | ~m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_struct_0(sK0) | v2_struct_0(sK0)),
% 1.56/0.58    inference(subsumption_resolution,[],[f248,f119])).
% 1.56/0.58  fof(f248,plain,(
% 1.56/0.58    ~l1_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK0) | r1_waybel_7(sK0,k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),sK2) | v1_xboole_0(k2_struct_0(sK0)) | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1)) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))))) | ~v13_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) | ~v2_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) | v1_xboole_0(sK1) | ~m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_struct_0(sK0) | v2_struct_0(sK0)),
% 1.56/0.58    inference(duplicate_literal_removal,[],[f247])).
% 1.56/0.58  fof(f247,plain,(
% 1.56/0.58    ~l1_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK0) | r1_waybel_7(sK0,k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),sK2) | v1_xboole_0(k2_struct_0(sK0)) | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1)) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))))) | ~v13_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) | ~v2_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) | v1_xboole_0(sK1) | ~m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) | v1_xboole_0(k2_struct_0(sK0)) | ~l1_struct_0(sK0) | v2_struct_0(sK0)),
% 1.56/0.58    inference(resolution,[],[f245,f125])).
% 1.56/0.58  fof(f245,plain,(
% 1.56/0.58    ~v4_orders_2(k3_yellow19(sK0,k2_struct_0(sK0),sK1)) | ~l1_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK0) | r1_waybel_7(sK0,k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),sK2) | v1_xboole_0(k2_struct_0(sK0)) | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))),
% 1.56/0.58    inference(subsumption_resolution,[],[f244,f138])).
% 1.56/0.58  fof(f244,plain,(
% 1.56/0.58    ~m1_subset_1(sK2,k2_struct_0(sK0)) | v1_xboole_0(k2_struct_0(sK0)) | ~l1_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK0) | r1_waybel_7(sK0,k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),sK2) | ~v4_orders_2(k3_yellow19(sK0,k2_struct_0(sK0),sK1)) | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))),
% 1.56/0.58    inference(forward_demodulation,[],[f243,f137])).
% 1.56/0.58  fof(f243,plain,(
% 1.56/0.58    v1_xboole_0(k2_struct_0(sK0)) | ~m1_subset_1(sK2,u1_struct_0(sK0)) | ~l1_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK0) | r1_waybel_7(sK0,k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),sK2) | ~v4_orders_2(k3_yellow19(sK0,k2_struct_0(sK0),sK1)) | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))),
% 1.56/0.58    inference(subsumption_resolution,[],[f242,f71])).
% 1.56/0.58  fof(f242,plain,(
% 1.56/0.58    v1_xboole_0(k2_struct_0(sK0)) | ~m1_subset_1(sK2,u1_struct_0(sK0)) | ~l1_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK0) | r1_waybel_7(sK0,k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),sK2) | ~v4_orders_2(k3_yellow19(sK0,k2_struct_0(sK0),sK1)) | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1)) | v2_struct_0(sK0)),
% 1.56/0.58    inference(subsumption_resolution,[],[f241,f72])).
% 1.56/0.58  fof(f241,plain,(
% 1.56/0.58    v1_xboole_0(k2_struct_0(sK0)) | ~m1_subset_1(sK2,u1_struct_0(sK0)) | ~l1_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK0) | r1_waybel_7(sK0,k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),sK2) | ~v4_orders_2(k3_yellow19(sK0,k2_struct_0(sK0),sK1)) | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1)) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 1.56/0.58    inference(subsumption_resolution,[],[f240,f73])).
% 1.56/0.58  fof(f240,plain,(
% 1.56/0.58    v1_xboole_0(k2_struct_0(sK0)) | ~m1_subset_1(sK2,u1_struct_0(sK0)) | ~l1_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK0) | r1_waybel_7(sK0,k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),sK2) | ~v4_orders_2(k3_yellow19(sK0,k2_struct_0(sK0),sK1)) | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1)) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 1.56/0.58    inference(duplicate_literal_removal,[],[f239])).
% 1.56/0.58  fof(f239,plain,(
% 1.56/0.58    v1_xboole_0(k2_struct_0(sK0)) | v1_xboole_0(k2_struct_0(sK0)) | ~m1_subset_1(sK2,u1_struct_0(sK0)) | ~l1_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK0) | r1_waybel_7(sK0,k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),sK2) | ~v4_orders_2(k3_yellow19(sK0,k2_struct_0(sK0),sK1)) | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1)) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 1.56/0.58    inference(resolution,[],[f237,f189])).
% 1.56/0.58  fof(f189,plain,(
% 1.56/0.58    ( ! [X2,X3] : (~r3_waybel_9(X2,k3_yellow19(sK0,k2_struct_0(sK0),sK1),X3) | v1_xboole_0(k2_struct_0(sK0)) | ~m1_subset_1(X3,u1_struct_0(X2)) | ~l1_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1),X2) | r1_waybel_7(X2,k2_yellow19(X2,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),X3) | ~v4_orders_2(k3_yellow19(sK0,k2_struct_0(sK0),sK1)) | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1)) | ~l1_pre_topc(X2) | ~v2_pre_topc(X2) | v2_struct_0(X2)) )),
% 1.56/0.58    inference(resolution,[],[f187,f95])).
% 1.56/0.58  fof(f95,plain,(
% 1.56/0.58    ( ! [X2,X0,X1] : (~v7_waybel_0(X1) | ~r3_waybel_9(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_waybel_0(X1,X0) | r1_waybel_7(X0,k2_yellow19(X0,X1),X2) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.56/0.58    inference(cnf_transformation,[],[f61])).
% 1.56/0.58  fof(f288,plain,(
% 1.56/0.58    ( ! [X0] : (~v1_xboole_0(X0) | k2_struct_0(sK0) = X0) )),
% 1.56/0.58    inference(resolution,[],[f287,f108])).
% 1.56/0.58  fof(f108,plain,(
% 1.56/0.58    ( ! [X0,X1] : (~v1_xboole_0(X1) | X0 = X1 | ~v1_xboole_0(X0)) )),
% 1.56/0.58    inference(cnf_transformation,[],[f42])).
% 1.56/0.58  fof(f42,plain,(
% 1.56/0.58    ! [X0,X1] : (~v1_xboole_0(X1) | X0 = X1 | ~v1_xboole_0(X0))),
% 1.56/0.58    inference(ennf_transformation,[],[f2])).
% 1.56/0.58  fof(f2,axiom,(
% 1.56/0.58    ! [X0,X1] : ~(v1_xboole_0(X1) & X0 != X1 & v1_xboole_0(X0))),
% 1.56/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_boole)).
% 1.56/0.58  fof(f560,plain,(
% 1.56/0.58    v1_xboole_0(sK4(sK0))),
% 1.56/0.58    inference(resolution,[],[f548,f349])).
% 1.56/0.58  fof(f349,plain,(
% 1.56/0.58    ( ! [X2] : (~m1_subset_1(X2,sK2) | v1_xboole_0(X2)) )),
% 1.56/0.58    inference(backward_demodulation,[],[f290,f303])).
% 1.56/0.58  fof(f548,plain,(
% 1.56/0.58    m1_subset_1(sK4(sK0),sK2)),
% 1.56/0.58    inference(subsumption_resolution,[],[f547,f73])).
% 1.56/0.58  fof(f547,plain,(
% 1.56/0.58    m1_subset_1(sK4(sK0),sK2) | ~l1_pre_topc(sK0)),
% 1.56/0.58    inference(resolution,[],[f541,f85])).
% 1.56/0.58  fof(f541,plain,(
% 1.56/0.58    ~l1_struct_0(sK0) | m1_subset_1(sK4(sK0),sK2)),
% 1.56/0.58    inference(forward_demodulation,[],[f539,f314])).
% 1.56/0.58  fof(f314,plain,(
% 1.56/0.58    u1_struct_0(sK0) = sK2),
% 1.56/0.58    inference(backward_demodulation,[],[f137,f303])).
% 1.56/0.58  fof(f539,plain,(
% 1.56/0.58    m1_subset_1(sK4(sK0),u1_struct_0(sK0)) | ~l1_struct_0(sK0)),
% 1.56/0.58    inference(resolution,[],[f537,f89])).
% 1.56/0.58  fof(f89,plain,(
% 1.56/0.58    ( ! [X0] : (v7_struct_0(X0) | m1_subset_1(sK4(X0),u1_struct_0(X0)) | ~l1_struct_0(X0)) )),
% 1.56/0.58    inference(cnf_transformation,[],[f59])).
% 1.56/0.58  fof(f59,plain,(
% 1.56/0.58    ! [X0] : (((v7_struct_0(X0) | ((sK3(X0) != sK4(X0) & m1_subset_1(sK4(X0),u1_struct_0(X0))) & m1_subset_1(sK3(X0),u1_struct_0(X0)))) & (! [X3] : (! [X4] : (X3 = X4 | ~m1_subset_1(X4,u1_struct_0(X0))) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~v7_struct_0(X0))) | ~l1_struct_0(X0))),
% 1.56/0.58    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f56,f58,f57])).
% 1.56/0.58  fof(f57,plain,(
% 1.56/0.58    ! [X0] : (? [X1] : (? [X2] : (X1 != X2 & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) => (? [X2] : (sK3(X0) != X2 & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(sK3(X0),u1_struct_0(X0))))),
% 1.56/0.58    introduced(choice_axiom,[])).
% 1.56/0.58  fof(f58,plain,(
% 1.56/0.58    ! [X0] : (? [X2] : (sK3(X0) != X2 & m1_subset_1(X2,u1_struct_0(X0))) => (sK3(X0) != sK4(X0) & m1_subset_1(sK4(X0),u1_struct_0(X0))))),
% 1.56/0.58    introduced(choice_axiom,[])).
% 1.56/0.58  fof(f56,plain,(
% 1.56/0.58    ! [X0] : (((v7_struct_0(X0) | ? [X1] : (? [X2] : (X1 != X2 & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0)))) & (! [X3] : (! [X4] : (X3 = X4 | ~m1_subset_1(X4,u1_struct_0(X0))) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~v7_struct_0(X0))) | ~l1_struct_0(X0))),
% 1.56/0.58    inference(rectify,[],[f55])).
% 1.56/0.58  fof(f55,plain,(
% 1.56/0.58    ! [X0] : (((v7_struct_0(X0) | ? [X1] : (? [X2] : (X1 != X2 & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0)))) & (! [X1] : (! [X2] : (X1 = X2 | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~v7_struct_0(X0))) | ~l1_struct_0(X0))),
% 1.56/0.58    inference(nnf_transformation,[],[f26])).
% 1.56/0.58  fof(f26,plain,(
% 1.56/0.58    ! [X0] : ((v7_struct_0(X0) <=> ! [X1] : (! [X2] : (X1 = X2 | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)))) | ~l1_struct_0(X0))),
% 1.56/0.58    inference(ennf_transformation,[],[f14])).
% 1.56/0.58  fof(f14,axiom,(
% 1.56/0.58    ! [X0] : (l1_struct_0(X0) => (v7_struct_0(X0) <=> ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => X1 = X2))))),
% 1.56/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_struct_0)).
% 1.56/0.58  fof(f537,plain,(
% 1.56/0.58    ~v7_struct_0(sK0)),
% 1.56/0.58    inference(subsumption_resolution,[],[f534,f134])).
% 1.56/0.58  fof(f534,plain,(
% 1.56/0.58    ~v7_struct_0(sK0) | ~m1_subset_1(sK2,k1_zfmisc_1(sK2))),
% 1.56/0.58    inference(resolution,[],[f532,f392])).
% 1.56/0.58  fof(f392,plain,(
% 1.56/0.58    ( ! [X1] : (m2_connsp_2(sK2,sK0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(sK2))) )),
% 1.56/0.58    inference(forward_demodulation,[],[f391,f314])).
% 1.56/0.58  fof(f391,plain,(
% 1.56/0.58    ( ! [X1] : (m2_connsp_2(sK2,sK0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) )),
% 1.56/0.58    inference(subsumption_resolution,[],[f390,f71])).
% 1.56/0.58  fof(f390,plain,(
% 1.56/0.58    ( ! [X1] : (m2_connsp_2(sK2,sK0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | v2_struct_0(sK0)) )),
% 1.56/0.58    inference(subsumption_resolution,[],[f389,f72])).
% 1.56/0.58  fof(f389,plain,(
% 1.56/0.58    ( ! [X1] : (m2_connsp_2(sK2,sK0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 1.56/0.58    inference(subsumption_resolution,[],[f387,f73])).
% 1.56/0.58  fof(f387,plain,(
% 1.56/0.58    ( ! [X1] : (m2_connsp_2(sK2,sK0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 1.56/0.58    inference(superposition,[],[f93,f303])).
% 1.56/0.58  fof(f93,plain,(
% 1.56/0.58    ( ! [X0,X1] : (m2_connsp_2(k2_struct_0(X0),X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.56/0.58    inference(cnf_transformation,[],[f30])).
% 1.56/0.58  fof(f30,plain,(
% 1.56/0.58    ! [X0] : (! [X1] : (m2_connsp_2(k2_struct_0(X0),X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.56/0.58    inference(flattening,[],[f29])).
% 1.56/0.58  fof(f29,plain,(
% 1.56/0.58    ! [X0] : (! [X1] : (m2_connsp_2(k2_struct_0(X0),X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 1.56/0.58    inference(ennf_transformation,[],[f10])).
% 1.56/0.58  fof(f10,axiom,(
% 1.56/0.58    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => m2_connsp_2(k2_struct_0(X0),X0,X1)))),
% 1.56/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_connsp_2)).
% 1.56/0.58  fof(f532,plain,(
% 1.56/0.58    ~m2_connsp_2(sK2,sK0,sK2) | ~v7_struct_0(sK0)),
% 1.56/0.58    inference(subsumption_resolution,[],[f531,f73])).
% 1.56/0.58  fof(f531,plain,(
% 1.56/0.58    ~v7_struct_0(sK0) | ~m2_connsp_2(sK2,sK0,sK2) | ~l1_pre_topc(sK0)),
% 1.56/0.58    inference(resolution,[],[f529,f85])).
% 1.56/0.58  fof(f529,plain,(
% 1.56/0.58    ~l1_struct_0(sK0) | ~v7_struct_0(sK0) | ~m2_connsp_2(sK2,sK0,sK2)),
% 1.56/0.58    inference(subsumption_resolution,[],[f527,f404])).
% 1.56/0.58  fof(f404,plain,(
% 1.56/0.58    m1_subset_1(sK5(sK0),sK2) | ~v7_struct_0(sK0)),
% 1.56/0.58    inference(subsumption_resolution,[],[f403,f73])).
% 1.56/0.58  fof(f403,plain,(
% 1.56/0.58    ~v7_struct_0(sK0) | m1_subset_1(sK5(sK0),sK2) | ~l1_pre_topc(sK0)),
% 1.56/0.58    inference(resolution,[],[f316,f85])).
% 1.56/0.58  fof(f316,plain,(
% 1.56/0.58    ~l1_struct_0(sK0) | ~v7_struct_0(sK0) | m1_subset_1(sK5(sK0),sK2)),
% 1.56/0.58    inference(backward_demodulation,[],[f140,f303])).
% 1.56/0.58  fof(f140,plain,(
% 1.56/0.58    m1_subset_1(sK5(sK0),k2_struct_0(sK0)) | ~v7_struct_0(sK0) | ~l1_struct_0(sK0)),
% 1.56/0.58    inference(subsumption_resolution,[],[f139,f71])).
% 1.56/0.58  fof(f139,plain,(
% 1.56/0.58    m1_subset_1(sK5(sK0),k2_struct_0(sK0)) | ~v7_struct_0(sK0) | ~l1_struct_0(sK0) | v2_struct_0(sK0)),
% 1.56/0.58    inference(superposition,[],[f97,f137])).
% 1.56/0.58  fof(f97,plain,(
% 1.56/0.58    ( ! [X0] : (m1_subset_1(sK5(X0),u1_struct_0(X0)) | ~v7_struct_0(X0) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 1.56/0.58    inference(cnf_transformation,[],[f65])).
% 1.56/0.58  fof(f65,plain,(
% 1.56/0.58    ! [X0] : (((v7_struct_0(X0) | ! [X1] : (u1_struct_0(X0) != k6_domain_1(u1_struct_0(X0),X1) | ~m1_subset_1(X1,u1_struct_0(X0)))) & ((u1_struct_0(X0) = k6_domain_1(u1_struct_0(X0),sK5(X0)) & m1_subset_1(sK5(X0),u1_struct_0(X0))) | ~v7_struct_0(X0))) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 1.56/0.58    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f63,f64])).
% 1.56/0.58  fof(f64,plain,(
% 1.56/0.58    ! [X0] : (? [X2] : (u1_struct_0(X0) = k6_domain_1(u1_struct_0(X0),X2) & m1_subset_1(X2,u1_struct_0(X0))) => (u1_struct_0(X0) = k6_domain_1(u1_struct_0(X0),sK5(X0)) & m1_subset_1(sK5(X0),u1_struct_0(X0))))),
% 1.56/0.58    introduced(choice_axiom,[])).
% 1.56/0.58  fof(f63,plain,(
% 1.56/0.58    ! [X0] : (((v7_struct_0(X0) | ! [X1] : (u1_struct_0(X0) != k6_domain_1(u1_struct_0(X0),X1) | ~m1_subset_1(X1,u1_struct_0(X0)))) & (? [X2] : (u1_struct_0(X0) = k6_domain_1(u1_struct_0(X0),X2) & m1_subset_1(X2,u1_struct_0(X0))) | ~v7_struct_0(X0))) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 1.56/0.58    inference(rectify,[],[f62])).
% 1.56/0.58  % (2328)Termination reason: Refutation not found, incomplete strategy
% 1.56/0.58  fof(f62,plain,(
% 1.56/0.58    ! [X0] : (((v7_struct_0(X0) | ! [X1] : (u1_struct_0(X0) != k6_domain_1(u1_struct_0(X0),X1) | ~m1_subset_1(X1,u1_struct_0(X0)))) & (? [X1] : (u1_struct_0(X0) = k6_domain_1(u1_struct_0(X0),X1) & m1_subset_1(X1,u1_struct_0(X0))) | ~v7_struct_0(X0))) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 1.56/0.58    inference(nnf_transformation,[],[f36])).
% 1.56/0.58  
% 1.56/0.58  % (2328)Memory used [KB]: 6524
% 1.56/0.58  % (2328)Time elapsed: 0.170 s
% 1.56/0.58  % (2328)------------------------------
% 1.56/0.58  % (2328)------------------------------
% 1.56/0.58  fof(f36,plain,(
% 1.56/0.58    ! [X0] : ((v7_struct_0(X0) <=> ? [X1] : (u1_struct_0(X0) = k6_domain_1(u1_struct_0(X0),X1) & m1_subset_1(X1,u1_struct_0(X0)))) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 1.56/0.58    inference(flattening,[],[f35])).
% 1.56/0.58  % (2314)Termination reason: Refutation not found, incomplete strategy
% 1.56/0.58  
% 1.56/0.58  % (2314)Memory used [KB]: 6652
% 1.56/0.58  % (2314)Time elapsed: 0.164 s
% 1.56/0.58  % (2314)------------------------------
% 1.56/0.58  % (2314)------------------------------
% 1.56/0.58  fof(f35,plain,(
% 1.56/0.58    ! [X0] : ((v7_struct_0(X0) <=> ? [X1] : (u1_struct_0(X0) = k6_domain_1(u1_struct_0(X0),X1) & m1_subset_1(X1,u1_struct_0(X0)))) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 1.56/0.58    inference(ennf_transformation,[],[f13])).
% 1.56/0.58  fof(f13,axiom,(
% 1.56/0.58    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => (v7_struct_0(X0) <=> ? [X1] : (u1_struct_0(X0) = k6_domain_1(u1_struct_0(X0),X1) & m1_subset_1(X1,u1_struct_0(X0)))))),
% 1.56/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tex_1)).
% 1.56/0.58  fof(f527,plain,(
% 1.56/0.58    ~m2_connsp_2(sK2,sK0,sK2) | ~m1_subset_1(sK5(sK0),sK2) | ~v7_struct_0(sK0) | ~l1_struct_0(sK0)),
% 1.56/0.58    inference(superposition,[],[f524,f317])).
% 1.56/0.58  fof(f317,plain,(
% 1.56/0.58    sK2 = k6_domain_1(sK2,sK5(sK0)) | ~v7_struct_0(sK0) | ~l1_struct_0(sK0)),
% 1.56/0.58    inference(backward_demodulation,[],[f142,f303])).
% 1.56/0.58  fof(f142,plain,(
% 1.56/0.58    k2_struct_0(sK0) = k6_domain_1(k2_struct_0(sK0),sK5(sK0)) | ~v7_struct_0(sK0) | ~l1_struct_0(sK0)),
% 1.56/0.58    inference(forward_demodulation,[],[f141,f137])).
% 1.56/0.58  fof(f141,plain,(
% 1.56/0.58    ~v7_struct_0(sK0) | ~l1_struct_0(sK0) | u1_struct_0(sK0) = k6_domain_1(u1_struct_0(sK0),sK5(sK0))),
% 1.56/0.58    inference(resolution,[],[f98,f71])).
% 1.56/0.58  fof(f98,plain,(
% 1.56/0.58    ( ! [X0] : (v2_struct_0(X0) | ~v7_struct_0(X0) | ~l1_struct_0(X0) | u1_struct_0(X0) = k6_domain_1(u1_struct_0(X0),sK5(X0))) )),
% 1.56/0.58    inference(cnf_transformation,[],[f65])).
% 1.56/0.58  fof(f524,plain,(
% 1.56/0.58    ( ! [X0] : (~m2_connsp_2(sK2,sK0,k6_domain_1(sK2,X0)) | ~m1_subset_1(X0,sK2)) )),
% 1.56/0.58    inference(subsumption_resolution,[],[f523,f134])).
% 1.56/0.58  fof(f523,plain,(
% 1.56/0.58    ( ! [X0] : (~m1_subset_1(X0,sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(sK2)) | ~m2_connsp_2(sK2,sK0,k6_domain_1(sK2,X0))) )),
% 1.56/0.58    inference(duplicate_literal_removal,[],[f522])).
% 1.56/0.58  fof(f522,plain,(
% 1.56/0.58    ( ! [X0] : (~m1_subset_1(X0,sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(sK2)) | ~m1_subset_1(X0,sK2) | ~m2_connsp_2(sK2,sK0,k6_domain_1(sK2,X0))) )),
% 1.56/0.58    inference(resolution,[],[f521,f367])).
% 1.56/0.58  fof(f367,plain,(
% 1.56/0.58    ( ! [X0,X1] : (m1_connsp_2(X0,sK0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(sK2)) | ~m1_subset_1(X1,sK2) | ~m2_connsp_2(X0,sK0,k6_domain_1(sK2,X1))) )),
% 1.56/0.58    inference(forward_demodulation,[],[f366,f303])).
% 1.56/0.58  fof(f366,plain,(
% 1.56/0.58    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(sK2)) | ~m1_subset_1(X1,sK2) | m1_connsp_2(X0,sK0,X1) | ~m2_connsp_2(X0,sK0,k6_domain_1(k2_struct_0(sK0),X1))) )),
% 1.56/0.58    inference(forward_demodulation,[],[f324,f303])).
% 1.56/0.58  fof(f324,plain,(
% 1.56/0.58    ( ! [X0,X1] : (~m1_subset_1(X1,sK2) | m1_connsp_2(X0,sK0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) | ~m2_connsp_2(X0,sK0,k6_domain_1(k2_struct_0(sK0),X1))) )),
% 1.56/0.58    inference(backward_demodulation,[],[f161,f303])).
% 1.56/0.58  fof(f161,plain,(
% 1.56/0.58    ( ! [X0,X1] : (m1_connsp_2(X0,sK0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) | ~m2_connsp_2(X0,sK0,k6_domain_1(k2_struct_0(sK0),X1)) | ~m1_subset_1(X1,k2_struct_0(sK0))) )),
% 1.56/0.58    inference(forward_demodulation,[],[f160,f137])).
% 1.56/0.58  fof(f160,plain,(
% 1.56/0.58    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) | ~m2_connsp_2(X0,sK0,k6_domain_1(k2_struct_0(sK0),X1)) | ~m1_subset_1(X1,u1_struct_0(sK0)) | m1_connsp_2(X0,sK0,X1)) )),
% 1.56/0.58    inference(forward_demodulation,[],[f159,f137])).
% 1.56/0.58  fof(f159,plain,(
% 1.56/0.58    ( ! [X0,X1] : (~m2_connsp_2(X0,sK0,k6_domain_1(k2_struct_0(sK0),X1)) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X1,u1_struct_0(sK0)) | m1_connsp_2(X0,sK0,X1)) )),
% 1.56/0.58    inference(forward_demodulation,[],[f158,f137])).
% 1.56/0.58  fof(f158,plain,(
% 1.56/0.58    ( ! [X0,X1] : (~m2_connsp_2(X0,sK0,k6_domain_1(u1_struct_0(sK0),X1)) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X1,u1_struct_0(sK0)) | m1_connsp_2(X0,sK0,X1)) )),
% 1.56/0.58    inference(subsumption_resolution,[],[f157,f71])).
% 1.56/0.58  fof(f157,plain,(
% 1.56/0.58    ( ! [X0,X1] : (~m2_connsp_2(X0,sK0,k6_domain_1(u1_struct_0(sK0),X1)) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X1,u1_struct_0(sK0)) | m1_connsp_2(X0,sK0,X1) | v2_struct_0(sK0)) )),
% 1.56/0.58    inference(subsumption_resolution,[],[f156,f73])).
% 1.56/0.58  fof(f156,plain,(
% 1.56/0.58    ( ! [X0,X1] : (~m2_connsp_2(X0,sK0,k6_domain_1(u1_struct_0(sK0),X1)) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~l1_pre_topc(sK0) | m1_connsp_2(X0,sK0,X1) | v2_struct_0(sK0)) )),
% 1.56/0.58    inference(resolution,[],[f91,f72])).
% 1.56/0.58  fof(f91,plain,(
% 1.56/0.58    ( ! [X2,X0,X1] : (~v2_pre_topc(X0) | ~m2_connsp_2(X2,X0,k6_domain_1(u1_struct_0(X0),X1)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | m1_connsp_2(X2,X0,X1) | v2_struct_0(X0)) )),
% 1.56/0.58    inference(cnf_transformation,[],[f60])).
% 1.56/0.58  fof(f60,plain,(
% 1.56/0.58    ! [X0] : (! [X1] : (! [X2] : (((m2_connsp_2(X2,X0,k6_domain_1(u1_struct_0(X0),X1)) | ~m1_connsp_2(X2,X0,X1)) & (m1_connsp_2(X2,X0,X1) | ~m2_connsp_2(X2,X0,k6_domain_1(u1_struct_0(X0),X1)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.56/0.58    inference(nnf_transformation,[],[f28])).
% 1.56/0.58  fof(f28,plain,(
% 1.56/0.58    ! [X0] : (! [X1] : (! [X2] : ((m2_connsp_2(X2,X0,k6_domain_1(u1_struct_0(X0),X1)) <=> m1_connsp_2(X2,X0,X1)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.56/0.58    inference(flattening,[],[f27])).
% 1.56/0.59  fof(f27,plain,(
% 1.56/0.59    ! [X0] : (! [X1] : (! [X2] : ((m2_connsp_2(X2,X0,k6_domain_1(u1_struct_0(X0),X1)) <=> m1_connsp_2(X2,X0,X1)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 1.56/0.59    inference(ennf_transformation,[],[f9])).
% 1.56/0.59  fof(f9,axiom,(
% 1.56/0.59    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (m2_connsp_2(X2,X0,k6_domain_1(u1_struct_0(X0),X1)) <=> m1_connsp_2(X2,X0,X1)))))),
% 1.56/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_connsp_2)).
% 1.56/0.59  fof(f521,plain,(
% 1.56/0.59    ( ! [X0] : (~m1_connsp_2(sK2,sK0,X0) | ~m1_subset_1(X0,sK2)) )),
% 1.56/0.59    inference(forward_demodulation,[],[f520,f314])).
% 1.56/0.59  fof(f520,plain,(
% 1.56/0.59    ( ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK0)) | ~m1_connsp_2(sK2,sK0,X0)) )),
% 1.56/0.59    inference(subsumption_resolution,[],[f519,f71])).
% 1.56/0.59  fof(f519,plain,(
% 1.56/0.59    ( ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK0)) | ~m1_connsp_2(sK2,sK0,X0) | v2_struct_0(sK0)) )),
% 1.56/0.59    inference(subsumption_resolution,[],[f518,f73])).
% 1.56/0.59  fof(f518,plain,(
% 1.56/0.59    ( ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK0)) | ~l1_pre_topc(sK0) | ~m1_connsp_2(sK2,sK0,X0) | v2_struct_0(sK0)) )),
% 1.56/0.59    inference(resolution,[],[f351,f72])).
% 1.56/0.59  fof(f351,plain,(
% 1.56/0.59    ( ! [X0,X1] : (~v2_pre_topc(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~m1_connsp_2(sK2,X0,X1) | v2_struct_0(X0)) )),
% 1.56/0.59    inference(backward_demodulation,[],[f295,f303])).
% 1.56/0.59  fof(f295,plain,(
% 1.56/0.59    ( ! [X0,X1] : (~m1_connsp_2(k2_struct_0(sK0),X0,X1) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.56/0.59    inference(subsumption_resolution,[],[f293,f107])).
% 1.56/0.59  fof(f107,plain,(
% 1.56/0.59    ( ! [X2,X0,X1] : (~m1_connsp_2(X2,X0,X1) | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.56/0.59    inference(cnf_transformation,[],[f41])).
% 1.56/0.59  fof(f41,plain,(
% 1.56/0.59    ! [X0,X1] : (! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_connsp_2(X2,X0,X1)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.56/0.59    inference(flattening,[],[f40])).
% 1.56/0.59  fof(f40,plain,(
% 1.56/0.59    ! [X0,X1] : (! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_connsp_2(X2,X0,X1)) | (~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 1.56/0.59    inference(ennf_transformation,[],[f8])).
% 1.56/0.59  fof(f8,axiom,(
% 1.56/0.59    ! [X0,X1] : ((m1_subset_1(X1,u1_struct_0(X0)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X2] : (m1_connsp_2(X2,X0,X1) => m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))))),
% 1.56/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_connsp_2)).
% 1.56/0.59  fof(f293,plain,(
% 1.56/0.59    ( ! [X0,X1] : (~m1_connsp_2(k2_struct_0(sK0),X0,X1) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.56/0.59    inference(resolution,[],[f291,f94])).
% 1.56/0.59  fof(f94,plain,(
% 1.56/0.59    ( ! [X2,X0,X1] : (r2_hidden(X2,X1) | ~m1_connsp_2(X1,X0,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.56/0.59    inference(cnf_transformation,[],[f32])).
% 1.56/0.59  fof(f32,plain,(
% 1.56/0.59    ! [X0] : (! [X1] : (! [X2] : (r2_hidden(X2,X1) | ~m1_connsp_2(X1,X0,X2) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.56/0.59    inference(flattening,[],[f31])).
% 1.56/0.59  fof(f31,plain,(
% 1.56/0.59    ! [X0] : (! [X1] : (! [X2] : ((r2_hidden(X2,X1) | ~m1_connsp_2(X1,X0,X2)) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 1.56/0.59    inference(ennf_transformation,[],[f11])).
% 1.56/0.59  fof(f11,axiom,(
% 1.56/0.59    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (m1_connsp_2(X1,X0,X2) => r2_hidden(X2,X1)))))),
% 1.56/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_connsp_2)).
% 1.56/0.59  fof(f291,plain,(
% 1.56/0.59    ( ! [X3] : (~r2_hidden(X3,k2_struct_0(sK0))) )),
% 1.56/0.59    inference(resolution,[],[f287,f101])).
% 1.56/0.59  fof(f101,plain,(
% 1.56/0.59    ( ! [X2,X0] : (~v1_xboole_0(X0) | ~r2_hidden(X2,X0)) )),
% 1.56/0.59    inference(cnf_transformation,[],[f69])).
% 1.56/0.59  fof(f69,plain,(
% 1.56/0.59    ! [X0] : ((v1_xboole_0(X0) | r2_hidden(sK6(X0),X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 1.56/0.59    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f67,f68])).
% 1.56/0.59  fof(f68,plain,(
% 1.56/0.59    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK6(X0),X0))),
% 1.56/0.59    introduced(choice_axiom,[])).
% 1.56/0.59  fof(f67,plain,(
% 1.56/0.59    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 1.56/0.59    inference(rectify,[],[f66])).
% 1.56/0.59  fof(f66,plain,(
% 1.56/0.59    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0)))),
% 1.56/0.59    inference(nnf_transformation,[],[f1])).
% 1.56/0.59  fof(f1,axiom,(
% 1.56/0.59    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 1.56/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).
% 1.56/0.59  fof(f559,plain,(
% 1.56/0.59    ( ! [X0] : (~m1_subset_1(X0,sK2) | sK4(sK0) = X0) )),
% 1.56/0.59    inference(global_subsumption,[],[f347,f349,f558])).
% 1.56/0.59  fof(f558,plain,(
% 1.56/0.59    ( ! [X0] : (sK2 != X0 | ~m1_subset_1(X0,sK2) | sK4(sK0) = X0) )),
% 1.56/0.59    inference(subsumption_resolution,[],[f554,f548])).
% 1.56/0.59  fof(f554,plain,(
% 1.56/0.59    ( ! [X0] : (sK2 != X0 | ~m1_subset_1(X0,sK2) | ~m1_subset_1(sK4(sK0),sK2) | sK4(sK0) = X0) )),
% 1.56/0.59    inference(equality_factoring,[],[f503])).
% 1.56/0.59  fof(f503,plain,(
% 1.56/0.59    ( ! [X12,X13] : (sK2 = sK4(sK0) | ~m1_subset_1(X13,sK2) | ~m1_subset_1(X12,sK2) | X12 = X13) )),
% 1.56/0.59    inference(resolution,[],[f481,f347])).
% 1.56/0.59  fof(f481,plain,(
% 1.56/0.59    ( ! [X0,X1] : (v1_xboole_0(sK4(sK0)) | X0 = X1 | ~m1_subset_1(X1,sK2) | ~m1_subset_1(X0,sK2)) )),
% 1.56/0.59    inference(resolution,[],[f459,f349])).
% 1.56/0.59  fof(f459,plain,(
% 1.56/0.59    ( ! [X0,X1] : (m1_subset_1(sK4(sK0),sK2) | ~m1_subset_1(X0,sK2) | X0 = X1 | ~m1_subset_1(X1,sK2)) )),
% 1.56/0.59    inference(subsumption_resolution,[],[f458,f73])).
% 1.56/0.59  fof(f458,plain,(
% 1.56/0.59    ( ! [X0,X1] : (m1_subset_1(sK4(sK0),sK2) | ~m1_subset_1(X0,sK2) | X0 = X1 | ~m1_subset_1(X1,sK2) | ~l1_pre_topc(sK0)) )),
% 1.56/0.59    inference(resolution,[],[f356,f85])).
% 1.56/0.59  fof(f356,plain,(
% 1.56/0.59    ( ! [X0,X1] : (~l1_struct_0(sK0) | m1_subset_1(sK4(sK0),sK2) | ~m1_subset_1(X0,sK2) | X0 = X1 | ~m1_subset_1(X1,sK2)) )),
% 1.56/0.59    inference(forward_demodulation,[],[f355,f303])).
% 1.56/0.59  fof(f355,plain,(
% 1.56/0.59    ( ! [X0,X1] : (m1_subset_1(sK4(sK0),sK2) | ~m1_subset_1(X0,sK2) | ~m1_subset_1(X1,k2_struct_0(sK0)) | X0 = X1 | ~l1_struct_0(sK0)) )),
% 1.56/0.59    inference(forward_demodulation,[],[f319,f303])).
% 1.56/0.59  fof(f319,plain,(
% 1.56/0.59    ( ! [X0,X1] : (~m1_subset_1(X0,sK2) | m1_subset_1(sK4(sK0),k2_struct_0(sK0)) | ~m1_subset_1(X1,k2_struct_0(sK0)) | X0 = X1 | ~l1_struct_0(sK0)) )),
% 1.56/0.59    inference(backward_demodulation,[],[f149,f303])).
% 1.56/0.59  fof(f149,plain,(
% 1.56/0.59    ( ! [X0,X1] : (m1_subset_1(sK4(sK0),k2_struct_0(sK0)) | ~m1_subset_1(X0,k2_struct_0(sK0)) | ~m1_subset_1(X1,k2_struct_0(sK0)) | X0 = X1 | ~l1_struct_0(sK0)) )),
% 1.56/0.59    inference(forward_demodulation,[],[f147,f137])).
% 1.56/0.59  fof(f147,plain,(
% 1.56/0.59    ( ! [X0,X1] : (~m1_subset_1(X0,k2_struct_0(sK0)) | ~m1_subset_1(X1,k2_struct_0(sK0)) | X0 = X1 | m1_subset_1(sK4(sK0),u1_struct_0(sK0)) | ~l1_struct_0(sK0)) )),
% 1.56/0.59    inference(resolution,[],[f146,f89])).
% 1.56/0.59  fof(f146,plain,(
% 1.56/0.59    ( ! [X0,X1] : (~v7_struct_0(sK0) | ~m1_subset_1(X0,k2_struct_0(sK0)) | ~m1_subset_1(X1,k2_struct_0(sK0)) | X0 = X1) )),
% 1.56/0.59    inference(forward_demodulation,[],[f145,f137])).
% 1.56/0.59  fof(f145,plain,(
% 1.56/0.59    ( ! [X0,X1] : (~m1_subset_1(X0,k2_struct_0(sK0)) | ~v7_struct_0(sK0) | X0 = X1 | ~m1_subset_1(X1,u1_struct_0(sK0))) )),
% 1.56/0.59    inference(forward_demodulation,[],[f144,f137])).
% 1.56/0.59  fof(f144,plain,(
% 1.56/0.59    ( ! [X0,X1] : (~m1_subset_1(X0,u1_struct_0(sK0)) | ~v7_struct_0(sK0) | X0 = X1 | ~m1_subset_1(X1,u1_struct_0(sK0))) )),
% 1.56/0.59    inference(resolution,[],[f143,f73])).
% 1.56/0.59  fof(f143,plain,(
% 1.56/0.59    ( ! [X2,X0,X1] : (~l1_pre_topc(X1) | ~m1_subset_1(X2,u1_struct_0(X1)) | ~v7_struct_0(X1) | X0 = X2 | ~m1_subset_1(X0,u1_struct_0(X1))) )),
% 1.56/0.59    inference(resolution,[],[f87,f85])).
% 1.56/0.59  fof(f87,plain,(
% 1.56/0.59    ( ! [X4,X0,X3] : (~l1_struct_0(X0) | ~m1_subset_1(X4,u1_struct_0(X0)) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~v7_struct_0(X0) | X3 = X4) )),
% 1.56/0.59    inference(cnf_transformation,[],[f59])).
% 1.56/0.59  fof(f624,plain,(
% 1.56/0.59    m1_subset_1(sK3(sK0),sK2)),
% 1.56/0.59    inference(subsumption_resolution,[],[f623,f73])).
% 1.56/0.59  fof(f623,plain,(
% 1.56/0.59    m1_subset_1(sK3(sK0),sK2) | ~l1_pre_topc(sK0)),
% 1.56/0.59    inference(resolution,[],[f542,f85])).
% 1.56/0.59  fof(f542,plain,(
% 1.56/0.59    ~l1_struct_0(sK0) | m1_subset_1(sK3(sK0),sK2)),
% 1.56/0.59    inference(forward_demodulation,[],[f540,f314])).
% 1.56/0.59  fof(f540,plain,(
% 1.56/0.59    m1_subset_1(sK3(sK0),u1_struct_0(sK0)) | ~l1_struct_0(sK0)),
% 1.56/0.59    inference(resolution,[],[f537,f88])).
% 1.56/0.59  fof(f88,plain,(
% 1.56/0.59    ( ! [X0] : (v7_struct_0(X0) | m1_subset_1(sK3(X0),u1_struct_0(X0)) | ~l1_struct_0(X0)) )),
% 1.56/0.59    inference(cnf_transformation,[],[f59])).
% 1.56/0.59  fof(f608,plain,(
% 1.56/0.59    sK2 != sK3(sK0) | ~l1_struct_0(sK0)),
% 1.56/0.59    inference(subsumption_resolution,[],[f607,f537])).
% 1.56/0.59  fof(f607,plain,(
% 1.56/0.59    sK2 != sK3(sK0) | v7_struct_0(sK0) | ~l1_struct_0(sK0)),
% 1.56/0.59    inference(superposition,[],[f90,f566])).
% 1.56/0.59  fof(f90,plain,(
% 1.56/0.59    ( ! [X0] : (sK3(X0) != sK4(X0) | v7_struct_0(X0) | ~l1_struct_0(X0)) )),
% 1.56/0.59    inference(cnf_transformation,[],[f59])).
% 1.56/0.59  fof(f73,plain,(
% 1.56/0.59    l1_pre_topc(sK0)),
% 1.56/0.59    inference(cnf_transformation,[],[f54])).
% 1.56/0.59  % SZS output end Proof for theBenchmark
% 1.56/0.59  % (2325)------------------------------
% 1.56/0.59  % (2325)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.56/0.59  % (2325)Termination reason: Refutation
% 1.56/0.59  
% 1.56/0.59  % (2325)Memory used [KB]: 6652
% 1.56/0.59  % (2325)Time elapsed: 0.173 s
% 1.56/0.59  % (2325)------------------------------
% 1.56/0.59  % (2325)------------------------------
% 1.56/0.59  % (2302)Success in time 0.212 s
%------------------------------------------------------------------------------
