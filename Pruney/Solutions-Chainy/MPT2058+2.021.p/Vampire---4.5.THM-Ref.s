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
% DateTime   : Thu Dec  3 13:23:34 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :  141 (2023 expanded)
%              Number of leaves         :   16 ( 657 expanded)
%              Depth                    :   35
%              Number of atoms          :  809 (19243 expanded)
%              Number of equality atoms :   14 ( 236 expanded)
%              Maximal formula depth    :   14 (   7 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f179,plain,(
    $false ),
    inference(subsumption_resolution,[],[f178,f47])).

fof(f47,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,
    ( ( ~ r1_waybel_7(sK3,sK4,sK5)
      | ~ r3_waybel_9(sK3,k3_yellow19(sK3,k2_struct_0(sK3),sK4),sK5) )
    & ( r1_waybel_7(sK3,sK4,sK5)
      | r3_waybel_9(sK3,k3_yellow19(sK3,k2_struct_0(sK3),sK4),sK5) )
    & m1_subset_1(sK5,u1_struct_0(sK3))
    & m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK3)))))
    & v13_waybel_0(sK4,k3_yellow_1(k2_struct_0(sK3)))
    & v2_waybel_0(sK4,k3_yellow_1(k2_struct_0(sK3)))
    & v1_subset_1(sK4,u1_struct_0(k3_yellow_1(k2_struct_0(sK3))))
    & ~ v1_xboole_0(sK4)
    & l1_pre_topc(sK3)
    & v2_pre_topc(sK3)
    & ~ v2_struct_0(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5])],[f35,f38,f37,f36])).

fof(f36,plain,
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
              ( ( ~ r1_waybel_7(sK3,X1,X2)
                | ~ r3_waybel_9(sK3,k3_yellow19(sK3,k2_struct_0(sK3),X1),X2) )
              & ( r1_waybel_7(sK3,X1,X2)
                | r3_waybel_9(sK3,k3_yellow19(sK3,k2_struct_0(sK3),X1),X2) )
              & m1_subset_1(X2,u1_struct_0(sK3)) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK3)))))
          & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(sK3)))
          & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(sK3)))
          & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(sK3))))
          & ~ v1_xboole_0(X1) )
      & l1_pre_topc(sK3)
      & v2_pre_topc(sK3)
      & ~ v2_struct_0(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f37,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ( ~ r1_waybel_7(sK3,X1,X2)
              | ~ r3_waybel_9(sK3,k3_yellow19(sK3,k2_struct_0(sK3),X1),X2) )
            & ( r1_waybel_7(sK3,X1,X2)
              | r3_waybel_9(sK3,k3_yellow19(sK3,k2_struct_0(sK3),X1),X2) )
            & m1_subset_1(X2,u1_struct_0(sK3)) )
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK3)))))
        & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(sK3)))
        & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(sK3)))
        & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(sK3))))
        & ~ v1_xboole_0(X1) )
   => ( ? [X2] :
          ( ( ~ r1_waybel_7(sK3,sK4,X2)
            | ~ r3_waybel_9(sK3,k3_yellow19(sK3,k2_struct_0(sK3),sK4),X2) )
          & ( r1_waybel_7(sK3,sK4,X2)
            | r3_waybel_9(sK3,k3_yellow19(sK3,k2_struct_0(sK3),sK4),X2) )
          & m1_subset_1(X2,u1_struct_0(sK3)) )
      & m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK3)))))
      & v13_waybel_0(sK4,k3_yellow_1(k2_struct_0(sK3)))
      & v2_waybel_0(sK4,k3_yellow_1(k2_struct_0(sK3)))
      & v1_subset_1(sK4,u1_struct_0(k3_yellow_1(k2_struct_0(sK3))))
      & ~ v1_xboole_0(sK4) ) ),
    introduced(choice_axiom,[])).

fof(f38,plain,
    ( ? [X2] :
        ( ( ~ r1_waybel_7(sK3,sK4,X2)
          | ~ r3_waybel_9(sK3,k3_yellow19(sK3,k2_struct_0(sK3),sK4),X2) )
        & ( r1_waybel_7(sK3,sK4,X2)
          | r3_waybel_9(sK3,k3_yellow19(sK3,k2_struct_0(sK3),sK4),X2) )
        & m1_subset_1(X2,u1_struct_0(sK3)) )
   => ( ( ~ r1_waybel_7(sK3,sK4,sK5)
        | ~ r3_waybel_9(sK3,k3_yellow19(sK3,k2_struct_0(sK3),sK4),sK5) )
      & ( r1_waybel_7(sK3,sK4,sK5)
        | r3_waybel_9(sK3,k3_yellow19(sK3,k2_struct_0(sK3),sK4),sK5) )
      & m1_subset_1(sK5,u1_struct_0(sK3)) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,(
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
    inference(flattening,[],[f34])).

fof(f34,plain,(
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
    inference(nnf_transformation,[],[f13])).

fof(f13,plain,(
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
    inference(flattening,[],[f12])).

fof(f12,plain,(
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
    inference(ennf_transformation,[],[f11])).

fof(f11,negated_conjecture,(
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
    inference(negated_conjecture,[],[f10])).

fof(f10,conjecture,(
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

fof(f178,plain,(
    v2_struct_0(sK3) ),
    inference(subsumption_resolution,[],[f177,f86])).

fof(f86,plain,(
    l1_struct_0(sK3) ),
    inference(resolution,[],[f59,f49])).

fof(f49,plain,(
    l1_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f39])).

fof(f59,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(f177,plain,
    ( ~ l1_struct_0(sK3)
    | v2_struct_0(sK3) ),
    inference(resolution,[],[f174,f63])).

fof(f63,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k2_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k2_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k2_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(k2_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc5_struct_0)).

fof(f174,plain,(
    v1_xboole_0(k2_struct_0(sK3)) ),
    inference(subsumption_resolution,[],[f171,f122])).

fof(f122,plain,
    ( sP2(sK4,k2_struct_0(sK3),sK3)
    | v1_xboole_0(k2_struct_0(sK3)) ),
    inference(subsumption_resolution,[],[f121,f47])).

fof(f121,plain,
    ( sP2(sK4,k2_struct_0(sK3),sK3)
    | v1_xboole_0(k2_struct_0(sK3))
    | v2_struct_0(sK3) ),
    inference(subsumption_resolution,[],[f120,f86])).

fof(f120,plain,
    ( sP2(sK4,k2_struct_0(sK3),sK3)
    | v1_xboole_0(k2_struct_0(sK3))
    | ~ l1_struct_0(sK3)
    | v2_struct_0(sK3) ),
    inference(resolution,[],[f119,f88])).

fof(f88,plain,(
    m1_subset_1(k2_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK3))) ),
    inference(resolution,[],[f60,f86])).

fof(f60,plain,(
    ! [X0] :
      ( ~ l1_struct_0(X0)
      | m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_struct_0)).

fof(f119,plain,(
    ! [X0] :
      ( ~ m1_subset_1(k2_struct_0(sK3),k1_zfmisc_1(u1_struct_0(X0)))
      | sP2(sK4,k2_struct_0(sK3),X0)
      | v1_xboole_0(k2_struct_0(sK3))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f118,f50])).

fof(f50,plain,(
    ~ v1_xboole_0(sK4) ),
    inference(cnf_transformation,[],[f39])).

fof(f118,plain,(
    ! [X0] :
      ( sP2(sK4,k2_struct_0(sK3),X0)
      | v1_xboole_0(sK4)
      | ~ m1_subset_1(k2_struct_0(sK3),k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(k2_struct_0(sK3))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f117,f81])).

fof(f81,plain,(
    v1_subset_1(sK4,u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK3))))) ),
    inference(definition_unfolding,[],[f51,f58])).

fof(f58,plain,(
    ! [X0] : k3_yellow_1(X0) = k3_lattice3(k1_lattice3(X0)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : k3_yellow_1(X0) = k3_lattice3(k1_lattice3(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_yellow_1)).

fof(f51,plain,(
    v1_subset_1(sK4,u1_struct_0(k3_yellow_1(k2_struct_0(sK3)))) ),
    inference(cnf_transformation,[],[f39])).

fof(f117,plain,(
    ! [X0] :
      ( sP2(sK4,k2_struct_0(sK3),X0)
      | ~ v1_subset_1(sK4,u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK3)))))
      | v1_xboole_0(sK4)
      | ~ m1_subset_1(k2_struct_0(sK3),k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(k2_struct_0(sK3))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f116,f80])).

fof(f80,plain,(
    v2_waybel_0(sK4,k3_lattice3(k1_lattice3(k2_struct_0(sK3)))) ),
    inference(definition_unfolding,[],[f52,f58])).

fof(f52,plain,(
    v2_waybel_0(sK4,k3_yellow_1(k2_struct_0(sK3))) ),
    inference(cnf_transformation,[],[f39])).

fof(f116,plain,(
    ! [X0] :
      ( sP2(sK4,k2_struct_0(sK3),X0)
      | ~ v2_waybel_0(sK4,k3_lattice3(k1_lattice3(k2_struct_0(sK3))))
      | ~ v1_subset_1(sK4,u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK3)))))
      | v1_xboole_0(sK4)
      | ~ m1_subset_1(k2_struct_0(sK3),k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(k2_struct_0(sK3))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f115,f79])).

fof(f79,plain,(
    v13_waybel_0(sK4,k3_lattice3(k1_lattice3(k2_struct_0(sK3)))) ),
    inference(definition_unfolding,[],[f53,f58])).

fof(f53,plain,(
    v13_waybel_0(sK4,k3_yellow_1(k2_struct_0(sK3))) ),
    inference(cnf_transformation,[],[f39])).

fof(f115,plain,(
    ! [X0] :
      ( sP2(sK4,k2_struct_0(sK3),X0)
      | ~ v13_waybel_0(sK4,k3_lattice3(k1_lattice3(k2_struct_0(sK3))))
      | ~ v2_waybel_0(sK4,k3_lattice3(k1_lattice3(k2_struct_0(sK3))))
      | ~ v1_subset_1(sK4,u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK3)))))
      | v1_xboole_0(sK4)
      | ~ m1_subset_1(k2_struct_0(sK3),k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(k2_struct_0(sK3))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(resolution,[],[f85,f78])).

fof(f78,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK3)))))) ),
    inference(definition_unfolding,[],[f54,f58])).

fof(f54,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK3))))) ),
    inference(cnf_transformation,[],[f39])).

fof(f85,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
      | sP2(X2,X1,X0)
      | ~ v13_waybel_0(X2,k3_lattice3(k1_lattice3(X1)))
      | ~ v2_waybel_0(X2,k3_lattice3(k1_lattice3(X1)))
      | ~ v1_subset_1(X2,u1_struct_0(k3_lattice3(k1_lattice3(X1))))
      | v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(definition_unfolding,[],[f77,f58,f58,f58,f58])).

fof(f77,plain,(
    ! [X2,X0,X1] :
      ( sP2(X2,X1,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1))))
      | ~ v13_waybel_0(X2,k3_yellow_1(X1))
      | ~ v2_waybel_0(X2,k3_yellow_1(X1))
      | ~ v1_subset_1(X2,u1_struct_0(k3_yellow_1(X1)))
      | v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( sP2(X2,X1,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1))))
      | ~ v13_waybel_0(X2,k3_yellow_1(X1))
      | ~ v2_waybel_0(X2,k3_yellow_1(X1))
      | ~ v1_subset_1(X2,u1_struct_0(k3_yellow_1(X1)))
      | v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(definition_folding,[],[f27,f32])).

fof(f32,plain,(
    ! [X2,X1,X0] :
      ( ( v7_waybel_0(k3_yellow19(X0,X1,X2))
        & v6_waybel_0(k3_yellow19(X0,X1,X2),X0)
        & ~ v2_struct_0(k3_yellow19(X0,X1,X2)) )
      | ~ sP2(X2,X1,X0) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).

fof(f27,plain,(
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
    inference(flattening,[],[f26])).

fof(f26,plain,(
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
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
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

fof(f171,plain,
    ( v1_xboole_0(k2_struct_0(sK3))
    | ~ sP2(sK4,k2_struct_0(sK3),sK3) ),
    inference(resolution,[],[f162,f74])).

fof(f74,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_struct_0(k3_yellow19(X2,X1,X0))
      | ~ sP2(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0,X1,X2] :
      ( ( v7_waybel_0(k3_yellow19(X2,X1,X0))
        & v6_waybel_0(k3_yellow19(X2,X1,X0),X2)
        & ~ v2_struct_0(k3_yellow19(X2,X1,X0)) )
      | ~ sP2(X0,X1,X2) ) ),
    inference(rectify,[],[f45])).

fof(f45,plain,(
    ! [X2,X1,X0] :
      ( ( v7_waybel_0(k3_yellow19(X0,X1,X2))
        & v6_waybel_0(k3_yellow19(X0,X1,X2),X0)
        & ~ v2_struct_0(k3_yellow19(X0,X1,X2)) )
      | ~ sP2(X2,X1,X0) ) ),
    inference(nnf_transformation,[],[f32])).

fof(f162,plain,
    ( v2_struct_0(k3_yellow19(sK3,k2_struct_0(sK3),sK4))
    | v1_xboole_0(k2_struct_0(sK3)) ),
    inference(subsumption_resolution,[],[f159,f143])).

fof(f143,plain,
    ( v2_struct_0(k3_yellow19(sK3,k2_struct_0(sK3),sK4))
    | v1_xboole_0(k2_struct_0(sK3))
    | r1_waybel_7(sK3,sK4,sK5) ),
    inference(subsumption_resolution,[],[f141,f124])).

fof(f124,plain,
    ( v7_waybel_0(k3_yellow19(sK3,k2_struct_0(sK3),sK4))
    | v1_xboole_0(k2_struct_0(sK3)) ),
    inference(resolution,[],[f122,f76])).

fof(f76,plain,(
    ! [X2,X0,X1] :
      ( ~ sP2(X0,X1,X2)
      | v7_waybel_0(k3_yellow19(X2,X1,X0)) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f141,plain,
    ( r1_waybel_7(sK3,sK4,sK5)
    | ~ v7_waybel_0(k3_yellow19(sK3,k2_struct_0(sK3),sK4))
    | v1_xboole_0(k2_struct_0(sK3))
    | v2_struct_0(k3_yellow19(sK3,k2_struct_0(sK3),sK4)) ),
    inference(duplicate_literal_removal,[],[f137])).

fof(f137,plain,
    ( r1_waybel_7(sK3,sK4,sK5)
    | ~ v7_waybel_0(k3_yellow19(sK3,k2_struct_0(sK3),sK4))
    | v1_xboole_0(k2_struct_0(sK3))
    | v2_struct_0(k3_yellow19(sK3,k2_struct_0(sK3),sK4))
    | r1_waybel_7(sK3,sK4,sK5) ),
    inference(backward_demodulation,[],[f114,f135])).

fof(f135,plain,(
    sK4 = k2_yellow19(sK3,k3_yellow19(sK3,k2_struct_0(sK3),sK4)) ),
    inference(subsumption_resolution,[],[f134,f47])).

fof(f134,plain,
    ( sK4 = k2_yellow19(sK3,k3_yellow19(sK3,k2_struct_0(sK3),sK4))
    | v2_struct_0(sK3) ),
    inference(subsumption_resolution,[],[f133,f86])).

fof(f133,plain,
    ( sK4 = k2_yellow19(sK3,k3_yellow19(sK3,k2_struct_0(sK3),sK4))
    | ~ l1_struct_0(sK3)
    | v2_struct_0(sK3) ),
    inference(subsumption_resolution,[],[f132,f50])).

fof(f132,plain,
    ( sK4 = k2_yellow19(sK3,k3_yellow19(sK3,k2_struct_0(sK3),sK4))
    | v1_xboole_0(sK4)
    | ~ l1_struct_0(sK3)
    | v2_struct_0(sK3) ),
    inference(subsumption_resolution,[],[f131,f81])).

fof(f131,plain,
    ( sK4 = k2_yellow19(sK3,k3_yellow19(sK3,k2_struct_0(sK3),sK4))
    | ~ v1_subset_1(sK4,u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK3)))))
    | v1_xboole_0(sK4)
    | ~ l1_struct_0(sK3)
    | v2_struct_0(sK3) ),
    inference(subsumption_resolution,[],[f130,f80])).

fof(f130,plain,
    ( sK4 = k2_yellow19(sK3,k3_yellow19(sK3,k2_struct_0(sK3),sK4))
    | ~ v2_waybel_0(sK4,k3_lattice3(k1_lattice3(k2_struct_0(sK3))))
    | ~ v1_subset_1(sK4,u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK3)))))
    | v1_xboole_0(sK4)
    | ~ l1_struct_0(sK3)
    | v2_struct_0(sK3) ),
    inference(subsumption_resolution,[],[f129,f79])).

fof(f129,plain,
    ( sK4 = k2_yellow19(sK3,k3_yellow19(sK3,k2_struct_0(sK3),sK4))
    | ~ v13_waybel_0(sK4,k3_lattice3(k1_lattice3(k2_struct_0(sK3))))
    | ~ v2_waybel_0(sK4,k3_lattice3(k1_lattice3(k2_struct_0(sK3))))
    | ~ v1_subset_1(sK4,u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK3)))))
    | v1_xboole_0(sK4)
    | ~ l1_struct_0(sK3)
    | v2_struct_0(sK3) ),
    inference(resolution,[],[f82,f78])).

fof(f82,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X0))))))
      | k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) = X1
      | ~ v13_waybel_0(X1,k3_lattice3(k1_lattice3(k2_struct_0(X0))))
      | ~ v2_waybel_0(X1,k3_lattice3(k1_lattice3(k2_struct_0(X0))))
      | ~ v1_subset_1(X1,u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X0)))))
      | v1_xboole_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(definition_unfolding,[],[f64,f58,f58,f58,f58])).

fof(f64,plain,(
    ! [X0,X1] :
      ( k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
      | ~ v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
      | ~ v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
      | ~ v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0))))
      | v1_xboole_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
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
    inference(flattening,[],[f20])).

fof(f20,plain,(
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
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
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

fof(f114,plain,
    ( ~ v7_waybel_0(k3_yellow19(sK3,k2_struct_0(sK3),sK4))
    | r1_waybel_7(sK3,k2_yellow19(sK3,k3_yellow19(sK3,k2_struct_0(sK3),sK4)),sK5)
    | v1_xboole_0(k2_struct_0(sK3))
    | v2_struct_0(k3_yellow19(sK3,k2_struct_0(sK3),sK4))
    | r1_waybel_7(sK3,sK4,sK5) ),
    inference(subsumption_resolution,[],[f113,f102])).

fof(f102,plain,
    ( v4_orders_2(k3_yellow19(sK3,k2_struct_0(sK3),sK4))
    | v1_xboole_0(k2_struct_0(sK3)) ),
    inference(resolution,[],[f100,f67])).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( ~ sP0(X0,X1,X2)
      | v4_orders_2(k3_yellow19(X0,X2,X1)) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1,X2] :
      ( ( v6_waybel_0(k3_yellow19(X0,X2,X1),X0)
        & v4_orders_2(k3_yellow19(X0,X2,X1))
        & v3_orders_2(k3_yellow19(X0,X2,X1))
        & ~ v2_struct_0(k3_yellow19(X0,X2,X1)) )
      | ~ sP0(X0,X1,X2) ) ),
    inference(rectify,[],[f41])).

fof(f41,plain,(
    ! [X0,X2,X1] :
      ( ( v6_waybel_0(k3_yellow19(X0,X1,X2),X0)
        & v4_orders_2(k3_yellow19(X0,X1,X2))
        & v3_orders_2(k3_yellow19(X0,X1,X2))
        & ~ v2_struct_0(k3_yellow19(X0,X1,X2)) )
      | ~ sP0(X0,X2,X1) ) ),
    inference(nnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X2,X1] :
      ( ( v6_waybel_0(k3_yellow19(X0,X1,X2),X0)
        & v4_orders_2(k3_yellow19(X0,X1,X2))
        & v3_orders_2(k3_yellow19(X0,X1,X2))
        & ~ v2_struct_0(k3_yellow19(X0,X1,X2)) )
      | ~ sP0(X0,X2,X1) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f100,plain,
    ( sP0(sK3,sK4,k2_struct_0(sK3))
    | v1_xboole_0(k2_struct_0(sK3)) ),
    inference(subsumption_resolution,[],[f99,f47])).

fof(f99,plain,
    ( sP0(sK3,sK4,k2_struct_0(sK3))
    | v1_xboole_0(k2_struct_0(sK3))
    | v2_struct_0(sK3) ),
    inference(subsumption_resolution,[],[f98,f86])).

fof(f98,plain,
    ( sP0(sK3,sK4,k2_struct_0(sK3))
    | v1_xboole_0(k2_struct_0(sK3))
    | ~ l1_struct_0(sK3)
    | v2_struct_0(sK3) ),
    inference(resolution,[],[f97,f88])).

fof(f97,plain,(
    ! [X0] :
      ( ~ m1_subset_1(k2_struct_0(sK3),k1_zfmisc_1(u1_struct_0(X0)))
      | sP0(X0,sK4,k2_struct_0(sK3))
      | v1_xboole_0(k2_struct_0(sK3))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f96,f50])).

fof(f96,plain,(
    ! [X0] :
      ( sP0(X0,sK4,k2_struct_0(sK3))
      | v1_xboole_0(sK4)
      | ~ m1_subset_1(k2_struct_0(sK3),k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(k2_struct_0(sK3))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f95,f80])).

fof(f95,plain,(
    ! [X0] :
      ( sP0(X0,sK4,k2_struct_0(sK3))
      | ~ v2_waybel_0(sK4,k3_lattice3(k1_lattice3(k2_struct_0(sK3))))
      | v1_xboole_0(sK4)
      | ~ m1_subset_1(k2_struct_0(sK3),k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(k2_struct_0(sK3))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f94,f79])).

fof(f94,plain,(
    ! [X0] :
      ( sP0(X0,sK4,k2_struct_0(sK3))
      | ~ v13_waybel_0(sK4,k3_lattice3(k1_lattice3(k2_struct_0(sK3))))
      | ~ v2_waybel_0(sK4,k3_lattice3(k1_lattice3(k2_struct_0(sK3))))
      | v1_xboole_0(sK4)
      | ~ m1_subset_1(k2_struct_0(sK3),k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(k2_struct_0(sK3))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(resolution,[],[f83,f78])).

fof(f83,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
      | sP0(X0,X2,X1)
      | ~ v13_waybel_0(X2,k3_lattice3(k1_lattice3(X1)))
      | ~ v2_waybel_0(X2,k3_lattice3(k1_lattice3(X1)))
      | v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(definition_unfolding,[],[f69,f58,f58,f58])).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( sP0(X0,X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1))))
      | ~ v13_waybel_0(X2,k3_yellow_1(X1))
      | ~ v2_waybel_0(X2,k3_yellow_1(X1))
      | v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( sP0(X0,X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1))))
      | ~ v13_waybel_0(X2,k3_yellow_1(X1))
      | ~ v2_waybel_0(X2,k3_yellow_1(X1))
      | v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(definition_folding,[],[f23,f28])).

fof(f23,plain,(
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
    inference(flattening,[],[f22])).

fof(f22,plain,(
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
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
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

fof(f113,plain,
    ( v1_xboole_0(k2_struct_0(sK3))
    | r1_waybel_7(sK3,k2_yellow19(sK3,k3_yellow19(sK3,k2_struct_0(sK3),sK4)),sK5)
    | ~ v7_waybel_0(k3_yellow19(sK3,k2_struct_0(sK3),sK4))
    | ~ v4_orders_2(k3_yellow19(sK3,k2_struct_0(sK3),sK4))
    | v2_struct_0(k3_yellow19(sK3,k2_struct_0(sK3),sK4))
    | r1_waybel_7(sK3,sK4,sK5) ),
    inference(resolution,[],[f111,f93])).

fof(f93,plain,
    ( ~ l1_waybel_0(k3_yellow19(sK3,k2_struct_0(sK3),sK4),sK3)
    | r1_waybel_7(sK3,k2_yellow19(sK3,k3_yellow19(sK3,k2_struct_0(sK3),sK4)),sK5)
    | ~ v7_waybel_0(k3_yellow19(sK3,k2_struct_0(sK3),sK4))
    | ~ v4_orders_2(k3_yellow19(sK3,k2_struct_0(sK3),sK4))
    | v2_struct_0(k3_yellow19(sK3,k2_struct_0(sK3),sK4))
    | r1_waybel_7(sK3,sK4,sK5) ),
    inference(subsumption_resolution,[],[f92,f47])).

fof(f92,plain,
    ( r1_waybel_7(sK3,k2_yellow19(sK3,k3_yellow19(sK3,k2_struct_0(sK3),sK4)),sK5)
    | ~ l1_waybel_0(k3_yellow19(sK3,k2_struct_0(sK3),sK4),sK3)
    | ~ v7_waybel_0(k3_yellow19(sK3,k2_struct_0(sK3),sK4))
    | ~ v4_orders_2(k3_yellow19(sK3,k2_struct_0(sK3),sK4))
    | v2_struct_0(k3_yellow19(sK3,k2_struct_0(sK3),sK4))
    | v2_struct_0(sK3)
    | r1_waybel_7(sK3,sK4,sK5) ),
    inference(subsumption_resolution,[],[f91,f48])).

fof(f48,plain,(
    v2_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f39])).

fof(f91,plain,
    ( r1_waybel_7(sK3,k2_yellow19(sK3,k3_yellow19(sK3,k2_struct_0(sK3),sK4)),sK5)
    | ~ l1_waybel_0(k3_yellow19(sK3,k2_struct_0(sK3),sK4),sK3)
    | ~ v7_waybel_0(k3_yellow19(sK3,k2_struct_0(sK3),sK4))
    | ~ v4_orders_2(k3_yellow19(sK3,k2_struct_0(sK3),sK4))
    | v2_struct_0(k3_yellow19(sK3,k2_struct_0(sK3),sK4))
    | ~ v2_pre_topc(sK3)
    | v2_struct_0(sK3)
    | r1_waybel_7(sK3,sK4,sK5) ),
    inference(subsumption_resolution,[],[f90,f49])).

fof(f90,plain,
    ( r1_waybel_7(sK3,k2_yellow19(sK3,k3_yellow19(sK3,k2_struct_0(sK3),sK4)),sK5)
    | ~ l1_waybel_0(k3_yellow19(sK3,k2_struct_0(sK3),sK4),sK3)
    | ~ v7_waybel_0(k3_yellow19(sK3,k2_struct_0(sK3),sK4))
    | ~ v4_orders_2(k3_yellow19(sK3,k2_struct_0(sK3),sK4))
    | v2_struct_0(k3_yellow19(sK3,k2_struct_0(sK3),sK4))
    | ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(sK3)
    | v2_struct_0(sK3)
    | r1_waybel_7(sK3,sK4,sK5) ),
    inference(subsumption_resolution,[],[f89,f55])).

fof(f55,plain,(
    m1_subset_1(sK5,u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f39])).

fof(f89,plain,
    ( r1_waybel_7(sK3,k2_yellow19(sK3,k3_yellow19(sK3,k2_struct_0(sK3),sK4)),sK5)
    | ~ m1_subset_1(sK5,u1_struct_0(sK3))
    | ~ l1_waybel_0(k3_yellow19(sK3,k2_struct_0(sK3),sK4),sK3)
    | ~ v7_waybel_0(k3_yellow19(sK3,k2_struct_0(sK3),sK4))
    | ~ v4_orders_2(k3_yellow19(sK3,k2_struct_0(sK3),sK4))
    | v2_struct_0(k3_yellow19(sK3,k2_struct_0(sK3),sK4))
    | ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(sK3)
    | v2_struct_0(sK3)
    | r1_waybel_7(sK3,sK4,sK5) ),
    inference(resolution,[],[f61,f56])).

fof(f56,plain,
    ( r3_waybel_9(sK3,k3_yellow19(sK3,k2_struct_0(sK3),sK4),sK5)
    | r1_waybel_7(sK3,sK4,sK5) ),
    inference(cnf_transformation,[],[f39])).

fof(f61,plain,(
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
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
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
    inference(nnf_transformation,[],[f17])).

fof(f17,plain,(
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
    inference(flattening,[],[f16])).

fof(f16,plain,(
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
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
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

fof(f111,plain,
    ( l1_waybel_0(k3_yellow19(sK3,k2_struct_0(sK3),sK4),sK3)
    | v1_xboole_0(k2_struct_0(sK3)) ),
    inference(resolution,[],[f110,f72])).

fof(f72,plain,(
    ! [X2,X0,X1] :
      ( ~ sP1(X0,X1,X2)
      | l1_waybel_0(k3_yellow19(X0,X2,X1),X0) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0,X1,X2] :
      ( ( l1_waybel_0(k3_yellow19(X0,X2,X1),X0)
        & v6_waybel_0(k3_yellow19(X0,X2,X1),X0)
        & ~ v2_struct_0(k3_yellow19(X0,X2,X1)) )
      | ~ sP1(X0,X1,X2) ) ),
    inference(rectify,[],[f43])).

fof(f43,plain,(
    ! [X0,X2,X1] :
      ( ( l1_waybel_0(k3_yellow19(X0,X1,X2),X0)
        & v6_waybel_0(k3_yellow19(X0,X1,X2),X0)
        & ~ v2_struct_0(k3_yellow19(X0,X1,X2)) )
      | ~ sP1(X0,X2,X1) ) ),
    inference(nnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X2,X1] :
      ( ( l1_waybel_0(k3_yellow19(X0,X1,X2),X0)
        & v6_waybel_0(k3_yellow19(X0,X1,X2),X0)
        & ~ v2_struct_0(k3_yellow19(X0,X1,X2)) )
      | ~ sP1(X0,X2,X1) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f110,plain,
    ( sP1(sK3,sK4,k2_struct_0(sK3))
    | v1_xboole_0(k2_struct_0(sK3)) ),
    inference(subsumption_resolution,[],[f109,f47])).

fof(f109,plain,
    ( sP1(sK3,sK4,k2_struct_0(sK3))
    | v1_xboole_0(k2_struct_0(sK3))
    | v2_struct_0(sK3) ),
    inference(subsumption_resolution,[],[f108,f86])).

fof(f108,plain,
    ( sP1(sK3,sK4,k2_struct_0(sK3))
    | v1_xboole_0(k2_struct_0(sK3))
    | ~ l1_struct_0(sK3)
    | v2_struct_0(sK3) ),
    inference(resolution,[],[f107,f88])).

fof(f107,plain,(
    ! [X0] :
      ( ~ m1_subset_1(k2_struct_0(sK3),k1_zfmisc_1(u1_struct_0(X0)))
      | sP1(X0,sK4,k2_struct_0(sK3))
      | v1_xboole_0(k2_struct_0(sK3))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f106,f50])).

fof(f106,plain,(
    ! [X0] :
      ( sP1(X0,sK4,k2_struct_0(sK3))
      | v1_xboole_0(sK4)
      | ~ m1_subset_1(k2_struct_0(sK3),k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(k2_struct_0(sK3))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f105,f80])).

fof(f105,plain,(
    ! [X0] :
      ( sP1(X0,sK4,k2_struct_0(sK3))
      | ~ v2_waybel_0(sK4,k3_lattice3(k1_lattice3(k2_struct_0(sK3))))
      | v1_xboole_0(sK4)
      | ~ m1_subset_1(k2_struct_0(sK3),k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(k2_struct_0(sK3))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f104,f79])).

fof(f104,plain,(
    ! [X0] :
      ( sP1(X0,sK4,k2_struct_0(sK3))
      | ~ v13_waybel_0(sK4,k3_lattice3(k1_lattice3(k2_struct_0(sK3))))
      | ~ v2_waybel_0(sK4,k3_lattice3(k1_lattice3(k2_struct_0(sK3))))
      | v1_xboole_0(sK4)
      | ~ m1_subset_1(k2_struct_0(sK3),k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(k2_struct_0(sK3))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(resolution,[],[f84,f78])).

fof(f84,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
      | sP1(X0,X2,X1)
      | ~ v13_waybel_0(X2,k3_lattice3(k1_lattice3(X1)))
      | ~ v2_waybel_0(X2,k3_lattice3(k1_lattice3(X1)))
      | v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(definition_unfolding,[],[f73,f58,f58,f58])).

fof(f73,plain,(
    ! [X2,X0,X1] :
      ( sP1(X0,X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1))))
      | ~ v13_waybel_0(X2,k3_yellow_1(X1))
      | ~ v2_waybel_0(X2,k3_yellow_1(X1))
      | v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( sP1(X0,X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1))))
      | ~ v13_waybel_0(X2,k3_yellow_1(X1))
      | ~ v2_waybel_0(X2,k3_yellow_1(X1))
      | v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(definition_folding,[],[f25,f30])).

fof(f25,plain,(
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
    inference(flattening,[],[f24])).

fof(f24,plain,(
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
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
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

fof(f159,plain,
    ( v2_struct_0(k3_yellow19(sK3,k2_struct_0(sK3),sK4))
    | v1_xboole_0(k2_struct_0(sK3))
    | ~ r1_waybel_7(sK3,sK4,sK5) ),
    inference(resolution,[],[f158,f57])).

fof(f57,plain,
    ( ~ r3_waybel_9(sK3,k3_yellow19(sK3,k2_struct_0(sK3),sK4),sK5)
    | ~ r1_waybel_7(sK3,sK4,sK5) ),
    inference(cnf_transformation,[],[f39])).

fof(f158,plain,
    ( r3_waybel_9(sK3,k3_yellow19(sK3,k2_struct_0(sK3),sK4),sK5)
    | v2_struct_0(k3_yellow19(sK3,k2_struct_0(sK3),sK4))
    | v1_xboole_0(k2_struct_0(sK3)) ),
    inference(subsumption_resolution,[],[f157,f102])).

fof(f157,plain,
    ( r3_waybel_9(sK3,k3_yellow19(sK3,k2_struct_0(sK3),sK4),sK5)
    | ~ v4_orders_2(k3_yellow19(sK3,k2_struct_0(sK3),sK4))
    | v2_struct_0(k3_yellow19(sK3,k2_struct_0(sK3),sK4))
    | v1_xboole_0(k2_struct_0(sK3)) ),
    inference(subsumption_resolution,[],[f156,f124])).

fof(f156,plain,
    ( r3_waybel_9(sK3,k3_yellow19(sK3,k2_struct_0(sK3),sK4),sK5)
    | ~ v7_waybel_0(k3_yellow19(sK3,k2_struct_0(sK3),sK4))
    | ~ v4_orders_2(k3_yellow19(sK3,k2_struct_0(sK3),sK4))
    | v2_struct_0(k3_yellow19(sK3,k2_struct_0(sK3),sK4))
    | v1_xboole_0(k2_struct_0(sK3)) ),
    inference(subsumption_resolution,[],[f155,f111])).

fof(f155,plain,
    ( r3_waybel_9(sK3,k3_yellow19(sK3,k2_struct_0(sK3),sK4),sK5)
    | ~ l1_waybel_0(k3_yellow19(sK3,k2_struct_0(sK3),sK4),sK3)
    | ~ v7_waybel_0(k3_yellow19(sK3,k2_struct_0(sK3),sK4))
    | ~ v4_orders_2(k3_yellow19(sK3,k2_struct_0(sK3),sK4))
    | v2_struct_0(k3_yellow19(sK3,k2_struct_0(sK3),sK4))
    | v1_xboole_0(k2_struct_0(sK3)) ),
    inference(subsumption_resolution,[],[f154,f55])).

fof(f154,plain,
    ( r3_waybel_9(sK3,k3_yellow19(sK3,k2_struct_0(sK3),sK4),sK5)
    | ~ m1_subset_1(sK5,u1_struct_0(sK3))
    | ~ l1_waybel_0(k3_yellow19(sK3,k2_struct_0(sK3),sK4),sK3)
    | ~ v7_waybel_0(k3_yellow19(sK3,k2_struct_0(sK3),sK4))
    | ~ v4_orders_2(k3_yellow19(sK3,k2_struct_0(sK3),sK4))
    | v2_struct_0(k3_yellow19(sK3,k2_struct_0(sK3),sK4))
    | v1_xboole_0(k2_struct_0(sK3)) ),
    inference(resolution,[],[f146,f150])).

fof(f150,plain,
    ( r1_waybel_7(sK3,sK4,sK5)
    | v1_xboole_0(k2_struct_0(sK3)) ),
    inference(subsumption_resolution,[],[f147,f122])).

fof(f147,plain,
    ( v1_xboole_0(k2_struct_0(sK3))
    | r1_waybel_7(sK3,sK4,sK5)
    | ~ sP2(sK4,k2_struct_0(sK3),sK3) ),
    inference(resolution,[],[f143,f74])).

fof(f146,plain,(
    ! [X0] :
      ( ~ r1_waybel_7(sK3,sK4,X0)
      | r3_waybel_9(sK3,k3_yellow19(sK3,k2_struct_0(sK3),sK4),X0)
      | ~ m1_subset_1(X0,u1_struct_0(sK3))
      | ~ l1_waybel_0(k3_yellow19(sK3,k2_struct_0(sK3),sK4),sK3)
      | ~ v7_waybel_0(k3_yellow19(sK3,k2_struct_0(sK3),sK4))
      | ~ v4_orders_2(k3_yellow19(sK3,k2_struct_0(sK3),sK4))
      | v2_struct_0(k3_yellow19(sK3,k2_struct_0(sK3),sK4)) ) ),
    inference(subsumption_resolution,[],[f145,f47])).

fof(f145,plain,(
    ! [X0] :
      ( ~ r1_waybel_7(sK3,sK4,X0)
      | r3_waybel_9(sK3,k3_yellow19(sK3,k2_struct_0(sK3),sK4),X0)
      | ~ m1_subset_1(X0,u1_struct_0(sK3))
      | ~ l1_waybel_0(k3_yellow19(sK3,k2_struct_0(sK3),sK4),sK3)
      | ~ v7_waybel_0(k3_yellow19(sK3,k2_struct_0(sK3),sK4))
      | ~ v4_orders_2(k3_yellow19(sK3,k2_struct_0(sK3),sK4))
      | v2_struct_0(k3_yellow19(sK3,k2_struct_0(sK3),sK4))
      | v2_struct_0(sK3) ) ),
    inference(subsumption_resolution,[],[f144,f48])).

fof(f144,plain,(
    ! [X0] :
      ( ~ r1_waybel_7(sK3,sK4,X0)
      | r3_waybel_9(sK3,k3_yellow19(sK3,k2_struct_0(sK3),sK4),X0)
      | ~ m1_subset_1(X0,u1_struct_0(sK3))
      | ~ l1_waybel_0(k3_yellow19(sK3,k2_struct_0(sK3),sK4),sK3)
      | ~ v7_waybel_0(k3_yellow19(sK3,k2_struct_0(sK3),sK4))
      | ~ v4_orders_2(k3_yellow19(sK3,k2_struct_0(sK3),sK4))
      | v2_struct_0(k3_yellow19(sK3,k2_struct_0(sK3),sK4))
      | ~ v2_pre_topc(sK3)
      | v2_struct_0(sK3) ) ),
    inference(subsumption_resolution,[],[f139,f49])).

fof(f139,plain,(
    ! [X0] :
      ( ~ r1_waybel_7(sK3,sK4,X0)
      | r3_waybel_9(sK3,k3_yellow19(sK3,k2_struct_0(sK3),sK4),X0)
      | ~ m1_subset_1(X0,u1_struct_0(sK3))
      | ~ l1_waybel_0(k3_yellow19(sK3,k2_struct_0(sK3),sK4),sK3)
      | ~ v7_waybel_0(k3_yellow19(sK3,k2_struct_0(sK3),sK4))
      | ~ v4_orders_2(k3_yellow19(sK3,k2_struct_0(sK3),sK4))
      | v2_struct_0(k3_yellow19(sK3,k2_struct_0(sK3),sK4))
      | ~ l1_pre_topc(sK3)
      | ~ v2_pre_topc(sK3)
      | v2_struct_0(sK3) ) ),
    inference(superposition,[],[f62,f135])).

fof(f62,plain,(
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
    inference(cnf_transformation,[],[f40])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.12  % Command    : run_vampire %s %d
% 0.11/0.33  % Computer   : n007.cluster.edu
% 0.11/0.33  % Model      : x86_64 x86_64
% 0.11/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.11/0.33  % Memory     : 8042.1875MB
% 0.11/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.11/0.33  % CPULimit   : 60
% 0.11/0.33  % WCLimit    : 600
% 0.11/0.33  % DateTime   : Tue Dec  1 17:30:51 EST 2020
% 0.11/0.33  % CPUTime    : 
% 0.19/0.39  % (25769)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.19/0.39  % (25769)Refutation found. Thanks to Tanya!
% 0.19/0.39  % SZS status Theorem for theBenchmark
% 0.19/0.39  % SZS output start Proof for theBenchmark
% 0.19/0.39  fof(f179,plain,(
% 0.19/0.39    $false),
% 0.19/0.39    inference(subsumption_resolution,[],[f178,f47])).
% 0.19/0.39  fof(f47,plain,(
% 0.19/0.39    ~v2_struct_0(sK3)),
% 0.19/0.39    inference(cnf_transformation,[],[f39])).
% 0.19/0.39  fof(f39,plain,(
% 0.19/0.39    (((~r1_waybel_7(sK3,sK4,sK5) | ~r3_waybel_9(sK3,k3_yellow19(sK3,k2_struct_0(sK3),sK4),sK5)) & (r1_waybel_7(sK3,sK4,sK5) | r3_waybel_9(sK3,k3_yellow19(sK3,k2_struct_0(sK3),sK4),sK5)) & m1_subset_1(sK5,u1_struct_0(sK3))) & m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK3))))) & v13_waybel_0(sK4,k3_yellow_1(k2_struct_0(sK3))) & v2_waybel_0(sK4,k3_yellow_1(k2_struct_0(sK3))) & v1_subset_1(sK4,u1_struct_0(k3_yellow_1(k2_struct_0(sK3)))) & ~v1_xboole_0(sK4)) & l1_pre_topc(sK3) & v2_pre_topc(sK3) & ~v2_struct_0(sK3)),
% 0.19/0.39    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5])],[f35,f38,f37,f36])).
% 0.19/0.39  fof(f36,plain,(
% 0.19/0.39    ? [X0] : (? [X1] : (? [X2] : ((~r1_waybel_7(X0,X1,X2) | ~r3_waybel_9(X0,k3_yellow19(X0,k2_struct_0(X0),X1),X2)) & (r1_waybel_7(X0,X1,X2) | r3_waybel_9(X0,k3_yellow19(X0,k2_struct_0(X0),X1),X2)) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) & ~v1_xboole_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : ((~r1_waybel_7(sK3,X1,X2) | ~r3_waybel_9(sK3,k3_yellow19(sK3,k2_struct_0(sK3),X1),X2)) & (r1_waybel_7(sK3,X1,X2) | r3_waybel_9(sK3,k3_yellow19(sK3,k2_struct_0(sK3),X1),X2)) & m1_subset_1(X2,u1_struct_0(sK3))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK3))))) & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(sK3))) & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(sK3))) & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(sK3)))) & ~v1_xboole_0(X1)) & l1_pre_topc(sK3) & v2_pre_topc(sK3) & ~v2_struct_0(sK3))),
% 0.19/0.39    introduced(choice_axiom,[])).
% 0.19/0.39  fof(f37,plain,(
% 0.19/0.39    ? [X1] : (? [X2] : ((~r1_waybel_7(sK3,X1,X2) | ~r3_waybel_9(sK3,k3_yellow19(sK3,k2_struct_0(sK3),X1),X2)) & (r1_waybel_7(sK3,X1,X2) | r3_waybel_9(sK3,k3_yellow19(sK3,k2_struct_0(sK3),X1),X2)) & m1_subset_1(X2,u1_struct_0(sK3))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK3))))) & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(sK3))) & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(sK3))) & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(sK3)))) & ~v1_xboole_0(X1)) => (? [X2] : ((~r1_waybel_7(sK3,sK4,X2) | ~r3_waybel_9(sK3,k3_yellow19(sK3,k2_struct_0(sK3),sK4),X2)) & (r1_waybel_7(sK3,sK4,X2) | r3_waybel_9(sK3,k3_yellow19(sK3,k2_struct_0(sK3),sK4),X2)) & m1_subset_1(X2,u1_struct_0(sK3))) & m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK3))))) & v13_waybel_0(sK4,k3_yellow_1(k2_struct_0(sK3))) & v2_waybel_0(sK4,k3_yellow_1(k2_struct_0(sK3))) & v1_subset_1(sK4,u1_struct_0(k3_yellow_1(k2_struct_0(sK3)))) & ~v1_xboole_0(sK4))),
% 0.19/0.39    introduced(choice_axiom,[])).
% 0.19/0.39  fof(f38,plain,(
% 0.19/0.39    ? [X2] : ((~r1_waybel_7(sK3,sK4,X2) | ~r3_waybel_9(sK3,k3_yellow19(sK3,k2_struct_0(sK3),sK4),X2)) & (r1_waybel_7(sK3,sK4,X2) | r3_waybel_9(sK3,k3_yellow19(sK3,k2_struct_0(sK3),sK4),X2)) & m1_subset_1(X2,u1_struct_0(sK3))) => ((~r1_waybel_7(sK3,sK4,sK5) | ~r3_waybel_9(sK3,k3_yellow19(sK3,k2_struct_0(sK3),sK4),sK5)) & (r1_waybel_7(sK3,sK4,sK5) | r3_waybel_9(sK3,k3_yellow19(sK3,k2_struct_0(sK3),sK4),sK5)) & m1_subset_1(sK5,u1_struct_0(sK3)))),
% 0.19/0.39    introduced(choice_axiom,[])).
% 0.19/0.39  fof(f35,plain,(
% 0.19/0.39    ? [X0] : (? [X1] : (? [X2] : ((~r1_waybel_7(X0,X1,X2) | ~r3_waybel_9(X0,k3_yellow19(X0,k2_struct_0(X0),X1),X2)) & (r1_waybel_7(X0,X1,X2) | r3_waybel_9(X0,k3_yellow19(X0,k2_struct_0(X0),X1),X2)) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) & ~v1_xboole_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.19/0.39    inference(flattening,[],[f34])).
% 0.19/0.39  fof(f34,plain,(
% 0.19/0.39    ? [X0] : (? [X1] : (? [X2] : (((~r1_waybel_7(X0,X1,X2) | ~r3_waybel_9(X0,k3_yellow19(X0,k2_struct_0(X0),X1),X2)) & (r1_waybel_7(X0,X1,X2) | r3_waybel_9(X0,k3_yellow19(X0,k2_struct_0(X0),X1),X2))) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) & ~v1_xboole_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.19/0.39    inference(nnf_transformation,[],[f13])).
% 0.19/0.39  fof(f13,plain,(
% 0.19/0.39    ? [X0] : (? [X1] : (? [X2] : ((r3_waybel_9(X0,k3_yellow19(X0,k2_struct_0(X0),X1),X2) <~> r1_waybel_7(X0,X1,X2)) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) & ~v1_xboole_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.19/0.39    inference(flattening,[],[f12])).
% 0.19/0.39  fof(f12,plain,(
% 0.19/0.39    ? [X0] : (? [X1] : (? [X2] : ((r3_waybel_9(X0,k3_yellow19(X0,k2_struct_0(X0),X1),X2) <~> r1_waybel_7(X0,X1,X2)) & m1_subset_1(X2,u1_struct_0(X0))) & (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) & ~v1_xboole_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 0.19/0.39    inference(ennf_transformation,[],[f11])).
% 0.19/0.39  fof(f11,negated_conjecture,(
% 0.19/0.39    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) & ~v1_xboole_0(X1)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r3_waybel_9(X0,k3_yellow19(X0,k2_struct_0(X0),X1),X2) <=> r1_waybel_7(X0,X1,X2)))))),
% 0.19/0.39    inference(negated_conjecture,[],[f10])).
% 0.19/0.39  fof(f10,conjecture,(
% 0.19/0.39    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) & ~v1_xboole_0(X1)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r3_waybel_9(X0,k3_yellow19(X0,k2_struct_0(X0),X1),X2) <=> r1_waybel_7(X0,X1,X2)))))),
% 0.19/0.39    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_yellow19)).
% 0.19/0.39  fof(f178,plain,(
% 0.19/0.39    v2_struct_0(sK3)),
% 0.19/0.39    inference(subsumption_resolution,[],[f177,f86])).
% 0.19/0.39  fof(f86,plain,(
% 0.19/0.39    l1_struct_0(sK3)),
% 0.19/0.39    inference(resolution,[],[f59,f49])).
% 0.19/0.39  fof(f49,plain,(
% 0.19/0.39    l1_pre_topc(sK3)),
% 0.19/0.39    inference(cnf_transformation,[],[f39])).
% 0.19/0.39  fof(f59,plain,(
% 0.19/0.39    ( ! [X0] : (~l1_pre_topc(X0) | l1_struct_0(X0)) )),
% 0.19/0.39    inference(cnf_transformation,[],[f14])).
% 0.19/0.39  fof(f14,plain,(
% 0.19/0.39    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 0.19/0.39    inference(ennf_transformation,[],[f2])).
% 0.19/0.39  fof(f2,axiom,(
% 0.19/0.39    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 0.19/0.39    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).
% 0.19/0.39  fof(f177,plain,(
% 0.19/0.39    ~l1_struct_0(sK3) | v2_struct_0(sK3)),
% 0.19/0.39    inference(resolution,[],[f174,f63])).
% 0.19/0.39  fof(f63,plain,(
% 0.19/0.39    ( ! [X0] : (~v1_xboole_0(k2_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 0.19/0.39    inference(cnf_transformation,[],[f19])).
% 0.19/0.39  fof(f19,plain,(
% 0.19/0.39    ! [X0] : (~v1_xboole_0(k2_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 0.19/0.39    inference(flattening,[],[f18])).
% 0.19/0.39  fof(f18,plain,(
% 0.19/0.39    ! [X0] : (~v1_xboole_0(k2_struct_0(X0)) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 0.19/0.39    inference(ennf_transformation,[],[f3])).
% 0.19/0.39  fof(f3,axiom,(
% 0.19/0.39    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ~v1_xboole_0(k2_struct_0(X0)))),
% 0.19/0.39    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc5_struct_0)).
% 0.19/0.39  fof(f174,plain,(
% 0.19/0.39    v1_xboole_0(k2_struct_0(sK3))),
% 0.19/0.39    inference(subsumption_resolution,[],[f171,f122])).
% 0.19/0.39  fof(f122,plain,(
% 0.19/0.39    sP2(sK4,k2_struct_0(sK3),sK3) | v1_xboole_0(k2_struct_0(sK3))),
% 0.19/0.39    inference(subsumption_resolution,[],[f121,f47])).
% 0.19/0.39  fof(f121,plain,(
% 0.19/0.39    sP2(sK4,k2_struct_0(sK3),sK3) | v1_xboole_0(k2_struct_0(sK3)) | v2_struct_0(sK3)),
% 0.19/0.39    inference(subsumption_resolution,[],[f120,f86])).
% 0.19/0.39  fof(f120,plain,(
% 0.19/0.39    sP2(sK4,k2_struct_0(sK3),sK3) | v1_xboole_0(k2_struct_0(sK3)) | ~l1_struct_0(sK3) | v2_struct_0(sK3)),
% 0.19/0.39    inference(resolution,[],[f119,f88])).
% 0.19/0.39  fof(f88,plain,(
% 0.19/0.39    m1_subset_1(k2_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK3)))),
% 0.19/0.39    inference(resolution,[],[f60,f86])).
% 0.19/0.39  fof(f60,plain,(
% 0.19/0.39    ( ! [X0] : (~l1_struct_0(X0) | m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0)))) )),
% 0.19/0.39    inference(cnf_transformation,[],[f15])).
% 0.19/0.39  fof(f15,plain,(
% 0.19/0.39    ! [X0] : (m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0))) | ~l1_struct_0(X0))),
% 0.19/0.39    inference(ennf_transformation,[],[f1])).
% 0.19/0.39  fof(f1,axiom,(
% 0.19/0.39    ! [X0] : (l1_struct_0(X0) => m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0))))),
% 0.19/0.39    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_struct_0)).
% 0.19/0.39  fof(f119,plain,(
% 0.19/0.39    ( ! [X0] : (~m1_subset_1(k2_struct_0(sK3),k1_zfmisc_1(u1_struct_0(X0))) | sP2(sK4,k2_struct_0(sK3),X0) | v1_xboole_0(k2_struct_0(sK3)) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 0.19/0.39    inference(subsumption_resolution,[],[f118,f50])).
% 0.19/0.39  fof(f50,plain,(
% 0.19/0.39    ~v1_xboole_0(sK4)),
% 0.19/0.39    inference(cnf_transformation,[],[f39])).
% 0.19/0.39  fof(f118,plain,(
% 0.19/0.39    ( ! [X0] : (sP2(sK4,k2_struct_0(sK3),X0) | v1_xboole_0(sK4) | ~m1_subset_1(k2_struct_0(sK3),k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(k2_struct_0(sK3)) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 0.19/0.39    inference(subsumption_resolution,[],[f117,f81])).
% 0.19/0.39  fof(f81,plain,(
% 0.19/0.39    v1_subset_1(sK4,u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK3)))))),
% 0.19/0.39    inference(definition_unfolding,[],[f51,f58])).
% 0.19/0.39  fof(f58,plain,(
% 0.19/0.39    ( ! [X0] : (k3_yellow_1(X0) = k3_lattice3(k1_lattice3(X0))) )),
% 0.19/0.39    inference(cnf_transformation,[],[f4])).
% 0.19/0.39  fof(f4,axiom,(
% 0.19/0.39    ! [X0] : k3_yellow_1(X0) = k3_lattice3(k1_lattice3(X0))),
% 0.19/0.39    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_yellow_1)).
% 0.19/0.39  fof(f51,plain,(
% 0.19/0.39    v1_subset_1(sK4,u1_struct_0(k3_yellow_1(k2_struct_0(sK3))))),
% 0.19/0.39    inference(cnf_transformation,[],[f39])).
% 0.19/0.39  fof(f117,plain,(
% 0.19/0.39    ( ! [X0] : (sP2(sK4,k2_struct_0(sK3),X0) | ~v1_subset_1(sK4,u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK3))))) | v1_xboole_0(sK4) | ~m1_subset_1(k2_struct_0(sK3),k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(k2_struct_0(sK3)) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 0.19/0.39    inference(subsumption_resolution,[],[f116,f80])).
% 0.19/0.39  fof(f80,plain,(
% 0.19/0.39    v2_waybel_0(sK4,k3_lattice3(k1_lattice3(k2_struct_0(sK3))))),
% 0.19/0.39    inference(definition_unfolding,[],[f52,f58])).
% 0.19/0.39  fof(f52,plain,(
% 0.19/0.39    v2_waybel_0(sK4,k3_yellow_1(k2_struct_0(sK3)))),
% 0.19/0.39    inference(cnf_transformation,[],[f39])).
% 0.19/0.39  fof(f116,plain,(
% 0.19/0.39    ( ! [X0] : (sP2(sK4,k2_struct_0(sK3),X0) | ~v2_waybel_0(sK4,k3_lattice3(k1_lattice3(k2_struct_0(sK3)))) | ~v1_subset_1(sK4,u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK3))))) | v1_xboole_0(sK4) | ~m1_subset_1(k2_struct_0(sK3),k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(k2_struct_0(sK3)) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 0.19/0.39    inference(subsumption_resolution,[],[f115,f79])).
% 0.19/0.39  fof(f79,plain,(
% 0.19/0.39    v13_waybel_0(sK4,k3_lattice3(k1_lattice3(k2_struct_0(sK3))))),
% 0.19/0.39    inference(definition_unfolding,[],[f53,f58])).
% 0.19/0.39  fof(f53,plain,(
% 0.19/0.39    v13_waybel_0(sK4,k3_yellow_1(k2_struct_0(sK3)))),
% 0.19/0.39    inference(cnf_transformation,[],[f39])).
% 0.19/0.39  fof(f115,plain,(
% 0.19/0.39    ( ! [X0] : (sP2(sK4,k2_struct_0(sK3),X0) | ~v13_waybel_0(sK4,k3_lattice3(k1_lattice3(k2_struct_0(sK3)))) | ~v2_waybel_0(sK4,k3_lattice3(k1_lattice3(k2_struct_0(sK3)))) | ~v1_subset_1(sK4,u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK3))))) | v1_xboole_0(sK4) | ~m1_subset_1(k2_struct_0(sK3),k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(k2_struct_0(sK3)) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 0.19/0.39    inference(resolution,[],[f85,f78])).
% 0.19/0.39  fof(f78,plain,(
% 0.19/0.39    m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK3))))))),
% 0.19/0.39    inference(definition_unfolding,[],[f54,f58])).
% 0.19/0.39  fof(f54,plain,(
% 0.19/0.39    m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK3)))))),
% 0.19/0.39    inference(cnf_transformation,[],[f39])).
% 0.19/0.39  fof(f85,plain,(
% 0.19/0.39    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1))))) | sP2(X2,X1,X0) | ~v13_waybel_0(X2,k3_lattice3(k1_lattice3(X1))) | ~v2_waybel_0(X2,k3_lattice3(k1_lattice3(X1))) | ~v1_subset_1(X2,u1_struct_0(k3_lattice3(k1_lattice3(X1)))) | v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 0.19/0.39    inference(definition_unfolding,[],[f77,f58,f58,f58,f58])).
% 0.19/0.39  fof(f77,plain,(
% 0.19/0.39    ( ! [X2,X0,X1] : (sP2(X2,X1,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1)))) | ~v13_waybel_0(X2,k3_yellow_1(X1)) | ~v2_waybel_0(X2,k3_yellow_1(X1)) | ~v1_subset_1(X2,u1_struct_0(k3_yellow_1(X1))) | v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 0.19/0.39    inference(cnf_transformation,[],[f33])).
% 0.19/0.39  fof(f33,plain,(
% 0.19/0.39    ! [X0,X1,X2] : (sP2(X2,X1,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1)))) | ~v13_waybel_0(X2,k3_yellow_1(X1)) | ~v2_waybel_0(X2,k3_yellow_1(X1)) | ~v1_subset_1(X2,u1_struct_0(k3_yellow_1(X1))) | v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 0.19/0.39    inference(definition_folding,[],[f27,f32])).
% 0.19/0.39  fof(f32,plain,(
% 0.19/0.39    ! [X2,X1,X0] : ((v7_waybel_0(k3_yellow19(X0,X1,X2)) & v6_waybel_0(k3_yellow19(X0,X1,X2),X0) & ~v2_struct_0(k3_yellow19(X0,X1,X2))) | ~sP2(X2,X1,X0))),
% 0.19/0.39    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).
% 0.19/0.39  fof(f27,plain,(
% 0.19/0.39    ! [X0,X1,X2] : ((v7_waybel_0(k3_yellow19(X0,X1,X2)) & v6_waybel_0(k3_yellow19(X0,X1,X2),X0) & ~v2_struct_0(k3_yellow19(X0,X1,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1)))) | ~v13_waybel_0(X2,k3_yellow_1(X1)) | ~v2_waybel_0(X2,k3_yellow_1(X1)) | ~v1_subset_1(X2,u1_struct_0(k3_yellow_1(X1))) | v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 0.19/0.39    inference(flattening,[],[f26])).
% 0.19/0.39  fof(f26,plain,(
% 0.19/0.39    ! [X0,X1,X2] : ((v7_waybel_0(k3_yellow19(X0,X1,X2)) & v6_waybel_0(k3_yellow19(X0,X1,X2),X0) & ~v2_struct_0(k3_yellow19(X0,X1,X2))) | (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1)))) | ~v13_waybel_0(X2,k3_yellow_1(X1)) | ~v2_waybel_0(X2,k3_yellow_1(X1)) | ~v1_subset_1(X2,u1_struct_0(k3_yellow_1(X1))) | v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)))),
% 0.19/0.39    inference(ennf_transformation,[],[f7])).
% 0.19/0.39  fof(f7,axiom,(
% 0.19/0.39    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1)))) & v13_waybel_0(X2,k3_yellow_1(X1)) & v2_waybel_0(X2,k3_yellow_1(X1)) & v1_subset_1(X2,u1_struct_0(k3_yellow_1(X1))) & ~v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1) & l1_struct_0(X0) & ~v2_struct_0(X0)) => (v7_waybel_0(k3_yellow19(X0,X1,X2)) & v6_waybel_0(k3_yellow19(X0,X1,X2),X0) & ~v2_struct_0(k3_yellow19(X0,X1,X2))))),
% 0.19/0.39    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc5_yellow19)).
% 0.19/0.39  fof(f171,plain,(
% 0.19/0.39    v1_xboole_0(k2_struct_0(sK3)) | ~sP2(sK4,k2_struct_0(sK3),sK3)),
% 0.19/0.39    inference(resolution,[],[f162,f74])).
% 0.19/0.39  fof(f74,plain,(
% 0.19/0.39    ( ! [X2,X0,X1] : (~v2_struct_0(k3_yellow19(X2,X1,X0)) | ~sP2(X0,X1,X2)) )),
% 0.19/0.39    inference(cnf_transformation,[],[f46])).
% 0.19/0.39  fof(f46,plain,(
% 0.19/0.39    ! [X0,X1,X2] : ((v7_waybel_0(k3_yellow19(X2,X1,X0)) & v6_waybel_0(k3_yellow19(X2,X1,X0),X2) & ~v2_struct_0(k3_yellow19(X2,X1,X0))) | ~sP2(X0,X1,X2))),
% 0.19/0.39    inference(rectify,[],[f45])).
% 0.19/0.39  fof(f45,plain,(
% 0.19/0.39    ! [X2,X1,X0] : ((v7_waybel_0(k3_yellow19(X0,X1,X2)) & v6_waybel_0(k3_yellow19(X0,X1,X2),X0) & ~v2_struct_0(k3_yellow19(X0,X1,X2))) | ~sP2(X2,X1,X0))),
% 0.19/0.39    inference(nnf_transformation,[],[f32])).
% 0.19/0.39  fof(f162,plain,(
% 0.19/0.39    v2_struct_0(k3_yellow19(sK3,k2_struct_0(sK3),sK4)) | v1_xboole_0(k2_struct_0(sK3))),
% 0.19/0.39    inference(subsumption_resolution,[],[f159,f143])).
% 0.19/0.39  fof(f143,plain,(
% 0.19/0.39    v2_struct_0(k3_yellow19(sK3,k2_struct_0(sK3),sK4)) | v1_xboole_0(k2_struct_0(sK3)) | r1_waybel_7(sK3,sK4,sK5)),
% 0.19/0.39    inference(subsumption_resolution,[],[f141,f124])).
% 0.19/0.39  fof(f124,plain,(
% 0.19/0.39    v7_waybel_0(k3_yellow19(sK3,k2_struct_0(sK3),sK4)) | v1_xboole_0(k2_struct_0(sK3))),
% 0.19/0.39    inference(resolution,[],[f122,f76])).
% 0.19/0.39  fof(f76,plain,(
% 0.19/0.39    ( ! [X2,X0,X1] : (~sP2(X0,X1,X2) | v7_waybel_0(k3_yellow19(X2,X1,X0))) )),
% 0.19/0.39    inference(cnf_transformation,[],[f46])).
% 0.19/0.39  fof(f141,plain,(
% 0.19/0.39    r1_waybel_7(sK3,sK4,sK5) | ~v7_waybel_0(k3_yellow19(sK3,k2_struct_0(sK3),sK4)) | v1_xboole_0(k2_struct_0(sK3)) | v2_struct_0(k3_yellow19(sK3,k2_struct_0(sK3),sK4))),
% 0.19/0.39    inference(duplicate_literal_removal,[],[f137])).
% 0.19/0.39  fof(f137,plain,(
% 0.19/0.39    r1_waybel_7(sK3,sK4,sK5) | ~v7_waybel_0(k3_yellow19(sK3,k2_struct_0(sK3),sK4)) | v1_xboole_0(k2_struct_0(sK3)) | v2_struct_0(k3_yellow19(sK3,k2_struct_0(sK3),sK4)) | r1_waybel_7(sK3,sK4,sK5)),
% 0.19/0.39    inference(backward_demodulation,[],[f114,f135])).
% 0.19/0.39  fof(f135,plain,(
% 0.19/0.39    sK4 = k2_yellow19(sK3,k3_yellow19(sK3,k2_struct_0(sK3),sK4))),
% 0.19/0.39    inference(subsumption_resolution,[],[f134,f47])).
% 0.19/0.39  fof(f134,plain,(
% 0.19/0.39    sK4 = k2_yellow19(sK3,k3_yellow19(sK3,k2_struct_0(sK3),sK4)) | v2_struct_0(sK3)),
% 0.19/0.39    inference(subsumption_resolution,[],[f133,f86])).
% 0.19/0.39  fof(f133,plain,(
% 0.19/0.39    sK4 = k2_yellow19(sK3,k3_yellow19(sK3,k2_struct_0(sK3),sK4)) | ~l1_struct_0(sK3) | v2_struct_0(sK3)),
% 0.19/0.39    inference(subsumption_resolution,[],[f132,f50])).
% 0.19/0.39  fof(f132,plain,(
% 0.19/0.39    sK4 = k2_yellow19(sK3,k3_yellow19(sK3,k2_struct_0(sK3),sK4)) | v1_xboole_0(sK4) | ~l1_struct_0(sK3) | v2_struct_0(sK3)),
% 0.19/0.39    inference(subsumption_resolution,[],[f131,f81])).
% 0.19/0.39  fof(f131,plain,(
% 0.19/0.39    sK4 = k2_yellow19(sK3,k3_yellow19(sK3,k2_struct_0(sK3),sK4)) | ~v1_subset_1(sK4,u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK3))))) | v1_xboole_0(sK4) | ~l1_struct_0(sK3) | v2_struct_0(sK3)),
% 0.19/0.39    inference(subsumption_resolution,[],[f130,f80])).
% 0.19/0.39  fof(f130,plain,(
% 0.19/0.39    sK4 = k2_yellow19(sK3,k3_yellow19(sK3,k2_struct_0(sK3),sK4)) | ~v2_waybel_0(sK4,k3_lattice3(k1_lattice3(k2_struct_0(sK3)))) | ~v1_subset_1(sK4,u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK3))))) | v1_xboole_0(sK4) | ~l1_struct_0(sK3) | v2_struct_0(sK3)),
% 0.19/0.39    inference(subsumption_resolution,[],[f129,f79])).
% 0.19/0.39  fof(f129,plain,(
% 0.19/0.39    sK4 = k2_yellow19(sK3,k3_yellow19(sK3,k2_struct_0(sK3),sK4)) | ~v13_waybel_0(sK4,k3_lattice3(k1_lattice3(k2_struct_0(sK3)))) | ~v2_waybel_0(sK4,k3_lattice3(k1_lattice3(k2_struct_0(sK3)))) | ~v1_subset_1(sK4,u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK3))))) | v1_xboole_0(sK4) | ~l1_struct_0(sK3) | v2_struct_0(sK3)),
% 0.19/0.39    inference(resolution,[],[f82,f78])).
% 0.19/0.39  fof(f82,plain,(
% 0.19/0.39    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X0)))))) | k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) = X1 | ~v13_waybel_0(X1,k3_lattice3(k1_lattice3(k2_struct_0(X0)))) | ~v2_waybel_0(X1,k3_lattice3(k1_lattice3(k2_struct_0(X0)))) | ~v1_subset_1(X1,u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X0))))) | v1_xboole_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 0.19/0.39    inference(definition_unfolding,[],[f64,f58,f58,f58,f58])).
% 0.19/0.39  fof(f64,plain,(
% 0.19/0.39    ( ! [X0,X1] : (k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) | ~v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) | ~v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) | ~v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) | v1_xboole_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 0.19/0.39    inference(cnf_transformation,[],[f21])).
% 0.19/0.39  fof(f21,plain,(
% 0.19/0.39    ! [X0] : (! [X1] : (k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) | ~v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) | ~v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) | ~v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) | v1_xboole_0(X1)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 0.19/0.39    inference(flattening,[],[f20])).
% 0.19/0.39  fof(f20,plain,(
% 0.19/0.39    ! [X0] : (! [X1] : (k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) = X1 | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) | ~v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) | ~v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) | ~v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) | v1_xboole_0(X1))) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 0.19/0.39    inference(ennf_transformation,[],[f9])).
% 0.19/0.39  fof(f9,axiom,(
% 0.19/0.39    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) & ~v1_xboole_0(X1)) => k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) = X1))),
% 0.19/0.39    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t15_yellow19)).
% 0.19/0.39  fof(f114,plain,(
% 0.19/0.39    ~v7_waybel_0(k3_yellow19(sK3,k2_struct_0(sK3),sK4)) | r1_waybel_7(sK3,k2_yellow19(sK3,k3_yellow19(sK3,k2_struct_0(sK3),sK4)),sK5) | v1_xboole_0(k2_struct_0(sK3)) | v2_struct_0(k3_yellow19(sK3,k2_struct_0(sK3),sK4)) | r1_waybel_7(sK3,sK4,sK5)),
% 0.19/0.39    inference(subsumption_resolution,[],[f113,f102])).
% 0.19/0.39  fof(f102,plain,(
% 0.19/0.39    v4_orders_2(k3_yellow19(sK3,k2_struct_0(sK3),sK4)) | v1_xboole_0(k2_struct_0(sK3))),
% 0.19/0.39    inference(resolution,[],[f100,f67])).
% 0.19/0.39  fof(f67,plain,(
% 0.19/0.39    ( ! [X2,X0,X1] : (~sP0(X0,X1,X2) | v4_orders_2(k3_yellow19(X0,X2,X1))) )),
% 0.19/0.39    inference(cnf_transformation,[],[f42])).
% 0.19/0.39  fof(f42,plain,(
% 0.19/0.39    ! [X0,X1,X2] : ((v6_waybel_0(k3_yellow19(X0,X2,X1),X0) & v4_orders_2(k3_yellow19(X0,X2,X1)) & v3_orders_2(k3_yellow19(X0,X2,X1)) & ~v2_struct_0(k3_yellow19(X0,X2,X1))) | ~sP0(X0,X1,X2))),
% 0.19/0.39    inference(rectify,[],[f41])).
% 0.19/0.39  fof(f41,plain,(
% 0.19/0.39    ! [X0,X2,X1] : ((v6_waybel_0(k3_yellow19(X0,X1,X2),X0) & v4_orders_2(k3_yellow19(X0,X1,X2)) & v3_orders_2(k3_yellow19(X0,X1,X2)) & ~v2_struct_0(k3_yellow19(X0,X1,X2))) | ~sP0(X0,X2,X1))),
% 0.19/0.39    inference(nnf_transformation,[],[f28])).
% 0.19/0.39  fof(f28,plain,(
% 0.19/0.39    ! [X0,X2,X1] : ((v6_waybel_0(k3_yellow19(X0,X1,X2),X0) & v4_orders_2(k3_yellow19(X0,X1,X2)) & v3_orders_2(k3_yellow19(X0,X1,X2)) & ~v2_struct_0(k3_yellow19(X0,X1,X2))) | ~sP0(X0,X2,X1))),
% 0.19/0.39    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 0.19/0.39  fof(f100,plain,(
% 0.19/0.39    sP0(sK3,sK4,k2_struct_0(sK3)) | v1_xboole_0(k2_struct_0(sK3))),
% 0.19/0.39    inference(subsumption_resolution,[],[f99,f47])).
% 0.19/0.39  fof(f99,plain,(
% 0.19/0.39    sP0(sK3,sK4,k2_struct_0(sK3)) | v1_xboole_0(k2_struct_0(sK3)) | v2_struct_0(sK3)),
% 0.19/0.39    inference(subsumption_resolution,[],[f98,f86])).
% 0.19/0.39  fof(f98,plain,(
% 0.19/0.39    sP0(sK3,sK4,k2_struct_0(sK3)) | v1_xboole_0(k2_struct_0(sK3)) | ~l1_struct_0(sK3) | v2_struct_0(sK3)),
% 0.19/0.39    inference(resolution,[],[f97,f88])).
% 0.19/0.39  fof(f97,plain,(
% 0.19/0.39    ( ! [X0] : (~m1_subset_1(k2_struct_0(sK3),k1_zfmisc_1(u1_struct_0(X0))) | sP0(X0,sK4,k2_struct_0(sK3)) | v1_xboole_0(k2_struct_0(sK3)) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 0.19/0.39    inference(subsumption_resolution,[],[f96,f50])).
% 0.19/0.39  fof(f96,plain,(
% 0.19/0.39    ( ! [X0] : (sP0(X0,sK4,k2_struct_0(sK3)) | v1_xboole_0(sK4) | ~m1_subset_1(k2_struct_0(sK3),k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(k2_struct_0(sK3)) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 0.19/0.39    inference(subsumption_resolution,[],[f95,f80])).
% 0.19/0.39  fof(f95,plain,(
% 0.19/0.39    ( ! [X0] : (sP0(X0,sK4,k2_struct_0(sK3)) | ~v2_waybel_0(sK4,k3_lattice3(k1_lattice3(k2_struct_0(sK3)))) | v1_xboole_0(sK4) | ~m1_subset_1(k2_struct_0(sK3),k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(k2_struct_0(sK3)) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 0.19/0.39    inference(subsumption_resolution,[],[f94,f79])).
% 0.19/0.39  fof(f94,plain,(
% 0.19/0.39    ( ! [X0] : (sP0(X0,sK4,k2_struct_0(sK3)) | ~v13_waybel_0(sK4,k3_lattice3(k1_lattice3(k2_struct_0(sK3)))) | ~v2_waybel_0(sK4,k3_lattice3(k1_lattice3(k2_struct_0(sK3)))) | v1_xboole_0(sK4) | ~m1_subset_1(k2_struct_0(sK3),k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(k2_struct_0(sK3)) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 0.19/0.39    inference(resolution,[],[f83,f78])).
% 0.19/0.39  fof(f83,plain,(
% 0.19/0.39    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1))))) | sP0(X0,X2,X1) | ~v13_waybel_0(X2,k3_lattice3(k1_lattice3(X1))) | ~v2_waybel_0(X2,k3_lattice3(k1_lattice3(X1))) | v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 0.19/0.39    inference(definition_unfolding,[],[f69,f58,f58,f58])).
% 0.19/0.39  fof(f69,plain,(
% 0.19/0.39    ( ! [X2,X0,X1] : (sP0(X0,X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1)))) | ~v13_waybel_0(X2,k3_yellow_1(X1)) | ~v2_waybel_0(X2,k3_yellow_1(X1)) | v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 0.19/0.39    inference(cnf_transformation,[],[f29])).
% 0.19/0.39  fof(f29,plain,(
% 0.19/0.39    ! [X0,X1,X2] : (sP0(X0,X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1)))) | ~v13_waybel_0(X2,k3_yellow_1(X1)) | ~v2_waybel_0(X2,k3_yellow_1(X1)) | v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 0.19/0.39    inference(definition_folding,[],[f23,f28])).
% 0.19/0.39  fof(f23,plain,(
% 0.19/0.39    ! [X0,X1,X2] : ((v6_waybel_0(k3_yellow19(X0,X1,X2),X0) & v4_orders_2(k3_yellow19(X0,X1,X2)) & v3_orders_2(k3_yellow19(X0,X1,X2)) & ~v2_struct_0(k3_yellow19(X0,X1,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1)))) | ~v13_waybel_0(X2,k3_yellow_1(X1)) | ~v2_waybel_0(X2,k3_yellow_1(X1)) | v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 0.19/0.39    inference(flattening,[],[f22])).
% 0.19/0.39  fof(f22,plain,(
% 0.19/0.39    ! [X0,X1,X2] : ((v6_waybel_0(k3_yellow19(X0,X1,X2),X0) & v4_orders_2(k3_yellow19(X0,X1,X2)) & v3_orders_2(k3_yellow19(X0,X1,X2)) & ~v2_struct_0(k3_yellow19(X0,X1,X2))) | (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1)))) | ~v13_waybel_0(X2,k3_yellow_1(X1)) | ~v2_waybel_0(X2,k3_yellow_1(X1)) | v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)))),
% 0.19/0.39    inference(ennf_transformation,[],[f6])).
% 0.19/0.39  fof(f6,axiom,(
% 0.19/0.39    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1)))) & v13_waybel_0(X2,k3_yellow_1(X1)) & v2_waybel_0(X2,k3_yellow_1(X1)) & ~v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1) & l1_struct_0(X0) & ~v2_struct_0(X0)) => (v6_waybel_0(k3_yellow19(X0,X1,X2),X0) & v4_orders_2(k3_yellow19(X0,X1,X2)) & v3_orders_2(k3_yellow19(X0,X1,X2)) & ~v2_struct_0(k3_yellow19(X0,X1,X2))))),
% 0.19/0.39    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc4_yellow19)).
% 0.19/0.39  fof(f113,plain,(
% 0.19/0.39    v1_xboole_0(k2_struct_0(sK3)) | r1_waybel_7(sK3,k2_yellow19(sK3,k3_yellow19(sK3,k2_struct_0(sK3),sK4)),sK5) | ~v7_waybel_0(k3_yellow19(sK3,k2_struct_0(sK3),sK4)) | ~v4_orders_2(k3_yellow19(sK3,k2_struct_0(sK3),sK4)) | v2_struct_0(k3_yellow19(sK3,k2_struct_0(sK3),sK4)) | r1_waybel_7(sK3,sK4,sK5)),
% 0.19/0.39    inference(resolution,[],[f111,f93])).
% 0.19/0.39  fof(f93,plain,(
% 0.19/0.39    ~l1_waybel_0(k3_yellow19(sK3,k2_struct_0(sK3),sK4),sK3) | r1_waybel_7(sK3,k2_yellow19(sK3,k3_yellow19(sK3,k2_struct_0(sK3),sK4)),sK5) | ~v7_waybel_0(k3_yellow19(sK3,k2_struct_0(sK3),sK4)) | ~v4_orders_2(k3_yellow19(sK3,k2_struct_0(sK3),sK4)) | v2_struct_0(k3_yellow19(sK3,k2_struct_0(sK3),sK4)) | r1_waybel_7(sK3,sK4,sK5)),
% 0.19/0.39    inference(subsumption_resolution,[],[f92,f47])).
% 0.19/0.39  fof(f92,plain,(
% 0.19/0.39    r1_waybel_7(sK3,k2_yellow19(sK3,k3_yellow19(sK3,k2_struct_0(sK3),sK4)),sK5) | ~l1_waybel_0(k3_yellow19(sK3,k2_struct_0(sK3),sK4),sK3) | ~v7_waybel_0(k3_yellow19(sK3,k2_struct_0(sK3),sK4)) | ~v4_orders_2(k3_yellow19(sK3,k2_struct_0(sK3),sK4)) | v2_struct_0(k3_yellow19(sK3,k2_struct_0(sK3),sK4)) | v2_struct_0(sK3) | r1_waybel_7(sK3,sK4,sK5)),
% 0.19/0.39    inference(subsumption_resolution,[],[f91,f48])).
% 0.19/0.39  fof(f48,plain,(
% 0.19/0.39    v2_pre_topc(sK3)),
% 0.19/0.39    inference(cnf_transformation,[],[f39])).
% 0.19/0.39  fof(f91,plain,(
% 0.19/0.39    r1_waybel_7(sK3,k2_yellow19(sK3,k3_yellow19(sK3,k2_struct_0(sK3),sK4)),sK5) | ~l1_waybel_0(k3_yellow19(sK3,k2_struct_0(sK3),sK4),sK3) | ~v7_waybel_0(k3_yellow19(sK3,k2_struct_0(sK3),sK4)) | ~v4_orders_2(k3_yellow19(sK3,k2_struct_0(sK3),sK4)) | v2_struct_0(k3_yellow19(sK3,k2_struct_0(sK3),sK4)) | ~v2_pre_topc(sK3) | v2_struct_0(sK3) | r1_waybel_7(sK3,sK4,sK5)),
% 0.19/0.39    inference(subsumption_resolution,[],[f90,f49])).
% 0.19/0.39  fof(f90,plain,(
% 0.19/0.39    r1_waybel_7(sK3,k2_yellow19(sK3,k3_yellow19(sK3,k2_struct_0(sK3),sK4)),sK5) | ~l1_waybel_0(k3_yellow19(sK3,k2_struct_0(sK3),sK4),sK3) | ~v7_waybel_0(k3_yellow19(sK3,k2_struct_0(sK3),sK4)) | ~v4_orders_2(k3_yellow19(sK3,k2_struct_0(sK3),sK4)) | v2_struct_0(k3_yellow19(sK3,k2_struct_0(sK3),sK4)) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3) | r1_waybel_7(sK3,sK4,sK5)),
% 0.19/0.39    inference(subsumption_resolution,[],[f89,f55])).
% 0.19/0.39  fof(f55,plain,(
% 0.19/0.39    m1_subset_1(sK5,u1_struct_0(sK3))),
% 0.19/0.39    inference(cnf_transformation,[],[f39])).
% 0.19/0.39  fof(f89,plain,(
% 0.19/0.39    r1_waybel_7(sK3,k2_yellow19(sK3,k3_yellow19(sK3,k2_struct_0(sK3),sK4)),sK5) | ~m1_subset_1(sK5,u1_struct_0(sK3)) | ~l1_waybel_0(k3_yellow19(sK3,k2_struct_0(sK3),sK4),sK3) | ~v7_waybel_0(k3_yellow19(sK3,k2_struct_0(sK3),sK4)) | ~v4_orders_2(k3_yellow19(sK3,k2_struct_0(sK3),sK4)) | v2_struct_0(k3_yellow19(sK3,k2_struct_0(sK3),sK4)) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3) | r1_waybel_7(sK3,sK4,sK5)),
% 0.19/0.39    inference(resolution,[],[f61,f56])).
% 0.19/0.39  fof(f56,plain,(
% 0.19/0.39    r3_waybel_9(sK3,k3_yellow19(sK3,k2_struct_0(sK3),sK4),sK5) | r1_waybel_7(sK3,sK4,sK5)),
% 0.19/0.39    inference(cnf_transformation,[],[f39])).
% 0.19/0.39  fof(f61,plain,(
% 0.19/0.39    ( ! [X2,X0,X1] : (~r3_waybel_9(X0,X1,X2) | r1_waybel_7(X0,k2_yellow19(X0,X1),X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.19/0.39    inference(cnf_transformation,[],[f40])).
% 0.19/0.39  fof(f40,plain,(
% 0.19/0.39    ! [X0] : (! [X1] : (! [X2] : (((r3_waybel_9(X0,X1,X2) | ~r1_waybel_7(X0,k2_yellow19(X0,X1),X2)) & (r1_waybel_7(X0,k2_yellow19(X0,X1),X2) | ~r3_waybel_9(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.19/0.39    inference(nnf_transformation,[],[f17])).
% 0.19/0.39  fof(f17,plain,(
% 0.19/0.39    ! [X0] : (! [X1] : (! [X2] : ((r3_waybel_9(X0,X1,X2) <=> r1_waybel_7(X0,k2_yellow19(X0,X1),X2)) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.19/0.39    inference(flattening,[],[f16])).
% 0.19/0.39  fof(f16,plain,(
% 0.19/0.39    ! [X0] : (! [X1] : (! [X2] : ((r3_waybel_9(X0,X1,X2) <=> r1_waybel_7(X0,k2_yellow19(X0,X1),X2)) | ~m1_subset_1(X2,u1_struct_0(X0))) | (~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.19/0.39    inference(ennf_transformation,[],[f8])).
% 0.19/0.39  fof(f8,axiom,(
% 0.19/0.39    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r3_waybel_9(X0,X1,X2) <=> r1_waybel_7(X0,k2_yellow19(X0,X1),X2)))))),
% 0.19/0.39    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_yellow19)).
% 0.19/0.39  fof(f111,plain,(
% 0.19/0.39    l1_waybel_0(k3_yellow19(sK3,k2_struct_0(sK3),sK4),sK3) | v1_xboole_0(k2_struct_0(sK3))),
% 0.19/0.39    inference(resolution,[],[f110,f72])).
% 0.19/0.39  fof(f72,plain,(
% 0.19/0.39    ( ! [X2,X0,X1] : (~sP1(X0,X1,X2) | l1_waybel_0(k3_yellow19(X0,X2,X1),X0)) )),
% 0.19/0.39    inference(cnf_transformation,[],[f44])).
% 0.19/0.39  fof(f44,plain,(
% 0.19/0.39    ! [X0,X1,X2] : ((l1_waybel_0(k3_yellow19(X0,X2,X1),X0) & v6_waybel_0(k3_yellow19(X0,X2,X1),X0) & ~v2_struct_0(k3_yellow19(X0,X2,X1))) | ~sP1(X0,X1,X2))),
% 0.19/0.39    inference(rectify,[],[f43])).
% 0.19/0.39  fof(f43,plain,(
% 0.19/0.39    ! [X0,X2,X1] : ((l1_waybel_0(k3_yellow19(X0,X1,X2),X0) & v6_waybel_0(k3_yellow19(X0,X1,X2),X0) & ~v2_struct_0(k3_yellow19(X0,X1,X2))) | ~sP1(X0,X2,X1))),
% 0.19/0.39    inference(nnf_transformation,[],[f30])).
% 0.19/0.39  fof(f30,plain,(
% 0.19/0.39    ! [X0,X2,X1] : ((l1_waybel_0(k3_yellow19(X0,X1,X2),X0) & v6_waybel_0(k3_yellow19(X0,X1,X2),X0) & ~v2_struct_0(k3_yellow19(X0,X1,X2))) | ~sP1(X0,X2,X1))),
% 0.19/0.39    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 0.19/0.39  fof(f110,plain,(
% 0.19/0.39    sP1(sK3,sK4,k2_struct_0(sK3)) | v1_xboole_0(k2_struct_0(sK3))),
% 0.19/0.39    inference(subsumption_resolution,[],[f109,f47])).
% 0.19/0.39  fof(f109,plain,(
% 0.19/0.39    sP1(sK3,sK4,k2_struct_0(sK3)) | v1_xboole_0(k2_struct_0(sK3)) | v2_struct_0(sK3)),
% 0.19/0.39    inference(subsumption_resolution,[],[f108,f86])).
% 0.19/0.39  fof(f108,plain,(
% 0.19/0.39    sP1(sK3,sK4,k2_struct_0(sK3)) | v1_xboole_0(k2_struct_0(sK3)) | ~l1_struct_0(sK3) | v2_struct_0(sK3)),
% 0.19/0.39    inference(resolution,[],[f107,f88])).
% 0.19/0.39  fof(f107,plain,(
% 0.19/0.39    ( ! [X0] : (~m1_subset_1(k2_struct_0(sK3),k1_zfmisc_1(u1_struct_0(X0))) | sP1(X0,sK4,k2_struct_0(sK3)) | v1_xboole_0(k2_struct_0(sK3)) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 0.19/0.39    inference(subsumption_resolution,[],[f106,f50])).
% 0.19/0.39  fof(f106,plain,(
% 0.19/0.39    ( ! [X0] : (sP1(X0,sK4,k2_struct_0(sK3)) | v1_xboole_0(sK4) | ~m1_subset_1(k2_struct_0(sK3),k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(k2_struct_0(sK3)) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 0.19/0.39    inference(subsumption_resolution,[],[f105,f80])).
% 0.19/0.39  fof(f105,plain,(
% 0.19/0.39    ( ! [X0] : (sP1(X0,sK4,k2_struct_0(sK3)) | ~v2_waybel_0(sK4,k3_lattice3(k1_lattice3(k2_struct_0(sK3)))) | v1_xboole_0(sK4) | ~m1_subset_1(k2_struct_0(sK3),k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(k2_struct_0(sK3)) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 0.19/0.39    inference(subsumption_resolution,[],[f104,f79])).
% 0.19/0.39  fof(f104,plain,(
% 0.19/0.39    ( ! [X0] : (sP1(X0,sK4,k2_struct_0(sK3)) | ~v13_waybel_0(sK4,k3_lattice3(k1_lattice3(k2_struct_0(sK3)))) | ~v2_waybel_0(sK4,k3_lattice3(k1_lattice3(k2_struct_0(sK3)))) | v1_xboole_0(sK4) | ~m1_subset_1(k2_struct_0(sK3),k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(k2_struct_0(sK3)) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 0.19/0.39    inference(resolution,[],[f84,f78])).
% 0.19/0.39  fof(f84,plain,(
% 0.19/0.39    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1))))) | sP1(X0,X2,X1) | ~v13_waybel_0(X2,k3_lattice3(k1_lattice3(X1))) | ~v2_waybel_0(X2,k3_lattice3(k1_lattice3(X1))) | v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 0.19/0.39    inference(definition_unfolding,[],[f73,f58,f58,f58])).
% 0.19/0.39  fof(f73,plain,(
% 0.19/0.39    ( ! [X2,X0,X1] : (sP1(X0,X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1)))) | ~v13_waybel_0(X2,k3_yellow_1(X1)) | ~v2_waybel_0(X2,k3_yellow_1(X1)) | v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 0.19/0.39    inference(cnf_transformation,[],[f31])).
% 0.19/0.39  fof(f31,plain,(
% 0.19/0.39    ! [X0,X1,X2] : (sP1(X0,X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1)))) | ~v13_waybel_0(X2,k3_yellow_1(X1)) | ~v2_waybel_0(X2,k3_yellow_1(X1)) | v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 0.19/0.39    inference(definition_folding,[],[f25,f30])).
% 0.19/0.39  fof(f25,plain,(
% 0.19/0.39    ! [X0,X1,X2] : ((l1_waybel_0(k3_yellow19(X0,X1,X2),X0) & v6_waybel_0(k3_yellow19(X0,X1,X2),X0) & ~v2_struct_0(k3_yellow19(X0,X1,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1)))) | ~v13_waybel_0(X2,k3_yellow_1(X1)) | ~v2_waybel_0(X2,k3_yellow_1(X1)) | v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 0.19/0.39    inference(flattening,[],[f24])).
% 0.19/0.40  fof(f24,plain,(
% 0.19/0.40    ! [X0,X1,X2] : ((l1_waybel_0(k3_yellow19(X0,X1,X2),X0) & v6_waybel_0(k3_yellow19(X0,X1,X2),X0) & ~v2_struct_0(k3_yellow19(X0,X1,X2))) | (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1)))) | ~v13_waybel_0(X2,k3_yellow_1(X1)) | ~v2_waybel_0(X2,k3_yellow_1(X1)) | v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)))),
% 0.19/0.40    inference(ennf_transformation,[],[f5])).
% 0.19/0.40  fof(f5,axiom,(
% 0.19/0.40    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1)))) & v13_waybel_0(X2,k3_yellow_1(X1)) & v2_waybel_0(X2,k3_yellow_1(X1)) & ~v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1) & l1_struct_0(X0) & ~v2_struct_0(X0)) => (l1_waybel_0(k3_yellow19(X0,X1,X2),X0) & v6_waybel_0(k3_yellow19(X0,X1,X2),X0) & ~v2_struct_0(k3_yellow19(X0,X1,X2))))),
% 0.19/0.40    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_yellow19)).
% 0.19/0.40  fof(f159,plain,(
% 0.19/0.40    v2_struct_0(k3_yellow19(sK3,k2_struct_0(sK3),sK4)) | v1_xboole_0(k2_struct_0(sK3)) | ~r1_waybel_7(sK3,sK4,sK5)),
% 0.19/0.40    inference(resolution,[],[f158,f57])).
% 0.19/0.40  fof(f57,plain,(
% 0.19/0.40    ~r3_waybel_9(sK3,k3_yellow19(sK3,k2_struct_0(sK3),sK4),sK5) | ~r1_waybel_7(sK3,sK4,sK5)),
% 0.19/0.40    inference(cnf_transformation,[],[f39])).
% 0.19/0.40  fof(f158,plain,(
% 0.19/0.40    r3_waybel_9(sK3,k3_yellow19(sK3,k2_struct_0(sK3),sK4),sK5) | v2_struct_0(k3_yellow19(sK3,k2_struct_0(sK3),sK4)) | v1_xboole_0(k2_struct_0(sK3))),
% 0.19/0.40    inference(subsumption_resolution,[],[f157,f102])).
% 0.19/0.40  fof(f157,plain,(
% 0.19/0.40    r3_waybel_9(sK3,k3_yellow19(sK3,k2_struct_0(sK3),sK4),sK5) | ~v4_orders_2(k3_yellow19(sK3,k2_struct_0(sK3),sK4)) | v2_struct_0(k3_yellow19(sK3,k2_struct_0(sK3),sK4)) | v1_xboole_0(k2_struct_0(sK3))),
% 0.19/0.40    inference(subsumption_resolution,[],[f156,f124])).
% 0.19/0.40  fof(f156,plain,(
% 0.19/0.40    r3_waybel_9(sK3,k3_yellow19(sK3,k2_struct_0(sK3),sK4),sK5) | ~v7_waybel_0(k3_yellow19(sK3,k2_struct_0(sK3),sK4)) | ~v4_orders_2(k3_yellow19(sK3,k2_struct_0(sK3),sK4)) | v2_struct_0(k3_yellow19(sK3,k2_struct_0(sK3),sK4)) | v1_xboole_0(k2_struct_0(sK3))),
% 0.19/0.40    inference(subsumption_resolution,[],[f155,f111])).
% 0.19/0.40  fof(f155,plain,(
% 0.19/0.40    r3_waybel_9(sK3,k3_yellow19(sK3,k2_struct_0(sK3),sK4),sK5) | ~l1_waybel_0(k3_yellow19(sK3,k2_struct_0(sK3),sK4),sK3) | ~v7_waybel_0(k3_yellow19(sK3,k2_struct_0(sK3),sK4)) | ~v4_orders_2(k3_yellow19(sK3,k2_struct_0(sK3),sK4)) | v2_struct_0(k3_yellow19(sK3,k2_struct_0(sK3),sK4)) | v1_xboole_0(k2_struct_0(sK3))),
% 0.19/0.40    inference(subsumption_resolution,[],[f154,f55])).
% 0.19/0.40  fof(f154,plain,(
% 0.19/0.40    r3_waybel_9(sK3,k3_yellow19(sK3,k2_struct_0(sK3),sK4),sK5) | ~m1_subset_1(sK5,u1_struct_0(sK3)) | ~l1_waybel_0(k3_yellow19(sK3,k2_struct_0(sK3),sK4),sK3) | ~v7_waybel_0(k3_yellow19(sK3,k2_struct_0(sK3),sK4)) | ~v4_orders_2(k3_yellow19(sK3,k2_struct_0(sK3),sK4)) | v2_struct_0(k3_yellow19(sK3,k2_struct_0(sK3),sK4)) | v1_xboole_0(k2_struct_0(sK3))),
% 0.19/0.40    inference(resolution,[],[f146,f150])).
% 0.19/0.40  fof(f150,plain,(
% 0.19/0.40    r1_waybel_7(sK3,sK4,sK5) | v1_xboole_0(k2_struct_0(sK3))),
% 0.19/0.40    inference(subsumption_resolution,[],[f147,f122])).
% 0.19/0.40  fof(f147,plain,(
% 0.19/0.40    v1_xboole_0(k2_struct_0(sK3)) | r1_waybel_7(sK3,sK4,sK5) | ~sP2(sK4,k2_struct_0(sK3),sK3)),
% 0.19/0.40    inference(resolution,[],[f143,f74])).
% 0.19/0.40  fof(f146,plain,(
% 0.19/0.40    ( ! [X0] : (~r1_waybel_7(sK3,sK4,X0) | r3_waybel_9(sK3,k3_yellow19(sK3,k2_struct_0(sK3),sK4),X0) | ~m1_subset_1(X0,u1_struct_0(sK3)) | ~l1_waybel_0(k3_yellow19(sK3,k2_struct_0(sK3),sK4),sK3) | ~v7_waybel_0(k3_yellow19(sK3,k2_struct_0(sK3),sK4)) | ~v4_orders_2(k3_yellow19(sK3,k2_struct_0(sK3),sK4)) | v2_struct_0(k3_yellow19(sK3,k2_struct_0(sK3),sK4))) )),
% 0.19/0.40    inference(subsumption_resolution,[],[f145,f47])).
% 0.19/0.40  fof(f145,plain,(
% 0.19/0.40    ( ! [X0] : (~r1_waybel_7(sK3,sK4,X0) | r3_waybel_9(sK3,k3_yellow19(sK3,k2_struct_0(sK3),sK4),X0) | ~m1_subset_1(X0,u1_struct_0(sK3)) | ~l1_waybel_0(k3_yellow19(sK3,k2_struct_0(sK3),sK4),sK3) | ~v7_waybel_0(k3_yellow19(sK3,k2_struct_0(sK3),sK4)) | ~v4_orders_2(k3_yellow19(sK3,k2_struct_0(sK3),sK4)) | v2_struct_0(k3_yellow19(sK3,k2_struct_0(sK3),sK4)) | v2_struct_0(sK3)) )),
% 0.19/0.40    inference(subsumption_resolution,[],[f144,f48])).
% 0.19/0.40  fof(f144,plain,(
% 0.19/0.40    ( ! [X0] : (~r1_waybel_7(sK3,sK4,X0) | r3_waybel_9(sK3,k3_yellow19(sK3,k2_struct_0(sK3),sK4),X0) | ~m1_subset_1(X0,u1_struct_0(sK3)) | ~l1_waybel_0(k3_yellow19(sK3,k2_struct_0(sK3),sK4),sK3) | ~v7_waybel_0(k3_yellow19(sK3,k2_struct_0(sK3),sK4)) | ~v4_orders_2(k3_yellow19(sK3,k2_struct_0(sK3),sK4)) | v2_struct_0(k3_yellow19(sK3,k2_struct_0(sK3),sK4)) | ~v2_pre_topc(sK3) | v2_struct_0(sK3)) )),
% 0.19/0.40    inference(subsumption_resolution,[],[f139,f49])).
% 0.19/0.40  fof(f139,plain,(
% 0.19/0.40    ( ! [X0] : (~r1_waybel_7(sK3,sK4,X0) | r3_waybel_9(sK3,k3_yellow19(sK3,k2_struct_0(sK3),sK4),X0) | ~m1_subset_1(X0,u1_struct_0(sK3)) | ~l1_waybel_0(k3_yellow19(sK3,k2_struct_0(sK3),sK4),sK3) | ~v7_waybel_0(k3_yellow19(sK3,k2_struct_0(sK3),sK4)) | ~v4_orders_2(k3_yellow19(sK3,k2_struct_0(sK3),sK4)) | v2_struct_0(k3_yellow19(sK3,k2_struct_0(sK3),sK4)) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3)) )),
% 0.19/0.40    inference(superposition,[],[f62,f135])).
% 0.19/0.40  fof(f62,plain,(
% 0.19/0.40    ( ! [X2,X0,X1] : (~r1_waybel_7(X0,k2_yellow19(X0,X1),X2) | r3_waybel_9(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.19/0.40    inference(cnf_transformation,[],[f40])).
% 0.19/0.40  % SZS output end Proof for theBenchmark
% 0.19/0.40  % (25769)------------------------------
% 0.19/0.40  % (25769)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.40  % (25769)Termination reason: Refutation
% 0.19/0.40  
% 0.19/0.40  % (25769)Memory used [KB]: 1791
% 0.19/0.40  % (25769)Time elapsed: 0.009 s
% 0.19/0.40  % (25769)------------------------------
% 0.19/0.40  % (25769)------------------------------
% 0.19/0.40  % (25756)Success in time 0.051 s
%------------------------------------------------------------------------------
