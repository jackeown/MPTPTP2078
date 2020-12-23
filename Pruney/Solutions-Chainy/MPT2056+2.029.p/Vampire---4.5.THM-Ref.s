%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:23:26 EST 2020

% Result     : Theorem 1.67s
% Output     : Refutation 1.67s
% Verified   : 
% Statistics : Number of formulae       :   83 ( 401 expanded)
%              Number of leaves         :   15 ( 107 expanded)
%              Depth                    :   13
%              Number of atoms          :  240 (1542 expanded)
%              Number of equality atoms :   42 ( 317 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1257,plain,(
    $false ),
    inference(global_subsumption,[],[f38,f1234])).

fof(f1234,plain,(
    ~ v1_xboole_0(k1_xboole_0) ),
    inference(backward_demodulation,[],[f811,f1223])).

fof(f1223,plain,(
    k1_xboole_0 = sK3(sK1,k1_tarski(k1_xboole_0)) ),
    inference(unit_resulting_resolution,[],[f816,f897,f331])).

fof(f331,plain,(
    ! [X6,X7,X5] :
      ( sP5(X5,k1_tarski(X6),X7)
      | ~ r2_hidden(X5,X7)
      | X5 = X6 ) ),
    inference(resolution,[],[f80,f83])).

fof(f83,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,k5_xboole_0(X0,k1_setfam_1(k1_enumset1(X0,X0,X1))))
      | sP5(X3,X1,X0) ) ),
    inference(equality_resolution,[],[f78])).

fof(f78,plain,(
    ! [X2,X0,X3,X1] :
      ( sP5(X3,X1,X0)
      | ~ r2_hidden(X3,X2)
      | k5_xboole_0(X0,k1_setfam_1(k1_enumset1(X0,X0,X1))) != X2 ) ),
    inference(definition_unfolding,[],[f59,f66])).

fof(f66,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k1_setfam_1(k1_enumset1(X0,X0,X1))) ),
    inference(definition_unfolding,[],[f48,f65])).

fof(f65,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k1_enumset1(X0,X0,X1)) ),
    inference(definition_unfolding,[],[f46,f47])).

fof(f47,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f46,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

fof(f48,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f59,plain,(
    ! [X2,X0,X3,X1] :
      ( sP5(X3,X1,X0)
      | ~ r2_hidden(X3,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( ~ r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).

fof(f80,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,k5_xboole_0(X1,k1_setfam_1(k1_enumset1(X1,X1,k1_tarski(X2)))))
      | X0 = X2
      | ~ r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f64,f66])).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | X0 = X2
      | r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) ) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))
    <=> ( X0 != X2
        & r2_hidden(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_zfmisc_1)).

fof(f897,plain,(
    ! [X0] : ~ sP5(sK3(sK1,k1_tarski(k1_xboole_0)),k1_tarski(k1_xboole_0),X0) ),
    inference(unit_resulting_resolution,[],[f814,f57])).

fof(f57,plain,(
    ! [X0,X3,X1] :
      ( ~ sP5(X3,X1,X0)
      | ~ r2_hidden(X3,X1) ) ),
    inference(cnf_transformation,[],[f2])).

fof(f814,plain,(
    r2_hidden(sK3(sK1,k1_tarski(k1_xboole_0)),k1_tarski(k1_xboole_0)) ),
    inference(unit_resulting_resolution,[],[f810,f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK3(X0,X1),X1)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X3] :
              ~ ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X2] :
              ~ ( r2_hidden(X2,X1)
                & r2_hidden(X2,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_0)).

fof(f810,plain,(
    ~ r1_xboole_0(sK1,k1_tarski(k1_xboole_0)) ),
    inference(global_subsumption,[],[f35,f67,f799])).

fof(f799,plain,
    ( sK1 = k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0))))))
    | ~ r1_xboole_0(sK1,k1_tarski(k1_xboole_0)) ),
    inference(superposition,[],[f290,f456])).

fof(f456,plain,(
    k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)) = k7_subset_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))),sK1,k1_tarski(k1_xboole_0)) ),
    inference(unit_resulting_resolution,[],[f36,f37,f30,f68,f69,f67,f72])).

fof(f72,plain,(
    ! [X0,X1] :
      ( k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) = k7_subset_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X0)))),X1,k1_tarski(k1_xboole_0))
      | ~ l1_struct_0(X0)
      | v1_xboole_0(X1)
      | ~ v2_waybel_0(X1,k3_lattice3(k1_lattice3(k2_struct_0(X0))))
      | ~ v13_waybel_0(X1,k3_lattice3(k1_lattice3(k2_struct_0(X0))))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X0))))))
      | v2_struct_0(X0) ) ),
    inference(definition_unfolding,[],[f43,f39,f39,f39,f39])).

fof(f39,plain,(
    ! [X0] : k3_yellow_1(X0) = k3_lattice3(k1_lattice3(X0)) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] : k3_yellow_1(X0) = k3_lattice3(k1_lattice3(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_yellow_1)).

fof(f43,plain,(
    ! [X0,X1] :
      ( v2_struct_0(X0)
      | ~ l1_struct_0(X0)
      | v1_xboole_0(X1)
      | ~ v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
      | ~ v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
      | k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))),X1,k1_tarski(k1_xboole_0)) = k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))),X1,k1_tarski(k1_xboole_0)) = k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
          | ~ v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
          | ~ v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
          | v1_xboole_0(X1) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))),X1,k1_tarski(k1_xboole_0)) = k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
          | ~ v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
          | ~ v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
          | v1_xboole_0(X1) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
            & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
            & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
            & ~ v1_xboole_0(X1) )
         => k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))),X1,k1_tarski(k1_xboole_0)) = k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t14_yellow19)).

fof(f69,plain,(
    v2_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) ),
    inference(definition_unfolding,[],[f32,f39])).

fof(f32,plain,(
    v2_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ? [X0] :
      ( ? [X1] :
          ( k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) != X1
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
          & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
          & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
          & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0))))
          & ~ v1_xboole_0(X1) )
      & l1_struct_0(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ? [X0] :
      ( ? [X1] :
          ( k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) != X1
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
          & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
          & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
          & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0))))
          & ~ v1_xboole_0(X1) )
      & l1_struct_0(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_struct_0(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
              & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
              & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
              & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0))))
              & ~ v1_xboole_0(X1) )
           => k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) = X1 ) ) ),
    inference(negated_conjecture,[],[f16])).

fof(f16,conjecture,(
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

fof(f68,plain,(
    v13_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) ),
    inference(definition_unfolding,[],[f33,f39])).

fof(f33,plain,(
    v13_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f20])).

fof(f30,plain,(
    ~ v1_xboole_0(sK1) ),
    inference(cnf_transformation,[],[f20])).

fof(f37,plain,(
    l1_struct_0(sK0) ),
    inference(cnf_transformation,[],[f20])).

fof(f36,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f20])).

fof(f290,plain,(
    ! [X6,X4,X5] :
      ( k7_subset_1(X6,X4,X5) = X4
      | ~ m1_subset_1(X4,k1_zfmisc_1(X6))
      | ~ r1_xboole_0(X4,X5) ) ),
    inference(superposition,[],[f75,f73])).

fof(f73,plain,(
    ! [X0,X1] :
      ( k5_xboole_0(X0,k1_setfam_1(k1_enumset1(X0,X0,X1))) = X0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(definition_unfolding,[],[f53,f66])).

fof(f53,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = X0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k4_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).

fof(f75,plain,(
    ! [X2,X0,X1] :
      ( k7_subset_1(X0,X1,X2) = k5_xboole_0(X1,k1_setfam_1(k1_enumset1(X1,X1,X2)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(definition_unfolding,[],[f54,f66])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

fof(f67,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))))) ),
    inference(definition_unfolding,[],[f34,f39])).

fof(f34,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))) ),
    inference(cnf_transformation,[],[f20])).

fof(f35,plain,(
    sK1 != k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)) ),
    inference(cnf_transformation,[],[f20])).

fof(f816,plain,(
    r2_hidden(sK3(sK1,k1_tarski(k1_xboole_0)),sK1) ),
    inference(unit_resulting_resolution,[],[f810,f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK3(X0,X1),X0)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f811,plain,(
    ~ v1_xboole_0(sK3(sK1,k1_tarski(k1_xboole_0))) ),
    inference(unit_resulting_resolution,[],[f810,f470])).

fof(f470,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(sK3(sK1,X0))
      | r1_xboole_0(sK1,X0) ) ),
    inference(resolution,[],[f448,f50])).

fof(f448,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK1)
      | ~ v1_xboole_0(X0) ) ),
    inference(global_subsumption,[],[f68,f69,f70,f30,f100,f446])).

fof(f446,plain,(
    ! [X0] :
      ( v1_xboole_0(sK1)
      | ~ v1_subset_1(sK1,u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))))
      | ~ v2_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(sK0))))
      | ~ v13_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(sK0))))
      | v1_xboole_0(k2_struct_0(sK0))
      | ~ r2_hidden(X0,sK1)
      | ~ v1_xboole_0(X0) ) ),
    inference(resolution,[],[f71,f67])).

fof(f71,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
      | v1_xboole_0(X1)
      | ~ v1_subset_1(X1,u1_struct_0(k3_lattice3(k1_lattice3(X0))))
      | ~ v2_waybel_0(X1,k3_lattice3(k1_lattice3(X0)))
      | ~ v13_waybel_0(X1,k3_lattice3(k1_lattice3(X0)))
      | v1_xboole_0(X0)
      | ~ r2_hidden(X2,X1)
      | ~ v1_xboole_0(X2) ) ),
    inference(definition_unfolding,[],[f40,f39,f39,f39,f39])).

fof(f40,plain,(
    ! [X2,X0,X1] :
      ( v1_xboole_0(X0)
      | v1_xboole_0(X1)
      | ~ v1_subset_1(X1,u1_struct_0(k3_yellow_1(X0)))
      | ~ v2_waybel_0(X1,k3_yellow_1(X0))
      | ~ v13_waybel_0(X1,k3_yellow_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0))))
      | ~ r2_hidden(X2,X1)
      | ~ v1_xboole_0(X2) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ~ v1_xboole_0(X2)
              | ~ r2_hidden(X2,X1) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0))))
          | ~ v13_waybel_0(X1,k3_yellow_1(X0))
          | ~ v2_waybel_0(X1,k3_yellow_1(X0))
          | ~ v1_subset_1(X1,u1_struct_0(k3_yellow_1(X0)))
          | v1_xboole_0(X1) )
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ~ v1_xboole_0(X2)
              | ~ r2_hidden(X2,X1) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0))))
          | ~ v13_waybel_0(X1,k3_yellow_1(X0))
          | ~ v2_waybel_0(X1,k3_yellow_1(X0))
          | ~ v1_subset_1(X1,u1_struct_0(k3_yellow_1(X0)))
          | v1_xboole_0(X1) )
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0))))
            & v13_waybel_0(X1,k3_yellow_1(X0))
            & v2_waybel_0(X1,k3_yellow_1(X0))
            & v1_subset_1(X1,u1_struct_0(k3_yellow_1(X0)))
            & ~ v1_xboole_0(X1) )
         => ! [X2] :
              ~ ( v1_xboole_0(X2)
                & r2_hidden(X2,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_yellow19)).

fof(f100,plain,(
    ~ v1_xboole_0(k2_struct_0(sK0)) ),
    inference(forward_demodulation,[],[f96,f93])).

fof(f93,plain,(
    k2_struct_0(sK0) = u1_struct_0(sK0) ),
    inference(unit_resulting_resolution,[],[f37,f41])).

fof(f41,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k2_struct_0(X0) = u1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).

fof(f96,plain,(
    ~ v1_xboole_0(u1_struct_0(sK0)) ),
    inference(unit_resulting_resolution,[],[f36,f37,f42])).

fof(f42,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_struct_0)).

fof(f70,plain,(
    v1_subset_1(sK1,u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0))))) ),
    inference(definition_unfolding,[],[f31,f39])).

fof(f31,plain,(
    v1_subset_1(sK1,u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))) ),
    inference(cnf_transformation,[],[f20])).

fof(f38,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_vampire %s %d
% 0.13/0.33  % Computer   : n016.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 09:20:49 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.19/0.52  % (12442)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.19/0.52  % (12434)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.19/0.52  % (12438)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.19/0.52  % (12454)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.19/0.52  % (12445)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.19/0.52  % (12437)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.19/0.52  % (12446)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.19/0.53  % (12444)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.19/0.54  % (12453)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.19/0.54  % (12452)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.19/0.54  % (12432)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.19/0.54  % (12450)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.19/0.54  % (12459)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.19/0.54  % (12458)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.19/0.54  % (12456)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.19/0.55  % (12443)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.19/0.55  % (12435)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.19/0.55  % (12448)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.19/0.55  % (12439)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.19/0.55  % (12455)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.19/0.55  % (12457)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.19/0.55  % (12447)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.19/0.55  % (12431)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.19/0.55  % (12436)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.19/0.56  % (12433)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.19/0.56  % (12430)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.19/0.56  % (12440)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.19/0.56  % (12451)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.19/0.56  % (12440)Refutation not found, incomplete strategy% (12440)------------------------------
% 0.19/0.56  % (12440)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.56  % (12440)Termination reason: Refutation not found, incomplete strategy
% 0.19/0.56  
% 0.19/0.56  % (12440)Memory used [KB]: 10746
% 0.19/0.56  % (12440)Time elapsed: 0.152 s
% 0.19/0.56  % (12440)------------------------------
% 0.19/0.56  % (12440)------------------------------
% 0.19/0.56  % (12449)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.19/0.57  % (12441)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 1.67/0.57  % (12452)Refutation not found, incomplete strategy% (12452)------------------------------
% 1.67/0.57  % (12452)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.67/0.58  % (12452)Termination reason: Refutation not found, incomplete strategy
% 1.67/0.58  
% 1.67/0.58  % (12452)Memory used [KB]: 10746
% 1.67/0.58  % (12452)Time elapsed: 0.171 s
% 1.67/0.58  % (12452)------------------------------
% 1.67/0.58  % (12452)------------------------------
% 1.67/0.58  % (12454)Refutation found. Thanks to Tanya!
% 1.67/0.58  % SZS status Theorem for theBenchmark
% 1.67/0.58  % SZS output start Proof for theBenchmark
% 1.67/0.58  fof(f1257,plain,(
% 1.67/0.58    $false),
% 1.67/0.58    inference(global_subsumption,[],[f38,f1234])).
% 1.67/0.58  fof(f1234,plain,(
% 1.67/0.58    ~v1_xboole_0(k1_xboole_0)),
% 1.67/0.58    inference(backward_demodulation,[],[f811,f1223])).
% 1.67/0.58  fof(f1223,plain,(
% 1.67/0.58    k1_xboole_0 = sK3(sK1,k1_tarski(k1_xboole_0))),
% 1.67/0.58    inference(unit_resulting_resolution,[],[f816,f897,f331])).
% 1.67/0.58  fof(f331,plain,(
% 1.67/0.58    ( ! [X6,X7,X5] : (sP5(X5,k1_tarski(X6),X7) | ~r2_hidden(X5,X7) | X5 = X6) )),
% 1.67/0.58    inference(resolution,[],[f80,f83])).
% 1.67/0.58  fof(f83,plain,(
% 1.67/0.58    ( ! [X0,X3,X1] : (~r2_hidden(X3,k5_xboole_0(X0,k1_setfam_1(k1_enumset1(X0,X0,X1)))) | sP5(X3,X1,X0)) )),
% 1.67/0.58    inference(equality_resolution,[],[f78])).
% 1.67/0.58  fof(f78,plain,(
% 1.67/0.58    ( ! [X2,X0,X3,X1] : (sP5(X3,X1,X0) | ~r2_hidden(X3,X2) | k5_xboole_0(X0,k1_setfam_1(k1_enumset1(X0,X0,X1))) != X2) )),
% 1.67/0.58    inference(definition_unfolding,[],[f59,f66])).
% 1.67/0.58  fof(f66,plain,(
% 1.67/0.58    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k1_setfam_1(k1_enumset1(X0,X0,X1)))) )),
% 1.67/0.58    inference(definition_unfolding,[],[f48,f65])).
% 1.67/0.58  fof(f65,plain,(
% 1.67/0.58    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k1_enumset1(X0,X0,X1))) )),
% 1.67/0.58    inference(definition_unfolding,[],[f46,f47])).
% 1.67/0.58  fof(f47,plain,(
% 1.67/0.58    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 1.67/0.58    inference(cnf_transformation,[],[f7])).
% 1.67/0.58  fof(f7,axiom,(
% 1.67/0.58    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 1.67/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 1.67/0.58  fof(f46,plain,(
% 1.67/0.58    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 1.67/0.58    inference(cnf_transformation,[],[f10])).
% 1.67/0.58  fof(f10,axiom,(
% 1.67/0.58    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 1.67/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).
% 1.67/0.58  fof(f48,plain,(
% 1.67/0.58    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 1.67/0.58    inference(cnf_transformation,[],[f5])).
% 1.67/0.58  fof(f5,axiom,(
% 1.67/0.58    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 1.67/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).
% 1.67/0.58  fof(f59,plain,(
% 1.67/0.58    ( ! [X2,X0,X3,X1] : (sP5(X3,X1,X0) | ~r2_hidden(X3,X2) | k4_xboole_0(X0,X1) != X2) )),
% 1.67/0.58    inference(cnf_transformation,[],[f2])).
% 1.67/0.58  fof(f2,axiom,(
% 1.67/0.58    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 1.67/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).
% 1.67/0.58  fof(f80,plain,(
% 1.67/0.58    ( ! [X2,X0,X1] : (r2_hidden(X0,k5_xboole_0(X1,k1_setfam_1(k1_enumset1(X1,X1,k1_tarski(X2))))) | X0 = X2 | ~r2_hidden(X0,X1)) )),
% 1.67/0.58    inference(definition_unfolding,[],[f64,f66])).
% 1.67/0.58  fof(f64,plain,(
% 1.67/0.58    ( ! [X2,X0,X1] : (~r2_hidden(X0,X1) | X0 = X2 | r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))) )),
% 1.67/0.58    inference(cnf_transformation,[],[f8])).
% 1.67/0.58  fof(f8,axiom,(
% 1.67/0.58    ! [X0,X1,X2] : (r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) <=> (X0 != X2 & r2_hidden(X0,X1)))),
% 1.67/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_zfmisc_1)).
% 1.67/0.58  fof(f897,plain,(
% 1.67/0.58    ( ! [X0] : (~sP5(sK3(sK1,k1_tarski(k1_xboole_0)),k1_tarski(k1_xboole_0),X0)) )),
% 1.67/0.58    inference(unit_resulting_resolution,[],[f814,f57])).
% 1.67/0.58  fof(f57,plain,(
% 1.67/0.58    ( ! [X0,X3,X1] : (~sP5(X3,X1,X0) | ~r2_hidden(X3,X1)) )),
% 1.67/0.58    inference(cnf_transformation,[],[f2])).
% 1.67/0.58  fof(f814,plain,(
% 1.67/0.58    r2_hidden(sK3(sK1,k1_tarski(k1_xboole_0)),k1_tarski(k1_xboole_0))),
% 1.67/0.58    inference(unit_resulting_resolution,[],[f810,f51])).
% 1.67/0.58  fof(f51,plain,(
% 1.67/0.58    ( ! [X0,X1] : (r2_hidden(sK3(X0,X1),X1) | r1_xboole_0(X0,X1)) )),
% 1.67/0.58    inference(cnf_transformation,[],[f28])).
% 1.67/0.58  fof(f28,plain,(
% 1.67/0.58    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r1_xboole_0(X0,X1)))),
% 1.67/0.58    inference(ennf_transformation,[],[f18])).
% 1.67/0.58  fof(f18,plain,(
% 1.67/0.58    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X3] : ~(r2_hidden(X3,X1) & r2_hidden(X3,X0)) & ~r1_xboole_0(X0,X1)))),
% 1.67/0.58    inference(rectify,[],[f4])).
% 1.67/0.58  fof(f4,axiom,(
% 1.67/0.58    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X2] : ~(r2_hidden(X2,X1) & r2_hidden(X2,X0)) & ~r1_xboole_0(X0,X1)))),
% 1.67/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_0)).
% 1.67/0.58  fof(f810,plain,(
% 1.67/0.58    ~r1_xboole_0(sK1,k1_tarski(k1_xboole_0))),
% 1.67/0.58    inference(global_subsumption,[],[f35,f67,f799])).
% 1.67/0.58  fof(f799,plain,(
% 1.67/0.58    sK1 = k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))))) | ~r1_xboole_0(sK1,k1_tarski(k1_xboole_0))),
% 1.67/0.58    inference(superposition,[],[f290,f456])).
% 1.67/0.58  fof(f456,plain,(
% 1.67/0.58    k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)) = k7_subset_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))),sK1,k1_tarski(k1_xboole_0))),
% 1.67/0.58    inference(unit_resulting_resolution,[],[f36,f37,f30,f68,f69,f67,f72])).
% 1.67/0.58  fof(f72,plain,(
% 1.67/0.58    ( ! [X0,X1] : (k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) = k7_subset_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X0)))),X1,k1_tarski(k1_xboole_0)) | ~l1_struct_0(X0) | v1_xboole_0(X1) | ~v2_waybel_0(X1,k3_lattice3(k1_lattice3(k2_struct_0(X0)))) | ~v13_waybel_0(X1,k3_lattice3(k1_lattice3(k2_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X0)))))) | v2_struct_0(X0)) )),
% 1.67/0.58    inference(definition_unfolding,[],[f43,f39,f39,f39,f39])).
% 1.67/0.58  fof(f39,plain,(
% 1.67/0.58    ( ! [X0] : (k3_yellow_1(X0) = k3_lattice3(k1_lattice3(X0))) )),
% 1.67/0.58    inference(cnf_transformation,[],[f13])).
% 1.67/0.58  fof(f13,axiom,(
% 1.67/0.58    ! [X0] : k3_yellow_1(X0) = k3_lattice3(k1_lattice3(X0))),
% 1.67/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_yellow_1)).
% 1.67/0.58  fof(f43,plain,(
% 1.67/0.58    ( ! [X0,X1] : (v2_struct_0(X0) | ~l1_struct_0(X0) | v1_xboole_0(X1) | ~v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) | ~v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) | k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))),X1,k1_tarski(k1_xboole_0)) = k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1))) )),
% 1.67/0.58    inference(cnf_transformation,[],[f27])).
% 1.67/0.58  fof(f27,plain,(
% 1.67/0.58    ! [X0] : (! [X1] : (k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))),X1,k1_tarski(k1_xboole_0)) = k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) | ~v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) | ~v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) | v1_xboole_0(X1)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 1.67/0.58    inference(flattening,[],[f26])).
% 1.67/0.58  fof(f26,plain,(
% 1.67/0.58    ! [X0] : (! [X1] : (k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))),X1,k1_tarski(k1_xboole_0)) = k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) | ~v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) | ~v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) | v1_xboole_0(X1))) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 1.67/0.58    inference(ennf_transformation,[],[f14])).
% 1.67/0.58  fof(f14,axiom,(
% 1.67/0.58    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & ~v1_xboole_0(X1)) => k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))),X1,k1_tarski(k1_xboole_0)) = k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1))))),
% 1.67/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t14_yellow19)).
% 1.67/0.58  fof(f69,plain,(
% 1.67/0.58    v2_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(sK0))))),
% 1.67/0.58    inference(definition_unfolding,[],[f32,f39])).
% 1.67/0.58  fof(f32,plain,(
% 1.67/0.58    v2_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0)))),
% 1.67/0.58    inference(cnf_transformation,[],[f20])).
% 1.67/0.58  fof(f20,plain,(
% 1.67/0.58    ? [X0] : (? [X1] : (k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) != X1 & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) & ~v1_xboole_0(X1)) & l1_struct_0(X0) & ~v2_struct_0(X0))),
% 1.67/0.58    inference(flattening,[],[f19])).
% 1.67/0.58  fof(f19,plain,(
% 1.67/0.58    ? [X0] : (? [X1] : (k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) != X1 & (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) & ~v1_xboole_0(X1))) & (l1_struct_0(X0) & ~v2_struct_0(X0)))),
% 1.67/0.58    inference(ennf_transformation,[],[f17])).
% 1.67/0.58  fof(f17,negated_conjecture,(
% 1.67/0.58    ~! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) & ~v1_xboole_0(X1)) => k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) = X1))),
% 1.67/0.58    inference(negated_conjecture,[],[f16])).
% 1.67/0.58  fof(f16,conjecture,(
% 1.67/0.58    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) & ~v1_xboole_0(X1)) => k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) = X1))),
% 1.67/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t15_yellow19)).
% 1.67/0.58  fof(f68,plain,(
% 1.67/0.58    v13_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(sK0))))),
% 1.67/0.58    inference(definition_unfolding,[],[f33,f39])).
% 1.67/0.58  fof(f33,plain,(
% 1.67/0.58    v13_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0)))),
% 1.67/0.58    inference(cnf_transformation,[],[f20])).
% 1.67/0.58  fof(f30,plain,(
% 1.67/0.58    ~v1_xboole_0(sK1)),
% 1.67/0.58    inference(cnf_transformation,[],[f20])).
% 1.67/0.58  fof(f37,plain,(
% 1.67/0.58    l1_struct_0(sK0)),
% 1.67/0.58    inference(cnf_transformation,[],[f20])).
% 1.67/0.58  fof(f36,plain,(
% 1.67/0.58    ~v2_struct_0(sK0)),
% 1.67/0.58    inference(cnf_transformation,[],[f20])).
% 1.67/0.58  fof(f290,plain,(
% 1.67/0.58    ( ! [X6,X4,X5] : (k7_subset_1(X6,X4,X5) = X4 | ~m1_subset_1(X4,k1_zfmisc_1(X6)) | ~r1_xboole_0(X4,X5)) )),
% 1.67/0.58    inference(superposition,[],[f75,f73])).
% 1.67/0.58  fof(f73,plain,(
% 1.67/0.58    ( ! [X0,X1] : (k5_xboole_0(X0,k1_setfam_1(k1_enumset1(X0,X0,X1))) = X0 | ~r1_xboole_0(X0,X1)) )),
% 1.67/0.58    inference(definition_unfolding,[],[f53,f66])).
% 1.67/0.58  fof(f53,plain,(
% 1.67/0.58    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1)) )),
% 1.67/0.58    inference(cnf_transformation,[],[f6])).
% 1.67/0.58  fof(f6,axiom,(
% 1.67/0.58    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k4_xboole_0(X0,X1) = X0)),
% 1.67/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).
% 1.67/0.58  fof(f75,plain,(
% 1.67/0.58    ( ! [X2,X0,X1] : (k7_subset_1(X0,X1,X2) = k5_xboole_0(X1,k1_setfam_1(k1_enumset1(X1,X1,X2))) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 1.67/0.58    inference(definition_unfolding,[],[f54,f66])).
% 1.67/0.58  fof(f54,plain,(
% 1.67/0.58    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)) )),
% 1.67/0.58    inference(cnf_transformation,[],[f29])).
% 1.67/0.58  fof(f29,plain,(
% 1.67/0.58    ! [X0,X1,X2] : (k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.67/0.58    inference(ennf_transformation,[],[f9])).
% 1.67/0.58  fof(f9,axiom,(
% 1.67/0.58    ! [X0,X1,X2] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2))),
% 1.67/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_subset_1)).
% 1.67/0.58  fof(f67,plain,(
% 1.67/0.58    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0))))))),
% 1.67/0.58    inference(definition_unfolding,[],[f34,f39])).
% 1.67/0.58  fof(f34,plain,(
% 1.67/0.58    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))))),
% 1.67/0.58    inference(cnf_transformation,[],[f20])).
% 1.67/0.58  fof(f35,plain,(
% 1.67/0.58    sK1 != k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1))),
% 1.67/0.58    inference(cnf_transformation,[],[f20])).
% 1.67/0.58  fof(f816,plain,(
% 1.67/0.58    r2_hidden(sK3(sK1,k1_tarski(k1_xboole_0)),sK1)),
% 1.67/0.58    inference(unit_resulting_resolution,[],[f810,f50])).
% 1.67/0.58  fof(f50,plain,(
% 1.67/0.58    ( ! [X0,X1] : (r2_hidden(sK3(X0,X1),X0) | r1_xboole_0(X0,X1)) )),
% 1.67/0.58    inference(cnf_transformation,[],[f28])).
% 1.67/0.58  fof(f811,plain,(
% 1.67/0.58    ~v1_xboole_0(sK3(sK1,k1_tarski(k1_xboole_0)))),
% 1.67/0.58    inference(unit_resulting_resolution,[],[f810,f470])).
% 1.67/0.58  fof(f470,plain,(
% 1.67/0.58    ( ! [X0] : (~v1_xboole_0(sK3(sK1,X0)) | r1_xboole_0(sK1,X0)) )),
% 1.67/0.58    inference(resolution,[],[f448,f50])).
% 1.67/0.58  fof(f448,plain,(
% 1.67/0.58    ( ! [X0] : (~r2_hidden(X0,sK1) | ~v1_xboole_0(X0)) )),
% 1.67/0.58    inference(global_subsumption,[],[f68,f69,f70,f30,f100,f446])).
% 1.67/0.58  fof(f446,plain,(
% 1.67/0.58    ( ! [X0] : (v1_xboole_0(sK1) | ~v1_subset_1(sK1,u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0))))) | ~v2_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) | ~v13_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) | v1_xboole_0(k2_struct_0(sK0)) | ~r2_hidden(X0,sK1) | ~v1_xboole_0(X0)) )),
% 1.67/0.58    inference(resolution,[],[f71,f67])).
% 1.67/0.58  fof(f71,plain,(
% 1.67/0.58    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0))))) | v1_xboole_0(X1) | ~v1_subset_1(X1,u1_struct_0(k3_lattice3(k1_lattice3(X0)))) | ~v2_waybel_0(X1,k3_lattice3(k1_lattice3(X0))) | ~v13_waybel_0(X1,k3_lattice3(k1_lattice3(X0))) | v1_xboole_0(X0) | ~r2_hidden(X2,X1) | ~v1_xboole_0(X2)) )),
% 1.67/0.58    inference(definition_unfolding,[],[f40,f39,f39,f39,f39])).
% 1.67/0.58  fof(f40,plain,(
% 1.67/0.58    ( ! [X2,X0,X1] : (v1_xboole_0(X0) | v1_xboole_0(X1) | ~v1_subset_1(X1,u1_struct_0(k3_yellow_1(X0))) | ~v2_waybel_0(X1,k3_yellow_1(X0)) | ~v13_waybel_0(X1,k3_yellow_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0)))) | ~r2_hidden(X2,X1) | ~v1_xboole_0(X2)) )),
% 1.67/0.58    inference(cnf_transformation,[],[f22])).
% 1.67/0.58  fof(f22,plain,(
% 1.67/0.58    ! [X0] : (! [X1] : (! [X2] : (~v1_xboole_0(X2) | ~r2_hidden(X2,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0)))) | ~v13_waybel_0(X1,k3_yellow_1(X0)) | ~v2_waybel_0(X1,k3_yellow_1(X0)) | ~v1_subset_1(X1,u1_struct_0(k3_yellow_1(X0))) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 1.67/0.58    inference(flattening,[],[f21])).
% 1.67/0.58  fof(f21,plain,(
% 1.67/0.58    ! [X0] : (! [X1] : (! [X2] : (~v1_xboole_0(X2) | ~r2_hidden(X2,X1)) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0)))) | ~v13_waybel_0(X1,k3_yellow_1(X0)) | ~v2_waybel_0(X1,k3_yellow_1(X0)) | ~v1_subset_1(X1,u1_struct_0(k3_yellow_1(X0))) | v1_xboole_0(X1))) | v1_xboole_0(X0))),
% 1.67/0.58    inference(ennf_transformation,[],[f15])).
% 1.67/0.58  fof(f15,axiom,(
% 1.67/0.58    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0)))) & v13_waybel_0(X1,k3_yellow_1(X0)) & v2_waybel_0(X1,k3_yellow_1(X0)) & v1_subset_1(X1,u1_struct_0(k3_yellow_1(X0))) & ~v1_xboole_0(X1)) => ! [X2] : ~(v1_xboole_0(X2) & r2_hidden(X2,X1))))),
% 1.67/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_yellow19)).
% 1.67/0.58  fof(f100,plain,(
% 1.67/0.58    ~v1_xboole_0(k2_struct_0(sK0))),
% 1.67/0.58    inference(forward_demodulation,[],[f96,f93])).
% 1.67/0.58  fof(f93,plain,(
% 1.67/0.58    k2_struct_0(sK0) = u1_struct_0(sK0)),
% 1.67/0.58    inference(unit_resulting_resolution,[],[f37,f41])).
% 1.67/0.58  fof(f41,plain,(
% 1.67/0.58    ( ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0)) )),
% 1.67/0.58    inference(cnf_transformation,[],[f23])).
% 1.67/0.58  fof(f23,plain,(
% 1.67/0.58    ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0))),
% 1.67/0.58    inference(ennf_transformation,[],[f11])).
% 1.67/0.58  fof(f11,axiom,(
% 1.67/0.58    ! [X0] : (l1_struct_0(X0) => k2_struct_0(X0) = u1_struct_0(X0))),
% 1.67/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).
% 1.67/0.58  fof(f96,plain,(
% 1.67/0.58    ~v1_xboole_0(u1_struct_0(sK0))),
% 1.67/0.58    inference(unit_resulting_resolution,[],[f36,f37,f42])).
% 1.67/0.58  fof(f42,plain,(
% 1.67/0.58    ( ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 1.67/0.58    inference(cnf_transformation,[],[f25])).
% 1.67/0.58  fof(f25,plain,(
% 1.67/0.58    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 1.67/0.58    inference(flattening,[],[f24])).
% 1.67/0.58  fof(f24,plain,(
% 1.67/0.58    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 1.67/0.58    inference(ennf_transformation,[],[f12])).
% 1.67/0.58  fof(f12,axiom,(
% 1.67/0.58    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ~v1_xboole_0(u1_struct_0(X0)))),
% 1.67/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_struct_0)).
% 1.67/0.58  fof(f70,plain,(
% 1.67/0.58    v1_subset_1(sK1,u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))))),
% 1.67/0.58    inference(definition_unfolding,[],[f31,f39])).
% 1.67/0.58  fof(f31,plain,(
% 1.67/0.58    v1_subset_1(sK1,u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))),
% 1.67/0.58    inference(cnf_transformation,[],[f20])).
% 1.67/0.58  fof(f38,plain,(
% 1.67/0.58    v1_xboole_0(k1_xboole_0)),
% 1.67/0.58    inference(cnf_transformation,[],[f3])).
% 1.67/0.58  fof(f3,axiom,(
% 1.67/0.58    v1_xboole_0(k1_xboole_0)),
% 1.67/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).
% 1.67/0.58  % SZS output end Proof for theBenchmark
% 1.67/0.58  % (12454)------------------------------
% 1.67/0.58  % (12454)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.67/0.58  % (12454)Termination reason: Refutation
% 1.67/0.58  
% 1.67/0.58  % (12454)Memory used [KB]: 7291
% 1.67/0.58  % (12454)Time elapsed: 0.173 s
% 1.67/0.58  % (12454)------------------------------
% 1.67/0.58  % (12454)------------------------------
% 1.83/0.61  % (12429)Success in time 0.259 s
%------------------------------------------------------------------------------
