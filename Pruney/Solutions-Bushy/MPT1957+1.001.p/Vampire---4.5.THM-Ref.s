%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1957+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n032.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:50:57 EST 2020

% Result     : Theorem 0.13s
% Output     : Refutation 0.13s
% Verified   : 
% Statistics : Number of formulae       :   36 (  41 expanded)
%              Number of leaves         :    9 (  12 expanded)
%              Depth                    :   10
%              Number of atoms          :   64 (  71 expanded)
%              Number of equality atoms :   40 (  42 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f43,plain,(
    $false ),
    inference(subsumption_resolution,[],[f27,f42])).

fof(f42,plain,(
    ! [X0] : k1_zfmisc_1(X0) = u1_struct_0(k3_yellow_1(X0)) ),
    inference(equality_resolution,[],[f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( k3_yellow_1(X0) != k3_yellow_1(X1)
      | k1_zfmisc_1(X0) = u1_struct_0(k3_yellow_1(X1)) ) ),
    inference(superposition,[],[f39,f28])).

fof(f28,plain,(
    ! [X0] : k3_yellow_1(X0) = k2_yellow_1(k1_zfmisc_1(X0)) ),
    inference(forward_demodulation,[],[f19,f18])).

fof(f18,plain,(
    ! [X0] : k9_setfam_1(X0) = k1_zfmisc_1(X0) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : k9_setfam_1(X0) = k1_zfmisc_1(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k9_setfam_1)).

fof(f19,plain,(
    ! [X0] : k3_yellow_1(X0) = k2_yellow_1(k9_setfam_1(X0)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] : k3_yellow_1(X0) = k2_yellow_1(k9_setfam_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_yellow_1)).

fof(f39,plain,(
    ! [X0,X1] :
      ( k2_yellow_1(X0) != k3_yellow_1(X1)
      | u1_struct_0(k3_yellow_1(X1)) = X0 ) ),
    inference(superposition,[],[f35,f20])).

fof(f20,plain,(
    ! [X0] : k2_yellow_1(X0) = g1_orders_2(X0,k1_yellow_1(X0)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : k2_yellow_1(X0) = g1_orders_2(X0,k1_yellow_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_yellow_1)).

fof(f35,plain,(
    ! [X2,X0,X1] :
      ( k3_yellow_1(X0) != g1_orders_2(X1,X2)
      | u1_struct_0(k3_yellow_1(X0)) = X1 ) ),
    inference(superposition,[],[f32,f30])).

fof(f30,plain,(
    ! [X0] : k3_yellow_1(X0) = g1_orders_2(u1_struct_0(k3_yellow_1(X0)),u1_orders_2(k3_yellow_1(X0))) ),
    inference(subsumption_resolution,[],[f29,f22])).

fof(f22,plain,(
    ! [X0] : l1_orders_2(k3_yellow_1(X0)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( l1_orders_2(k3_yellow_1(X0))
      & v1_orders_2(k3_yellow_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_yellow_1)).

fof(f29,plain,(
    ! [X0] :
      ( k3_yellow_1(X0) = g1_orders_2(u1_struct_0(k3_yellow_1(X0)),u1_orders_2(k3_yellow_1(X0)))
      | ~ l1_orders_2(k3_yellow_1(X0)) ) ),
    inference(resolution,[],[f24,f21])).

fof(f21,plain,(
    ! [X0] : v1_orders_2(k3_yellow_1(X0)) ),
    inference(cnf_transformation,[],[f3])).

fof(f24,plain,(
    ! [X0] :
      ( ~ v1_orders_2(X0)
      | g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = X0
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = X0
      | ~ v1_orders_2(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = X0
      | ~ v1_orders_2(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ( v1_orders_2(X0)
       => g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',abstractness_v1_orders_2)).

fof(f32,plain,(
    ! [X2,X0,X1] :
      ( g1_orders_2(u1_struct_0(k3_yellow_1(X0)),u1_orders_2(k3_yellow_1(X0))) != g1_orders_2(X1,X2)
      | u1_struct_0(k3_yellow_1(X0)) = X1 ) ),
    inference(resolution,[],[f31,f22])).

fof(f31,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_orders_2(X0)
      | u1_struct_0(X0) = X1
      | g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(X1,X2) ) ),
    inference(resolution,[],[f25,f23])).

fof(f23,plain,(
    ! [X0] :
      ( m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0] :
      ( m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_u1_orders_2)).

fof(f25,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | g1_orders_2(X0,X1) != g1_orders_2(X2,X3)
      | X0 = X2 ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( ! [X2,X3] :
          ( ( X1 = X3
            & X0 = X2 )
          | g1_orders_2(X0,X1) != g1_orders_2(X2,X3) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
     => ! [X2,X3] :
          ( g1_orders_2(X0,X1) = g1_orders_2(X2,X3)
         => ( X1 = X3
            & X0 = X2 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',free_g1_orders_2)).

fof(f27,plain,(
    u1_struct_0(k3_yellow_1(sK0)) != k1_zfmisc_1(sK0) ),
    inference(backward_demodulation,[],[f17,f18])).

fof(f17,plain,(
    k9_setfam_1(sK0) != u1_struct_0(k3_yellow_1(sK0)) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    k9_setfam_1(sK0) != u1_struct_0(k3_yellow_1(sK0)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f10,f15])).

fof(f15,plain,
    ( ? [X0] : k9_setfam_1(X0) != u1_struct_0(k3_yellow_1(X0))
   => k9_setfam_1(sK0) != u1_struct_0(k3_yellow_1(sK0)) ),
    introduced(choice_axiom,[])).

fof(f10,plain,(
    ? [X0] : k9_setfam_1(X0) != u1_struct_0(k3_yellow_1(X0)) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,negated_conjecture,(
    ~ ! [X0] : k9_setfam_1(X0) = u1_struct_0(k3_yellow_1(X0)) ),
    inference(negated_conjecture,[],[f8])).

fof(f8,conjecture,(
    ! [X0] : k9_setfam_1(X0) = u1_struct_0(k3_yellow_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_waybel_7)).

%------------------------------------------------------------------------------
