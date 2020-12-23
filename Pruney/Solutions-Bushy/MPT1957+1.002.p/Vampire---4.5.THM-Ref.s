%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1957+1.002 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n028.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:50:57 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   42 ( 111 expanded)
%              Number of leaves         :    8 (  32 expanded)
%              Depth                    :   15
%              Number of atoms          :   76 ( 196 expanded)
%              Number of equality atoms :   43 (  96 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f88,plain,(
    $false ),
    inference(trivial_inequality_removal,[],[f85])).

fof(f85,plain,(
    k1_zfmisc_1(sK0) != k1_zfmisc_1(sK0) ),
    inference(superposition,[],[f26,f75])).

fof(f75,plain,(
    ! [X0] : u1_struct_0(g1_orders_2(X0,k1_yellow_1(X0))) = X0 ),
    inference(equality_resolution,[],[f73])).

fof(f73,plain,(
    ! [X2,X0,X1] :
      ( g1_orders_2(X0,k1_yellow_1(X0)) != g1_orders_2(X1,X2)
      | u1_struct_0(g1_orders_2(X0,k1_yellow_1(X0))) = X1 ) ),
    inference(resolution,[],[f52,f63])).

fof(f63,plain,(
    ! [X0] : m1_subset_1(k1_yellow_1(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_orders_2(X0,k1_yellow_1(X0))),u1_struct_0(g1_orders_2(X0,k1_yellow_1(X0)))))) ),
    inference(subsumption_resolution,[],[f62,f27])).

fof(f27,plain,(
    ! [X0] : l1_orders_2(g1_orders_2(X0,k1_yellow_1(X0))) ),
    inference(definition_unfolding,[],[f20,f18])).

fof(f18,plain,(
    ! [X0] : k2_yellow_1(X0) = g1_orders_2(X0,k1_yellow_1(X0)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : k2_yellow_1(X0) = g1_orders_2(X0,k1_yellow_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_yellow_1)).

fof(f20,plain,(
    ! [X0] : l1_orders_2(k2_yellow_1(X0)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( l1_orders_2(k2_yellow_1(X0))
      & v1_orders_2(k2_yellow_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_yellow_1)).

fof(f62,plain,(
    ! [X0] :
      ( m1_subset_1(k1_yellow_1(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_orders_2(X0,k1_yellow_1(X0))),u1_struct_0(g1_orders_2(X0,k1_yellow_1(X0))))))
      | ~ l1_orders_2(g1_orders_2(X0,k1_yellow_1(X0))) ) ),
    inference(superposition,[],[f21,f48])).

fof(f48,plain,(
    ! [X0] : k1_yellow_1(X0) = u1_orders_2(g1_orders_2(X0,k1_yellow_1(X0))) ),
    inference(equality_resolution,[],[f46])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( g1_orders_2(X0,k1_yellow_1(X0)) != g1_orders_2(X1,X2)
      | u1_orders_2(g1_orders_2(X0,k1_yellow_1(X0))) = X2 ) ),
    inference(subsumption_resolution,[],[f45,f27])).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( g1_orders_2(X0,k1_yellow_1(X0)) != g1_orders_2(X1,X2)
      | u1_orders_2(g1_orders_2(X0,k1_yellow_1(X0))) = X2
      | ~ l1_orders_2(g1_orders_2(X0,k1_yellow_1(X0))) ) ),
    inference(resolution,[],[f34,f21])).

fof(f34,plain,(
    ! [X4,X5,X3] :
      ( ~ m1_subset_1(u1_orders_2(g1_orders_2(X3,k1_yellow_1(X3))),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_orders_2(X3,k1_yellow_1(X3))),u1_struct_0(g1_orders_2(X3,k1_yellow_1(X3))))))
      | g1_orders_2(X3,k1_yellow_1(X3)) != g1_orders_2(X4,X5)
      | u1_orders_2(g1_orders_2(X3,k1_yellow_1(X3))) = X5 ) ),
    inference(superposition,[],[f24,f30])).

fof(f30,plain,(
    ! [X0] : g1_orders_2(X0,k1_yellow_1(X0)) = g1_orders_2(u1_struct_0(g1_orders_2(X0,k1_yellow_1(X0))),u1_orders_2(g1_orders_2(X0,k1_yellow_1(X0)))) ),
    inference(subsumption_resolution,[],[f29,f27])).

fof(f29,plain,(
    ! [X0] :
      ( ~ l1_orders_2(g1_orders_2(X0,k1_yellow_1(X0)))
      | g1_orders_2(X0,k1_yellow_1(X0)) = g1_orders_2(u1_struct_0(g1_orders_2(X0,k1_yellow_1(X0))),u1_orders_2(g1_orders_2(X0,k1_yellow_1(X0)))) ) ),
    inference(resolution,[],[f22,f28])).

fof(f28,plain,(
    ! [X0] : v1_orders_2(g1_orders_2(X0,k1_yellow_1(X0))) ),
    inference(definition_unfolding,[],[f19,f18])).

fof(f19,plain,(
    ! [X0] : v1_orders_2(k2_yellow_1(X0)) ),
    inference(cnf_transformation,[],[f3])).

fof(f22,plain,(
    ! [X0] :
      ( ~ v1_orders_2(X0)
      | ~ l1_orders_2(X0)
      | g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = X0 ) ),
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',abstractness_v1_orders_2)).

fof(f24,plain,(
    ! [X2,X0,X3,X1] :
      ( g1_orders_2(X0,X1) != g1_orders_2(X2,X3)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | X1 = X3 ) ),
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',free_g1_orders_2)).

fof(f21,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_u1_orders_2)).

fof(f52,plain,(
    ! [X10,X11,X9] :
      ( ~ m1_subset_1(k1_yellow_1(X9),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_orders_2(X9,k1_yellow_1(X9))),u1_struct_0(g1_orders_2(X9,k1_yellow_1(X9))))))
      | g1_orders_2(X9,k1_yellow_1(X9)) != g1_orders_2(X10,X11)
      | u1_struct_0(g1_orders_2(X9,k1_yellow_1(X9))) = X10 ) ),
    inference(backward_demodulation,[],[f36,f48])).

fof(f36,plain,(
    ! [X10,X11,X9] :
      ( g1_orders_2(X9,k1_yellow_1(X9)) != g1_orders_2(X10,X11)
      | ~ m1_subset_1(u1_orders_2(g1_orders_2(X9,k1_yellow_1(X9))),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_orders_2(X9,k1_yellow_1(X9))),u1_struct_0(g1_orders_2(X9,k1_yellow_1(X9))))))
      | u1_struct_0(g1_orders_2(X9,k1_yellow_1(X9))) = X10 ) ),
    inference(superposition,[],[f23,f30])).

% (16107)Refutation not found, incomplete strategy% (16107)------------------------------
% (16107)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (16107)Termination reason: Refutation not found, incomplete strategy

% (16107)Memory used [KB]: 10618
% (16107)Time elapsed: 0.092 s
% (16107)------------------------------
% (16107)------------------------------
fof(f23,plain,(
    ! [X2,X0,X3,X1] :
      ( g1_orders_2(X0,X1) != g1_orders_2(X2,X3)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | X0 = X2 ) ),
    inference(cnf_transformation,[],[f14])).

fof(f26,plain,(
    k1_zfmisc_1(sK0) != u1_struct_0(g1_orders_2(k1_zfmisc_1(sK0),k1_yellow_1(k1_zfmisc_1(sK0)))) ),
    inference(definition_unfolding,[],[f15,f16,f25])).

fof(f25,plain,(
    ! [X0] : k3_yellow_1(X0) = g1_orders_2(k1_zfmisc_1(X0),k1_yellow_1(k1_zfmisc_1(X0))) ),
    inference(definition_unfolding,[],[f17,f18,f16])).

fof(f17,plain,(
    ! [X0] : k3_yellow_1(X0) = k2_yellow_1(k9_setfam_1(X0)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] : k3_yellow_1(X0) = k2_yellow_1(k9_setfam_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_yellow_1)).

fof(f16,plain,(
    ! [X0] : k9_setfam_1(X0) = k1_zfmisc_1(X0) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : k9_setfam_1(X0) = k1_zfmisc_1(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k9_setfam_1)).

fof(f15,plain,(
    k9_setfam_1(sK0) != u1_struct_0(k3_yellow_1(sK0)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ? [X0] : k9_setfam_1(X0) != u1_struct_0(k3_yellow_1(X0)) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,negated_conjecture,(
    ~ ! [X0] : k9_setfam_1(X0) = u1_struct_0(k3_yellow_1(X0)) ),
    inference(negated_conjecture,[],[f8])).

fof(f8,conjecture,(
    ! [X0] : k9_setfam_1(X0) = u1_struct_0(k3_yellow_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_waybel_7)).

%------------------------------------------------------------------------------
