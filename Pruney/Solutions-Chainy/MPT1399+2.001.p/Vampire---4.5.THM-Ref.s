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
% DateTime   : Thu Dec  3 13:15:11 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 1.45s
% Verified   : 
% Statistics : Number of formulae       :  113 ( 722 expanded)
%              Number of leaves         :   23 ( 184 expanded)
%              Depth                    :   14
%              Number of atoms          :  266 (3657 expanded)
%              Number of equality atoms :   51 ( 578 expanded)
%              Maximal formula depth    :   15 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f505,plain,(
    $false ),
    inference(unit_resulting_resolution,[],[f255,f220,f425,f411,f426,f58])).

fof(f58,plain,(
    ! [X3] :
      ( ~ r2_hidden(sK1,X3)
      | ~ v3_pre_topc(X3,sK0)
      | ~ v4_pre_topc(X3,sK0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))
      | r2_hidden(X3,sK2) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( k1_xboole_0 = X2
              & ! [X3] :
                  ( ( r2_hidden(X3,X2)
                  <=> ( r2_hidden(X1,X3)
                      & v4_pre_topc(X3,X0)
                      & v3_pre_topc(X3,X0) ) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f35])).

fof(f35,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( k1_xboole_0 = X2
              & ! [X3] :
                  ( ( r2_hidden(X3,X2)
                  <=> ( r2_hidden(X1,X3)
                      & v4_pre_topc(X3,X0)
                      & v3_pre_topc(X3,X0) ) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f33])).

fof(f33,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
               => ~ ( k1_xboole_0 = X2
                    & ! [X3] :
                        ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                       => ( r2_hidden(X3,X2)
                        <=> ( r2_hidden(X1,X3)
                            & v4_pre_topc(X3,X0)
                            & v3_pre_topc(X3,X0) ) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f32])).

fof(f32,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
             => ~ ( k1_xboole_0 = X2
                  & ! [X3] :
                      ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                     => ( r2_hidden(X3,X2)
                      <=> ( r2_hidden(X1,X3)
                          & v4_pre_topc(X3,X0)
                          & v3_pre_topc(X3,X0) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_connsp_2)).

fof(f426,plain,(
    v3_pre_topc(u1_struct_0(sK0),sK0) ),
    inference(backward_demodulation,[],[f169,f408])).

fof(f408,plain,(
    ! [X0] : k4_xboole_0(X0,sK2) = X0 ),
    inference(backward_demodulation,[],[f100,f403])).

fof(f403,plain,(
    ! [X1] : sK2 = k4_xboole_0(X1,X1) ),
    inference(superposition,[],[f246,f174])).

fof(f174,plain,(
    ! [X1] : k2_xboole_0(sK2,X1) = X1 ),
    inference(superposition,[],[f102,f95])).

fof(f95,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(f102,plain,(
    ! [X0] : k2_xboole_0(X0,sK2) = X0 ),
    inference(definition_unfolding,[],[f68,f60])).

fof(f60,plain,(
    k1_xboole_0 = sK2 ),
    inference(cnf_transformation,[],[f36])).

fof(f68,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).

fof(f246,plain,(
    ! [X9] : sK2 = k2_xboole_0(sK2,k4_xboole_0(X9,X9)) ),
    inference(backward_demodulation,[],[f241,f245])).

fof(f245,plain,(
    ! [X10,X11] : k4_xboole_0(k4_xboole_0(X10,sK2),X11) = k4_xboole_0(X10,X11) ),
    inference(forward_demodulation,[],[f244,f108])).

fof(f108,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(definition_unfolding,[],[f92,f93])).

fof(f93,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f92,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_xboole_1)).

fof(f244,plain,(
    ! [X10,X11] : k4_xboole_0(k4_xboole_0(X10,sK2),X11) = k4_xboole_0(X10,k4_xboole_0(X10,k4_xboole_0(X10,X11))) ),
    inference(backward_demodulation,[],[f230,f243])).

fof(f243,plain,(
    ! [X14,X15] : k4_xboole_0(X14,k4_xboole_0(k4_xboole_0(X14,sK2),X15)) = k4_xboole_0(X14,k4_xboole_0(X14,X15)) ),
    inference(forward_demodulation,[],[f232,f174])).

fof(f232,plain,(
    ! [X14,X15] : k4_xboole_0(X14,k4_xboole_0(k4_xboole_0(X14,sK2),X15)) = k2_xboole_0(sK2,k4_xboole_0(X14,k4_xboole_0(X14,X15))) ),
    inference(superposition,[],[f105,f103])).

fof(f103,plain,(
    ! [X0] : sK2 = k4_xboole_0(X0,k4_xboole_0(X0,sK2)) ),
    inference(definition_unfolding,[],[f69,f60,f93,f60])).

fof(f69,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

fof(f105,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,k4_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X2))) ),
    inference(definition_unfolding,[],[f89,f93])).

fof(f89,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,k4_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X2)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(X0,k4_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_xboole_1)).

fof(f230,plain,(
    ! [X10,X11] : k4_xboole_0(k4_xboole_0(X10,sK2),X11) = k4_xboole_0(X10,k4_xboole_0(X10,k4_xboole_0(k4_xboole_0(X10,sK2),X11))) ),
    inference(superposition,[],[f106,f103])).

fof(f106,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2) ),
    inference(definition_unfolding,[],[f90,f93,f93])).

fof(f90,plain,(
    ! [X2,X0,X1] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_xboole_1)).

fof(f241,plain,(
    ! [X9] : sK2 = k2_xboole_0(sK2,k4_xboole_0(k4_xboole_0(X9,sK2),X9)) ),
    inference(forward_demodulation,[],[f240,f103])).

fof(f240,plain,(
    ! [X9] : k4_xboole_0(X9,k4_xboole_0(X9,sK2)) = k2_xboole_0(sK2,k4_xboole_0(k4_xboole_0(X9,sK2),X9)) ),
    inference(forward_demodulation,[],[f229,f227])).

fof(f227,plain,(
    ! [X7] : k2_xboole_0(X7,k4_xboole_0(X7,sK2)) = X7 ),
    inference(superposition,[],[f109,f103])).

fof(f109,plain,(
    ! [X0,X1] : k2_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = X0 ),
    inference(definition_unfolding,[],[f94,f93])).

fof(f94,plain,(
    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_xboole_1)).

fof(f229,plain,(
    ! [X9] : k2_xboole_0(sK2,k4_xboole_0(k4_xboole_0(X9,sK2),X9)) = k4_xboole_0(k2_xboole_0(X9,k4_xboole_0(X9,sK2)),k4_xboole_0(X9,sK2)) ),
    inference(superposition,[],[f107,f103])).

fof(f107,plain,(
    ! [X0,X1] : k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) = k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(definition_unfolding,[],[f91,f93])).

fof(f91,plain,(
    ! [X0,X1] : k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1)) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] : k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1)) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_xboole_1)).

fof(f100,plain,(
    ! [X0] : k4_xboole_0(X0,k4_xboole_0(X0,X0)) = X0 ),
    inference(definition_unfolding,[],[f66,f93])).

fof(f66,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

fof(f169,plain,(
    v3_pre_topc(k4_xboole_0(u1_struct_0(sK0),sK2),sK0) ),
    inference(forward_demodulation,[],[f168,f129])).

fof(f129,plain,(
    ! [X0] : k4_xboole_0(X0,sK2) = k3_subset_1(X0,sK2) ),
    inference(unit_resulting_resolution,[],[f104,f97])).

fof(f97,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

fof(f104,plain,(
    ! [X0] : m1_subset_1(sK2,k1_zfmisc_1(X0)) ),
    inference(definition_unfolding,[],[f70,f60])).

fof(f70,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

fof(f168,plain,(
    v3_pre_topc(k3_subset_1(u1_struct_0(sK0),sK2),sK0) ),
    inference(unit_resulting_resolution,[],[f64,f104,f141,f75])).

fof(f75,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)
      | ~ v4_pre_topc(X1,X0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v4_pre_topc(X1,X0)
          <=> v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f30])).

fof(f30,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v4_pre_topc(X1,X0)
          <=> v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_tops_1)).

fof(f141,plain,(
    v4_pre_topc(sK2,sK0) ),
    inference(unit_resulting_resolution,[],[f63,f64,f104,f130,f71])).

fof(f71,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v1_xboole_0(X1)
      | v4_pre_topc(X1,X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v4_pre_topc(X1,X0)
          | ~ v1_xboole_0(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f39])).

fof(f39,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v4_pre_topc(X1,X0)
          | ~ v1_xboole_0(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f27])).

fof(f27,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v1_xboole_0(X1)
           => v4_pre_topc(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_pre_topc)).

fof(f130,plain,(
    v1_xboole_0(sK2) ),
    inference(unit_resulting_resolution,[],[f83,f104,f84])).

fof(f84,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f48,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_xboole_0(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_subset_1)).

fof(f83,plain,(
    ! [X0] : v1_xboole_0(sK3(X0)) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0] :
    ? [X1] :
      ( v1_xboole_0(X1)
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',rc2_subset_1)).

fof(f63,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f36])).

fof(f64,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f36])).

fof(f411,plain,(
    ! [X0] : m1_subset_1(X0,k1_zfmisc_1(X0)) ),
    inference(backward_demodulation,[],[f135,f408])).

fof(f135,plain,(
    ! [X0] : m1_subset_1(k4_xboole_0(X0,sK2),k1_zfmisc_1(X0)) ),
    inference(forward_demodulation,[],[f128,f129])).

fof(f128,plain,(
    ! [X0] : m1_subset_1(k3_subset_1(X0,sK2),k1_zfmisc_1(X0)) ),
    inference(unit_resulting_resolution,[],[f104,f98])).

fof(f98,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f53,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_subset_1)).

fof(f425,plain,(
    v4_pre_topc(u1_struct_0(sK0),sK0) ),
    inference(backward_demodulation,[],[f171,f408])).

fof(f171,plain,(
    v4_pre_topc(k4_xboole_0(u1_struct_0(sK0),sK2),sK0) ),
    inference(forward_demodulation,[],[f170,f129])).

fof(f170,plain,(
    v4_pre_topc(k3_subset_1(u1_struct_0(sK0),sK2),sK0) ),
    inference(unit_resulting_resolution,[],[f64,f104,f142,f73])).

fof(f73,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v4_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)
      | ~ v3_pre_topc(X1,X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v3_pre_topc(X1,X0)
          <=> v4_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f31])).

fof(f31,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v3_pre_topc(X1,X0)
          <=> v4_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t30_tops_1)).

fof(f142,plain,(
    v3_pre_topc(sK2,sK0) ),
    inference(unit_resulting_resolution,[],[f63,f64,f104,f130,f76])).

fof(f76,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v1_xboole_0(X1)
      | v3_pre_topc(X1,X0) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v3_pre_topc(X1,X0)
          | ~ v1_xboole_0(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f43])).

fof(f43,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v3_pre_topc(X1,X0)
          | ~ v1_xboole_0(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f28])).

fof(f28,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v1_xboole_0(X1)
           => v3_pre_topc(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_tops_1)).

fof(f220,plain,(
    r2_hidden(sK1,u1_struct_0(sK0)) ),
    inference(unit_resulting_resolution,[],[f61,f208,f81])).

fof(f81,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,X0)
      | r2_hidden(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ( ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) )
        | ~ v1_xboole_0(X0) )
      & ( ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) )
        | v1_xboole_0(X0) ) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( ( v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) ) )
      & ( ~ v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).

fof(f208,plain,(
    ~ v1_xboole_0(u1_struct_0(sK0)) ),
    inference(unit_resulting_resolution,[],[f116,f115,f84])).

fof(f115,plain,(
    m1_subset_1(sK4(sK0),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(unit_resulting_resolution,[],[f63,f62,f64,f85])).

fof(f85,plain,(
    ! [X0] :
      ( v2_struct_0(X0)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | m1_subset_1(sK4(X0),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f50,plain,(
    ! [X0] :
      ( ? [X1] :
          ( v4_pre_topc(X1,X0)
          & v3_pre_topc(X1,X0)
          & ~ v1_xboole_0(X1)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f49])).

fof(f49,plain,(
    ! [X0] :
      ( ? [X1] :
          ( v4_pre_topc(X1,X0)
          & v3_pre_topc(X1,X0)
          & ~ v1_xboole_0(X1)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f29])).

fof(f29,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ? [X1] :
          ( v4_pre_topc(X1,X0)
          & v3_pre_topc(X1,X0)
          & ~ v1_xboole_0(X1)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',rc3_tops_1)).

fof(f62,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f36])).

fof(f116,plain,(
    ~ v1_xboole_0(sK4(sK0)) ),
    inference(unit_resulting_resolution,[],[f62,f63,f64,f86])).

fof(f86,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(sK4(X0))
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f61,plain,(
    m1_subset_1(sK1,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f36])).

fof(f255,plain,(
    ~ r2_hidden(u1_struct_0(sK0),sK2) ),
    inference(unit_resulting_resolution,[],[f104,f219,f77])).

fof(f77,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1)
      | m1_subset_1(X0,X2) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f45])).

fof(f45,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).

fof(f219,plain,(
    ~ m1_subset_1(u1_struct_0(sK0),sK2) ),
    inference(unit_resulting_resolution,[],[f130,f208,f79])).

fof(f79,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X0)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f47])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 18:11:11 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.50  % (18954)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.20/0.51  % (18968)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.20/0.51  % (18947)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.20/0.51  % (18960)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.20/0.51  % (18956)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.20/0.51  % (18949)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.20/0.52  % (18955)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.20/0.52  % (18953)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.20/0.52  % (18965)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.20/0.52  % (18964)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.20/0.52  % (18966)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.20/0.53  % (18957)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.53  % (18958)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.20/0.53  % (18967)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.20/0.53  % (18972)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.20/0.53  % (18946)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.20/0.53  % (18974)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.20/0.53  % (18950)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.20/0.53  % (18959)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.20/0.53  % (18948)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.20/0.54  % (18945)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.20/0.54  % (18951)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.20/0.54  % (18949)Refutation found. Thanks to Tanya!
% 0.20/0.54  % SZS status Theorem for theBenchmark
% 0.20/0.54  % (18961)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.20/0.54  % (18952)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.20/0.54  % (18969)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.20/0.54  % (18971)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.20/0.55  % (18970)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 1.45/0.55  % (18962)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 1.45/0.55  % (18973)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 1.45/0.55  % (18963)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 1.45/0.55  % SZS output start Proof for theBenchmark
% 1.45/0.55  fof(f505,plain,(
% 1.45/0.55    $false),
% 1.45/0.55    inference(unit_resulting_resolution,[],[f255,f220,f425,f411,f426,f58])).
% 1.45/0.55  fof(f58,plain,(
% 1.45/0.55    ( ! [X3] : (~r2_hidden(sK1,X3) | ~v3_pre_topc(X3,sK0) | ~v4_pre_topc(X3,sK0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) | r2_hidden(X3,sK2)) )),
% 1.45/0.55    inference(cnf_transformation,[],[f36])).
% 1.45/0.55  fof(f36,plain,(
% 1.45/0.55    ? [X0] : (? [X1] : (? [X2] : (k1_xboole_0 = X2 & ! [X3] : ((r2_hidden(X3,X2) <=> (r2_hidden(X1,X3) & v4_pre_topc(X3,X0) & v3_pre_topc(X3,X0))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 1.45/0.55    inference(flattening,[],[f35])).
% 1.45/0.55  fof(f35,plain,(
% 1.45/0.55    ? [X0] : (? [X1] : (? [X2] : ((k1_xboole_0 = X2 & ! [X3] : ((r2_hidden(X3,X2) <=> (r2_hidden(X1,X3) & v4_pre_topc(X3,X0) & v3_pre_topc(X3,X0))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & m1_subset_1(X1,u1_struct_0(X0))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 1.45/0.55    inference(ennf_transformation,[],[f33])).
% 1.45/0.55  fof(f33,negated_conjecture,(
% 1.45/0.55    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => ~(k1_xboole_0 = X2 & ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) => (r2_hidden(X3,X2) <=> (r2_hidden(X1,X3) & v4_pre_topc(X3,X0) & v3_pre_topc(X3,X0))))))))),
% 1.45/0.55    inference(negated_conjecture,[],[f32])).
% 1.45/0.55  fof(f32,conjecture,(
% 1.45/0.55    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => ~(k1_xboole_0 = X2 & ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) => (r2_hidden(X3,X2) <=> (r2_hidden(X1,X3) & v4_pre_topc(X3,X0) & v3_pre_topc(X3,X0))))))))),
% 1.45/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_connsp_2)).
% 1.45/0.55  fof(f426,plain,(
% 1.45/0.55    v3_pre_topc(u1_struct_0(sK0),sK0)),
% 1.45/0.55    inference(backward_demodulation,[],[f169,f408])).
% 1.45/0.55  fof(f408,plain,(
% 1.45/0.55    ( ! [X0] : (k4_xboole_0(X0,sK2) = X0) )),
% 1.45/0.55    inference(backward_demodulation,[],[f100,f403])).
% 1.45/0.55  fof(f403,plain,(
% 1.45/0.55    ( ! [X1] : (sK2 = k4_xboole_0(X1,X1)) )),
% 1.45/0.55    inference(superposition,[],[f246,f174])).
% 1.45/0.55  fof(f174,plain,(
% 1.45/0.55    ( ! [X1] : (k2_xboole_0(sK2,X1) = X1) )),
% 1.45/0.55    inference(superposition,[],[f102,f95])).
% 1.45/0.55  fof(f95,plain,(
% 1.45/0.55    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 1.45/0.55    inference(cnf_transformation,[],[f1])).
% 1.45/0.55  fof(f1,axiom,(
% 1.45/0.55    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 1.45/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).
% 1.45/0.55  fof(f102,plain,(
% 1.45/0.55    ( ! [X0] : (k2_xboole_0(X0,sK2) = X0) )),
% 1.45/0.55    inference(definition_unfolding,[],[f68,f60])).
% 1.45/0.55  fof(f60,plain,(
% 1.45/0.55    k1_xboole_0 = sK2),
% 1.45/0.55    inference(cnf_transformation,[],[f36])).
% 1.45/0.55  fof(f68,plain,(
% 1.45/0.55    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = X0) )),
% 1.45/0.55    inference(cnf_transformation,[],[f4])).
% 1.45/0.55  fof(f4,axiom,(
% 1.45/0.55    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0),
% 1.45/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).
% 1.45/0.55  fof(f246,plain,(
% 1.45/0.55    ( ! [X9] : (sK2 = k2_xboole_0(sK2,k4_xboole_0(X9,X9))) )),
% 1.45/0.55    inference(backward_demodulation,[],[f241,f245])).
% 1.45/0.55  fof(f245,plain,(
% 1.45/0.55    ( ! [X10,X11] : (k4_xboole_0(k4_xboole_0(X10,sK2),X11) = k4_xboole_0(X10,X11)) )),
% 1.45/0.55    inference(forward_demodulation,[],[f244,f108])).
% 1.45/0.55  fof(f108,plain,(
% 1.45/0.55    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) )),
% 1.45/0.55    inference(definition_unfolding,[],[f92,f93])).
% 1.45/0.55  fof(f93,plain,(
% 1.45/0.55    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 1.45/0.55    inference(cnf_transformation,[],[f8])).
% 1.45/0.55  fof(f8,axiom,(
% 1.45/0.55    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 1.45/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).
% 1.45/0.55  fof(f92,plain,(
% 1.45/0.55    ( ! [X0,X1] : (k4_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1)) )),
% 1.45/0.55    inference(cnf_transformation,[],[f7])).
% 1.45/0.56  fof(f7,axiom,(
% 1.45/0.56    ! [X0,X1] : k4_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1)),
% 1.45/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_xboole_1)).
% 1.45/0.56  fof(f244,plain,(
% 1.45/0.56    ( ! [X10,X11] : (k4_xboole_0(k4_xboole_0(X10,sK2),X11) = k4_xboole_0(X10,k4_xboole_0(X10,k4_xboole_0(X10,X11)))) )),
% 1.45/0.56    inference(backward_demodulation,[],[f230,f243])).
% 1.45/0.56  fof(f243,plain,(
% 1.45/0.56    ( ! [X14,X15] : (k4_xboole_0(X14,k4_xboole_0(k4_xboole_0(X14,sK2),X15)) = k4_xboole_0(X14,k4_xboole_0(X14,X15))) )),
% 1.45/0.56    inference(forward_demodulation,[],[f232,f174])).
% 1.45/0.56  fof(f232,plain,(
% 1.45/0.56    ( ! [X14,X15] : (k4_xboole_0(X14,k4_xboole_0(k4_xboole_0(X14,sK2),X15)) = k2_xboole_0(sK2,k4_xboole_0(X14,k4_xboole_0(X14,X15)))) )),
% 1.45/0.56    inference(superposition,[],[f105,f103])).
% 1.45/0.56  fof(f103,plain,(
% 1.45/0.56    ( ! [X0] : (sK2 = k4_xboole_0(X0,k4_xboole_0(X0,sK2))) )),
% 1.45/0.56    inference(definition_unfolding,[],[f69,f60,f93,f60])).
% 1.45/0.56  fof(f69,plain,(
% 1.45/0.56    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)) )),
% 1.45/0.56    inference(cnf_transformation,[],[f6])).
% 1.45/0.56  fof(f6,axiom,(
% 1.45/0.56    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)),
% 1.45/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).
% 1.45/0.56  fof(f105,plain,(
% 1.45/0.56    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X2)))) )),
% 1.45/0.56    inference(definition_unfolding,[],[f89,f93])).
% 1.45/0.56  fof(f89,plain,(
% 1.45/0.56    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X2))) )),
% 1.45/0.56    inference(cnf_transformation,[],[f10])).
% 1.45/0.56  fof(f10,axiom,(
% 1.45/0.56    ! [X0,X1,X2] : k4_xboole_0(X0,k4_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X2))),
% 1.45/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_xboole_1)).
% 1.45/0.56  fof(f230,plain,(
% 1.45/0.56    ( ! [X10,X11] : (k4_xboole_0(k4_xboole_0(X10,sK2),X11) = k4_xboole_0(X10,k4_xboole_0(X10,k4_xboole_0(k4_xboole_0(X10,sK2),X11)))) )),
% 1.45/0.56    inference(superposition,[],[f106,f103])).
% 1.45/0.56  fof(f106,plain,(
% 1.45/0.56    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2)) )),
% 1.45/0.56    inference(definition_unfolding,[],[f90,f93,f93])).
% 1.45/0.56  fof(f90,plain,(
% 1.45/0.56    ( ! [X2,X0,X1] : (k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2)) )),
% 1.45/0.56    inference(cnf_transformation,[],[f9])).
% 1.45/0.56  fof(f9,axiom,(
% 1.45/0.56    ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2)),
% 1.45/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_xboole_1)).
% 1.45/0.56  fof(f241,plain,(
% 1.45/0.56    ( ! [X9] : (sK2 = k2_xboole_0(sK2,k4_xboole_0(k4_xboole_0(X9,sK2),X9))) )),
% 1.45/0.56    inference(forward_demodulation,[],[f240,f103])).
% 1.45/0.56  fof(f240,plain,(
% 1.45/0.56    ( ! [X9] : (k4_xboole_0(X9,k4_xboole_0(X9,sK2)) = k2_xboole_0(sK2,k4_xboole_0(k4_xboole_0(X9,sK2),X9))) )),
% 1.45/0.56    inference(forward_demodulation,[],[f229,f227])).
% 1.45/0.56  fof(f227,plain,(
% 1.45/0.56    ( ! [X7] : (k2_xboole_0(X7,k4_xboole_0(X7,sK2)) = X7) )),
% 1.45/0.56    inference(superposition,[],[f109,f103])).
% 1.45/0.56  fof(f109,plain,(
% 1.45/0.56    ( ! [X0,X1] : (k2_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = X0) )),
% 1.45/0.56    inference(definition_unfolding,[],[f94,f93])).
% 1.45/0.56  fof(f94,plain,(
% 1.45/0.56    ( ! [X0,X1] : (k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0) )),
% 1.45/0.56    inference(cnf_transformation,[],[f5])).
% 1.45/0.56  fof(f5,axiom,(
% 1.45/0.56    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0),
% 1.45/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_xboole_1)).
% 1.45/0.56  fof(f229,plain,(
% 1.45/0.56    ( ! [X9] : (k2_xboole_0(sK2,k4_xboole_0(k4_xboole_0(X9,sK2),X9)) = k4_xboole_0(k2_xboole_0(X9,k4_xboole_0(X9,sK2)),k4_xboole_0(X9,sK2))) )),
% 1.45/0.56    inference(superposition,[],[f107,f103])).
% 1.45/0.56  fof(f107,plain,(
% 1.45/0.56    ( ! [X0,X1] : (k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) = k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1)))) )),
% 1.45/0.56    inference(definition_unfolding,[],[f91,f93])).
% 1.45/0.56  fof(f91,plain,(
% 1.45/0.56    ( ! [X0,X1] : (k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1)) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0))) )),
% 1.45/0.56    inference(cnf_transformation,[],[f11])).
% 1.45/0.56  fof(f11,axiom,(
% 1.45/0.56    ! [X0,X1] : k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1)) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0))),
% 1.45/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_xboole_1)).
% 1.45/0.56  fof(f100,plain,(
% 1.45/0.56    ( ! [X0] : (k4_xboole_0(X0,k4_xboole_0(X0,X0)) = X0) )),
% 1.45/0.56    inference(definition_unfolding,[],[f66,f93])).
% 1.45/0.56  fof(f66,plain,(
% 1.45/0.56    ( ! [X0] : (k3_xboole_0(X0,X0) = X0) )),
% 1.45/0.56    inference(cnf_transformation,[],[f34])).
% 1.45/0.56  fof(f34,plain,(
% 1.45/0.56    ! [X0] : k3_xboole_0(X0,X0) = X0),
% 1.45/0.56    inference(rectify,[],[f2])).
% 1.45/0.56  fof(f2,axiom,(
% 1.45/0.56    ! [X0,X1] : k3_xboole_0(X0,X0) = X0),
% 1.45/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).
% 1.45/0.56  fof(f169,plain,(
% 1.45/0.56    v3_pre_topc(k4_xboole_0(u1_struct_0(sK0),sK2),sK0)),
% 1.45/0.56    inference(forward_demodulation,[],[f168,f129])).
% 1.45/0.56  fof(f129,plain,(
% 1.45/0.56    ( ! [X0] : (k4_xboole_0(X0,sK2) = k3_subset_1(X0,sK2)) )),
% 1.45/0.56    inference(unit_resulting_resolution,[],[f104,f97])).
% 1.45/0.56  fof(f97,plain,(
% 1.45/0.56    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 1.45/0.56    inference(cnf_transformation,[],[f52])).
% 1.45/0.56  fof(f52,plain,(
% 1.45/0.56    ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.45/0.56    inference(ennf_transformation,[],[f16])).
% 1.45/0.56  fof(f16,axiom,(
% 1.45/0.56    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1))),
% 1.45/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).
% 1.45/0.56  fof(f104,plain,(
% 1.45/0.56    ( ! [X0] : (m1_subset_1(sK2,k1_zfmisc_1(X0))) )),
% 1.45/0.56    inference(definition_unfolding,[],[f70,f60])).
% 1.45/0.56  fof(f70,plain,(
% 1.45/0.56    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 1.45/0.56    inference(cnf_transformation,[],[f19])).
% 1.45/0.56  fof(f19,axiom,(
% 1.45/0.56    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 1.45/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).
% 1.45/0.56  fof(f168,plain,(
% 1.45/0.56    v3_pre_topc(k3_subset_1(u1_struct_0(sK0),sK2),sK0)),
% 1.45/0.56    inference(unit_resulting_resolution,[],[f64,f104,f141,f75])).
% 1.45/0.56  fof(f75,plain,(
% 1.45/0.56    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) | ~v4_pre_topc(X1,X0)) )),
% 1.45/0.56    inference(cnf_transformation,[],[f42])).
% 1.45/0.56  fof(f42,plain,(
% 1.45/0.56    ! [X0] : (! [X1] : ((v4_pre_topc(X1,X0) <=> v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.45/0.56    inference(ennf_transformation,[],[f30])).
% 1.45/0.56  fof(f30,axiom,(
% 1.45/0.56    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_pre_topc(X1,X0) <=> v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0))))),
% 1.45/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_tops_1)).
% 1.45/0.56  fof(f141,plain,(
% 1.45/0.56    v4_pre_topc(sK2,sK0)),
% 1.45/0.56    inference(unit_resulting_resolution,[],[f63,f64,f104,f130,f71])).
% 1.45/0.56  fof(f71,plain,(
% 1.45/0.56    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v1_xboole_0(X1) | v4_pre_topc(X1,X0)) )),
% 1.45/0.56    inference(cnf_transformation,[],[f40])).
% 1.45/0.56  fof(f40,plain,(
% 1.45/0.56    ! [X0] : (! [X1] : (v4_pre_topc(X1,X0) | ~v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 1.45/0.56    inference(flattening,[],[f39])).
% 1.45/0.56  fof(f39,plain,(
% 1.45/0.56    ! [X0] : (! [X1] : ((v4_pre_topc(X1,X0) | ~v1_xboole_0(X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 1.45/0.56    inference(ennf_transformation,[],[f27])).
% 1.45/0.56  fof(f27,axiom,(
% 1.45/0.56    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v1_xboole_0(X1) => v4_pre_topc(X1,X0))))),
% 1.45/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_pre_topc)).
% 1.45/0.56  fof(f130,plain,(
% 1.45/0.56    v1_xboole_0(sK2)),
% 1.45/0.56    inference(unit_resulting_resolution,[],[f83,f104,f84])).
% 1.45/0.56  fof(f84,plain,(
% 1.45/0.56    ( ! [X0,X1] : (~v1_xboole_0(X0) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | v1_xboole_0(X1)) )),
% 1.45/0.56    inference(cnf_transformation,[],[f48])).
% 1.45/0.56  fof(f48,plain,(
% 1.45/0.56    ! [X0] : (! [X1] : (v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_xboole_0(X0))),
% 1.45/0.56    inference(ennf_transformation,[],[f20])).
% 1.45/0.56  fof(f20,axiom,(
% 1.45/0.56    ! [X0] : (v1_xboole_0(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_xboole_0(X1)))),
% 1.45/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_subset_1)).
% 1.45/0.56  fof(f83,plain,(
% 1.45/0.56    ( ! [X0] : (v1_xboole_0(sK3(X0))) )),
% 1.45/0.56    inference(cnf_transformation,[],[f18])).
% 1.45/0.56  fof(f18,axiom,(
% 1.45/0.56    ! [X0] : ? [X1] : (v1_xboole_0(X1) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.45/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',rc2_subset_1)).
% 1.45/0.56  fof(f63,plain,(
% 1.45/0.56    v2_pre_topc(sK0)),
% 1.45/0.56    inference(cnf_transformation,[],[f36])).
% 1.45/0.56  fof(f64,plain,(
% 1.45/0.56    l1_pre_topc(sK0)),
% 1.45/0.56    inference(cnf_transformation,[],[f36])).
% 1.45/0.56  fof(f411,plain,(
% 1.45/0.56    ( ! [X0] : (m1_subset_1(X0,k1_zfmisc_1(X0))) )),
% 1.45/0.56    inference(backward_demodulation,[],[f135,f408])).
% 1.45/0.56  fof(f135,plain,(
% 1.45/0.56    ( ! [X0] : (m1_subset_1(k4_xboole_0(X0,sK2),k1_zfmisc_1(X0))) )),
% 1.45/0.56    inference(forward_demodulation,[],[f128,f129])).
% 1.45/0.56  fof(f128,plain,(
% 1.45/0.56    ( ! [X0] : (m1_subset_1(k3_subset_1(X0,sK2),k1_zfmisc_1(X0))) )),
% 1.45/0.56    inference(unit_resulting_resolution,[],[f104,f98])).
% 1.45/0.56  fof(f98,plain,(
% 1.45/0.56    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))) )),
% 1.45/0.56    inference(cnf_transformation,[],[f53])).
% 1.45/0.56  fof(f53,plain,(
% 1.45/0.56    ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.45/0.56    inference(ennf_transformation,[],[f17])).
% 1.45/0.56  fof(f17,axiom,(
% 1.45/0.56    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)))),
% 1.45/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_subset_1)).
% 1.45/0.56  fof(f425,plain,(
% 1.45/0.56    v4_pre_topc(u1_struct_0(sK0),sK0)),
% 1.45/0.56    inference(backward_demodulation,[],[f171,f408])).
% 1.45/0.56  fof(f171,plain,(
% 1.45/0.56    v4_pre_topc(k4_xboole_0(u1_struct_0(sK0),sK2),sK0)),
% 1.45/0.56    inference(forward_demodulation,[],[f170,f129])).
% 1.45/0.56  fof(f170,plain,(
% 1.45/0.56    v4_pre_topc(k3_subset_1(u1_struct_0(sK0),sK2),sK0)),
% 1.45/0.56    inference(unit_resulting_resolution,[],[f64,f104,f142,f73])).
% 1.45/0.56  fof(f73,plain,(
% 1.45/0.56    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v4_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) | ~v3_pre_topc(X1,X0)) )),
% 1.45/0.56    inference(cnf_transformation,[],[f41])).
% 1.45/0.56  fof(f41,plain,(
% 1.45/0.56    ! [X0] : (! [X1] : ((v3_pre_topc(X1,X0) <=> v4_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.45/0.56    inference(ennf_transformation,[],[f31])).
% 1.45/0.56  fof(f31,axiom,(
% 1.45/0.56    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_pre_topc(X1,X0) <=> v4_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0))))),
% 1.45/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t30_tops_1)).
% 1.45/0.56  fof(f142,plain,(
% 1.45/0.56    v3_pre_topc(sK2,sK0)),
% 1.45/0.56    inference(unit_resulting_resolution,[],[f63,f64,f104,f130,f76])).
% 1.45/0.56  fof(f76,plain,(
% 1.45/0.56    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v1_xboole_0(X1) | v3_pre_topc(X1,X0)) )),
% 1.45/0.56    inference(cnf_transformation,[],[f44])).
% 1.45/0.56  fof(f44,plain,(
% 1.45/0.56    ! [X0] : (! [X1] : (v3_pre_topc(X1,X0) | ~v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 1.45/0.56    inference(flattening,[],[f43])).
% 1.45/0.56  fof(f43,plain,(
% 1.45/0.56    ! [X0] : (! [X1] : ((v3_pre_topc(X1,X0) | ~v1_xboole_0(X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 1.45/0.56    inference(ennf_transformation,[],[f28])).
% 1.45/0.56  fof(f28,axiom,(
% 1.45/0.56    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v1_xboole_0(X1) => v3_pre_topc(X1,X0))))),
% 1.45/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_tops_1)).
% 1.45/0.56  fof(f220,plain,(
% 1.45/0.56    r2_hidden(sK1,u1_struct_0(sK0))),
% 1.45/0.56    inference(unit_resulting_resolution,[],[f61,f208,f81])).
% 1.45/0.56  fof(f81,plain,(
% 1.45/0.56    ( ! [X0,X1] : (~m1_subset_1(X1,X0) | r2_hidden(X1,X0) | v1_xboole_0(X0)) )),
% 1.45/0.56    inference(cnf_transformation,[],[f47])).
% 1.45/0.56  fof(f47,plain,(
% 1.45/0.56    ! [X0,X1] : (((m1_subset_1(X1,X0) <=> v1_xboole_0(X1)) | ~v1_xboole_0(X0)) & ((m1_subset_1(X1,X0) <=> r2_hidden(X1,X0)) | v1_xboole_0(X0)))),
% 1.45/0.56    inference(ennf_transformation,[],[f15])).
% 1.45/0.56  fof(f15,axiom,(
% 1.45/0.56    ! [X0,X1] : ((v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> v1_xboole_0(X1))) & (~v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> r2_hidden(X1,X0))))),
% 1.45/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).
% 1.45/0.56  fof(f208,plain,(
% 1.45/0.56    ~v1_xboole_0(u1_struct_0(sK0))),
% 1.45/0.56    inference(unit_resulting_resolution,[],[f116,f115,f84])).
% 1.45/0.56  fof(f115,plain,(
% 1.45/0.56    m1_subset_1(sK4(sK0),k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.45/0.56    inference(unit_resulting_resolution,[],[f63,f62,f64,f85])).
% 1.45/0.56  fof(f85,plain,(
% 1.45/0.56    ( ! [X0] : (v2_struct_0(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | m1_subset_1(sK4(X0),k1_zfmisc_1(u1_struct_0(X0)))) )),
% 1.45/0.56    inference(cnf_transformation,[],[f50])).
% 1.45/0.56  fof(f50,plain,(
% 1.45/0.56    ! [X0] : (? [X1] : (v4_pre_topc(X1,X0) & v3_pre_topc(X1,X0) & ~v1_xboole_0(X1) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.45/0.56    inference(flattening,[],[f49])).
% 1.45/0.56  fof(f49,plain,(
% 1.45/0.56    ! [X0] : (? [X1] : (v4_pre_topc(X1,X0) & v3_pre_topc(X1,X0) & ~v1_xboole_0(X1) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 1.45/0.56    inference(ennf_transformation,[],[f29])).
% 1.45/0.56  fof(f29,axiom,(
% 1.45/0.56    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ? [X1] : (v4_pre_topc(X1,X0) & v3_pre_topc(X1,X0) & ~v1_xboole_0(X1) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))))),
% 1.45/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',rc3_tops_1)).
% 1.45/0.56  fof(f62,plain,(
% 1.45/0.56    ~v2_struct_0(sK0)),
% 1.45/0.56    inference(cnf_transformation,[],[f36])).
% 1.45/0.56  fof(f116,plain,(
% 1.45/0.56    ~v1_xboole_0(sK4(sK0))),
% 1.45/0.56    inference(unit_resulting_resolution,[],[f62,f63,f64,f86])).
% 1.45/0.56  fof(f86,plain,(
% 1.45/0.56    ( ! [X0] : (~v1_xboole_0(sK4(X0)) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.45/0.56    inference(cnf_transformation,[],[f50])).
% 1.45/0.56  fof(f61,plain,(
% 1.45/0.56    m1_subset_1(sK1,u1_struct_0(sK0))),
% 1.45/0.56    inference(cnf_transformation,[],[f36])).
% 1.45/0.56  fof(f255,plain,(
% 1.45/0.56    ~r2_hidden(u1_struct_0(sK0),sK2)),
% 1.45/0.56    inference(unit_resulting_resolution,[],[f104,f219,f77])).
% 1.45/0.56  fof(f77,plain,(
% 1.45/0.56    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1) | m1_subset_1(X0,X2)) )),
% 1.45/0.56    inference(cnf_transformation,[],[f46])).
% 1.45/0.56  fof(f46,plain,(
% 1.45/0.56    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 1.45/0.56    inference(flattening,[],[f45])).
% 1.45/0.56  fof(f45,plain,(
% 1.45/0.56    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)))),
% 1.45/0.56    inference(ennf_transformation,[],[f21])).
% 1.45/0.56  fof(f21,axiom,(
% 1.45/0.56    ! [X0,X1,X2] : ((m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1)) => m1_subset_1(X0,X2))),
% 1.45/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).
% 1.45/0.56  fof(f219,plain,(
% 1.45/0.56    ~m1_subset_1(u1_struct_0(sK0),sK2)),
% 1.45/0.56    inference(unit_resulting_resolution,[],[f130,f208,f79])).
% 1.45/0.56  fof(f79,plain,(
% 1.45/0.56    ( ! [X0,X1] : (~v1_xboole_0(X0) | v1_xboole_0(X1) | ~m1_subset_1(X1,X0)) )),
% 1.45/0.56    inference(cnf_transformation,[],[f47])).
% 1.45/0.56  % SZS output end Proof for theBenchmark
% 1.45/0.56  % (18949)------------------------------
% 1.45/0.56  % (18949)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.45/0.56  % (18949)Termination reason: Refutation
% 1.45/0.56  
% 1.45/0.56  % (18949)Memory used [KB]: 6396
% 1.45/0.56  % (18949)Time elapsed: 0.143 s
% 1.45/0.56  % (18949)------------------------------
% 1.45/0.56  % (18949)------------------------------
% 1.45/0.56  % (18944)Success in time 0.201 s
%------------------------------------------------------------------------------
