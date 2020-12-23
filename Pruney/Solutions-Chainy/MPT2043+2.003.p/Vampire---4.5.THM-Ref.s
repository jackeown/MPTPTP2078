%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:23:19 EST 2020

% Result     : Theorem 2.14s
% Output     : Refutation 2.25s
% Verified   : 
% Statistics : Number of formulae       :   85 ( 211 expanded)
%              Number of leaves         :   14 (  59 expanded)
%              Depth                    :   17
%              Number of atoms          :  228 ( 623 expanded)
%              Number of equality atoms :   18 (  86 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1863,plain,(
    $false ),
    inference(unit_resulting_resolution,[],[f84,f1841,f71])).

fof(f71,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | m1_subset_1(X0,k9_setfam_1(X1)) ) ),
    inference(definition_unfolding,[],[f44,f60])).

fof(f60,plain,(
    ! [X0] : k1_zfmisc_1(X0) = k9_setfam_1(X0) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] : k1_zfmisc_1(X0) = k9_setfam_1(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k9_setfam_1)).

fof(f44,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f1841,plain,(
    ~ m1_subset_1(sK1,k9_setfam_1(sK1)) ),
    inference(resolution,[],[f1840,f82])).

fof(f82,plain,(
    ! [X1] :
      ( ~ m1_subset_1(X1,k9_setfam_1(X1))
      | ~ v1_subset_1(X1,X1) ) ),
    inference(equality_resolution,[],[f77])).

fof(f77,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k9_setfam_1(X0))
      | X0 != X1
      | ~ v1_subset_1(X1,X0) ) ),
    inference(definition_unfolding,[],[f52,f60])).

fof(f52,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | X0 != X1
      | ~ v1_subset_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( v1_subset_1(X1,X0)
      <=> X0 != X1 )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ( v1_subset_1(X1,X0)
      <=> X0 != X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_subset_1)).

fof(f1840,plain,(
    v1_subset_1(sK1,sK1) ),
    inference(duplicate_literal_removal,[],[f1828])).

fof(f1828,plain,
    ( v1_subset_1(sK1,sK1)
    | v1_subset_1(sK1,sK1) ),
    inference(resolution,[],[f1045,f329])).

fof(f329,plain,
    ( r1_tarski(sK3(sK0,sK1),sK0)
    | v1_subset_1(sK1,sK1) ),
    inference(duplicate_literal_removal,[],[f321])).

fof(f321,plain,
    ( r1_tarski(sK3(sK0,sK1),sK0)
    | r1_tarski(sK3(sK0,sK1),sK0)
    | v1_subset_1(sK1,sK1) ),
    inference(resolution,[],[f209,f96])).

fof(f96,plain,(
    ! [X0] :
      ( r2_hidden(sK3(sK0,X0),X0)
      | r1_tarski(sK3(sK0,X0),sK0)
      | v1_subset_1(sK1,X0) ) ),
    inference(superposition,[],[f90,f67])).

fof(f67,plain,(
    ! [X0,X1] :
      ( r1_tarski(sK3(X0,X1),X0)
      | r2_hidden(sK3(X0,X1),X1)
      | k9_setfam_1(X0) = X1 ) ),
    inference(definition_unfolding,[],[f37,f60])).

fof(f37,plain,(
    ! [X0,X1] :
      ( r1_tarski(sK3(X0,X1),X0)
      | r2_hidden(sK3(X0,X1),X1)
      | k1_zfmisc_1(X0) = X1 ) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( k1_zfmisc_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> r1_tarski(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_zfmisc_1)).

fof(f90,plain,(
    v1_subset_1(sK1,k9_setfam_1(sK0)) ),
    inference(forward_demodulation,[],[f64,f53])).

fof(f53,plain,(
    ! [X0] : u1_struct_0(k2_yellow_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( u1_orders_2(k2_yellow_1(X0)) = k1_yellow_1(X0)
      & u1_struct_0(k2_yellow_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_yellow_1)).

fof(f64,plain,(
    v1_subset_1(sK1,u1_struct_0(k2_yellow_1(k9_setfam_1(sK0)))) ),
    inference(definition_unfolding,[],[f29,f55])).

fof(f55,plain,(
    ! [X0] : k3_yellow_1(X0) = k2_yellow_1(k9_setfam_1(X0)) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] : k3_yellow_1(X0) = k2_yellow_1(k9_setfam_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_yellow_1)).

fof(f29,plain,(
    v1_subset_1(sK1,u1_struct_0(k3_yellow_1(sK0))) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( v1_xboole_0(X2)
              & r2_hidden(X2,X1) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0))))
          & v13_waybel_0(X1,k3_yellow_1(X0))
          & v2_waybel_0(X1,k3_yellow_1(X0))
          & v1_subset_1(X1,u1_struct_0(k3_yellow_1(X0)))
          & ~ v1_xboole_0(X1) )
      & ~ v1_xboole_0(X0) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( v1_xboole_0(X2)
              & r2_hidden(X2,X1) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0))))
          & v13_waybel_0(X1,k3_yellow_1(X0))
          & v2_waybel_0(X1,k3_yellow_1(X0))
          & v1_subset_1(X1,u1_struct_0(k3_yellow_1(X0)))
          & ~ v1_xboole_0(X1) )
      & ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,negated_conjecture,(
    ~ ! [X0] :
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
    inference(negated_conjecture,[],[f14])).

fof(f14,conjecture,(
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

fof(f209,plain,(
    ! [X1] :
      ( ~ r2_hidden(X1,sK1)
      | r1_tarski(X1,sK0) ) ),
    inference(resolution,[],[f107,f70])).

fof(f70,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k9_setfam_1(X1)) ) ),
    inference(definition_unfolding,[],[f45,f60])).

fof(f45,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f6])).

fof(f107,plain,(
    ! [X0] :
      ( m1_subset_1(X0,k9_setfam_1(sK0))
      | ~ r2_hidden(X0,sK1) ) ),
    inference(resolution,[],[f89,f65])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ m1_subset_1(X1,k9_setfam_1(X2))
      | m1_subset_1(X0,X2) ) ),
    inference(definition_unfolding,[],[f34,f60])).

fof(f34,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | m1_subset_1(X0,X2) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).

fof(f89,plain,(
    m1_subset_1(sK1,k9_setfam_1(k9_setfam_1(sK0))) ),
    inference(forward_demodulation,[],[f61,f53])).

fof(f61,plain,(
    m1_subset_1(sK1,k9_setfam_1(u1_struct_0(k2_yellow_1(k9_setfam_1(sK0))))) ),
    inference(definition_unfolding,[],[f32,f60,f55])).

fof(f32,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(sK0)))) ),
    inference(cnf_transformation,[],[f17])).

fof(f1045,plain,
    ( ~ r1_tarski(sK3(sK0,sK1),sK0)
    | v1_subset_1(sK1,sK1) ),
    inference(resolution,[],[f963,f624])).

fof(f624,plain,(
    ! [X0] :
      ( r2_hidden(X0,sK1)
      | ~ r1_tarski(X0,sK0) ) ),
    inference(resolution,[],[f286,f474])).

fof(f474,plain,(
    ! [X13] : sP8(X13,sK1) ),
    inference(resolution,[],[f175,f26])).

fof(f26,plain,(
    r2_hidden(sK2,sK1) ),
    inference(cnf_transformation,[],[f17])).

fof(f175,plain,(
    ! [X6,X7] :
      ( ~ r2_hidden(sK2,X6)
      | sP8(X7,X6) ) ),
    inference(resolution,[],[f158,f85])).

fof(f85,plain,(
    ! [X2,X3,X1] :
      ( ~ r1_tarski(X2,X3)
      | ~ r2_hidden(X2,X1)
      | sP8(X3,X1) ) ),
    inference(cnf_transformation,[],[f85_D])).

fof(f85_D,plain,(
    ! [X1,X3] :
      ( ! [X2] :
          ( ~ r1_tarski(X2,X3)
          | ~ r2_hidden(X2,X1) )
    <=> ~ sP8(X3,X1) ) ),
    introduced(general_splitting_component_introduction,[new_symbols(naming,[sP8])])).

fof(f158,plain,(
    ! [X0] : r1_tarski(sK2,X0) ),
    inference(resolution,[],[f152,f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK4(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(f152,plain,(
    ! [X0] : ~ r2_hidden(X0,sK2) ),
    inference(resolution,[],[f147,f88])).

fof(f88,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ sP9(X1) ) ),
    inference(general_splitting,[],[f79,f87_D])).

fof(f87,plain,(
    ! [X2,X1] :
      ( ~ m1_subset_1(X1,k9_setfam_1(X2))
      | ~ v1_xboole_0(X2)
      | sP9(X1) ) ),
    inference(cnf_transformation,[],[f87_D])).

fof(f87_D,plain,(
    ! [X1] :
      ( ! [X2] :
          ( ~ m1_subset_1(X1,k9_setfam_1(X2))
          | ~ v1_xboole_0(X2) )
    <=> ~ sP9(X1) ) ),
    introduced(general_splitting_component_introduction,[new_symbols(naming,[sP9])])).

fof(f79,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ m1_subset_1(X1,k9_setfam_1(X2))
      | ~ v1_xboole_0(X2) ) ),
    inference(definition_unfolding,[],[f56,f60])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ v1_xboole_0(X2) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).

fof(f147,plain,(
    sP9(sK2) ),
    inference(resolution,[],[f139,f84])).

fof(f139,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,sK2)
      | sP9(X0) ) ),
    inference(resolution,[],[f91,f71])).

fof(f91,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k9_setfam_1(sK2))
      | sP9(X0) ) ),
    inference(resolution,[],[f27,f87])).

% (30226)Refutation not found, incomplete strategy% (30226)------------------------------
% (30226)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (30226)Termination reason: Refutation not found, incomplete strategy

% (30226)Memory used [KB]: 6268
% (30226)Time elapsed: 0.081 s
% (30226)------------------------------
% (30226)------------------------------
fof(f27,plain,(
    v1_xboole_0(sK2) ),
    inference(cnf_transformation,[],[f17])).

fof(f286,plain,(
    ! [X0] :
      ( ~ sP8(X0,sK1)
      | r2_hidden(X0,sK1)
      | ~ r1_tarski(X0,sK0) ) ),
    inference(resolution,[],[f102,f89])).

fof(f102,plain,(
    ! [X0] :
      ( ~ m1_subset_1(sK1,k9_setfam_1(k9_setfam_1(sK0)))
      | ~ r1_tarski(X0,sK0)
      | r2_hidden(X0,sK1)
      | ~ sP8(X0,sK1) ) ),
    inference(forward_demodulation,[],[f99,f53])).

fof(f99,plain,(
    ! [X0] :
      ( ~ m1_subset_1(sK1,k9_setfam_1(u1_struct_0(k2_yellow_1(k9_setfam_1(sK0)))))
      | ~ r1_tarski(X0,sK0)
      | r2_hidden(X0,sK1)
      | ~ sP8(X0,sK1) ) ),
    inference(resolution,[],[f62,f86])).

fof(f86,plain,(
    ! [X0,X3,X1] :
      ( ~ m1_subset_1(X1,k9_setfam_1(u1_struct_0(k2_yellow_1(k9_setfam_1(X0)))))
      | ~ r1_tarski(X3,X0)
      | r2_hidden(X3,X1)
      | ~ v13_waybel_0(X1,k2_yellow_1(k9_setfam_1(X0)))
      | ~ sP8(X3,X1) ) ),
    inference(general_splitting,[],[f76,f85_D])).

fof(f76,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X1,k9_setfam_1(u1_struct_0(k2_yellow_1(k9_setfam_1(X0)))))
      | ~ r1_tarski(X2,X3)
      | ~ r1_tarski(X3,X0)
      | ~ r2_hidden(X2,X1)
      | r2_hidden(X3,X1)
      | ~ v13_waybel_0(X1,k2_yellow_1(k9_setfam_1(X0))) ) ),
    inference(definition_unfolding,[],[f46,f60,f55,f55])).

fof(f46,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0))))
      | ~ r1_tarski(X2,X3)
      | ~ r1_tarski(X3,X0)
      | ~ r2_hidden(X2,X1)
      | r2_hidden(X3,X1)
      | ~ v13_waybel_0(X1,k3_yellow_1(X0)) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( v13_waybel_0(X1,k3_yellow_1(X0))
      <=> ! [X2,X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X2,X1)
            | ~ r1_tarski(X3,X0)
            | ~ r1_tarski(X2,X3) ) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0)))) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ( v13_waybel_0(X1,k3_yellow_1(X0))
      <=> ! [X2,X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X2,X1)
            | ~ r1_tarski(X3,X0)
            | ~ r1_tarski(X2,X3) ) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0)))) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0))))
     => ( v13_waybel_0(X1,k3_yellow_1(X0))
      <=> ! [X2,X3] :
            ( ( r2_hidden(X2,X1)
              & r1_tarski(X3,X0)
              & r1_tarski(X2,X3) )
           => r2_hidden(X3,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_waybel_7)).

fof(f62,plain,(
    v13_waybel_0(sK1,k2_yellow_1(k9_setfam_1(sK0))) ),
    inference(definition_unfolding,[],[f31,f55])).

fof(f31,plain,(
    v13_waybel_0(sK1,k3_yellow_1(sK0)) ),
    inference(cnf_transformation,[],[f17])).

fof(f963,plain,
    ( ~ r2_hidden(sK3(sK0,sK1),sK1)
    | v1_subset_1(sK1,sK1) ),
    inference(duplicate_literal_removal,[],[f954])).

fof(f954,plain,
    ( v1_subset_1(sK1,sK1)
    | v1_subset_1(sK1,sK1)
    | ~ r2_hidden(sK3(sK0,sK1),sK1) ),
    inference(resolution,[],[f329,f97])).

fof(f97,plain,(
    ! [X1] :
      ( ~ r1_tarski(sK3(sK0,X1),sK0)
      | v1_subset_1(sK1,X1)
      | ~ r2_hidden(sK3(sK0,X1),X1) ) ),
    inference(superposition,[],[f90,f66])).

fof(f66,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(sK3(X0,X1),X0)
      | ~ r2_hidden(sK3(X0,X1),X1)
      | k9_setfam_1(X0) = X1 ) ),
    inference(definition_unfolding,[],[f38,f60])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(sK3(X0,X1),X0)
      | ~ r2_hidden(sK3(X0,X1),X1)
      | k1_zfmisc_1(X0) = X1 ) ),
    inference(cnf_transformation,[],[f4])).

fof(f84,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f57])).

fof(f57,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n023.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 11:29:51 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.20/0.50  % (30204)ott+11_2:1_add=large:afp=40000:afq=2.0:amm=sco:anc=none:br=off:cond=on:irw=on:nwc=1:sd=2:ss=axioms:st=2.0:sos=all:urr=on:updr=off_6 on theBenchmark
% 0.20/0.51  % (30217)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_157 on theBenchmark
% 0.20/0.51  % (30209)dis+1002_5_av=off:cond=on:gs=on:lma=on:nm=2:nwc=1:sd=3:ss=axioms:st=1.5:sos=on:updr=off_4 on theBenchmark
% 0.20/0.51  % (30199)dis+4_8:1_add=large:afp=100000:afq=1.4:ep=RST:fde=unused:gsp=input_only:lcm=predicate:nwc=1:sos=all:sp=occurrence:updr=off:uhcvi=on_33 on theBenchmark
% 0.20/0.51  % (30214)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_6 on theBenchmark
% 0.20/0.51  % (30201)dis+1004_1_aac=none:acc=on:afp=40000:afq=1.2:anc=none:cond=on:fde=unused:gs=on:gsem=off:irw=on:nm=32:nwc=2:sd=1:ss=axioms:sos=theory:sp=reverse_arity:urr=ec_only_17 on theBenchmark
% 0.20/0.51  % (30202)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_6 on theBenchmark
% 0.20/0.52  % (30198)lrs+2_5:4_av=off:bce=on:cond=fast:ep=R:fde=none:gs=on:lcm=reverse:lwlo=on:nwc=1:stl=30:sd=1:ss=axioms:sos=all:sp=occurrence_8 on theBenchmark
% 0.20/0.52  % (30200)lrs+11_4_av=off:gsp=input_only:irw=on:lma=on:nm=0:nwc=1.2:stl=30:sd=2:ss=axioms:sp=reverse_arity:urr=on:updr=off_8 on theBenchmark
% 0.20/0.52  % (30210)lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.20/0.52  % (30218)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.20/0.52  % (30223)lrs+1011_10_av=off:bce=on:cond=on:fsr=off:fde=unused:gs=on:nm=2:nwc=1.1:stl=30:sd=4:ss=axioms:s2a=on:st=1.5:sos=on:sp=frequency:urr=on:updr=off:uhcvi=on_4 on theBenchmark
% 0.20/0.52  % (30196)lrs+1011_4:1_acc=model:add=large:afp=40000:afq=1.4:ccuc=first:cond=on:fsr=off:gsp=input_only:gs=on:gsem=off:irw=on:nwc=1:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:urr=on_21 on theBenchmark
% 0.20/0.52  % (30201)Refutation not found, incomplete strategy% (30201)------------------------------
% 0.20/0.52  % (30201)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.52  % (30201)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.52  
% 0.20/0.52  % (30201)Memory used [KB]: 10746
% 0.20/0.52  % (30201)Time elapsed: 0.083 s
% 0.20/0.52  % (30201)------------------------------
% 0.20/0.52  % (30201)------------------------------
% 0.20/0.52  % (30216)ott+11_4:1_awrs=converge:awrsf=16:acc=model:add=large:afr=on:afp=4000:afq=1.4:amm=off:br=off:cond=fast:fde=none:gsp=input_only:nm=64:nwc=2:nicw=on:sd=3:ss=axioms:s2a=on:sac=on:sp=frequency:urr=on:updr=off_70 on theBenchmark
% 0.20/0.53  % (30222)ott+11_8:1_av=off:bs=on:bce=on:fde=none:gsp=input_only:gs=on:gsem=on:irw=on:lcm=predicate:nm=6:nwc=1.5:sd=2:ss=axioms:st=1.2:sos=theory:urr=on:updr=off_49 on theBenchmark
% 0.20/0.53  % (30220)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_88 on theBenchmark
% 0.20/0.53  % (30215)lrs+1010_4:1_aac=none:add=off:afp=40000:afq=2.0:amm=sco:anc=none:gs=on:gsem=off:lma=on:lwlo=on:nm=4:nwc=10:stl=30:sd=3:ss=axioms:sos=all:sac=on_49 on theBenchmark
% 0.20/0.53  % (30212)lrs-2_3:2_av=off:bce=on:cond=on:gsp=input_only:gs=on:gsem=on:lcm=predicate:lma=on:newcnf=on:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=all:sp=occurrence:updr=off:uhcvi=on_62 on theBenchmark
% 0.20/0.53  % (30195)lrs-11_3_av=off:bs=unit_only:bsr=on:cond=on:gsp=input_only:gs=on:gsem=on:lma=on:nm=2:nwc=1:stl=30:sd=3:ss=axioms:st=1.2:sos=all:sp=reverse_arity:urr=on:updr=off_11 on theBenchmark
% 0.20/0.53  % (30203)lrs+11_2:1_av=off:bsr=on:gs=on:gsem=on:irw=on:lma=on:lwlo=on:nm=16:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sp=reverse_arity_11 on theBenchmark
% 0.20/0.53  % (30206)dis+1010_2:3_afr=on:afp=40000:afq=1.4:amm=off:anc=none:lma=on:nm=16:nwc=1:sp=occurrence:updr=off:uhcvi=on_34 on theBenchmark
% 0.20/0.53  % (30208)dis+4_2_av=off:bs=on:fsr=off:gsp=input_only:newcnf=on:nwc=1:sd=3:ss=axioms:st=3.0:sos=all:sp=reverse_arity:urr=ec_only:updr=off_127 on theBenchmark
% 0.20/0.53  % (30197)lrs+1002_8:1_av=off:cond=on:gsp=input_only:gs=on:irw=on:lma=on:nm=0:nwc=1.7:stl=30:sd=2:ss=axioms:sos=on:sp=occurrence:urr=on_41 on theBenchmark
% 0.20/0.53  % (30203)Refutation not found, incomplete strategy% (30203)------------------------------
% 0.20/0.53  % (30203)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.53  % (30203)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.53  
% 0.20/0.53  % (30203)Memory used [KB]: 6268
% 0.20/0.53  % (30203)Time elapsed: 0.131 s
% 0.20/0.53  % (30203)------------------------------
% 0.20/0.53  % (30203)------------------------------
% 0.20/0.53  % (30207)dis+10_5:4_add=off:afr=on:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gs=on:nm=64:nwc=1:sas=z3:sd=3:ss=axioms:st=3.0:sos=all:sp=occurrence:urr=on:updr=off_15 on theBenchmark
% 0.20/0.53  % (30224)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_48 on theBenchmark
% 0.20/0.53  % (30214)Refutation not found, incomplete strategy% (30214)------------------------------
% 0.20/0.53  % (30214)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.53  % (30214)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.53  
% 0.20/0.53  % (30214)Memory used [KB]: 1791
% 0.20/0.53  % (30214)Time elapsed: 0.134 s
% 0.20/0.53  % (30214)------------------------------
% 0.20/0.53  % (30214)------------------------------
% 0.20/0.54  % (30219)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 0.20/0.54  % (30221)dis+11_2_add=large:afr=on:anc=none:gs=on:gsem=on:lwlo=on:nm=16:nwc=1:sd=1:ss=axioms:st=3.0:sos=on_4 on theBenchmark
% 0.20/0.54  % (30211)lrs+1010_4_awrs=decay:awrsf=64:add=large:afp=4000:afq=1.2:amm=off:anc=none:bs=on:bsr=on:fde=none:gs=on:gsaa=from_current:gsem=on:lma=on:newcnf=on:nwc=1.7:sas=z3:stl=30:sd=10:ss=axioms:s2a=on:st=1.2:sp=frequency:updr=off:uhcvi=on_23 on theBenchmark
% 0.20/0.55  % (30213)lrs+1_2:3_aac=none:afr=on:afp=100000:afq=1.0:amm=sco:bd=off:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=on:sac=on:sp=occurrence:urr=ec_only:updr=off:uhcvi=on_11 on theBenchmark
% 0.20/0.55  % (30205)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_3 on theBenchmark
% 1.52/0.56  % (30219)Refutation not found, incomplete strategy% (30219)------------------------------
% 1.52/0.56  % (30219)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.52/0.56  % (30219)Termination reason: Refutation not found, incomplete strategy
% 1.52/0.56  
% 1.52/0.56  % (30219)Memory used [KB]: 10746
% 1.52/0.56  % (30219)Time elapsed: 0.145 s
% 1.52/0.56  % (30219)------------------------------
% 1.52/0.56  % (30219)------------------------------
% 2.14/0.65  % (30208)Refutation found. Thanks to Tanya!
% 2.14/0.65  % SZS status Theorem for theBenchmark
% 2.25/0.66  % (30226)ott+1_5:1_acc=on:add=off:afr=on:afp=100000:afq=1.1:amm=sco:anc=none:lcm=predicate:nm=16:nwc=1.1:sd=1:ss=axioms:st=3.0:sos=on:sac=on:updr=off_18 on theBenchmark
% 2.25/0.66  % (30225)dis+1011_8:1_aac=none:acc=on:afp=1000:afq=1.4:amm=off:anc=all:bs=unit_only:bce=on:ccuc=small_ones:fsr=off:fde=unused:gsp=input_only:gs=on:gsem=off:lma=on:nm=16:nwc=2.5:sd=4:ss=axioms:st=1.5:sos=all:uhcvi=on_65 on theBenchmark
% 2.25/0.67  % SZS output start Proof for theBenchmark
% 2.25/0.67  fof(f1863,plain,(
% 2.25/0.67    $false),
% 2.25/0.67    inference(unit_resulting_resolution,[],[f84,f1841,f71])).
% 2.25/0.67  fof(f71,plain,(
% 2.25/0.67    ( ! [X0,X1] : (~r1_tarski(X0,X1) | m1_subset_1(X0,k9_setfam_1(X1))) )),
% 2.25/0.67    inference(definition_unfolding,[],[f44,f60])).
% 2.25/0.67  fof(f60,plain,(
% 2.25/0.67    ( ! [X0] : (k1_zfmisc_1(X0) = k9_setfam_1(X0)) )),
% 2.25/0.67    inference(cnf_transformation,[],[f9])).
% 2.25/0.67  fof(f9,axiom,(
% 2.25/0.67    ! [X0] : k1_zfmisc_1(X0) = k9_setfam_1(X0)),
% 2.25/0.67    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k9_setfam_1)).
% 2.25/0.67  fof(f44,plain,(
% 2.25/0.67    ( ! [X0,X1] : (~r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 2.25/0.67    inference(cnf_transformation,[],[f6])).
% 2.25/0.67  fof(f6,axiom,(
% 2.25/0.67    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 2.25/0.67    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).
% 2.25/0.67  fof(f1841,plain,(
% 2.25/0.67    ~m1_subset_1(sK1,k9_setfam_1(sK1))),
% 2.25/0.67    inference(resolution,[],[f1840,f82])).
% 2.25/0.67  fof(f82,plain,(
% 2.25/0.67    ( ! [X1] : (~m1_subset_1(X1,k9_setfam_1(X1)) | ~v1_subset_1(X1,X1)) )),
% 2.25/0.67    inference(equality_resolution,[],[f77])).
% 2.25/0.67  fof(f77,plain,(
% 2.25/0.67    ( ! [X0,X1] : (~m1_subset_1(X1,k9_setfam_1(X0)) | X0 != X1 | ~v1_subset_1(X1,X0)) )),
% 2.25/0.67    inference(definition_unfolding,[],[f52,f60])).
% 2.25/0.67  fof(f52,plain,(
% 2.25/0.67    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | X0 != X1 | ~v1_subset_1(X1,X0)) )),
% 2.25/0.67    inference(cnf_transformation,[],[f24])).
% 2.25/0.67  fof(f24,plain,(
% 2.25/0.67    ! [X0,X1] : ((v1_subset_1(X1,X0) <=> X0 != X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.25/0.67    inference(ennf_transformation,[],[f12])).
% 2.25/0.67  fof(f12,axiom,(
% 2.25/0.67    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => (v1_subset_1(X1,X0) <=> X0 != X1))),
% 2.25/0.67    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_subset_1)).
% 2.25/0.67  fof(f1840,plain,(
% 2.25/0.67    v1_subset_1(sK1,sK1)),
% 2.25/0.67    inference(duplicate_literal_removal,[],[f1828])).
% 2.25/0.67  fof(f1828,plain,(
% 2.25/0.67    v1_subset_1(sK1,sK1) | v1_subset_1(sK1,sK1)),
% 2.25/0.67    inference(resolution,[],[f1045,f329])).
% 2.25/0.67  fof(f329,plain,(
% 2.25/0.67    r1_tarski(sK3(sK0,sK1),sK0) | v1_subset_1(sK1,sK1)),
% 2.25/0.67    inference(duplicate_literal_removal,[],[f321])).
% 2.25/0.67  fof(f321,plain,(
% 2.25/0.67    r1_tarski(sK3(sK0,sK1),sK0) | r1_tarski(sK3(sK0,sK1),sK0) | v1_subset_1(sK1,sK1)),
% 2.25/0.67    inference(resolution,[],[f209,f96])).
% 2.25/0.67  fof(f96,plain,(
% 2.25/0.67    ( ! [X0] : (r2_hidden(sK3(sK0,X0),X0) | r1_tarski(sK3(sK0,X0),sK0) | v1_subset_1(sK1,X0)) )),
% 2.25/0.67    inference(superposition,[],[f90,f67])).
% 2.25/0.67  fof(f67,plain,(
% 2.25/0.67    ( ! [X0,X1] : (r1_tarski(sK3(X0,X1),X0) | r2_hidden(sK3(X0,X1),X1) | k9_setfam_1(X0) = X1) )),
% 2.25/0.67    inference(definition_unfolding,[],[f37,f60])).
% 2.25/0.67  fof(f37,plain,(
% 2.25/0.67    ( ! [X0,X1] : (r1_tarski(sK3(X0,X1),X0) | r2_hidden(sK3(X0,X1),X1) | k1_zfmisc_1(X0) = X1) )),
% 2.25/0.67    inference(cnf_transformation,[],[f4])).
% 2.25/0.67  fof(f4,axiom,(
% 2.25/0.67    ! [X0,X1] : (k1_zfmisc_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> r1_tarski(X2,X0)))),
% 2.25/0.67    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_zfmisc_1)).
% 2.25/0.67  fof(f90,plain,(
% 2.25/0.67    v1_subset_1(sK1,k9_setfam_1(sK0))),
% 2.25/0.67    inference(forward_demodulation,[],[f64,f53])).
% 2.25/0.67  fof(f53,plain,(
% 2.25/0.67    ( ! [X0] : (u1_struct_0(k2_yellow_1(X0)) = X0) )),
% 2.25/0.67    inference(cnf_transformation,[],[f10])).
% 2.25/0.67  fof(f10,axiom,(
% 2.25/0.67    ! [X0] : (u1_orders_2(k2_yellow_1(X0)) = k1_yellow_1(X0) & u1_struct_0(k2_yellow_1(X0)) = X0)),
% 2.25/0.67    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_yellow_1)).
% 2.25/0.67  fof(f64,plain,(
% 2.25/0.67    v1_subset_1(sK1,u1_struct_0(k2_yellow_1(k9_setfam_1(sK0))))),
% 2.25/0.67    inference(definition_unfolding,[],[f29,f55])).
% 2.25/0.67  fof(f55,plain,(
% 2.25/0.67    ( ! [X0] : (k3_yellow_1(X0) = k2_yellow_1(k9_setfam_1(X0))) )),
% 2.25/0.67    inference(cnf_transformation,[],[f11])).
% 2.25/0.67  fof(f11,axiom,(
% 2.25/0.67    ! [X0] : k3_yellow_1(X0) = k2_yellow_1(k9_setfam_1(X0))),
% 2.25/0.67    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_yellow_1)).
% 2.25/0.67  fof(f29,plain,(
% 2.25/0.67    v1_subset_1(sK1,u1_struct_0(k3_yellow_1(sK0)))),
% 2.25/0.67    inference(cnf_transformation,[],[f17])).
% 2.25/0.67  fof(f17,plain,(
% 2.25/0.67    ? [X0] : (? [X1] : (? [X2] : (v1_xboole_0(X2) & r2_hidden(X2,X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0)))) & v13_waybel_0(X1,k3_yellow_1(X0)) & v2_waybel_0(X1,k3_yellow_1(X0)) & v1_subset_1(X1,u1_struct_0(k3_yellow_1(X0))) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0))),
% 2.25/0.67    inference(flattening,[],[f16])).
% 2.25/0.67  fof(f16,plain,(
% 2.25/0.67    ? [X0] : (? [X1] : (? [X2] : (v1_xboole_0(X2) & r2_hidden(X2,X1)) & (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0)))) & v13_waybel_0(X1,k3_yellow_1(X0)) & v2_waybel_0(X1,k3_yellow_1(X0)) & v1_subset_1(X1,u1_struct_0(k3_yellow_1(X0))) & ~v1_xboole_0(X1))) & ~v1_xboole_0(X0))),
% 2.25/0.67    inference(ennf_transformation,[],[f15])).
% 2.25/0.67  fof(f15,negated_conjecture,(
% 2.25/0.67    ~! [X0] : (~v1_xboole_0(X0) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0)))) & v13_waybel_0(X1,k3_yellow_1(X0)) & v2_waybel_0(X1,k3_yellow_1(X0)) & v1_subset_1(X1,u1_struct_0(k3_yellow_1(X0))) & ~v1_xboole_0(X1)) => ! [X2] : ~(v1_xboole_0(X2) & r2_hidden(X2,X1))))),
% 2.25/0.67    inference(negated_conjecture,[],[f14])).
% 2.25/0.67  fof(f14,conjecture,(
% 2.25/0.67    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0)))) & v13_waybel_0(X1,k3_yellow_1(X0)) & v2_waybel_0(X1,k3_yellow_1(X0)) & v1_subset_1(X1,u1_struct_0(k3_yellow_1(X0))) & ~v1_xboole_0(X1)) => ! [X2] : ~(v1_xboole_0(X2) & r2_hidden(X2,X1))))),
% 2.25/0.67    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_yellow19)).
% 2.25/0.67  fof(f209,plain,(
% 2.25/0.67    ( ! [X1] : (~r2_hidden(X1,sK1) | r1_tarski(X1,sK0)) )),
% 2.25/0.67    inference(resolution,[],[f107,f70])).
% 2.25/0.67  fof(f70,plain,(
% 2.25/0.67    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k9_setfam_1(X1))) )),
% 2.25/0.67    inference(definition_unfolding,[],[f45,f60])).
% 2.25/0.67  fof(f45,plain,(
% 2.25/0.67    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 2.25/0.67    inference(cnf_transformation,[],[f6])).
% 2.25/0.67  fof(f107,plain,(
% 2.25/0.67    ( ! [X0] : (m1_subset_1(X0,k9_setfam_1(sK0)) | ~r2_hidden(X0,sK1)) )),
% 2.25/0.67    inference(resolution,[],[f89,f65])).
% 2.25/0.67  fof(f65,plain,(
% 2.25/0.67    ( ! [X2,X0,X1] : (~r2_hidden(X0,X1) | ~m1_subset_1(X1,k9_setfam_1(X2)) | m1_subset_1(X0,X2)) )),
% 2.25/0.67    inference(definition_unfolding,[],[f34,f60])).
% 2.25/0.67  fof(f34,plain,(
% 2.25/0.67    ( ! [X2,X0,X1] : (~r2_hidden(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | m1_subset_1(X0,X2)) )),
% 2.25/0.67    inference(cnf_transformation,[],[f19])).
% 2.25/0.67  fof(f19,plain,(
% 2.25/0.67    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 2.25/0.67    inference(flattening,[],[f18])).
% 2.25/0.67  fof(f18,plain,(
% 2.25/0.67    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)))),
% 2.25/0.67    inference(ennf_transformation,[],[f7])).
% 2.25/0.67  fof(f7,axiom,(
% 2.25/0.67    ! [X0,X1,X2] : ((m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1)) => m1_subset_1(X0,X2))),
% 2.25/0.67    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).
% 2.25/0.67  fof(f89,plain,(
% 2.25/0.67    m1_subset_1(sK1,k9_setfam_1(k9_setfam_1(sK0)))),
% 2.25/0.67    inference(forward_demodulation,[],[f61,f53])).
% 2.25/0.67  fof(f61,plain,(
% 2.25/0.67    m1_subset_1(sK1,k9_setfam_1(u1_struct_0(k2_yellow_1(k9_setfam_1(sK0)))))),
% 2.25/0.67    inference(definition_unfolding,[],[f32,f60,f55])).
% 2.25/0.67  fof(f32,plain,(
% 2.25/0.67    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(sK0))))),
% 2.25/0.67    inference(cnf_transformation,[],[f17])).
% 2.25/0.67  fof(f1045,plain,(
% 2.25/0.67    ~r1_tarski(sK3(sK0,sK1),sK0) | v1_subset_1(sK1,sK1)),
% 2.25/0.67    inference(resolution,[],[f963,f624])).
% 2.25/0.67  fof(f624,plain,(
% 2.25/0.67    ( ! [X0] : (r2_hidden(X0,sK1) | ~r1_tarski(X0,sK0)) )),
% 2.25/0.67    inference(resolution,[],[f286,f474])).
% 2.25/0.67  fof(f474,plain,(
% 2.25/0.67    ( ! [X13] : (sP8(X13,sK1)) )),
% 2.25/0.67    inference(resolution,[],[f175,f26])).
% 2.25/0.67  fof(f26,plain,(
% 2.25/0.67    r2_hidden(sK2,sK1)),
% 2.25/0.67    inference(cnf_transformation,[],[f17])).
% 2.25/0.67  fof(f175,plain,(
% 2.25/0.67    ( ! [X6,X7] : (~r2_hidden(sK2,X6) | sP8(X7,X6)) )),
% 2.25/0.67    inference(resolution,[],[f158,f85])).
% 2.25/0.67  fof(f85,plain,(
% 2.25/0.67    ( ! [X2,X3,X1] : (~r1_tarski(X2,X3) | ~r2_hidden(X2,X1) | sP8(X3,X1)) )),
% 2.25/0.67    inference(cnf_transformation,[],[f85_D])).
% 2.25/0.67  fof(f85_D,plain,(
% 2.25/0.67    ( ! [X1,X3] : (( ! [X2] : (~r1_tarski(X2,X3) | ~r2_hidden(X2,X1)) ) <=> ~sP8(X3,X1)) )),
% 2.25/0.67    introduced(general_splitting_component_introduction,[new_symbols(naming,[sP8])])).
% 2.25/0.67  fof(f158,plain,(
% 2.25/0.67    ( ! [X0] : (r1_tarski(sK2,X0)) )),
% 2.25/0.67    inference(resolution,[],[f152,f40])).
% 2.25/0.67  fof(f40,plain,(
% 2.25/0.67    ( ! [X0,X1] : (r2_hidden(sK4(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 2.25/0.67    inference(cnf_transformation,[],[f20])).
% 2.25/0.67  fof(f20,plain,(
% 2.25/0.67    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 2.25/0.67    inference(ennf_transformation,[],[f1])).
% 2.25/0.67  fof(f1,axiom,(
% 2.25/0.67    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 2.25/0.67    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).
% 2.25/0.67  fof(f152,plain,(
% 2.25/0.67    ( ! [X0] : (~r2_hidden(X0,sK2)) )),
% 2.25/0.67    inference(resolution,[],[f147,f88])).
% 2.25/0.67  fof(f88,plain,(
% 2.25/0.67    ( ! [X0,X1] : (~r2_hidden(X0,X1) | ~sP9(X1)) )),
% 2.25/0.67    inference(general_splitting,[],[f79,f87_D])).
% 2.25/0.67  fof(f87,plain,(
% 2.25/0.67    ( ! [X2,X1] : (~m1_subset_1(X1,k9_setfam_1(X2)) | ~v1_xboole_0(X2) | sP9(X1)) )),
% 2.25/0.67    inference(cnf_transformation,[],[f87_D])).
% 2.25/0.67  fof(f87_D,plain,(
% 2.25/0.67    ( ! [X1] : (( ! [X2] : (~m1_subset_1(X1,k9_setfam_1(X2)) | ~v1_xboole_0(X2)) ) <=> ~sP9(X1)) )),
% 2.25/0.67    introduced(general_splitting_component_introduction,[new_symbols(naming,[sP9])])).
% 2.25/0.67  fof(f79,plain,(
% 2.25/0.67    ( ! [X2,X0,X1] : (~r2_hidden(X0,X1) | ~m1_subset_1(X1,k9_setfam_1(X2)) | ~v1_xboole_0(X2)) )),
% 2.25/0.67    inference(definition_unfolding,[],[f56,f60])).
% 2.25/0.67  fof(f56,plain,(
% 2.25/0.67    ( ! [X2,X0,X1] : (~r2_hidden(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~v1_xboole_0(X2)) )),
% 2.25/0.67    inference(cnf_transformation,[],[f25])).
% 2.25/0.67  fof(f25,plain,(
% 2.25/0.67    ! [X0,X1,X2] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 2.25/0.67    inference(ennf_transformation,[],[f8])).
% 2.25/0.67  fof(f8,axiom,(
% 2.25/0.67    ! [X0,X1,X2] : ~(v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1))),
% 2.25/0.67    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).
% 2.25/0.67  fof(f147,plain,(
% 2.25/0.67    sP9(sK2)),
% 2.25/0.67    inference(resolution,[],[f139,f84])).
% 2.25/0.67  fof(f139,plain,(
% 2.25/0.67    ( ! [X0] : (~r1_tarski(X0,sK2) | sP9(X0)) )),
% 2.25/0.67    inference(resolution,[],[f91,f71])).
% 2.25/0.67  fof(f91,plain,(
% 2.25/0.67    ( ! [X0] : (~m1_subset_1(X0,k9_setfam_1(sK2)) | sP9(X0)) )),
% 2.25/0.67    inference(resolution,[],[f27,f87])).
% 2.25/0.67  % (30226)Refutation not found, incomplete strategy% (30226)------------------------------
% 2.25/0.67  % (30226)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.25/0.67  % (30226)Termination reason: Refutation not found, incomplete strategy
% 2.25/0.67  
% 2.25/0.67  % (30226)Memory used [KB]: 6268
% 2.25/0.67  % (30226)Time elapsed: 0.081 s
% 2.25/0.67  % (30226)------------------------------
% 2.25/0.67  % (30226)------------------------------
% 2.25/0.67  fof(f27,plain,(
% 2.25/0.67    v1_xboole_0(sK2)),
% 2.25/0.67    inference(cnf_transformation,[],[f17])).
% 2.25/0.67  fof(f286,plain,(
% 2.25/0.67    ( ! [X0] : (~sP8(X0,sK1) | r2_hidden(X0,sK1) | ~r1_tarski(X0,sK0)) )),
% 2.25/0.67    inference(resolution,[],[f102,f89])).
% 2.25/0.67  fof(f102,plain,(
% 2.25/0.67    ( ! [X0] : (~m1_subset_1(sK1,k9_setfam_1(k9_setfam_1(sK0))) | ~r1_tarski(X0,sK0) | r2_hidden(X0,sK1) | ~sP8(X0,sK1)) )),
% 2.25/0.67    inference(forward_demodulation,[],[f99,f53])).
% 2.25/0.67  fof(f99,plain,(
% 2.25/0.67    ( ! [X0] : (~m1_subset_1(sK1,k9_setfam_1(u1_struct_0(k2_yellow_1(k9_setfam_1(sK0))))) | ~r1_tarski(X0,sK0) | r2_hidden(X0,sK1) | ~sP8(X0,sK1)) )),
% 2.25/0.67    inference(resolution,[],[f62,f86])).
% 2.25/0.67  fof(f86,plain,(
% 2.25/0.67    ( ! [X0,X3,X1] : (~m1_subset_1(X1,k9_setfam_1(u1_struct_0(k2_yellow_1(k9_setfam_1(X0))))) | ~r1_tarski(X3,X0) | r2_hidden(X3,X1) | ~v13_waybel_0(X1,k2_yellow_1(k9_setfam_1(X0))) | ~sP8(X3,X1)) )),
% 2.25/0.67    inference(general_splitting,[],[f76,f85_D])).
% 2.25/0.67  fof(f76,plain,(
% 2.25/0.67    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X1,k9_setfam_1(u1_struct_0(k2_yellow_1(k9_setfam_1(X0))))) | ~r1_tarski(X2,X3) | ~r1_tarski(X3,X0) | ~r2_hidden(X2,X1) | r2_hidden(X3,X1) | ~v13_waybel_0(X1,k2_yellow_1(k9_setfam_1(X0)))) )),
% 2.25/0.67    inference(definition_unfolding,[],[f46,f60,f55,f55])).
% 2.25/0.67  fof(f46,plain,(
% 2.25/0.67    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0)))) | ~r1_tarski(X2,X3) | ~r1_tarski(X3,X0) | ~r2_hidden(X2,X1) | r2_hidden(X3,X1) | ~v13_waybel_0(X1,k3_yellow_1(X0))) )),
% 2.25/0.67    inference(cnf_transformation,[],[f23])).
% 2.25/0.67  fof(f23,plain,(
% 2.25/0.67    ! [X0,X1] : ((v13_waybel_0(X1,k3_yellow_1(X0)) <=> ! [X2,X3] : (r2_hidden(X3,X1) | ~r2_hidden(X2,X1) | ~r1_tarski(X3,X0) | ~r1_tarski(X2,X3))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0)))))),
% 2.25/0.67    inference(flattening,[],[f22])).
% 2.25/0.67  fof(f22,plain,(
% 2.25/0.67    ! [X0,X1] : ((v13_waybel_0(X1,k3_yellow_1(X0)) <=> ! [X2,X3] : (r2_hidden(X3,X1) | (~r2_hidden(X2,X1) | ~r1_tarski(X3,X0) | ~r1_tarski(X2,X3)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0)))))),
% 2.25/0.67    inference(ennf_transformation,[],[f13])).
% 2.25/0.67  fof(f13,axiom,(
% 2.25/0.67    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0)))) => (v13_waybel_0(X1,k3_yellow_1(X0)) <=> ! [X2,X3] : ((r2_hidden(X2,X1) & r1_tarski(X3,X0) & r1_tarski(X2,X3)) => r2_hidden(X3,X1))))),
% 2.25/0.67    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_waybel_7)).
% 2.25/0.67  fof(f62,plain,(
% 2.25/0.67    v13_waybel_0(sK1,k2_yellow_1(k9_setfam_1(sK0)))),
% 2.25/0.67    inference(definition_unfolding,[],[f31,f55])).
% 2.25/0.67  fof(f31,plain,(
% 2.25/0.67    v13_waybel_0(sK1,k3_yellow_1(sK0))),
% 2.25/0.67    inference(cnf_transformation,[],[f17])).
% 2.25/0.67  fof(f963,plain,(
% 2.25/0.67    ~r2_hidden(sK3(sK0,sK1),sK1) | v1_subset_1(sK1,sK1)),
% 2.25/0.67    inference(duplicate_literal_removal,[],[f954])).
% 2.25/0.67  fof(f954,plain,(
% 2.25/0.67    v1_subset_1(sK1,sK1) | v1_subset_1(sK1,sK1) | ~r2_hidden(sK3(sK0,sK1),sK1)),
% 2.25/0.67    inference(resolution,[],[f329,f97])).
% 2.25/0.67  fof(f97,plain,(
% 2.25/0.67    ( ! [X1] : (~r1_tarski(sK3(sK0,X1),sK0) | v1_subset_1(sK1,X1) | ~r2_hidden(sK3(sK0,X1),X1)) )),
% 2.25/0.67    inference(superposition,[],[f90,f66])).
% 2.25/0.67  fof(f66,plain,(
% 2.25/0.67    ( ! [X0,X1] : (~r1_tarski(sK3(X0,X1),X0) | ~r2_hidden(sK3(X0,X1),X1) | k9_setfam_1(X0) = X1) )),
% 2.25/0.67    inference(definition_unfolding,[],[f38,f60])).
% 2.25/0.67  fof(f38,plain,(
% 2.25/0.67    ( ! [X0,X1] : (~r1_tarski(sK3(X0,X1),X0) | ~r2_hidden(sK3(X0,X1),X1) | k1_zfmisc_1(X0) = X1) )),
% 2.25/0.67    inference(cnf_transformation,[],[f4])).
% 2.25/0.67  fof(f84,plain,(
% 2.25/0.67    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 2.25/0.67    inference(equality_resolution,[],[f57])).
% 2.25/0.67  fof(f57,plain,(
% 2.25/0.67    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 2.25/0.67    inference(cnf_transformation,[],[f3])).
% 2.25/0.67  fof(f3,axiom,(
% 2.25/0.67    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 2.25/0.67    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 2.25/0.67  % SZS output end Proof for theBenchmark
% 2.25/0.67  % (30208)------------------------------
% 2.25/0.67  % (30208)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.25/0.67  % (30208)Termination reason: Refutation
% 2.25/0.67  
% 2.25/0.67  % (30208)Memory used [KB]: 2430
% 2.25/0.67  % (30208)Time elapsed: 0.259 s
% 2.25/0.67  % (30208)------------------------------
% 2.25/0.67  % (30208)------------------------------
% 2.25/0.67  % (30194)Success in time 0.307 s
%------------------------------------------------------------------------------
