%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:15:23 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   61 ( 151 expanded)
%              Number of leaves         :    6 (  27 expanded)
%              Depth                    :   16
%              Number of atoms          :  263 (1069 expanded)
%              Number of equality atoms :   33 ( 113 expanded)
%              Maximal formula depth    :   16 (   6 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f115,plain,(
    $false ),
    inference(subsumption_resolution,[],[f114,f66])).

fof(f66,plain,(
    ~ r1_tarski(k1_connsp_2(sK0,sK1),sK2) ),
    inference(subsumption_resolution,[],[f64,f21])).

fof(f21,plain,(
    sK2 != k1_connsp_2(sK0,sK1) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( k1_connsp_2(X0,X1) != X2
              & r1_tarski(X2,k1_connsp_2(X0,X1))
              & r2_hidden(X1,X2)
              & v4_pre_topc(X2,X0)
              & v3_pre_topc(X2,X0)
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f8])).

fof(f8,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( k1_connsp_2(X0,X1) != X2
              & r1_tarski(X2,k1_connsp_2(X0,X1))
              & r2_hidden(X1,X2)
              & v4_pre_topc(X2,X0)
              & v3_pre_topc(X2,X0)
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => ( ( r1_tarski(X2,k1_connsp_2(X0,X1))
                    & r2_hidden(X1,X2)
                    & v4_pre_topc(X2,X0)
                    & v3_pre_topc(X2,X0) )
                 => k1_connsp_2(X0,X1) = X2 ) ) ) ) ),
    inference(negated_conjecture,[],[f6])).

fof(f6,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( ( r1_tarski(X2,k1_connsp_2(X0,X1))
                  & r2_hidden(X1,X2)
                  & v4_pre_topc(X2,X0)
                  & v3_pre_topc(X2,X0) )
               => k1_connsp_2(X0,X1) = X2 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_connsp_2)).

fof(f64,plain,
    ( ~ r1_tarski(k1_connsp_2(sK0,sK1),sK2)
    | sK2 = k1_connsp_2(sK0,sK1) ),
    inference(resolution,[],[f42,f20])).

fof(f20,plain,(
    r1_tarski(sK2,k1_connsp_2(sK0,sK1)) ),
    inference(cnf_transformation,[],[f9])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f114,plain,(
    r1_tarski(k1_connsp_2(sK0,sK1),sK2) ),
    inference(forward_demodulation,[],[f113,f99])).

fof(f99,plain,(
    k1_connsp_2(sK0,sK1) = k1_setfam_1(sK3(sK0,sK1,k1_connsp_2(sK0,sK1))) ),
    inference(forward_demodulation,[],[f98,f80])).

fof(f80,plain,(
    k1_connsp_2(sK0,sK1) = k6_setfam_1(u1_struct_0(sK0),sK3(sK0,sK1,k1_connsp_2(sK0,sK1))) ),
    inference(resolution,[],[f79,f22])).

fof(f22,plain,(
    m1_subset_1(sK1,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f9])).

fof(f79,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK0))
      | k1_connsp_2(sK0,X0) = k6_setfam_1(u1_struct_0(sK0),sK3(sK0,X0,k1_connsp_2(sK0,X0))) ) ),
    inference(subsumption_resolution,[],[f78,f23])).

fof(f23,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f9])).

fof(f78,plain,(
    ! [X0] :
      ( v2_struct_0(sK0)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | k1_connsp_2(sK0,X0) = k6_setfam_1(u1_struct_0(sK0),sK3(sK0,X0,k1_connsp_2(sK0,X0))) ) ),
    inference(subsumption_resolution,[],[f77,f24])).

fof(f24,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f9])).

fof(f77,plain,(
    ! [X0] :
      ( ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | k1_connsp_2(sK0,X0) = k6_setfam_1(u1_struct_0(sK0),sK3(sK0,X0,k1_connsp_2(sK0,X0))) ) ),
    inference(resolution,[],[f61,f25])).

fof(f25,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f9])).

fof(f61,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | k1_connsp_2(X0,X1) = k6_setfam_1(u1_struct_0(X0),sK3(X0,X1,k1_connsp_2(X0,X1))) ) ),
    inference(subsumption_resolution,[],[f43,f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_connsp_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_connsp_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_connsp_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,u1_struct_0(X0))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => m1_subset_1(k1_connsp_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_connsp_2)).

fof(f43,plain,(
    ! [X0,X1] :
      ( v2_struct_0(X0)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(k1_connsp_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | k1_connsp_2(X0,X1) = k6_setfam_1(u1_struct_0(X0),sK3(X0,X1,k1_connsp_2(X0,X1))) ) ),
    inference(equality_resolution,[],[f36])).

fof(f36,plain,(
    ! [X2,X0,X1] :
      ( v2_struct_0(X0)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | k6_setfam_1(u1_struct_0(X0),sK3(X0,X1,X2)) = X2
      | k1_connsp_2(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( k1_connsp_2(X0,X1) = X2
              <=> ? [X3] :
                    ( k6_setfam_1(u1_struct_0(X0),X3) = X2
                    & ! [X4] :
                        ( ( r2_hidden(X4,X3)
                        <=> ( r2_hidden(X1,X4)
                            & v4_pre_topc(X4,X0)
                            & v3_pre_topc(X4,X0) ) )
                        | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
                    & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( k1_connsp_2(X0,X1) = X2
              <=> ? [X3] :
                    ( k6_setfam_1(u1_struct_0(X0),X3) = X2
                    & ! [X4] :
                        ( ( r2_hidden(X4,X3)
                        <=> ( r2_hidden(X1,X4)
                            & v4_pre_topc(X4,X0)
                            & v3_pre_topc(X4,X0) ) )
                        | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
                    & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( k1_connsp_2(X0,X1) = X2
              <=> ? [X3] :
                    ( k6_setfam_1(u1_struct_0(X0),X3) = X2
                    & ! [X4] :
                        ( m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))
                       => ( r2_hidden(X4,X3)
                        <=> ( r2_hidden(X1,X4)
                            & v4_pre_topc(X4,X0)
                            & v3_pre_topc(X4,X0) ) ) )
                    & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_connsp_2)).

fof(f98,plain,(
    k6_setfam_1(u1_struct_0(sK0),sK3(sK0,sK1,k1_connsp_2(sK0,sK1))) = k1_setfam_1(sK3(sK0,sK1,k1_connsp_2(sK0,sK1))) ),
    inference(resolution,[],[f97,f22])).

fof(f97,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK0))
      | k6_setfam_1(u1_struct_0(sK0),sK3(sK0,X0,k1_connsp_2(sK0,X0))) = k1_setfam_1(sK3(sK0,X0,k1_connsp_2(sK0,X0))) ) ),
    inference(subsumption_resolution,[],[f96,f23])).

fof(f96,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK0))
      | v2_struct_0(sK0)
      | k6_setfam_1(u1_struct_0(sK0),sK3(sK0,X0,k1_connsp_2(sK0,X0))) = k1_setfam_1(sK3(sK0,X0,k1_connsp_2(sK0,X0))) ) ),
    inference(subsumption_resolution,[],[f95,f24])).

fof(f95,plain,(
    ! [X0] :
      ( ~ v2_pre_topc(sK0)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | v2_struct_0(sK0)
      | k6_setfam_1(u1_struct_0(sK0),sK3(sK0,X0,k1_connsp_2(sK0,X0))) = k1_setfam_1(sK3(sK0,X0,k1_connsp_2(sK0,X0))) ) ),
    inference(resolution,[],[f76,f25])).

fof(f76,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | v2_struct_0(X0)
      | k6_setfam_1(u1_struct_0(X0),sK3(X0,X1,k1_connsp_2(X0,X1))) = k1_setfam_1(sK3(X0,X1,k1_connsp_2(X0,X1))) ) ),
    inference(resolution,[],[f60,f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | k6_setfam_1(X0,X1) = k1_setfam_1(X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( k6_setfam_1(X0,X1) = k1_setfam_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => k6_setfam_1(X0,X1) = k1_setfam_1(X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_setfam_1)).

fof(f60,plain,(
    ! [X0,X1] :
      ( m1_subset_1(sK3(X0,X1,k1_connsp_2(X0,X1)),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | v2_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f44,f39])).

fof(f44,plain,(
    ! [X0,X1] :
      ( v2_struct_0(X0)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(k1_connsp_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | m1_subset_1(sK3(X0,X1,k1_connsp_2(X0,X1)),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) ),
    inference(equality_resolution,[],[f35])).

fof(f35,plain,(
    ! [X2,X0,X1] :
      ( v2_struct_0(X0)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | m1_subset_1(sK3(X0,X1,X2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | k1_connsp_2(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f11])).

fof(f113,plain,(
    r1_tarski(k1_setfam_1(sK3(sK0,sK1,k1_connsp_2(sK0,sK1))),sK2) ),
    inference(subsumption_resolution,[],[f112,f22])).

fof(f112,plain,
    ( ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | r1_tarski(k1_setfam_1(sK3(sK0,sK1,k1_connsp_2(sK0,sK1))),sK2) ),
    inference(resolution,[],[f110,f19])).

fof(f19,plain,(
    r2_hidden(sK1,sK2) ),
    inference(cnf_transformation,[],[f9])).

fof(f110,plain,(
    ! [X1] :
      ( ~ r2_hidden(X1,sK2)
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | r1_tarski(k1_setfam_1(sK3(sK0,X1,k1_connsp_2(sK0,X1))),sK2) ) ),
    inference(resolution,[],[f107,f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | r1_tarski(k1_setfam_1(X1),X0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_setfam_1(X1),X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => r1_tarski(k1_setfam_1(X1),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_setfam_1)).

fof(f107,plain,(
    ! [X0] :
      ( r2_hidden(sK2,sK3(sK0,X0,k1_connsp_2(sK0,X0)))
      | ~ r2_hidden(X0,sK2)
      | ~ m1_subset_1(X0,u1_struct_0(sK0)) ) ),
    inference(subsumption_resolution,[],[f106,f17])).

fof(f17,plain,(
    v3_pre_topc(sK2,sK0) ),
    inference(cnf_transformation,[],[f9])).

fof(f106,plain,(
    ! [X0] :
      ( ~ v3_pre_topc(sK2,sK0)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ r2_hidden(X0,sK2)
      | r2_hidden(sK2,sK3(sK0,X0,k1_connsp_2(sK0,X0))) ) ),
    inference(subsumption_resolution,[],[f103,f16])).

fof(f16,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f9])).

fof(f103,plain,(
    ! [X0] :
      ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v3_pre_topc(sK2,sK0)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ r2_hidden(X0,sK2)
      | r2_hidden(sK2,sK3(sK0,X0,k1_connsp_2(sK0,X0))) ) ),
    inference(resolution,[],[f102,f18])).

fof(f18,plain,(
    v4_pre_topc(sK2,sK0) ),
    inference(cnf_transformation,[],[f9])).

fof(f102,plain,(
    ! [X0,X1] :
      ( ~ v4_pre_topc(X1,sK0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v3_pre_topc(X1,sK0)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ r2_hidden(X0,X1)
      | r2_hidden(X1,sK3(sK0,X0,k1_connsp_2(sK0,X0))) ) ),
    inference(subsumption_resolution,[],[f101,f23])).

fof(f101,plain,(
    ! [X0,X1] :
      ( v2_struct_0(sK0)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v3_pre_topc(X1,sK0)
      | ~ v4_pre_topc(X1,sK0)
      | ~ r2_hidden(X0,X1)
      | r2_hidden(X1,sK3(sK0,X0,k1_connsp_2(sK0,X0))) ) ),
    inference(subsumption_resolution,[],[f100,f24])).

fof(f100,plain,(
    ! [X0,X1] :
      ( ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v3_pre_topc(X1,sK0)
      | ~ v4_pre_topc(X1,sK0)
      | ~ r2_hidden(X0,X1)
      | r2_hidden(X1,sK3(sK0,X0,k1_connsp_2(sK0,X0))) ) ),
    inference(resolution,[],[f59,f25])).

fof(f59,plain,(
    ! [X4,X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v3_pre_topc(X4,X0)
      | ~ v4_pre_topc(X4,X0)
      | ~ r2_hidden(X1,X4)
      | r2_hidden(X4,sK3(X0,X1,k1_connsp_2(X0,X1))) ) ),
    inference(subsumption_resolution,[],[f46,f39])).

fof(f46,plain,(
    ! [X4,X0,X1] :
      ( v2_struct_0(X0)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(k1_connsp_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v3_pre_topc(X4,X0)
      | ~ v4_pre_topc(X4,X0)
      | ~ r2_hidden(X1,X4)
      | r2_hidden(X4,sK3(X0,X1,k1_connsp_2(X0,X1))) ) ),
    inference(equality_resolution,[],[f33])).

fof(f33,plain,(
    ! [X4,X2,X0,X1] :
      ( v2_struct_0(X0)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v3_pre_topc(X4,X0)
      | ~ v4_pre_topc(X4,X0)
      | ~ r2_hidden(X1,X4)
      | r2_hidden(X4,sK3(X0,X1,X2))
      | k1_connsp_2(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f11])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.14  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 18:39:30 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.20/0.49  % (8115)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 0.20/0.50  % (8115)Refutation found. Thanks to Tanya!
% 0.20/0.50  % SZS status Theorem for theBenchmark
% 0.20/0.50  % SZS output start Proof for theBenchmark
% 0.20/0.50  fof(f115,plain,(
% 0.20/0.50    $false),
% 0.20/0.50    inference(subsumption_resolution,[],[f114,f66])).
% 0.20/0.50  fof(f66,plain,(
% 0.20/0.50    ~r1_tarski(k1_connsp_2(sK0,sK1),sK2)),
% 0.20/0.50    inference(subsumption_resolution,[],[f64,f21])).
% 0.20/0.50  fof(f21,plain,(
% 0.20/0.50    sK2 != k1_connsp_2(sK0,sK1)),
% 0.20/0.50    inference(cnf_transformation,[],[f9])).
% 0.20/0.50  fof(f9,plain,(
% 0.20/0.50    ? [X0] : (? [X1] : (? [X2] : (k1_connsp_2(X0,X1) != X2 & r1_tarski(X2,k1_connsp_2(X0,X1)) & r2_hidden(X1,X2) & v4_pre_topc(X2,X0) & v3_pre_topc(X2,X0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.20/0.50    inference(flattening,[],[f8])).
% 0.20/0.50  fof(f8,plain,(
% 0.20/0.50    ? [X0] : (? [X1] : (? [X2] : ((k1_connsp_2(X0,X1) != X2 & (r1_tarski(X2,k1_connsp_2(X0,X1)) & r2_hidden(X1,X2) & v4_pre_topc(X2,X0) & v3_pre_topc(X2,X0))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,u1_struct_0(X0))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 0.20/0.50    inference(ennf_transformation,[],[f7])).
% 0.20/0.50  fof(f7,negated_conjecture,(
% 0.20/0.50    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((r1_tarski(X2,k1_connsp_2(X0,X1)) & r2_hidden(X1,X2) & v4_pre_topc(X2,X0) & v3_pre_topc(X2,X0)) => k1_connsp_2(X0,X1) = X2))))),
% 0.20/0.50    inference(negated_conjecture,[],[f6])).
% 0.20/0.50  fof(f6,conjecture,(
% 0.20/0.50    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((r1_tarski(X2,k1_connsp_2(X0,X1)) & r2_hidden(X1,X2) & v4_pre_topc(X2,X0) & v3_pre_topc(X2,X0)) => k1_connsp_2(X0,X1) = X2))))),
% 0.20/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_connsp_2)).
% 0.20/0.50  fof(f64,plain,(
% 0.20/0.50    ~r1_tarski(k1_connsp_2(sK0,sK1),sK2) | sK2 = k1_connsp_2(sK0,sK1)),
% 0.20/0.50    inference(resolution,[],[f42,f20])).
% 0.20/0.50  fof(f20,plain,(
% 0.20/0.50    r1_tarski(sK2,k1_connsp_2(sK0,sK1))),
% 0.20/0.50    inference(cnf_transformation,[],[f9])).
% 0.20/0.50  fof(f42,plain,(
% 0.20/0.50    ( ! [X0,X1] : (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1) | X0 = X1) )),
% 0.20/0.50    inference(cnf_transformation,[],[f1])).
% 0.20/0.50  fof(f1,axiom,(
% 0.20/0.50    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.20/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.20/0.50  fof(f114,plain,(
% 0.20/0.50    r1_tarski(k1_connsp_2(sK0,sK1),sK2)),
% 0.20/0.50    inference(forward_demodulation,[],[f113,f99])).
% 0.20/0.50  fof(f99,plain,(
% 0.20/0.50    k1_connsp_2(sK0,sK1) = k1_setfam_1(sK3(sK0,sK1,k1_connsp_2(sK0,sK1)))),
% 0.20/0.50    inference(forward_demodulation,[],[f98,f80])).
% 0.20/0.50  fof(f80,plain,(
% 0.20/0.50    k1_connsp_2(sK0,sK1) = k6_setfam_1(u1_struct_0(sK0),sK3(sK0,sK1,k1_connsp_2(sK0,sK1)))),
% 0.20/0.50    inference(resolution,[],[f79,f22])).
% 0.20/0.50  fof(f22,plain,(
% 0.20/0.50    m1_subset_1(sK1,u1_struct_0(sK0))),
% 0.20/0.50    inference(cnf_transformation,[],[f9])).
% 0.20/0.50  fof(f79,plain,(
% 0.20/0.50    ( ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK0)) | k1_connsp_2(sK0,X0) = k6_setfam_1(u1_struct_0(sK0),sK3(sK0,X0,k1_connsp_2(sK0,X0)))) )),
% 0.20/0.50    inference(subsumption_resolution,[],[f78,f23])).
% 0.20/0.50  fof(f23,plain,(
% 0.20/0.50    ~v2_struct_0(sK0)),
% 0.20/0.50    inference(cnf_transformation,[],[f9])).
% 0.20/0.50  fof(f78,plain,(
% 0.20/0.50    ( ! [X0] : (v2_struct_0(sK0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | k1_connsp_2(sK0,X0) = k6_setfam_1(u1_struct_0(sK0),sK3(sK0,X0,k1_connsp_2(sK0,X0)))) )),
% 0.20/0.50    inference(subsumption_resolution,[],[f77,f24])).
% 0.20/0.50  fof(f24,plain,(
% 0.20/0.50    v2_pre_topc(sK0)),
% 0.20/0.50    inference(cnf_transformation,[],[f9])).
% 0.20/0.50  fof(f77,plain,(
% 0.20/0.50    ( ! [X0] : (~v2_pre_topc(sK0) | v2_struct_0(sK0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | k1_connsp_2(sK0,X0) = k6_setfam_1(u1_struct_0(sK0),sK3(sK0,X0,k1_connsp_2(sK0,X0)))) )),
% 0.20/0.50    inference(resolution,[],[f61,f25])).
% 0.20/0.50  fof(f25,plain,(
% 0.20/0.50    l1_pre_topc(sK0)),
% 0.20/0.50    inference(cnf_transformation,[],[f9])).
% 0.20/0.50  fof(f61,plain,(
% 0.20/0.50    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | k1_connsp_2(X0,X1) = k6_setfam_1(u1_struct_0(X0),sK3(X0,X1,k1_connsp_2(X0,X1)))) )),
% 0.20/0.50    inference(subsumption_resolution,[],[f43,f39])).
% 0.20/0.50  fof(f39,plain,(
% 0.20/0.50    ( ! [X0,X1] : (m1_subset_1(k1_connsp_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | v2_struct_0(X0)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f15])).
% 0.20/0.50  fof(f15,plain,(
% 0.20/0.50    ! [X0,X1] : (m1_subset_1(k1_connsp_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.20/0.50    inference(flattening,[],[f14])).
% 0.20/0.50  fof(f14,plain,(
% 0.20/0.50    ! [X0,X1] : (m1_subset_1(k1_connsp_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.20/0.50    inference(ennf_transformation,[],[f5])).
% 0.20/0.50  fof(f5,axiom,(
% 0.20/0.50    ! [X0,X1] : ((m1_subset_1(X1,u1_struct_0(X0)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => m1_subset_1(k1_connsp_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 0.20/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_connsp_2)).
% 0.20/0.50  fof(f43,plain,(
% 0.20/0.50    ( ! [X0,X1] : (v2_struct_0(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(k1_connsp_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | k1_connsp_2(X0,X1) = k6_setfam_1(u1_struct_0(X0),sK3(X0,X1,k1_connsp_2(X0,X1)))) )),
% 0.20/0.50    inference(equality_resolution,[],[f36])).
% 0.20/0.50  fof(f36,plain,(
% 0.20/0.50    ( ! [X2,X0,X1] : (v2_struct_0(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | k6_setfam_1(u1_struct_0(X0),sK3(X0,X1,X2)) = X2 | k1_connsp_2(X0,X1) != X2) )),
% 0.20/0.50    inference(cnf_transformation,[],[f11])).
% 0.20/0.50  fof(f11,plain,(
% 0.20/0.50    ! [X0] : (! [X1] : (! [X2] : ((k1_connsp_2(X0,X1) = X2 <=> ? [X3] : (k6_setfam_1(u1_struct_0(X0),X3) = X2 & ! [X4] : ((r2_hidden(X4,X3) <=> (r2_hidden(X1,X4) & v4_pre_topc(X4,X0) & v3_pre_topc(X4,X0))) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.20/0.50    inference(flattening,[],[f10])).
% 0.20/0.50  fof(f10,plain,(
% 0.20/0.50    ! [X0] : (! [X1] : (! [X2] : ((k1_connsp_2(X0,X1) = X2 <=> ? [X3] : (k6_setfam_1(u1_struct_0(X0),X3) = X2 & ! [X4] : ((r2_hidden(X4,X3) <=> (r2_hidden(X1,X4) & v4_pre_topc(X4,X0) & v3_pre_topc(X4,X0))) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.20/0.50    inference(ennf_transformation,[],[f4])).
% 0.20/0.50  fof(f4,axiom,(
% 0.20/0.50    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (k1_connsp_2(X0,X1) = X2 <=> ? [X3] : (k6_setfam_1(u1_struct_0(X0),X3) = X2 & ! [X4] : (m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) => (r2_hidden(X4,X3) <=> (r2_hidden(X1,X4) & v4_pre_topc(X4,X0) & v3_pre_topc(X4,X0)))) & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))))))))),
% 0.20/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_connsp_2)).
% 0.20/0.50  fof(f98,plain,(
% 0.20/0.50    k6_setfam_1(u1_struct_0(sK0),sK3(sK0,sK1,k1_connsp_2(sK0,sK1))) = k1_setfam_1(sK3(sK0,sK1,k1_connsp_2(sK0,sK1)))),
% 0.20/0.50    inference(resolution,[],[f97,f22])).
% 0.20/0.50  fof(f97,plain,(
% 0.20/0.50    ( ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK0)) | k6_setfam_1(u1_struct_0(sK0),sK3(sK0,X0,k1_connsp_2(sK0,X0))) = k1_setfam_1(sK3(sK0,X0,k1_connsp_2(sK0,X0)))) )),
% 0.20/0.50    inference(subsumption_resolution,[],[f96,f23])).
% 0.20/0.50  fof(f96,plain,(
% 0.20/0.50    ( ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK0)) | v2_struct_0(sK0) | k6_setfam_1(u1_struct_0(sK0),sK3(sK0,X0,k1_connsp_2(sK0,X0))) = k1_setfam_1(sK3(sK0,X0,k1_connsp_2(sK0,X0)))) )),
% 0.20/0.50    inference(subsumption_resolution,[],[f95,f24])).
% 0.20/0.50  fof(f95,plain,(
% 0.20/0.50    ( ! [X0] : (~v2_pre_topc(sK0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | v2_struct_0(sK0) | k6_setfam_1(u1_struct_0(sK0),sK3(sK0,X0,k1_connsp_2(sK0,X0))) = k1_setfam_1(sK3(sK0,X0,k1_connsp_2(sK0,X0)))) )),
% 0.20/0.50    inference(resolution,[],[f76,f25])).
% 0.20/0.50  fof(f76,plain,(
% 0.20/0.50    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | v2_struct_0(X0) | k6_setfam_1(u1_struct_0(X0),sK3(X0,X1,k1_connsp_2(X0,X1))) = k1_setfam_1(sK3(X0,X1,k1_connsp_2(X0,X1)))) )),
% 0.20/0.50    inference(resolution,[],[f60,f38])).
% 0.20/0.50  fof(f38,plain,(
% 0.20/0.50    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) | k6_setfam_1(X0,X1) = k1_setfam_1(X1)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f13])).
% 0.20/0.50  fof(f13,plain,(
% 0.20/0.50    ! [X0,X1] : (k6_setfam_1(X0,X1) = k1_setfam_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 0.20/0.50    inference(ennf_transformation,[],[f2])).
% 0.20/0.50  fof(f2,axiom,(
% 0.20/0.50    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => k6_setfam_1(X0,X1) = k1_setfam_1(X1))),
% 0.20/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_setfam_1)).
% 0.20/0.50  fof(f60,plain,(
% 0.20/0.50    ( ! [X0,X1] : (m1_subset_1(sK3(X0,X1,k1_connsp_2(X0,X1)),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | v2_struct_0(X0)) )),
% 0.20/0.50    inference(subsumption_resolution,[],[f44,f39])).
% 0.20/0.50  fof(f44,plain,(
% 0.20/0.50    ( ! [X0,X1] : (v2_struct_0(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(k1_connsp_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | m1_subset_1(sK3(X0,X1,k1_connsp_2(X0,X1)),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) )),
% 0.20/0.50    inference(equality_resolution,[],[f35])).
% 0.20/0.50  fof(f35,plain,(
% 0.20/0.50    ( ! [X2,X0,X1] : (v2_struct_0(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | m1_subset_1(sK3(X0,X1,X2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | k1_connsp_2(X0,X1) != X2) )),
% 0.20/0.50    inference(cnf_transformation,[],[f11])).
% 0.20/0.50  fof(f113,plain,(
% 0.20/0.50    r1_tarski(k1_setfam_1(sK3(sK0,sK1,k1_connsp_2(sK0,sK1))),sK2)),
% 0.20/0.50    inference(subsumption_resolution,[],[f112,f22])).
% 0.20/0.50  fof(f112,plain,(
% 0.20/0.50    ~m1_subset_1(sK1,u1_struct_0(sK0)) | r1_tarski(k1_setfam_1(sK3(sK0,sK1,k1_connsp_2(sK0,sK1))),sK2)),
% 0.20/0.50    inference(resolution,[],[f110,f19])).
% 0.20/0.50  fof(f19,plain,(
% 0.20/0.50    r2_hidden(sK1,sK2)),
% 0.20/0.50    inference(cnf_transformation,[],[f9])).
% 0.20/0.50  fof(f110,plain,(
% 0.20/0.50    ( ! [X1] : (~r2_hidden(X1,sK2) | ~m1_subset_1(X1,u1_struct_0(sK0)) | r1_tarski(k1_setfam_1(sK3(sK0,X1,k1_connsp_2(sK0,X1))),sK2)) )),
% 0.20/0.50    inference(resolution,[],[f107,f37])).
% 0.20/0.50  fof(f37,plain,(
% 0.20/0.50    ( ! [X0,X1] : (~r2_hidden(X0,X1) | r1_tarski(k1_setfam_1(X1),X0)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f12])).
% 0.20/0.50  fof(f12,plain,(
% 0.20/0.50    ! [X0,X1] : (r1_tarski(k1_setfam_1(X1),X0) | ~r2_hidden(X0,X1))),
% 0.20/0.50    inference(ennf_transformation,[],[f3])).
% 0.20/0.50  fof(f3,axiom,(
% 0.20/0.50    ! [X0,X1] : (r2_hidden(X0,X1) => r1_tarski(k1_setfam_1(X1),X0))),
% 0.20/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_setfam_1)).
% 0.20/0.50  fof(f107,plain,(
% 0.20/0.50    ( ! [X0] : (r2_hidden(sK2,sK3(sK0,X0,k1_connsp_2(sK0,X0))) | ~r2_hidden(X0,sK2) | ~m1_subset_1(X0,u1_struct_0(sK0))) )),
% 0.20/0.50    inference(subsumption_resolution,[],[f106,f17])).
% 0.20/0.50  fof(f17,plain,(
% 0.20/0.50    v3_pre_topc(sK2,sK0)),
% 0.20/0.50    inference(cnf_transformation,[],[f9])).
% 0.20/0.50  fof(f106,plain,(
% 0.20/0.50    ( ! [X0] : (~v3_pre_topc(sK2,sK0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~r2_hidden(X0,sK2) | r2_hidden(sK2,sK3(sK0,X0,k1_connsp_2(sK0,X0)))) )),
% 0.20/0.50    inference(subsumption_resolution,[],[f103,f16])).
% 0.20/0.50  fof(f16,plain,(
% 0.20/0.50    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.20/0.50    inference(cnf_transformation,[],[f9])).
% 0.20/0.50  fof(f103,plain,(
% 0.20/0.50    ( ! [X0] : (~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) | ~v3_pre_topc(sK2,sK0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~r2_hidden(X0,sK2) | r2_hidden(sK2,sK3(sK0,X0,k1_connsp_2(sK0,X0)))) )),
% 0.20/0.50    inference(resolution,[],[f102,f18])).
% 0.20/0.50  fof(f18,plain,(
% 0.20/0.50    v4_pre_topc(sK2,sK0)),
% 0.20/0.50    inference(cnf_transformation,[],[f9])).
% 0.20/0.50  fof(f102,plain,(
% 0.20/0.50    ( ! [X0,X1] : (~v4_pre_topc(X1,sK0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | ~v3_pre_topc(X1,sK0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~r2_hidden(X0,X1) | r2_hidden(X1,sK3(sK0,X0,k1_connsp_2(sK0,X0)))) )),
% 0.20/0.50    inference(subsumption_resolution,[],[f101,f23])).
% 0.20/0.50  fof(f101,plain,(
% 0.20/0.50    ( ! [X0,X1] : (v2_struct_0(sK0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | ~v3_pre_topc(X1,sK0) | ~v4_pre_topc(X1,sK0) | ~r2_hidden(X0,X1) | r2_hidden(X1,sK3(sK0,X0,k1_connsp_2(sK0,X0)))) )),
% 0.20/0.50    inference(subsumption_resolution,[],[f100,f24])).
% 0.20/0.50  fof(f100,plain,(
% 0.20/0.50    ( ! [X0,X1] : (~v2_pre_topc(sK0) | v2_struct_0(sK0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | ~v3_pre_topc(X1,sK0) | ~v4_pre_topc(X1,sK0) | ~r2_hidden(X0,X1) | r2_hidden(X1,sK3(sK0,X0,k1_connsp_2(sK0,X0)))) )),
% 0.20/0.50    inference(resolution,[],[f59,f25])).
% 0.20/0.50  fof(f59,plain,(
% 0.20/0.50    ( ! [X4,X0,X1] : (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) | ~v3_pre_topc(X4,X0) | ~v4_pre_topc(X4,X0) | ~r2_hidden(X1,X4) | r2_hidden(X4,sK3(X0,X1,k1_connsp_2(X0,X1)))) )),
% 0.20/0.50    inference(subsumption_resolution,[],[f46,f39])).
% 0.20/0.50  fof(f46,plain,(
% 0.20/0.50    ( ! [X4,X0,X1] : (v2_struct_0(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(k1_connsp_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) | ~v3_pre_topc(X4,X0) | ~v4_pre_topc(X4,X0) | ~r2_hidden(X1,X4) | r2_hidden(X4,sK3(X0,X1,k1_connsp_2(X0,X1)))) )),
% 0.20/0.50    inference(equality_resolution,[],[f33])).
% 0.20/0.50  fof(f33,plain,(
% 0.20/0.50    ( ! [X4,X2,X0,X1] : (v2_struct_0(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) | ~v3_pre_topc(X4,X0) | ~v4_pre_topc(X4,X0) | ~r2_hidden(X1,X4) | r2_hidden(X4,sK3(X0,X1,X2)) | k1_connsp_2(X0,X1) != X2) )),
% 0.20/0.50    inference(cnf_transformation,[],[f11])).
% 0.20/0.50  % SZS output end Proof for theBenchmark
% 0.20/0.50  % (8115)------------------------------
% 0.20/0.50  % (8115)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.50  % (8115)Termination reason: Refutation
% 0.20/0.50  
% 0.20/0.50  % (8115)Memory used [KB]: 10746
% 0.20/0.50  % (8115)Time elapsed: 0.076 s
% 0.20/0.50  % (8115)------------------------------
% 0.20/0.50  % (8115)------------------------------
% 0.20/0.50  % (8092)Success in time 0.142 s
%------------------------------------------------------------------------------
