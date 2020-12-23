%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:14:55 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   76 ( 165 expanded)
%              Number of leaves         :   10 (  31 expanded)
%              Depth                    :   22
%              Number of atoms          :  274 ( 960 expanded)
%              Number of equality atoms :    6 (   6 expanded)
%              Maximal formula depth    :   12 (   6 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f137,plain,(
    $false ),
    inference(resolution,[],[f134,f50])).

fof(f50,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f134,plain,(
    ! [X0] : ~ r1_tarski(k2_xboole_0(sK2,X0),k2_xboole_0(sK2,sK3)) ),
    inference(subsumption_resolution,[],[f133,f60])).

fof(f60,plain,(
    r1_tarski(sK2,u1_struct_0(sK0)) ),
    inference(resolution,[],[f30,f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f30,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ m1_connsp_2(k4_subset_1(u1_struct_0(X0),X2,X3),X0,X1)
                  & m1_connsp_2(X3,X0,X1)
                  & m1_connsp_2(X2,X0,X1)
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ m1_connsp_2(k4_subset_1(u1_struct_0(X0),X2,X3),X0,X1)
                  & m1_connsp_2(X3,X0,X1)
                  & m1_connsp_2(X2,X0,X1)
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
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
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => ! [X3] :
                    ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                   => ( ( m1_connsp_2(X3,X0,X1)
                        & m1_connsp_2(X2,X0,X1) )
                     => m1_connsp_2(k4_subset_1(u1_struct_0(X0),X2,X3),X0,X1) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f10,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ! [X3] :
                  ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                 => ( ( m1_connsp_2(X3,X0,X1)
                      & m1_connsp_2(X2,X0,X1) )
                   => m1_connsp_2(k4_subset_1(u1_struct_0(X0),X2,X3),X0,X1) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_connsp_2)).

fof(f133,plain,(
    ! [X0] :
      ( ~ r1_tarski(k2_xboole_0(sK2,X0),k2_xboole_0(sK2,sK3))
      | ~ r1_tarski(sK2,u1_struct_0(sK0)) ) ),
    inference(subsumption_resolution,[],[f130,f58])).

fof(f58,plain,(
    r1_tarski(sK3,u1_struct_0(sK0)) ),
    inference(resolution,[],[f26,f46])).

fof(f26,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f13])).

fof(f130,plain,(
    ! [X0] :
      ( ~ r1_tarski(k2_xboole_0(sK2,X0),k2_xboole_0(sK2,sK3))
      | ~ r1_tarski(sK3,u1_struct_0(sK0))
      | ~ r1_tarski(sK2,u1_struct_0(sK0)) ) ),
    inference(resolution,[],[f129,f48])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k2_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X2,X1)
        & r1_tarski(X0,X1) )
     => r1_tarski(k2_xboole_0(X0,X2),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_xboole_1)).

fof(f129,plain,(
    ! [X2] :
      ( ~ r1_tarski(k2_xboole_0(sK2,sK3),u1_struct_0(sK0))
      | ~ r1_tarski(k2_xboole_0(sK2,X2),k2_xboole_0(sK2,sK3)) ) ),
    inference(resolution,[],[f127,f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f6])).

fof(f127,plain,(
    ! [X0] :
      ( ~ m1_subset_1(k2_xboole_0(sK2,sK3),k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r1_tarski(k2_xboole_0(sK2,X0),k2_xboole_0(sK2,sK3)) ) ),
    inference(resolution,[],[f124,f47])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(k2_xboole_0(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(k2_xboole_0(X0,X1),X2) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X1),X2)
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_xboole_1)).

fof(f124,plain,
    ( ~ r1_tarski(sK2,k2_xboole_0(sK2,sK3))
    | ~ m1_subset_1(k2_xboole_0(sK2,sK3),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(resolution,[],[f122,f64])).

fof(f64,plain,(
    ~ m1_connsp_2(k2_xboole_0(sK2,sK3),sK0,sK1) ),
    inference(subsumption_resolution,[],[f63,f30])).

fof(f63,plain,
    ( ~ m1_connsp_2(k2_xboole_0(sK2,sK3),sK0,sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(subsumption_resolution,[],[f62,f26])).

fof(f62,plain,
    ( ~ m1_connsp_2(k2_xboole_0(sK2,sK3),sK0,sK1)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(superposition,[],[f29,f49])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X0))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

fof(f29,plain,(
    ~ m1_connsp_2(k4_subset_1(u1_struct_0(sK0),sK2,sK3),sK0,sK1) ),
    inference(cnf_transformation,[],[f13])).

fof(f122,plain,(
    ! [X0] :
      ( m1_connsp_2(X0,sK0,sK1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r1_tarski(sK2,X0) ) ),
    inference(subsumption_resolution,[],[f121,f34])).

fof(f34,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f13])).

fof(f121,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | m1_connsp_2(X0,sK0,sK1)
      | ~ r1_tarski(sK2,X0)
      | ~ l1_pre_topc(sK0) ) ),
    inference(subsumption_resolution,[],[f120,f30])).

fof(f120,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | m1_connsp_2(X0,sK0,sK1)
      | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r1_tarski(sK2,X0)
      | ~ l1_pre_topc(sK0) ) ),
    inference(duplicate_literal_removal,[],[f116])).

fof(f116,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | m1_connsp_2(X0,sK0,sK1)
      | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r1_tarski(sK2,X0)
      | ~ l1_pre_topc(sK0) ) ),
    inference(resolution,[],[f114,f35])).

fof(f35,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ r1_tarski(X1,X2)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2))
              | ~ r1_tarski(X1,X2)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2))
              | ~ r1_tarski(X1,X2)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( r1_tarski(X1,X2)
               => r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_tops_1)).

fof(f114,plain,(
    ! [X0] :
      ( ~ r1_tarski(k1_tops_1(sK0,sK2),k1_tops_1(sK0,X0))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | m1_connsp_2(X0,sK0,sK1) ) ),
    inference(resolution,[],[f111,f27])).

fof(f27,plain,(
    m1_connsp_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f13])).

fof(f111,plain,(
    ! [X2,X1] :
      ( ~ m1_connsp_2(X1,sK0,sK1)
      | m1_connsp_2(X2,sK0,sK1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r1_tarski(k1_tops_1(sK0,X1),k1_tops_1(sK0,X2)) ) ),
    inference(resolution,[],[f109,f99])).

fof(f99,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK1,X1)
      | m1_connsp_2(X0,sK0,sK1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r1_tarski(X1,k1_tops_1(sK0,X0)) ) ),
    inference(resolution,[],[f98,f42])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X2,X1)
      | ~ r2_hidden(X2,X0)
      | ~ r1_tarski(X0,X1) ) ),
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

fof(f98,plain,(
    ! [X0] :
      ( ~ r2_hidden(sK1,k1_tops_1(sK0,X0))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | m1_connsp_2(X0,sK0,sK1) ) ),
    inference(resolution,[],[f85,f31])).

fof(f31,plain,(
    m1_subset_1(sK1,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f13])).

fof(f85,plain,(
    ! [X2,X3] :
      ( ~ m1_subset_1(X2,u1_struct_0(sK0))
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r2_hidden(X2,k1_tops_1(sK0,X3))
      | m1_connsp_2(X3,sK0,X2) ) ),
    inference(subsumption_resolution,[],[f56,f34])).

fof(f56,plain,(
    ! [X2,X3] :
      ( ~ l1_pre_topc(sK0)
      | ~ m1_subset_1(X2,u1_struct_0(sK0))
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r2_hidden(X2,k1_tops_1(sK0,X3))
      | m1_connsp_2(X3,sK0,X2) ) ),
    inference(subsumption_resolution,[],[f53,f32])).

fof(f32,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f13])).

fof(f53,plain,(
    ! [X2,X3] :
      ( v2_struct_0(sK0)
      | ~ l1_pre_topc(sK0)
      | ~ m1_subset_1(X2,u1_struct_0(sK0))
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r2_hidden(X2,k1_tops_1(sK0,X3))
      | m1_connsp_2(X3,sK0,X2) ) ),
    inference(resolution,[],[f33,f36])).

fof(f36,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ r2_hidden(X1,k1_tops_1(X0,X2))
      | m1_connsp_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( m1_connsp_2(X2,X0,X1)
              <=> r2_hidden(X1,k1_tops_1(X0,X2)) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( m1_connsp_2(X2,X0,X1)
              <=> r2_hidden(X1,k1_tops_1(X0,X2)) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
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
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( m1_connsp_2(X2,X0,X1)
              <=> r2_hidden(X1,k1_tops_1(X0,X2)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_connsp_2)).

fof(f33,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f13])).

fof(f109,plain,(
    ! [X0] :
      ( r2_hidden(sK1,k1_tops_1(sK0,X0))
      | ~ m1_connsp_2(X0,sK0,sK1) ) ),
    inference(resolution,[],[f108,f31])).

fof(f108,plain,(
    ! [X4,X5] :
      ( ~ m1_subset_1(X4,u1_struct_0(sK0))
      | r2_hidden(X4,k1_tops_1(sK0,X5))
      | ~ m1_connsp_2(X5,sK0,X4) ) ),
    inference(subsumption_resolution,[],[f107,f65])).

fof(f65,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_connsp_2(X1,sK0,X0)
      | ~ m1_subset_1(X0,u1_struct_0(sK0)) ) ),
    inference(subsumption_resolution,[],[f55,f34])).

fof(f55,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(sK0)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ m1_connsp_2(X1,sK0,X0)
      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(subsumption_resolution,[],[f52,f32])).

fof(f52,plain,(
    ! [X0,X1] :
      ( v2_struct_0(sK0)
      | ~ l1_pre_topc(sK0)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ m1_connsp_2(X1,sK0,X0)
      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(resolution,[],[f33,f38])).

fof(f38,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_connsp_2(X2,X0,X1)
      | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_connsp_2(X2,X0,X1) )
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_connsp_2(X2,X0,X1) )
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,u1_struct_0(X0))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X2] :
          ( m1_connsp_2(X2,X0,X1)
         => m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_connsp_2)).

fof(f107,plain,(
    ! [X4,X5] :
      ( ~ m1_subset_1(X4,u1_struct_0(sK0))
      | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(sK0)))
      | r2_hidden(X4,k1_tops_1(sK0,X5))
      | ~ m1_connsp_2(X5,sK0,X4) ) ),
    inference(subsumption_resolution,[],[f57,f34])).

fof(f57,plain,(
    ! [X4,X5] :
      ( ~ l1_pre_topc(sK0)
      | ~ m1_subset_1(X4,u1_struct_0(sK0))
      | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(sK0)))
      | r2_hidden(X4,k1_tops_1(sK0,X5))
      | ~ m1_connsp_2(X5,sK0,X4) ) ),
    inference(subsumption_resolution,[],[f54,f32])).

fof(f54,plain,(
    ! [X4,X5] :
      ( v2_struct_0(sK0)
      | ~ l1_pre_topc(sK0)
      | ~ m1_subset_1(X4,u1_struct_0(sK0))
      | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(sK0)))
      | r2_hidden(X4,k1_tops_1(sK0,X5))
      | ~ m1_connsp_2(X5,sK0,X4) ) ),
    inference(resolution,[],[f33,f37])).

fof(f37,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | r2_hidden(X1,k1_tops_1(X0,X2))
      | ~ m1_connsp_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f17])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 12:35:52 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.47  % (31673)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.21/0.49  % (31681)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.21/0.49  % (31681)Refutation not found, incomplete strategy% (31681)------------------------------
% 0.21/0.49  % (31681)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.49  % (31681)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.49  
% 0.21/0.49  % (31681)Memory used [KB]: 10746
% 0.21/0.49  % (31681)Time elapsed: 0.079 s
% 0.21/0.49  % (31681)------------------------------
% 0.21/0.49  % (31681)------------------------------
% 0.21/0.51  % (31672)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.51  % (31670)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.21/0.51  % (31674)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.52  % (31683)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.21/0.52  % (31676)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.21/0.52  % (31698)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.21/0.53  % (31685)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.21/0.53  % (31669)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.21/0.53  % (31693)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.21/0.54  % (31675)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.21/0.54  % (31689)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.21/0.54  % (31692)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.21/0.54  % (31695)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.21/0.54  % (31697)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.21/0.54  % (31677)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.21/0.54  % (31691)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.21/0.54  % (31679)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.21/0.55  % (31691)Refutation found. Thanks to Tanya!
% 0.21/0.55  % SZS status Theorem for theBenchmark
% 0.21/0.55  % SZS output start Proof for theBenchmark
% 0.21/0.55  fof(f137,plain,(
% 0.21/0.55    $false),
% 0.21/0.55    inference(resolution,[],[f134,f50])).
% 0.21/0.55  fof(f50,plain,(
% 0.21/0.55    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 0.21/0.55    inference(equality_resolution,[],[f40])).
% 0.21/0.55  fof(f40,plain,(
% 0.21/0.55    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 0.21/0.55    inference(cnf_transformation,[],[f2])).
% 0.21/0.55  fof(f2,axiom,(
% 0.21/0.55    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.21/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.21/0.55  fof(f134,plain,(
% 0.21/0.55    ( ! [X0] : (~r1_tarski(k2_xboole_0(sK2,X0),k2_xboole_0(sK2,sK3))) )),
% 0.21/0.55    inference(subsumption_resolution,[],[f133,f60])).
% 0.21/0.55  fof(f60,plain,(
% 0.21/0.55    r1_tarski(sK2,u1_struct_0(sK0))),
% 0.21/0.55    inference(resolution,[],[f30,f46])).
% 0.21/0.55  fof(f46,plain,(
% 0.21/0.55    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 0.21/0.55    inference(cnf_transformation,[],[f6])).
% 0.21/0.55  fof(f6,axiom,(
% 0.21/0.55    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.21/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).
% 0.21/0.55  fof(f30,plain,(
% 0.21/0.55    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.21/0.55    inference(cnf_transformation,[],[f13])).
% 0.21/0.55  fof(f13,plain,(
% 0.21/0.55    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (~m1_connsp_2(k4_subset_1(u1_struct_0(X0),X2,X3),X0,X1) & m1_connsp_2(X3,X0,X1) & m1_connsp_2(X2,X0,X1) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.21/0.55    inference(flattening,[],[f12])).
% 0.21/0.55  fof(f12,plain,(
% 0.21/0.55    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((~m1_connsp_2(k4_subset_1(u1_struct_0(X0),X2,X3),X0,X1) & (m1_connsp_2(X3,X0,X1) & m1_connsp_2(X2,X0,X1))) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,u1_struct_0(X0))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 0.21/0.55    inference(ennf_transformation,[],[f11])).
% 0.21/0.55  fof(f11,negated_conjecture,(
% 0.21/0.55    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) => ((m1_connsp_2(X3,X0,X1) & m1_connsp_2(X2,X0,X1)) => m1_connsp_2(k4_subset_1(u1_struct_0(X0),X2,X3),X0,X1))))))),
% 0.21/0.55    inference(negated_conjecture,[],[f10])).
% 0.21/0.55  fof(f10,conjecture,(
% 0.21/0.55    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) => ((m1_connsp_2(X3,X0,X1) & m1_connsp_2(X2,X0,X1)) => m1_connsp_2(k4_subset_1(u1_struct_0(X0),X2,X3),X0,X1))))))),
% 0.21/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_connsp_2)).
% 0.21/0.55  fof(f133,plain,(
% 0.21/0.55    ( ! [X0] : (~r1_tarski(k2_xboole_0(sK2,X0),k2_xboole_0(sK2,sK3)) | ~r1_tarski(sK2,u1_struct_0(sK0))) )),
% 0.21/0.55    inference(subsumption_resolution,[],[f130,f58])).
% 0.21/0.55  fof(f58,plain,(
% 0.21/0.55    r1_tarski(sK3,u1_struct_0(sK0))),
% 0.21/0.55    inference(resolution,[],[f26,f46])).
% 0.21/0.55  fof(f26,plain,(
% 0.21/0.55    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.21/0.55    inference(cnf_transformation,[],[f13])).
% 0.21/0.55  fof(f130,plain,(
% 0.21/0.55    ( ! [X0] : (~r1_tarski(k2_xboole_0(sK2,X0),k2_xboole_0(sK2,sK3)) | ~r1_tarski(sK3,u1_struct_0(sK0)) | ~r1_tarski(sK2,u1_struct_0(sK0))) )),
% 0.21/0.55    inference(resolution,[],[f129,f48])).
% 0.21/0.55  fof(f48,plain,(
% 0.21/0.55    ( ! [X2,X0,X1] : (r1_tarski(k2_xboole_0(X0,X2),X1) | ~r1_tarski(X2,X1) | ~r1_tarski(X0,X1)) )),
% 0.21/0.55    inference(cnf_transformation,[],[f23])).
% 0.21/0.55  fof(f23,plain,(
% 0.21/0.55    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X2),X1) | ~r1_tarski(X2,X1) | ~r1_tarski(X0,X1))),
% 0.21/0.55    inference(flattening,[],[f22])).
% 0.21/0.55  fof(f22,plain,(
% 0.21/0.55    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X2),X1) | (~r1_tarski(X2,X1) | ~r1_tarski(X0,X1)))),
% 0.21/0.55    inference(ennf_transformation,[],[f4])).
% 0.21/0.55  fof(f4,axiom,(
% 0.21/0.55    ! [X0,X1,X2] : ((r1_tarski(X2,X1) & r1_tarski(X0,X1)) => r1_tarski(k2_xboole_0(X0,X2),X1))),
% 0.21/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_xboole_1)).
% 0.21/0.55  fof(f129,plain,(
% 0.21/0.55    ( ! [X2] : (~r1_tarski(k2_xboole_0(sK2,sK3),u1_struct_0(sK0)) | ~r1_tarski(k2_xboole_0(sK2,X2),k2_xboole_0(sK2,sK3))) )),
% 0.21/0.55    inference(resolution,[],[f127,f45])).
% 0.21/0.55  fof(f45,plain,(
% 0.21/0.55    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 0.21/0.55    inference(cnf_transformation,[],[f6])).
% 0.21/0.55  fof(f127,plain,(
% 0.21/0.55    ( ! [X0] : (~m1_subset_1(k2_xboole_0(sK2,sK3),k1_zfmisc_1(u1_struct_0(sK0))) | ~r1_tarski(k2_xboole_0(sK2,X0),k2_xboole_0(sK2,sK3))) )),
% 0.21/0.55    inference(resolution,[],[f124,f47])).
% 0.21/0.55  fof(f47,plain,(
% 0.21/0.55    ( ! [X2,X0,X1] : (r1_tarski(X0,X2) | ~r1_tarski(k2_xboole_0(X0,X1),X2)) )),
% 0.21/0.55    inference(cnf_transformation,[],[f21])).
% 0.21/0.55  fof(f21,plain,(
% 0.21/0.55    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(k2_xboole_0(X0,X1),X2))),
% 0.21/0.55    inference(ennf_transformation,[],[f3])).
% 0.21/0.55  fof(f3,axiom,(
% 0.21/0.55    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X1),X2) => r1_tarski(X0,X2))),
% 0.21/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_xboole_1)).
% 0.21/0.55  fof(f124,plain,(
% 0.21/0.55    ~r1_tarski(sK2,k2_xboole_0(sK2,sK3)) | ~m1_subset_1(k2_xboole_0(sK2,sK3),k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.21/0.55    inference(resolution,[],[f122,f64])).
% 0.21/0.55  fof(f64,plain,(
% 0.21/0.55    ~m1_connsp_2(k2_xboole_0(sK2,sK3),sK0,sK1)),
% 0.21/0.55    inference(subsumption_resolution,[],[f63,f30])).
% 0.21/0.55  fof(f63,plain,(
% 0.21/0.55    ~m1_connsp_2(k2_xboole_0(sK2,sK3),sK0,sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.21/0.55    inference(subsumption_resolution,[],[f62,f26])).
% 0.21/0.55  fof(f62,plain,(
% 0.21/0.55    ~m1_connsp_2(k2_xboole_0(sK2,sK3),sK0,sK1) | ~m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.21/0.55    inference(superposition,[],[f29,f49])).
% 0.21/0.55  fof(f49,plain,(
% 0.21/0.55    ( ! [X2,X0,X1] : (k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.21/0.55    inference(cnf_transformation,[],[f25])).
% 0.21/0.55  fof(f25,plain,(
% 0.21/0.55    ! [X0,X1,X2] : (k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.21/0.55    inference(flattening,[],[f24])).
% 0.21/0.55  fof(f24,plain,(
% 0.21/0.55    ! [X0,X1,X2] : (k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) | (~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))))),
% 0.21/0.55    inference(ennf_transformation,[],[f5])).
% 0.21/0.55  fof(f5,axiom,(
% 0.21/0.55    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2))),
% 0.21/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_subset_1)).
% 0.21/0.55  fof(f29,plain,(
% 0.21/0.55    ~m1_connsp_2(k4_subset_1(u1_struct_0(sK0),sK2,sK3),sK0,sK1)),
% 0.21/0.55    inference(cnf_transformation,[],[f13])).
% 0.21/0.55  fof(f122,plain,(
% 0.21/0.55    ( ! [X0] : (m1_connsp_2(X0,sK0,sK1) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~r1_tarski(sK2,X0)) )),
% 0.21/0.55    inference(subsumption_resolution,[],[f121,f34])).
% 0.21/0.55  fof(f34,plain,(
% 0.21/0.55    l1_pre_topc(sK0)),
% 0.21/0.55    inference(cnf_transformation,[],[f13])).
% 0.21/0.55  fof(f121,plain,(
% 0.21/0.55    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | m1_connsp_2(X0,sK0,sK1) | ~r1_tarski(sK2,X0) | ~l1_pre_topc(sK0)) )),
% 0.21/0.55    inference(subsumption_resolution,[],[f120,f30])).
% 0.21/0.55  fof(f120,plain,(
% 0.21/0.55    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | m1_connsp_2(X0,sK0,sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) | ~r1_tarski(sK2,X0) | ~l1_pre_topc(sK0)) )),
% 0.21/0.55    inference(duplicate_literal_removal,[],[f116])).
% 0.21/0.55  fof(f116,plain,(
% 0.21/0.55    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | m1_connsp_2(X0,sK0,sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~r1_tarski(sK2,X0) | ~l1_pre_topc(sK0)) )),
% 0.21/0.55    inference(resolution,[],[f114,f35])).
% 0.21/0.55  fof(f35,plain,(
% 0.21/0.55    ( ! [X2,X0,X1] : (r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~r1_tarski(X1,X2) | ~l1_pre_topc(X0)) )),
% 0.21/0.55    inference(cnf_transformation,[],[f15])).
% 0.21/0.55  fof(f15,plain,(
% 0.21/0.55    ! [X0] : (! [X1] : (! [X2] : (r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2)) | ~r1_tarski(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.21/0.55    inference(flattening,[],[f14])).
% 0.21/0.55  fof(f14,plain,(
% 0.21/0.55    ! [X0] : (! [X1] : (! [X2] : ((r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2)) | ~r1_tarski(X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.21/0.55    inference(ennf_transformation,[],[f7])).
% 0.21/0.55  fof(f7,axiom,(
% 0.21/0.55    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (r1_tarski(X1,X2) => r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2))))))),
% 0.21/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_tops_1)).
% 0.21/0.55  fof(f114,plain,(
% 0.21/0.55    ( ! [X0] : (~r1_tarski(k1_tops_1(sK0,sK2),k1_tops_1(sK0,X0)) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | m1_connsp_2(X0,sK0,sK1)) )),
% 0.21/0.55    inference(resolution,[],[f111,f27])).
% 0.21/0.55  fof(f27,plain,(
% 0.21/0.55    m1_connsp_2(sK2,sK0,sK1)),
% 0.21/0.55    inference(cnf_transformation,[],[f13])).
% 0.21/0.55  fof(f111,plain,(
% 0.21/0.55    ( ! [X2,X1] : (~m1_connsp_2(X1,sK0,sK1) | m1_connsp_2(X2,sK0,sK1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) | ~r1_tarski(k1_tops_1(sK0,X1),k1_tops_1(sK0,X2))) )),
% 0.21/0.55    inference(resolution,[],[f109,f99])).
% 0.21/0.55  fof(f99,plain,(
% 0.21/0.55    ( ! [X0,X1] : (~r2_hidden(sK1,X1) | m1_connsp_2(X0,sK0,sK1) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~r1_tarski(X1,k1_tops_1(sK0,X0))) )),
% 0.21/0.55    inference(resolution,[],[f98,f42])).
% 0.21/0.55  fof(f42,plain,(
% 0.21/0.55    ( ! [X2,X0,X1] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0) | ~r1_tarski(X0,X1)) )),
% 0.21/0.55    inference(cnf_transformation,[],[f20])).
% 0.21/0.55  fof(f20,plain,(
% 0.21/0.55    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 0.21/0.55    inference(ennf_transformation,[],[f1])).
% 0.21/0.55  fof(f1,axiom,(
% 0.21/0.55    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 0.21/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).
% 0.21/0.55  fof(f98,plain,(
% 0.21/0.55    ( ! [X0] : (~r2_hidden(sK1,k1_tops_1(sK0,X0)) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | m1_connsp_2(X0,sK0,sK1)) )),
% 0.21/0.55    inference(resolution,[],[f85,f31])).
% 0.21/0.55  fof(f31,plain,(
% 0.21/0.55    m1_subset_1(sK1,u1_struct_0(sK0))),
% 0.21/0.55    inference(cnf_transformation,[],[f13])).
% 0.21/0.55  fof(f85,plain,(
% 0.21/0.55    ( ! [X2,X3] : (~m1_subset_1(X2,u1_struct_0(sK0)) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) | ~r2_hidden(X2,k1_tops_1(sK0,X3)) | m1_connsp_2(X3,sK0,X2)) )),
% 0.21/0.55    inference(subsumption_resolution,[],[f56,f34])).
% 0.21/0.55  fof(f56,plain,(
% 0.21/0.55    ( ! [X2,X3] : (~l1_pre_topc(sK0) | ~m1_subset_1(X2,u1_struct_0(sK0)) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) | ~r2_hidden(X2,k1_tops_1(sK0,X3)) | m1_connsp_2(X3,sK0,X2)) )),
% 0.21/0.55    inference(subsumption_resolution,[],[f53,f32])).
% 0.21/0.55  fof(f32,plain,(
% 0.21/0.55    ~v2_struct_0(sK0)),
% 0.21/0.55    inference(cnf_transformation,[],[f13])).
% 0.21/0.55  fof(f53,plain,(
% 0.21/0.55    ( ! [X2,X3] : (v2_struct_0(sK0) | ~l1_pre_topc(sK0) | ~m1_subset_1(X2,u1_struct_0(sK0)) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) | ~r2_hidden(X2,k1_tops_1(sK0,X3)) | m1_connsp_2(X3,sK0,X2)) )),
% 0.21/0.55    inference(resolution,[],[f33,f36])).
% 0.21/0.55  fof(f36,plain,(
% 0.21/0.55    ( ! [X2,X0,X1] : (~v2_pre_topc(X0) | v2_struct_0(X0) | ~l1_pre_topc(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~r2_hidden(X1,k1_tops_1(X0,X2)) | m1_connsp_2(X2,X0,X1)) )),
% 0.21/0.55    inference(cnf_transformation,[],[f17])).
% 0.21/0.55  fof(f17,plain,(
% 0.21/0.55    ! [X0] : (! [X1] : (! [X2] : ((m1_connsp_2(X2,X0,X1) <=> r2_hidden(X1,k1_tops_1(X0,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.55    inference(flattening,[],[f16])).
% 0.21/0.55  fof(f16,plain,(
% 0.21/0.55    ! [X0] : (! [X1] : (! [X2] : ((m1_connsp_2(X2,X0,X1) <=> r2_hidden(X1,k1_tops_1(X0,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.21/0.55    inference(ennf_transformation,[],[f8])).
% 0.21/0.55  fof(f8,axiom,(
% 0.21/0.55    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (m1_connsp_2(X2,X0,X1) <=> r2_hidden(X1,k1_tops_1(X0,X2))))))),
% 0.21/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_connsp_2)).
% 0.21/0.55  fof(f33,plain,(
% 0.21/0.55    v2_pre_topc(sK0)),
% 0.21/0.55    inference(cnf_transformation,[],[f13])).
% 0.21/0.55  fof(f109,plain,(
% 0.21/0.55    ( ! [X0] : (r2_hidden(sK1,k1_tops_1(sK0,X0)) | ~m1_connsp_2(X0,sK0,sK1)) )),
% 0.21/0.55    inference(resolution,[],[f108,f31])).
% 0.21/0.55  fof(f108,plain,(
% 0.21/0.55    ( ! [X4,X5] : (~m1_subset_1(X4,u1_struct_0(sK0)) | r2_hidden(X4,k1_tops_1(sK0,X5)) | ~m1_connsp_2(X5,sK0,X4)) )),
% 0.21/0.55    inference(subsumption_resolution,[],[f107,f65])).
% 0.21/0.55  fof(f65,plain,(
% 0.21/0.55    ( ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_connsp_2(X1,sK0,X0) | ~m1_subset_1(X0,u1_struct_0(sK0))) )),
% 0.21/0.55    inference(subsumption_resolution,[],[f55,f34])).
% 0.21/0.55  fof(f55,plain,(
% 0.21/0.55    ( ! [X0,X1] : (~l1_pre_topc(sK0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~m1_connsp_2(X1,sK0,X0) | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) )),
% 0.21/0.55    inference(subsumption_resolution,[],[f52,f32])).
% 0.21/0.55  fof(f52,plain,(
% 0.21/0.55    ( ! [X0,X1] : (v2_struct_0(sK0) | ~l1_pre_topc(sK0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~m1_connsp_2(X1,sK0,X0) | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) )),
% 0.21/0.55    inference(resolution,[],[f33,f38])).
% 0.21/0.55  fof(f38,plain,(
% 0.21/0.55    ( ! [X2,X0,X1] : (~v2_pre_topc(X0) | v2_struct_0(X0) | ~l1_pre_topc(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_connsp_2(X2,X0,X1) | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) )),
% 0.21/0.55    inference(cnf_transformation,[],[f19])).
% 0.21/0.55  fof(f19,plain,(
% 0.21/0.55    ! [X0,X1] : (! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_connsp_2(X2,X0,X1)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.55    inference(flattening,[],[f18])).
% 0.21/0.55  fof(f18,plain,(
% 0.21/0.55    ! [X0,X1] : (! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_connsp_2(X2,X0,X1)) | (~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.21/0.55    inference(ennf_transformation,[],[f9])).
% 0.21/0.55  fof(f9,axiom,(
% 0.21/0.55    ! [X0,X1] : ((m1_subset_1(X1,u1_struct_0(X0)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X2] : (m1_connsp_2(X2,X0,X1) => m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))))),
% 0.21/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_connsp_2)).
% 0.21/0.55  fof(f107,plain,(
% 0.21/0.55    ( ! [X4,X5] : (~m1_subset_1(X4,u1_struct_0(sK0)) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(sK0))) | r2_hidden(X4,k1_tops_1(sK0,X5)) | ~m1_connsp_2(X5,sK0,X4)) )),
% 0.21/0.55    inference(subsumption_resolution,[],[f57,f34])).
% 0.21/0.55  fof(f57,plain,(
% 0.21/0.55    ( ! [X4,X5] : (~l1_pre_topc(sK0) | ~m1_subset_1(X4,u1_struct_0(sK0)) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(sK0))) | r2_hidden(X4,k1_tops_1(sK0,X5)) | ~m1_connsp_2(X5,sK0,X4)) )),
% 0.21/0.55    inference(subsumption_resolution,[],[f54,f32])).
% 0.21/0.55  fof(f54,plain,(
% 0.21/0.55    ( ! [X4,X5] : (v2_struct_0(sK0) | ~l1_pre_topc(sK0) | ~m1_subset_1(X4,u1_struct_0(sK0)) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(sK0))) | r2_hidden(X4,k1_tops_1(sK0,X5)) | ~m1_connsp_2(X5,sK0,X4)) )),
% 0.21/0.55    inference(resolution,[],[f33,f37])).
% 0.21/0.55  fof(f37,plain,(
% 0.21/0.55    ( ! [X2,X0,X1] : (~v2_pre_topc(X0) | v2_struct_0(X0) | ~l1_pre_topc(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | r2_hidden(X1,k1_tops_1(X0,X2)) | ~m1_connsp_2(X2,X0,X1)) )),
% 0.21/0.55    inference(cnf_transformation,[],[f17])).
% 0.21/0.55  % SZS output end Proof for theBenchmark
% 0.21/0.55  % (31691)------------------------------
% 0.21/0.55  % (31691)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (31691)Termination reason: Refutation
% 0.21/0.55  
% 0.21/0.55  % (31691)Memory used [KB]: 1791
% 0.21/0.55  % (31691)Time elapsed: 0.141 s
% 0.21/0.55  % (31691)------------------------------
% 0.21/0.55  % (31691)------------------------------
% 0.21/0.55  % (31666)Success in time 0.188 s
%------------------------------------------------------------------------------
