%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:14:57 EST 2020

% Result     : Theorem 1.27s
% Output     : Refutation 1.27s
% Verified   : 
% Statistics : Number of formulae       :   71 ( 160 expanded)
%              Number of leaves         :    9 (  30 expanded)
%              Depth                    :   23
%              Number of atoms          :  257 ( 943 expanded)
%              Number of equality atoms :    4 (   4 expanded)
%              Maximal formula depth    :   12 (   6 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f99,plain,(
    $false ),
    inference(subsumption_resolution,[],[f98,f52])).

fof(f52,plain,(
    r1_tarski(sK2,u1_struct_0(sK0)) ),
    inference(resolution,[],[f28,f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f28,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f12])).

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
    inference(flattening,[],[f11])).

fof(f11,plain,(
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
    inference(ennf_transformation,[],[f10])).

fof(f10,negated_conjecture,(
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
    inference(negated_conjecture,[],[f9])).

fof(f9,conjecture,(
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

fof(f98,plain,(
    ~ r1_tarski(sK2,u1_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f95,f51])).

fof(f51,plain,(
    r1_tarski(sK3,u1_struct_0(sK0)) ),
    inference(resolution,[],[f24,f42])).

fof(f24,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f12])).

fof(f95,plain,
    ( ~ r1_tarski(sK3,u1_struct_0(sK0))
    | ~ r1_tarski(sK2,u1_struct_0(sK0)) ),
    inference(resolution,[],[f94,f43])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k2_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X2,X1)
        & r1_tarski(X0,X1) )
     => r1_tarski(k2_xboole_0(X0,X2),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_xboole_1)).

fof(f94,plain,(
    ~ r1_tarski(k2_xboole_0(sK2,sK3),u1_struct_0(sK0)) ),
    inference(resolution,[],[f92,f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f5])).

fof(f92,plain,(
    ~ m1_subset_1(k2_xboole_0(sK2,sK3),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(subsumption_resolution,[],[f90,f36])).

fof(f36,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

fof(f90,plain,
    ( ~ m1_subset_1(k2_xboole_0(sK2,sK3),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r1_tarski(sK2,k2_xboole_0(sK2,sK3)) ),
    inference(resolution,[],[f88,f55])).

fof(f55,plain,(
    ~ m1_connsp_2(k2_xboole_0(sK2,sK3),sK0,sK1) ),
    inference(subsumption_resolution,[],[f54,f28])).

fof(f54,plain,
    ( ~ m1_connsp_2(k2_xboole_0(sK2,sK3),sK0,sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(subsumption_resolution,[],[f53,f24])).

fof(f53,plain,
    ( ~ m1_connsp_2(k2_xboole_0(sK2,sK3),sK0,sK1)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(superposition,[],[f27,f44])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X0))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

fof(f27,plain,(
    ~ m1_connsp_2(k4_subset_1(u1_struct_0(sK0),sK2,sK3),sK0,sK1) ),
    inference(cnf_transformation,[],[f12])).

fof(f88,plain,(
    ! [X0] :
      ( m1_connsp_2(X0,sK0,sK1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r1_tarski(sK2,X0) ) ),
    inference(subsumption_resolution,[],[f87,f32])).

fof(f32,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f12])).

fof(f87,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | m1_connsp_2(X0,sK0,sK1)
      | ~ r1_tarski(sK2,X0)
      | ~ l1_pre_topc(sK0) ) ),
    inference(subsumption_resolution,[],[f86,f28])).

fof(f86,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | m1_connsp_2(X0,sK0,sK1)
      | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r1_tarski(sK2,X0)
      | ~ l1_pre_topc(sK0) ) ),
    inference(duplicate_literal_removal,[],[f84])).

fof(f84,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | m1_connsp_2(X0,sK0,sK1)
      | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r1_tarski(sK2,X0)
      | ~ l1_pre_topc(sK0) ) ),
    inference(resolution,[],[f68,f33])).

fof(f33,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ r1_tarski(X1,X2)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2))
              | ~ r1_tarski(X1,X2)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2))
              | ~ r1_tarski(X1,X2)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( r1_tarski(X1,X2)
               => r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_tops_1)).

fof(f68,plain,(
    ! [X2] :
      ( ~ r1_tarski(k1_tops_1(sK0,sK2),k1_tops_1(sK0,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
      | m1_connsp_2(X2,sK0,sK1) ) ),
    inference(subsumption_resolution,[],[f67,f29])).

fof(f29,plain,(
    m1_subset_1(sK1,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f12])).

fof(f67,plain,(
    ! [X2] :
      ( ~ r1_tarski(k1_tops_1(sK0,sK2),k1_tops_1(sK0,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(sK1,u1_struct_0(sK0))
      | m1_connsp_2(X2,sK0,sK1) ) ),
    inference(resolution,[],[f64,f58])).

fof(f58,plain,(
    ! [X2,X3] :
      ( ~ r2_hidden(X2,k1_tops_1(sK0,X3))
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X2,u1_struct_0(sK0))
      | m1_connsp_2(X3,sK0,X2) ) ),
    inference(subsumption_resolution,[],[f49,f32])).

fof(f49,plain,(
    ! [X2,X3] :
      ( ~ l1_pre_topc(sK0)
      | ~ m1_subset_1(X2,u1_struct_0(sK0))
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r2_hidden(X2,k1_tops_1(sK0,X3))
      | m1_connsp_2(X3,sK0,X2) ) ),
    inference(subsumption_resolution,[],[f46,f30])).

fof(f30,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f12])).

fof(f46,plain,(
    ! [X2,X3] :
      ( v2_struct_0(sK0)
      | ~ l1_pre_topc(sK0)
      | ~ m1_subset_1(X2,u1_struct_0(sK0))
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r2_hidden(X2,k1_tops_1(sK0,X3))
      | m1_connsp_2(X3,sK0,X2) ) ),
    inference(resolution,[],[f31,f34])).

fof(f34,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ r2_hidden(X1,k1_tops_1(X0,X2))
      | m1_connsp_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f16])).

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
    inference(flattening,[],[f15])).

fof(f15,plain,(
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
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
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

fof(f31,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f12])).

fof(f64,plain,(
    ! [X0] :
      ( r2_hidden(sK1,X0)
      | ~ r1_tarski(k1_tops_1(sK0,sK2),X0) ) ),
    inference(resolution,[],[f63,f25])).

fof(f25,plain,(
    m1_connsp_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f12])).

fof(f63,plain,(
    ! [X2,X1] :
      ( ~ m1_connsp_2(X1,sK0,sK1)
      | r2_hidden(sK1,X2)
      | ~ r1_tarski(k1_tops_1(sK0,X1),X2) ) ),
    inference(resolution,[],[f61,f38])).

fof(f38,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,X0)
      | r2_hidden(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
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

fof(f61,plain,(
    ! [X0] :
      ( r2_hidden(sK1,k1_tops_1(sK0,X0))
      | ~ m1_connsp_2(X0,sK0,sK1) ) ),
    inference(resolution,[],[f60,f29])).

fof(f60,plain,(
    ! [X4,X5] :
      ( ~ m1_subset_1(X4,u1_struct_0(sK0))
      | r2_hidden(X4,k1_tops_1(sK0,X5))
      | ~ m1_connsp_2(X5,sK0,X4) ) ),
    inference(subsumption_resolution,[],[f59,f56])).

fof(f56,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_connsp_2(X1,sK0,X0)
      | ~ m1_subset_1(X0,u1_struct_0(sK0)) ) ),
    inference(subsumption_resolution,[],[f48,f32])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(sK0)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ m1_connsp_2(X1,sK0,X0)
      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(subsumption_resolution,[],[f45,f30])).

fof(f45,plain,(
    ! [X0,X1] :
      ( v2_struct_0(sK0)
      | ~ l1_pre_topc(sK0)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ m1_connsp_2(X1,sK0,X0)
      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(resolution,[],[f31,f37])).

fof(f37,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_connsp_2(X2,X0,X1)
      | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_connsp_2(X2,X0,X1) )
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
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

fof(f59,plain,(
    ! [X4,X5] :
      ( ~ m1_subset_1(X4,u1_struct_0(sK0))
      | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(sK0)))
      | r2_hidden(X4,k1_tops_1(sK0,X5))
      | ~ m1_connsp_2(X5,sK0,X4) ) ),
    inference(subsumption_resolution,[],[f50,f32])).

fof(f50,plain,(
    ! [X4,X5] :
      ( ~ l1_pre_topc(sK0)
      | ~ m1_subset_1(X4,u1_struct_0(sK0))
      | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(sK0)))
      | r2_hidden(X4,k1_tops_1(sK0,X5))
      | ~ m1_connsp_2(X5,sK0,X4) ) ),
    inference(subsumption_resolution,[],[f47,f30])).

fof(f47,plain,(
    ! [X4,X5] :
      ( v2_struct_0(sK0)
      | ~ l1_pre_topc(sK0)
      | ~ m1_subset_1(X4,u1_struct_0(sK0))
      | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(sK0)))
      | r2_hidden(X4,k1_tops_1(sK0,X5))
      | ~ m1_connsp_2(X5,sK0,X4) ) ),
    inference(resolution,[],[f31,f35])).

fof(f35,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | r2_hidden(X1,k1_tops_1(X0,X2))
      | ~ m1_connsp_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f16])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n008.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 17:33:45 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.50  % (29355)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.21/0.52  % (29345)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.21/0.52  % (29345)Refutation not found, incomplete strategy% (29345)------------------------------
% 0.21/0.52  % (29345)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (29345)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (29345)Memory used [KB]: 1663
% 0.21/0.52  % (29345)Time elapsed: 0.101 s
% 0.21/0.52  % (29345)------------------------------
% 0.21/0.52  % (29345)------------------------------
% 0.21/0.52  % (29348)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.21/0.52  % (29360)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.21/0.52  % (29354)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.21/0.52  % (29354)Refutation not found, incomplete strategy% (29354)------------------------------
% 0.21/0.52  % (29354)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (29354)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (29354)Memory used [KB]: 10618
% 0.21/0.52  % (29354)Time elapsed: 0.116 s
% 0.21/0.52  % (29354)------------------------------
% 0.21/0.52  % (29354)------------------------------
% 0.21/0.52  % (29350)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 1.27/0.52  % (29368)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 1.27/0.52  % (29355)Refutation not found, incomplete strategy% (29355)------------------------------
% 1.27/0.52  % (29355)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.27/0.52  % (29355)Termination reason: Refutation not found, incomplete strategy
% 1.27/0.52  
% 1.27/0.52  % (29355)Memory used [KB]: 10618
% 1.27/0.52  % (29355)Time elapsed: 0.117 s
% 1.27/0.52  % (29355)------------------------------
% 1.27/0.52  % (29355)------------------------------
% 1.27/0.52  % (29347)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 1.27/0.53  % (29353)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 1.27/0.53  % (29372)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 1.27/0.53  % (29359)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 1.27/0.53  % (29346)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 1.27/0.53  % (29363)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 1.27/0.53  % (29351)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 1.27/0.53  % (29369)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 1.27/0.53  % (29366)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 1.27/0.53  % (29366)Refutation found. Thanks to Tanya!
% 1.27/0.53  % SZS status Theorem for theBenchmark
% 1.27/0.53  % SZS output start Proof for theBenchmark
% 1.27/0.53  fof(f99,plain,(
% 1.27/0.53    $false),
% 1.27/0.53    inference(subsumption_resolution,[],[f98,f52])).
% 1.27/0.53  fof(f52,plain,(
% 1.27/0.53    r1_tarski(sK2,u1_struct_0(sK0))),
% 1.27/0.53    inference(resolution,[],[f28,f42])).
% 1.27/0.53  fof(f42,plain,(
% 1.27/0.53    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 1.27/0.53    inference(cnf_transformation,[],[f5])).
% 1.27/0.53  fof(f5,axiom,(
% 1.27/0.53    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 1.27/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).
% 1.27/0.53  fof(f28,plain,(
% 1.27/0.53    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.27/0.53    inference(cnf_transformation,[],[f12])).
% 1.27/0.53  fof(f12,plain,(
% 1.27/0.53    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (~m1_connsp_2(k4_subset_1(u1_struct_0(X0),X2,X3),X0,X1) & m1_connsp_2(X3,X0,X1) & m1_connsp_2(X2,X0,X1) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 1.27/0.53    inference(flattening,[],[f11])).
% 1.27/0.53  fof(f11,plain,(
% 1.27/0.53    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((~m1_connsp_2(k4_subset_1(u1_struct_0(X0),X2,X3),X0,X1) & (m1_connsp_2(X3,X0,X1) & m1_connsp_2(X2,X0,X1))) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,u1_struct_0(X0))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 1.27/0.53    inference(ennf_transformation,[],[f10])).
% 1.27/0.53  fof(f10,negated_conjecture,(
% 1.27/0.53    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) => ((m1_connsp_2(X3,X0,X1) & m1_connsp_2(X2,X0,X1)) => m1_connsp_2(k4_subset_1(u1_struct_0(X0),X2,X3),X0,X1))))))),
% 1.27/0.53    inference(negated_conjecture,[],[f9])).
% 1.27/0.53  fof(f9,conjecture,(
% 1.27/0.53    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) => ((m1_connsp_2(X3,X0,X1) & m1_connsp_2(X2,X0,X1)) => m1_connsp_2(k4_subset_1(u1_struct_0(X0),X2,X3),X0,X1))))))),
% 1.27/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_connsp_2)).
% 1.27/0.53  fof(f98,plain,(
% 1.27/0.53    ~r1_tarski(sK2,u1_struct_0(sK0))),
% 1.27/0.53    inference(subsumption_resolution,[],[f95,f51])).
% 1.27/0.53  fof(f51,plain,(
% 1.27/0.53    r1_tarski(sK3,u1_struct_0(sK0))),
% 1.27/0.53    inference(resolution,[],[f24,f42])).
% 1.27/0.53  fof(f24,plain,(
% 1.27/0.53    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.27/0.53    inference(cnf_transformation,[],[f12])).
% 1.27/0.53  fof(f95,plain,(
% 1.27/0.53    ~r1_tarski(sK3,u1_struct_0(sK0)) | ~r1_tarski(sK2,u1_struct_0(sK0))),
% 1.27/0.53    inference(resolution,[],[f94,f43])).
% 1.27/0.53  fof(f43,plain,(
% 1.27/0.53    ( ! [X2,X0,X1] : (r1_tarski(k2_xboole_0(X0,X2),X1) | ~r1_tarski(X2,X1) | ~r1_tarski(X0,X1)) )),
% 1.27/0.53    inference(cnf_transformation,[],[f21])).
% 1.27/0.53  fof(f21,plain,(
% 1.27/0.53    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X2),X1) | ~r1_tarski(X2,X1) | ~r1_tarski(X0,X1))),
% 1.27/0.53    inference(flattening,[],[f20])).
% 1.27/0.53  fof(f20,plain,(
% 1.27/0.53    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X2),X1) | (~r1_tarski(X2,X1) | ~r1_tarski(X0,X1)))),
% 1.27/0.53    inference(ennf_transformation,[],[f3])).
% 1.27/0.53  fof(f3,axiom,(
% 1.27/0.53    ! [X0,X1,X2] : ((r1_tarski(X2,X1) & r1_tarski(X0,X1)) => r1_tarski(k2_xboole_0(X0,X2),X1))),
% 1.27/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_xboole_1)).
% 1.27/0.53  fof(f94,plain,(
% 1.27/0.53    ~r1_tarski(k2_xboole_0(sK2,sK3),u1_struct_0(sK0))),
% 1.27/0.53    inference(resolution,[],[f92,f41])).
% 1.27/0.53  fof(f41,plain,(
% 1.27/0.53    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 1.27/0.53    inference(cnf_transformation,[],[f5])).
% 1.27/0.53  fof(f92,plain,(
% 1.27/0.53    ~m1_subset_1(k2_xboole_0(sK2,sK3),k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.27/0.53    inference(subsumption_resolution,[],[f90,f36])).
% 1.27/0.53  fof(f36,plain,(
% 1.27/0.53    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 1.27/0.53    inference(cnf_transformation,[],[f2])).
% 1.27/0.53  fof(f2,axiom,(
% 1.27/0.53    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 1.27/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).
% 1.27/0.53  fof(f90,plain,(
% 1.27/0.53    ~m1_subset_1(k2_xboole_0(sK2,sK3),k1_zfmisc_1(u1_struct_0(sK0))) | ~r1_tarski(sK2,k2_xboole_0(sK2,sK3))),
% 1.27/0.53    inference(resolution,[],[f88,f55])).
% 1.27/0.53  fof(f55,plain,(
% 1.27/0.53    ~m1_connsp_2(k2_xboole_0(sK2,sK3),sK0,sK1)),
% 1.27/0.53    inference(subsumption_resolution,[],[f54,f28])).
% 1.27/0.53  fof(f54,plain,(
% 1.27/0.53    ~m1_connsp_2(k2_xboole_0(sK2,sK3),sK0,sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.27/0.53    inference(subsumption_resolution,[],[f53,f24])).
% 1.27/0.53  fof(f53,plain,(
% 1.27/0.53    ~m1_connsp_2(k2_xboole_0(sK2,sK3),sK0,sK1) | ~m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.27/0.53    inference(superposition,[],[f27,f44])).
% 1.27/0.53  fof(f44,plain,(
% 1.27/0.53    ( ! [X2,X0,X1] : (k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 1.27/0.53    inference(cnf_transformation,[],[f23])).
% 1.27/0.53  fof(f23,plain,(
% 1.27/0.53    ! [X0,X1,X2] : (k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.27/0.53    inference(flattening,[],[f22])).
% 1.27/0.53  fof(f22,plain,(
% 1.27/0.53    ! [X0,X1,X2] : (k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) | (~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))))),
% 1.27/0.53    inference(ennf_transformation,[],[f4])).
% 1.27/0.53  fof(f4,axiom,(
% 1.27/0.53    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2))),
% 1.27/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_subset_1)).
% 1.27/0.53  fof(f27,plain,(
% 1.27/0.53    ~m1_connsp_2(k4_subset_1(u1_struct_0(sK0),sK2,sK3),sK0,sK1)),
% 1.27/0.53    inference(cnf_transformation,[],[f12])).
% 1.27/0.53  fof(f88,plain,(
% 1.27/0.53    ( ! [X0] : (m1_connsp_2(X0,sK0,sK1) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~r1_tarski(sK2,X0)) )),
% 1.27/0.53    inference(subsumption_resolution,[],[f87,f32])).
% 1.27/0.53  fof(f32,plain,(
% 1.27/0.53    l1_pre_topc(sK0)),
% 1.27/0.53    inference(cnf_transformation,[],[f12])).
% 1.27/0.53  fof(f87,plain,(
% 1.27/0.53    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | m1_connsp_2(X0,sK0,sK1) | ~r1_tarski(sK2,X0) | ~l1_pre_topc(sK0)) )),
% 1.27/0.53    inference(subsumption_resolution,[],[f86,f28])).
% 1.27/0.53  fof(f86,plain,(
% 1.27/0.53    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | m1_connsp_2(X0,sK0,sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) | ~r1_tarski(sK2,X0) | ~l1_pre_topc(sK0)) )),
% 1.27/0.53    inference(duplicate_literal_removal,[],[f84])).
% 1.27/0.53  fof(f84,plain,(
% 1.27/0.53    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | m1_connsp_2(X0,sK0,sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~r1_tarski(sK2,X0) | ~l1_pre_topc(sK0)) )),
% 1.27/0.53    inference(resolution,[],[f68,f33])).
% 1.27/0.53  fof(f33,plain,(
% 1.27/0.53    ( ! [X2,X0,X1] : (r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~r1_tarski(X1,X2) | ~l1_pre_topc(X0)) )),
% 1.27/0.53    inference(cnf_transformation,[],[f14])).
% 1.27/0.53  fof(f14,plain,(
% 1.27/0.53    ! [X0] : (! [X1] : (! [X2] : (r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2)) | ~r1_tarski(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.27/0.53    inference(flattening,[],[f13])).
% 1.27/0.53  fof(f13,plain,(
% 1.27/0.53    ! [X0] : (! [X1] : (! [X2] : ((r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2)) | ~r1_tarski(X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.27/0.53    inference(ennf_transformation,[],[f6])).
% 1.27/0.53  fof(f6,axiom,(
% 1.27/0.53    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (r1_tarski(X1,X2) => r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2))))))),
% 1.27/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_tops_1)).
% 1.27/0.53  fof(f68,plain,(
% 1.27/0.53    ( ! [X2] : (~r1_tarski(k1_tops_1(sK0,sK2),k1_tops_1(sK0,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) | m1_connsp_2(X2,sK0,sK1)) )),
% 1.27/0.53    inference(subsumption_resolution,[],[f67,f29])).
% 1.27/0.53  fof(f29,plain,(
% 1.27/0.53    m1_subset_1(sK1,u1_struct_0(sK0))),
% 1.27/0.53    inference(cnf_transformation,[],[f12])).
% 1.27/0.53  fof(f67,plain,(
% 1.27/0.53    ( ! [X2] : (~r1_tarski(k1_tops_1(sK0,sK2),k1_tops_1(sK0,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | m1_connsp_2(X2,sK0,sK1)) )),
% 1.27/0.53    inference(resolution,[],[f64,f58])).
% 1.27/0.53  fof(f58,plain,(
% 1.27/0.53    ( ! [X2,X3] : (~r2_hidden(X2,k1_tops_1(sK0,X3)) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X2,u1_struct_0(sK0)) | m1_connsp_2(X3,sK0,X2)) )),
% 1.27/0.53    inference(subsumption_resolution,[],[f49,f32])).
% 1.27/0.53  fof(f49,plain,(
% 1.27/0.53    ( ! [X2,X3] : (~l1_pre_topc(sK0) | ~m1_subset_1(X2,u1_struct_0(sK0)) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) | ~r2_hidden(X2,k1_tops_1(sK0,X3)) | m1_connsp_2(X3,sK0,X2)) )),
% 1.27/0.53    inference(subsumption_resolution,[],[f46,f30])).
% 1.27/0.53  fof(f30,plain,(
% 1.27/0.53    ~v2_struct_0(sK0)),
% 1.27/0.53    inference(cnf_transformation,[],[f12])).
% 1.27/0.53  fof(f46,plain,(
% 1.27/0.53    ( ! [X2,X3] : (v2_struct_0(sK0) | ~l1_pre_topc(sK0) | ~m1_subset_1(X2,u1_struct_0(sK0)) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) | ~r2_hidden(X2,k1_tops_1(sK0,X3)) | m1_connsp_2(X3,sK0,X2)) )),
% 1.27/0.53    inference(resolution,[],[f31,f34])).
% 1.27/0.53  fof(f34,plain,(
% 1.27/0.53    ( ! [X2,X0,X1] : (~v2_pre_topc(X0) | v2_struct_0(X0) | ~l1_pre_topc(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~r2_hidden(X1,k1_tops_1(X0,X2)) | m1_connsp_2(X2,X0,X1)) )),
% 1.27/0.53    inference(cnf_transformation,[],[f16])).
% 1.27/0.53  fof(f16,plain,(
% 1.27/0.53    ! [X0] : (! [X1] : (! [X2] : ((m1_connsp_2(X2,X0,X1) <=> r2_hidden(X1,k1_tops_1(X0,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.27/0.53    inference(flattening,[],[f15])).
% 1.27/0.53  fof(f15,plain,(
% 1.27/0.53    ! [X0] : (! [X1] : (! [X2] : ((m1_connsp_2(X2,X0,X1) <=> r2_hidden(X1,k1_tops_1(X0,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 1.27/0.53    inference(ennf_transformation,[],[f7])).
% 1.27/0.53  fof(f7,axiom,(
% 1.27/0.53    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (m1_connsp_2(X2,X0,X1) <=> r2_hidden(X1,k1_tops_1(X0,X2))))))),
% 1.27/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_connsp_2)).
% 1.27/0.53  fof(f31,plain,(
% 1.27/0.53    v2_pre_topc(sK0)),
% 1.27/0.53    inference(cnf_transformation,[],[f12])).
% 1.27/0.53  fof(f64,plain,(
% 1.27/0.53    ( ! [X0] : (r2_hidden(sK1,X0) | ~r1_tarski(k1_tops_1(sK0,sK2),X0)) )),
% 1.27/0.53    inference(resolution,[],[f63,f25])).
% 1.27/0.53  fof(f25,plain,(
% 1.27/0.53    m1_connsp_2(sK2,sK0,sK1)),
% 1.27/0.53    inference(cnf_transformation,[],[f12])).
% 1.27/0.53  fof(f63,plain,(
% 1.27/0.53    ( ! [X2,X1] : (~m1_connsp_2(X1,sK0,sK1) | r2_hidden(sK1,X2) | ~r1_tarski(k1_tops_1(sK0,X1),X2)) )),
% 1.27/0.53    inference(resolution,[],[f61,f38])).
% 1.27/0.53  fof(f38,plain,(
% 1.27/0.53    ( ! [X2,X0,X1] : (~r2_hidden(X2,X0) | r2_hidden(X2,X1) | ~r1_tarski(X0,X1)) )),
% 1.27/0.53    inference(cnf_transformation,[],[f19])).
% 1.27/0.53  fof(f19,plain,(
% 1.27/0.53    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 1.27/0.53    inference(ennf_transformation,[],[f1])).
% 1.27/0.53  fof(f1,axiom,(
% 1.27/0.53    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 1.27/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).
% 1.27/0.53  fof(f61,plain,(
% 1.27/0.53    ( ! [X0] : (r2_hidden(sK1,k1_tops_1(sK0,X0)) | ~m1_connsp_2(X0,sK0,sK1)) )),
% 1.27/0.53    inference(resolution,[],[f60,f29])).
% 1.27/0.53  fof(f60,plain,(
% 1.27/0.53    ( ! [X4,X5] : (~m1_subset_1(X4,u1_struct_0(sK0)) | r2_hidden(X4,k1_tops_1(sK0,X5)) | ~m1_connsp_2(X5,sK0,X4)) )),
% 1.27/0.53    inference(subsumption_resolution,[],[f59,f56])).
% 1.27/0.53  fof(f56,plain,(
% 1.27/0.53    ( ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_connsp_2(X1,sK0,X0) | ~m1_subset_1(X0,u1_struct_0(sK0))) )),
% 1.27/0.53    inference(subsumption_resolution,[],[f48,f32])).
% 1.27/0.53  fof(f48,plain,(
% 1.27/0.53    ( ! [X0,X1] : (~l1_pre_topc(sK0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~m1_connsp_2(X1,sK0,X0) | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) )),
% 1.27/0.53    inference(subsumption_resolution,[],[f45,f30])).
% 1.27/0.53  fof(f45,plain,(
% 1.27/0.53    ( ! [X0,X1] : (v2_struct_0(sK0) | ~l1_pre_topc(sK0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~m1_connsp_2(X1,sK0,X0) | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) )),
% 1.27/0.53    inference(resolution,[],[f31,f37])).
% 1.27/0.53  fof(f37,plain,(
% 1.27/0.53    ( ! [X2,X0,X1] : (~v2_pre_topc(X0) | v2_struct_0(X0) | ~l1_pre_topc(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_connsp_2(X2,X0,X1) | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) )),
% 1.27/0.53    inference(cnf_transformation,[],[f18])).
% 1.27/0.53  fof(f18,plain,(
% 1.27/0.53    ! [X0,X1] : (! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_connsp_2(X2,X0,X1)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.27/0.53    inference(flattening,[],[f17])).
% 1.27/0.53  fof(f17,plain,(
% 1.27/0.53    ! [X0,X1] : (! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_connsp_2(X2,X0,X1)) | (~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 1.27/0.53    inference(ennf_transformation,[],[f8])).
% 1.27/0.53  fof(f8,axiom,(
% 1.27/0.53    ! [X0,X1] : ((m1_subset_1(X1,u1_struct_0(X0)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X2] : (m1_connsp_2(X2,X0,X1) => m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))))),
% 1.27/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_connsp_2)).
% 1.27/0.53  fof(f59,plain,(
% 1.27/0.53    ( ! [X4,X5] : (~m1_subset_1(X4,u1_struct_0(sK0)) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(sK0))) | r2_hidden(X4,k1_tops_1(sK0,X5)) | ~m1_connsp_2(X5,sK0,X4)) )),
% 1.27/0.53    inference(subsumption_resolution,[],[f50,f32])).
% 1.27/0.53  fof(f50,plain,(
% 1.27/0.53    ( ! [X4,X5] : (~l1_pre_topc(sK0) | ~m1_subset_1(X4,u1_struct_0(sK0)) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(sK0))) | r2_hidden(X4,k1_tops_1(sK0,X5)) | ~m1_connsp_2(X5,sK0,X4)) )),
% 1.27/0.53    inference(subsumption_resolution,[],[f47,f30])).
% 1.27/0.53  fof(f47,plain,(
% 1.27/0.53    ( ! [X4,X5] : (v2_struct_0(sK0) | ~l1_pre_topc(sK0) | ~m1_subset_1(X4,u1_struct_0(sK0)) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(sK0))) | r2_hidden(X4,k1_tops_1(sK0,X5)) | ~m1_connsp_2(X5,sK0,X4)) )),
% 1.27/0.53    inference(resolution,[],[f31,f35])).
% 1.27/0.53  fof(f35,plain,(
% 1.27/0.53    ( ! [X2,X0,X1] : (~v2_pre_topc(X0) | v2_struct_0(X0) | ~l1_pre_topc(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | r2_hidden(X1,k1_tops_1(X0,X2)) | ~m1_connsp_2(X2,X0,X1)) )),
% 1.27/0.53    inference(cnf_transformation,[],[f16])).
% 1.27/0.53  % SZS output end Proof for theBenchmark
% 1.27/0.53  % (29366)------------------------------
% 1.27/0.53  % (29366)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.27/0.53  % (29366)Termination reason: Refutation
% 1.27/0.53  
% 1.27/0.53  % (29366)Memory used [KB]: 1791
% 1.27/0.53  % (29366)Time elapsed: 0.133 s
% 1.27/0.53  % (29366)------------------------------
% 1.27/0.53  % (29366)------------------------------
% 1.27/0.53  % (29349)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 1.27/0.54  % (29344)Success in time 0.177 s
%------------------------------------------------------------------------------
