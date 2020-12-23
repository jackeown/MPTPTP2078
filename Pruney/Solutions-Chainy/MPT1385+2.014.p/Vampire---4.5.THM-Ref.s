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
% DateTime   : Thu Dec  3 13:15:10 EST 2020

% Result     : Theorem 0.37s
% Output     : Refutation 0.37s
% Verified   : 
% Statistics : Number of formulae       :   98 ( 921 expanded)
%              Number of leaves         :   10 ( 162 expanded)
%              Depth                    :   28
%              Number of atoms          :  398 (4905 expanded)
%              Number of equality atoms :    6 (  36 expanded)
%              Maximal formula depth    :   15 (   6 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f216,plain,(
    $false ),
    inference(subsumption_resolution,[],[f215,f209])).

fof(f209,plain,(
    m1_connsp_2(sK2,sK0,sK1) ),
    inference(subsumption_resolution,[],[f208,f32])).

fof(f32,plain,(
    m1_subset_1(sK1,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( m2_connsp_2(X2,X0,k6_domain_1(u1_struct_0(X0),X1))
              <~> m1_connsp_2(X2,X0,X1) )
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
              ( ( m2_connsp_2(X2,X0,k6_domain_1(u1_struct_0(X0),X1))
              <~> m1_connsp_2(X2,X0,X1) )
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
               => ( m2_connsp_2(X2,X0,k6_domain_1(u1_struct_0(X0),X1))
                <=> m1_connsp_2(X2,X0,X1) ) ) ) ) ),
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
             => ( m2_connsp_2(X2,X0,k6_domain_1(u1_struct_0(X0),X1))
              <=> m1_connsp_2(X2,X0,X1) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_connsp_2)).

fof(f208,plain,
    ( m1_connsp_2(sK2,sK0,sK1)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0)) ),
    inference(duplicate_literal_removal,[],[f207])).

fof(f207,plain,
    ( m1_connsp_2(sK2,sK0,sK1)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | m1_connsp_2(sK2,sK0,sK1) ),
    inference(resolution,[],[f206,f128])).

fof(f128,plain,(
    ! [X6] :
      ( ~ r2_hidden(X6,k1_tops_1(sK0,sK2))
      | ~ m1_subset_1(X6,u1_struct_0(sK0))
      | m1_connsp_2(sK2,sK0,X6) ) ),
    inference(subsumption_resolution,[],[f127,f33])).

fof(f33,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f13])).

fof(f127,plain,(
    ! [X6] :
      ( ~ m1_subset_1(X6,u1_struct_0(sK0))
      | v2_struct_0(sK0)
      | ~ r2_hidden(X6,k1_tops_1(sK0,sK2))
      | m1_connsp_2(sK2,sK0,X6) ) ),
    inference(subsumption_resolution,[],[f126,f35])).

fof(f35,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f13])).

fof(f126,plain,(
    ! [X6] :
      ( ~ l1_pre_topc(sK0)
      | ~ m1_subset_1(X6,u1_struct_0(sK0))
      | v2_struct_0(sK0)
      | ~ r2_hidden(X6,k1_tops_1(sK0,sK2))
      | m1_connsp_2(sK2,sK0,X6) ) ),
    inference(subsumption_resolution,[],[f122,f34])).

fof(f34,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f13])).

fof(f122,plain,(
    ! [X6] :
      ( ~ v2_pre_topc(sK0)
      | ~ l1_pre_topc(sK0)
      | ~ m1_subset_1(X6,u1_struct_0(sK0))
      | v2_struct_0(sK0)
      | ~ r2_hidden(X6,k1_tops_1(sK0,sK2))
      | m1_connsp_2(sK2,sK0,X6) ) ),
    inference(resolution,[],[f36,f31])).

fof(f31,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f13])).

fof(f36,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | v2_struct_0(X0)
      | ~ r2_hidden(X1,k1_tops_1(X0,X2))
      | m1_connsp_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f15])).

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
    inference(flattening,[],[f14])).

fof(f14,plain,(
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
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_connsp_2)).

fof(f206,plain,
    ( r2_hidden(sK1,k1_tops_1(sK0,sK2))
    | m1_connsp_2(sK2,sK0,sK1) ),
    inference(resolution,[],[f205,f168])).

fof(f168,plain,
    ( m2_connsp_2(sK2,sK0,k1_tarski(sK1))
    | m1_connsp_2(sK2,sK0,sK1) ),
    inference(backward_demodulation,[],[f29,f166])).

fof(f166,plain,(
    k6_domain_1(u1_struct_0(sK0),sK1) = k1_tarski(sK1) ),
    inference(resolution,[],[f165,f51])).

fof(f51,plain,
    ( v1_xboole_0(u1_struct_0(sK0))
    | k6_domain_1(u1_struct_0(sK0),sK1) = k1_tarski(sK1) ),
    inference(resolution,[],[f40,f32])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0)
      | k6_domain_1(X0,X1) = k1_tarski(X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( k6_domain_1(X0,X1) = k1_tarski(X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( k6_domain_1(X0,X1) = k1_tarski(X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,X0)
        & ~ v1_xboole_0(X0) )
     => k6_domain_1(X0,X1) = k1_tarski(X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

fof(f165,plain,(
    ~ v1_xboole_0(u1_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f164,f35])).

fof(f164,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ v1_xboole_0(u1_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f163,f34])).

fof(f163,plain,
    ( ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v1_xboole_0(u1_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f162,f33])).

fof(f162,plain,
    ( v2_struct_0(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v1_xboole_0(u1_struct_0(sK0)) ),
    inference(resolution,[],[f161,f32])).

fof(f161,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,u1_struct_0(X1))
      | v2_struct_0(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X1)
      | ~ v1_xboole_0(u1_struct_0(X1)) ) ),
    inference(duplicate_literal_removal,[],[f160])).

fof(f160,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,u1_struct_0(X1))
      | v2_struct_0(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X1)
      | ~ m1_subset_1(X0,u1_struct_0(X1))
      | ~ v1_xboole_0(u1_struct_0(X1))
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X1)
      | ~ m1_subset_1(X0,u1_struct_0(X1))
      | v2_struct_0(X1) ) ),
    inference(resolution,[],[f158,f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( m1_connsp_2(sK3(X0,X1),X0,X1)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ? [X2] : m1_connsp_2(X2,X0,X1)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ? [X2] : m1_connsp_2(X2,X0,X1)
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
     => ? [X2] : m1_connsp_2(X2,X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',existence_m1_connsp_2)).

fof(f158,plain,(
    ! [X4,X5,X3] :
      ( ~ m1_connsp_2(sK3(X3,X5),X3,X4)
      | ~ m1_subset_1(X4,u1_struct_0(X3))
      | v2_struct_0(X3)
      | ~ v2_pre_topc(X3)
      | ~ l1_pre_topc(X3)
      | ~ m1_subset_1(X5,u1_struct_0(X3))
      | ~ v1_xboole_0(u1_struct_0(X3)) ) ),
    inference(duplicate_literal_removal,[],[f157])).

fof(f157,plain,(
    ! [X4,X5,X3] :
      ( ~ l1_pre_topc(X3)
      | ~ m1_subset_1(X4,u1_struct_0(X3))
      | v2_struct_0(X3)
      | ~ v2_pre_topc(X3)
      | ~ m1_connsp_2(sK3(X3,X5),X3,X4)
      | ~ m1_subset_1(X5,u1_struct_0(X3))
      | ~ m1_subset_1(X5,u1_struct_0(X3))
      | v2_struct_0(X3)
      | ~ v2_pre_topc(X3)
      | ~ l1_pre_topc(X3)
      | ~ v1_xboole_0(u1_struct_0(X3)) ) ),
    inference(resolution,[],[f133,f68])).

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,k1_tops_1(X0,sK3(X0,X1)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | v2_struct_0(X0)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    inference(duplicate_literal_removal,[],[f65])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | v2_struct_0(X0)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ r2_hidden(X2,k1_tops_1(X0,sK3(X0,X1)))
      | ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    inference(resolution,[],[f64,f56])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_pre_topc(X1)
      | ~ r2_hidden(X2,k1_tops_1(X1,X0))
      | ~ v1_xboole_0(u1_struct_0(X1)) ) ),
    inference(resolution,[],[f44,f47])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1)
      | ~ v1_xboole_0(X2) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).

fof(f44,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_tops_1)).

fof(f64,plain,(
    ! [X0,X1] :
      ( m1_subset_1(sK3(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | v2_struct_0(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(duplicate_literal_removal,[],[f63])).

fof(f63,plain,(
    ! [X0,X1] :
      ( ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | v2_struct_0(X0)
      | m1_subset_1(sK3(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | v2_struct_0(X0) ) ),
    inference(resolution,[],[f42,f43])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_connsp_2(X2,X0,X1)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | v2_struct_0(X0)
      | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_connsp_2(X2,X0,X1) )
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_connsp_2)).

fof(f133,plain,(
    ! [X8,X7,X9] :
      ( r2_hidden(X8,k1_tops_1(X7,sK3(X7,X9)))
      | ~ l1_pre_topc(X7)
      | ~ m1_subset_1(X8,u1_struct_0(X7))
      | v2_struct_0(X7)
      | ~ v2_pre_topc(X7)
      | ~ m1_connsp_2(sK3(X7,X9),X7,X8)
      | ~ m1_subset_1(X9,u1_struct_0(X7)) ) ),
    inference(duplicate_literal_removal,[],[f132])).

fof(f132,plain,(
    ! [X8,X7,X9] :
      ( ~ v2_pre_topc(X7)
      | ~ l1_pre_topc(X7)
      | ~ m1_subset_1(X8,u1_struct_0(X7))
      | v2_struct_0(X7)
      | r2_hidden(X8,k1_tops_1(X7,sK3(X7,X9)))
      | ~ m1_connsp_2(sK3(X7,X9),X7,X8)
      | ~ l1_pre_topc(X7)
      | ~ m1_subset_1(X9,u1_struct_0(X7))
      | v2_struct_0(X7)
      | ~ v2_pre_topc(X7) ) ),
    inference(resolution,[],[f37,f64])).

fof(f37,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | v2_struct_0(X0)
      | r2_hidden(X1,k1_tops_1(X0,X2))
      | ~ m1_connsp_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f29,plain,
    ( m2_connsp_2(sK2,sK0,k6_domain_1(u1_struct_0(sK0),sK1))
    | m1_connsp_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f13])).

fof(f205,plain,
    ( ~ m2_connsp_2(sK2,sK0,k1_tarski(sK1))
    | r2_hidden(sK1,k1_tops_1(sK0,sK2)) ),
    inference(resolution,[],[f175,f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k1_tarski(X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
    <=> r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l1_zfmisc_1)).

fof(f175,plain,
    ( r1_tarski(k1_tarski(sK1),k1_tops_1(sK0,sK2))
    | ~ m2_connsp_2(sK2,sK0,k1_tarski(sK1)) ),
    inference(subsumption_resolution,[],[f174,f165])).

fof(f174,plain,
    ( r1_tarski(k1_tarski(sK1),k1_tops_1(sK0,sK2))
    | ~ m2_connsp_2(sK2,sK0,k1_tarski(sK1))
    | v1_xboole_0(u1_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f171,f32])).

fof(f171,plain,
    ( r1_tarski(k1_tarski(sK1),k1_tops_1(sK0,sK2))
    | ~ m2_connsp_2(sK2,sK0,k1_tarski(sK1))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | v1_xboole_0(u1_struct_0(sK0)) ),
    inference(superposition,[],[f98,f166])).

fof(f98,plain,(
    ! [X0] :
      ( r1_tarski(k6_domain_1(u1_struct_0(sK0),X0),k1_tops_1(sK0,sK2))
      | ~ m2_connsp_2(sK2,sK0,k6_domain_1(u1_struct_0(sK0),X0))
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | v1_xboole_0(u1_struct_0(sK0)) ) ),
    inference(resolution,[],[f97,f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,X0)
        & ~ v1_xboole_0(X0) )
     => m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_domain_1)).

fof(f97,plain,(
    ! [X6] :
      ( ~ m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(sK0)))
      | r1_tarski(X6,k1_tops_1(sK0,sK2))
      | ~ m2_connsp_2(sK2,sK0,X6) ) ),
    inference(subsumption_resolution,[],[f96,f34])).

fof(f96,plain,(
    ! [X6] :
      ( ~ m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v2_pre_topc(sK0)
      | r1_tarski(X6,k1_tops_1(sK0,sK2))
      | ~ m2_connsp_2(sK2,sK0,X6) ) ),
    inference(subsumption_resolution,[],[f92,f35])).

fof(f92,plain,(
    ! [X6] :
      ( ~ l1_pre_topc(sK0)
      | ~ m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v2_pre_topc(sK0)
      | r1_tarski(X6,k1_tops_1(sK0,sK2))
      | ~ m2_connsp_2(sK2,sK0,X6) ) ),
    inference(resolution,[],[f39,f31])).

fof(f39,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v2_pre_topc(X0)
      | r1_tarski(X1,k1_tops_1(X0,X2))
      | ~ m2_connsp_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( m2_connsp_2(X2,X0,X1)
              <=> r1_tarski(X1,k1_tops_1(X0,X2)) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( m2_connsp_2(X2,X0,X1)
              <=> r1_tarski(X1,k1_tops_1(X0,X2)) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( m2_connsp_2(X2,X0,X1)
              <=> r1_tarski(X1,k1_tops_1(X0,X2)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_connsp_2)).

fof(f215,plain,(
    ~ m1_connsp_2(sK2,sK0,sK1) ),
    inference(subsumption_resolution,[],[f214,f32])).

fof(f214,plain,
    ( ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ m1_connsp_2(sK2,sK0,sK1) ),
    inference(resolution,[],[f213,f137])).

% (24321)lrs+1011_7_afp=100000:afq=1.0:amm=sco:anc=all_dependent:bs=unit_only:bsr=on:ep=RS:fde=none:gsp=input_only:gs=on:gsem=off:lwlo=on:nm=4:nwc=1:stl=120:sos=theory:sp=occurrence:uhcvi=on_412 on theBenchmark
fof(f137,plain,(
    ! [X6] :
      ( r2_hidden(X6,k1_tops_1(sK0,sK2))
      | ~ m1_subset_1(X6,u1_struct_0(sK0))
      | ~ m1_connsp_2(sK2,sK0,X6) ) ),
    inference(subsumption_resolution,[],[f136,f33])).

fof(f136,plain,(
    ! [X6] :
      ( ~ m1_subset_1(X6,u1_struct_0(sK0))
      | v2_struct_0(sK0)
      | r2_hidden(X6,k1_tops_1(sK0,sK2))
      | ~ m1_connsp_2(sK2,sK0,X6) ) ),
    inference(subsumption_resolution,[],[f135,f35])).

fof(f135,plain,(
    ! [X6] :
      ( ~ l1_pre_topc(sK0)
      | ~ m1_subset_1(X6,u1_struct_0(sK0))
      | v2_struct_0(sK0)
      | r2_hidden(X6,k1_tops_1(sK0,sK2))
      | ~ m1_connsp_2(sK2,sK0,X6) ) ),
    inference(subsumption_resolution,[],[f131,f34])).

fof(f131,plain,(
    ! [X6] :
      ( ~ v2_pre_topc(sK0)
      | ~ l1_pre_topc(sK0)
      | ~ m1_subset_1(X6,u1_struct_0(sK0))
      | v2_struct_0(sK0)
      | r2_hidden(X6,k1_tops_1(sK0,sK2))
      | ~ m1_connsp_2(sK2,sK0,X6) ) ),
    inference(resolution,[],[f37,f31])).

fof(f213,plain,(
    ~ r2_hidden(sK1,k1_tops_1(sK0,sK2)) ),
    inference(global_subsumption,[],[f169,f209,f212])).

fof(f212,plain,
    ( m2_connsp_2(sK2,sK0,k1_tarski(sK1))
    | ~ r2_hidden(sK1,k1_tops_1(sK0,sK2)) ),
    inference(resolution,[],[f177,f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f1])).

fof(f177,plain,
    ( ~ r1_tarski(k1_tarski(sK1),k1_tops_1(sK0,sK2))
    | m2_connsp_2(sK2,sK0,k1_tarski(sK1)) ),
    inference(subsumption_resolution,[],[f176,f165])).

fof(f176,plain,
    ( ~ r1_tarski(k1_tarski(sK1),k1_tops_1(sK0,sK2))
    | m2_connsp_2(sK2,sK0,k1_tarski(sK1))
    | v1_xboole_0(u1_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f172,f32])).

fof(f172,plain,
    ( ~ r1_tarski(k1_tarski(sK1),k1_tops_1(sK0,sK2))
    | m2_connsp_2(sK2,sK0,k1_tarski(sK1))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | v1_xboole_0(u1_struct_0(sK0)) ),
    inference(superposition,[],[f82,f166])).

% (24300)Refutation not found, incomplete strategy% (24300)------------------------------
% (24300)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (24300)Termination reason: Refutation not found, incomplete strategy

% (24300)Memory used [KB]: 10618
% (24300)Time elapsed: 0.087 s
% (24300)------------------------------
% (24300)------------------------------
fof(f82,plain,(
    ! [X0] :
      ( ~ r1_tarski(k6_domain_1(u1_struct_0(sK0),X0),k1_tops_1(sK0,sK2))
      | m2_connsp_2(sK2,sK0,k6_domain_1(u1_struct_0(sK0),X0))
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | v1_xboole_0(u1_struct_0(sK0)) ) ),
    inference(resolution,[],[f81,f41])).

fof(f81,plain,(
    ! [X6] :
      ( ~ m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r1_tarski(X6,k1_tops_1(sK0,sK2))
      | m2_connsp_2(sK2,sK0,X6) ) ),
    inference(subsumption_resolution,[],[f80,f34])).

fof(f80,plain,(
    ! [X6] :
      ( ~ m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v2_pre_topc(sK0)
      | ~ r1_tarski(X6,k1_tops_1(sK0,sK2))
      | m2_connsp_2(sK2,sK0,X6) ) ),
    inference(subsumption_resolution,[],[f76,f35])).

fof(f76,plain,(
    ! [X6] :
      ( ~ l1_pre_topc(sK0)
      | ~ m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v2_pre_topc(sK0)
      | ~ r1_tarski(X6,k1_tops_1(sK0,sK2))
      | m2_connsp_2(sK2,sK0,X6) ) ),
    inference(resolution,[],[f38,f31])).

fof(f38,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v2_pre_topc(X0)
      | ~ r1_tarski(X1,k1_tops_1(X0,X2))
      | m2_connsp_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f169,plain,
    ( ~ m2_connsp_2(sK2,sK0,k1_tarski(sK1))
    | ~ m1_connsp_2(sK2,sK0,sK1) ),
    inference(backward_demodulation,[],[f30,f166])).

fof(f30,plain,
    ( ~ m2_connsp_2(sK2,sK0,k6_domain_1(u1_struct_0(sK0),sK1))
    | ~ m1_connsp_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f13])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 19:35:22 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.37  ipcrm: permission denied for id (814350336)
% 0.13/0.37  ipcrm: permission denied for id (814383106)
% 0.13/0.37  ipcrm: permission denied for id (816939012)
% 0.13/0.37  ipcrm: permission denied for id (816971781)
% 0.13/0.38  ipcrm: permission denied for id (814448649)
% 0.13/0.38  ipcrm: permission denied for id (814481419)
% 0.13/0.38  ipcrm: permission denied for id (814514188)
% 0.13/0.38  ipcrm: permission denied for id (814546957)
% 0.13/0.38  ipcrm: permission denied for id (817168399)
% 0.13/0.38  ipcrm: permission denied for id (814612496)
% 0.13/0.39  ipcrm: permission denied for id (817201169)
% 0.13/0.39  ipcrm: permission denied for id (814645266)
% 0.20/0.39  ipcrm: permission denied for id (814678035)
% 0.20/0.39  ipcrm: permission denied for id (817233940)
% 0.20/0.39  ipcrm: permission denied for id (817332247)
% 0.20/0.40  ipcrm: permission denied for id (814809113)
% 0.20/0.40  ipcrm: permission denied for id (817397786)
% 0.20/0.40  ipcrm: permission denied for id (814874651)
% 0.20/0.40  ipcrm: permission denied for id (817430556)
% 0.20/0.40  ipcrm: permission denied for id (817463325)
% 0.20/0.41  ipcrm: permission denied for id (815005728)
% 0.20/0.41  ipcrm: permission denied for id (815038497)
% 0.20/0.41  ipcrm: permission denied for id (817594403)
% 0.20/0.41  ipcrm: permission denied for id (817627172)
% 0.20/0.41  ipcrm: permission denied for id (817692710)
% 0.20/0.42  ipcrm: permission denied for id (817791017)
% 0.20/0.42  ipcrm: permission denied for id (815202346)
% 0.20/0.42  ipcrm: permission denied for id (815235116)
% 0.20/0.42  ipcrm: permission denied for id (817856557)
% 0.20/0.42  ipcrm: permission denied for id (815300655)
% 0.20/0.43  ipcrm: permission denied for id (817922096)
% 0.20/0.43  ipcrm: permission denied for id (817954865)
% 0.20/0.43  ipcrm: permission denied for id (815366196)
% 0.20/0.43  ipcrm: permission denied for id (818053173)
% 0.20/0.43  ipcrm: permission denied for id (818118711)
% 0.20/0.44  ipcrm: permission denied for id (818184249)
% 0.20/0.44  ipcrm: permission denied for id (818249787)
% 0.20/0.44  ipcrm: permission denied for id (818282556)
% 0.20/0.44  ipcrm: permission denied for id (815497277)
% 0.20/0.44  ipcrm: permission denied for id (815530046)
% 0.20/0.45  ipcrm: permission denied for id (815562816)
% 0.20/0.45  ipcrm: permission denied for id (815595585)
% 0.20/0.45  ipcrm: permission denied for id (818413636)
% 0.20/0.45  ipcrm: permission denied for id (818446405)
% 0.20/0.45  ipcrm: permission denied for id (818479174)
% 0.20/0.45  ipcrm: permission denied for id (815661127)
% 0.20/0.46  ipcrm: permission denied for id (818511944)
% 0.20/0.46  ipcrm: permission denied for id (815726665)
% 0.20/0.46  ipcrm: permission denied for id (815759434)
% 0.20/0.46  ipcrm: permission denied for id (815824973)
% 0.20/0.47  ipcrm: permission denied for id (818675792)
% 0.20/0.47  ipcrm: permission denied for id (815890514)
% 0.20/0.47  ipcrm: permission denied for id (818872407)
% 0.20/0.48  ipcrm: permission denied for id (815988826)
% 0.20/0.48  ipcrm: permission denied for id (819003483)
% 0.20/0.48  ipcrm: permission denied for id (819036252)
% 0.20/0.48  ipcrm: permission denied for id (816087133)
% 0.20/0.48  ipcrm: permission denied for id (819101791)
% 0.20/0.49  ipcrm: permission denied for id (816119904)
% 0.20/0.49  ipcrm: permission denied for id (819167330)
% 0.20/0.49  ipcrm: permission denied for id (819232867)
% 0.20/0.49  ipcrm: permission denied for id (819331174)
% 0.20/0.49  ipcrm: permission denied for id (819363943)
% 0.20/0.50  ipcrm: permission denied for id (816349289)
% 0.20/0.50  ipcrm: permission denied for id (816382058)
% 0.20/0.50  ipcrm: permission denied for id (819462252)
% 0.20/0.50  ipcrm: permission denied for id (819495021)
% 0.20/0.51  ipcrm: permission denied for id (819593328)
% 0.20/0.51  ipcrm: permission denied for id (819626097)
% 0.20/0.51  ipcrm: permission denied for id (816480370)
% 0.20/0.51  ipcrm: permission denied for id (819658867)
% 0.20/0.51  ipcrm: permission denied for id (816513140)
% 0.20/0.52  ipcrm: permission denied for id (819757175)
% 0.20/0.52  ipcrm: permission denied for id (819789944)
% 0.20/0.52  ipcrm: permission denied for id (816611449)
% 0.35/0.52  ipcrm: permission denied for id (816644218)
% 0.35/0.52  ipcrm: permission denied for id (816676987)
% 0.35/0.52  ipcrm: permission denied for id (816775293)
% 0.35/0.52  ipcrm: permission denied for id (816808062)
% 0.35/0.53  ipcrm: permission denied for id (816840831)
% 0.37/0.63  % (24302)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_20 on theBenchmark
% 0.37/0.63  % (24310)lrs+10_128_av=off:bs=on:cond=on:gs=on:gsem=on:irw=on:lma=on:nm=2:newcnf=on:nwc=1:stl=30:updr=off_207 on theBenchmark
% 0.37/0.65  % (24310)Refutation found. Thanks to Tanya!
% 0.37/0.65  % SZS status Theorem for theBenchmark
% 0.37/0.65  % (24319)ott+11_8:1_av=off:fde=unused:nm=2:newcnf=on:nwc=1:sd=2:ss=axioms:st=3.0:sos=all:sp=reverse_arity:updr=off:uhcvi=on_70 on theBenchmark
% 0.37/0.66  % (24300)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_22 on theBenchmark
% 0.37/0.66  % (24299)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_118 on theBenchmark
% 0.37/0.66  % (24297)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_18 on theBenchmark
% 0.37/0.66  % (24303)lrs+1011_4:1_acc=model:add=large:afp=40000:afq=1.4:ccuc=first:cond=on:fsr=off:gsp=input_only:gs=on:gsem=off:irw=on:nwc=1:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:urr=on_42 on theBenchmark
% 0.37/0.66  % (24298)lrs+4_14_afr=on:afp=4000:afq=1.1:anc=none:cond=on:gs=on:gsem=on:irw=on:lma=on:nm=6:nwc=1.1:sas=z3:stl=30:sd=4:ss=axioms:st=1.2:sos=all:updr=off_51 on theBenchmark
% 0.37/0.66  % (24309)dis-10_1_aac=none:afr=on:afp=10000:afq=1.0:amm=off:anc=none:fsr=off:gs=on:gsem=off:irw=on:nm=4:newcnf=on:nwc=2:sp=occurrence_2 on theBenchmark
% 0.37/0.66  % (24301)lrs+1010_32_afr=on:anc=none:bd=off:fsr=off:gs=on:gsem=on:nwc=1.3:nicw=on:sas=z3:stl=30:updr=off_63 on theBenchmark
% 0.37/0.66  % (24308)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_136 on theBenchmark
% 0.37/0.66  % (24305)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_71 on theBenchmark
% 0.37/0.66  % SZS output start Proof for theBenchmark
% 0.37/0.66  fof(f216,plain,(
% 0.37/0.66    $false),
% 0.37/0.66    inference(subsumption_resolution,[],[f215,f209])).
% 0.37/0.66  fof(f209,plain,(
% 0.37/0.66    m1_connsp_2(sK2,sK0,sK1)),
% 0.37/0.66    inference(subsumption_resolution,[],[f208,f32])).
% 0.37/0.66  fof(f32,plain,(
% 0.37/0.66    m1_subset_1(sK1,u1_struct_0(sK0))),
% 0.37/0.66    inference(cnf_transformation,[],[f13])).
% 0.37/0.66  fof(f13,plain,(
% 0.37/0.66    ? [X0] : (? [X1] : (? [X2] : ((m2_connsp_2(X2,X0,k6_domain_1(u1_struct_0(X0),X1)) <~> m1_connsp_2(X2,X0,X1)) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.37/0.66    inference(flattening,[],[f12])).
% 0.37/0.66  fof(f12,plain,(
% 0.37/0.66    ? [X0] : (? [X1] : (? [X2] : ((m2_connsp_2(X2,X0,k6_domain_1(u1_struct_0(X0),X1)) <~> m1_connsp_2(X2,X0,X1)) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,u1_struct_0(X0))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 0.37/0.66    inference(ennf_transformation,[],[f11])).
% 0.37/0.66  fof(f11,negated_conjecture,(
% 0.37/0.66    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (m2_connsp_2(X2,X0,k6_domain_1(u1_struct_0(X0),X1)) <=> m1_connsp_2(X2,X0,X1)))))),
% 0.37/0.66    inference(negated_conjecture,[],[f10])).
% 0.37/0.66  fof(f10,conjecture,(
% 0.37/0.66    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (m2_connsp_2(X2,X0,k6_domain_1(u1_struct_0(X0),X1)) <=> m1_connsp_2(X2,X0,X1)))))),
% 0.37/0.66    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_connsp_2)).
% 0.37/0.66  fof(f208,plain,(
% 0.37/0.66    m1_connsp_2(sK2,sK0,sK1) | ~m1_subset_1(sK1,u1_struct_0(sK0))),
% 0.37/0.66    inference(duplicate_literal_removal,[],[f207])).
% 0.37/0.66  fof(f207,plain,(
% 0.37/0.66    m1_connsp_2(sK2,sK0,sK1) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | m1_connsp_2(sK2,sK0,sK1)),
% 0.37/0.66    inference(resolution,[],[f206,f128])).
% 0.37/0.66  fof(f128,plain,(
% 0.37/0.66    ( ! [X6] : (~r2_hidden(X6,k1_tops_1(sK0,sK2)) | ~m1_subset_1(X6,u1_struct_0(sK0)) | m1_connsp_2(sK2,sK0,X6)) )),
% 0.37/0.66    inference(subsumption_resolution,[],[f127,f33])).
% 0.37/0.66  fof(f33,plain,(
% 0.37/0.66    ~v2_struct_0(sK0)),
% 0.37/0.66    inference(cnf_transformation,[],[f13])).
% 0.37/0.66  fof(f127,plain,(
% 0.37/0.66    ( ! [X6] : (~m1_subset_1(X6,u1_struct_0(sK0)) | v2_struct_0(sK0) | ~r2_hidden(X6,k1_tops_1(sK0,sK2)) | m1_connsp_2(sK2,sK0,X6)) )),
% 0.37/0.66    inference(subsumption_resolution,[],[f126,f35])).
% 0.37/0.66  fof(f35,plain,(
% 0.37/0.66    l1_pre_topc(sK0)),
% 0.37/0.66    inference(cnf_transformation,[],[f13])).
% 0.37/0.66  fof(f126,plain,(
% 0.37/0.66    ( ! [X6] : (~l1_pre_topc(sK0) | ~m1_subset_1(X6,u1_struct_0(sK0)) | v2_struct_0(sK0) | ~r2_hidden(X6,k1_tops_1(sK0,sK2)) | m1_connsp_2(sK2,sK0,X6)) )),
% 0.37/0.66    inference(subsumption_resolution,[],[f122,f34])).
% 0.37/0.66  fof(f34,plain,(
% 0.37/0.66    v2_pre_topc(sK0)),
% 0.37/0.66    inference(cnf_transformation,[],[f13])).
% 0.37/0.66  fof(f122,plain,(
% 0.37/0.66    ( ! [X6] : (~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | ~m1_subset_1(X6,u1_struct_0(sK0)) | v2_struct_0(sK0) | ~r2_hidden(X6,k1_tops_1(sK0,sK2)) | m1_connsp_2(sK2,sK0,X6)) )),
% 0.37/0.66    inference(resolution,[],[f36,f31])).
% 0.37/0.67  fof(f31,plain,(
% 0.37/0.67    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.37/0.67    inference(cnf_transformation,[],[f13])).
% 0.37/0.67  fof(f36,plain,(
% 0.37/0.67    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | v2_struct_0(X0) | ~r2_hidden(X1,k1_tops_1(X0,X2)) | m1_connsp_2(X2,X0,X1)) )),
% 0.37/0.67    inference(cnf_transformation,[],[f15])).
% 0.37/0.67  fof(f15,plain,(
% 0.37/0.67    ! [X0] : (! [X1] : (! [X2] : ((m1_connsp_2(X2,X0,X1) <=> r2_hidden(X1,k1_tops_1(X0,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.37/0.67    inference(flattening,[],[f14])).
% 0.37/0.67  fof(f14,plain,(
% 0.37/0.67    ! [X0] : (! [X1] : (! [X2] : ((m1_connsp_2(X2,X0,X1) <=> r2_hidden(X1,k1_tops_1(X0,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.37/0.67    inference(ennf_transformation,[],[f6])).
% 0.37/0.67  fof(f6,axiom,(
% 0.37/0.67    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (m1_connsp_2(X2,X0,X1) <=> r2_hidden(X1,k1_tops_1(X0,X2))))))),
% 0.37/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_connsp_2)).
% 0.37/0.67  fof(f206,plain,(
% 0.37/0.67    r2_hidden(sK1,k1_tops_1(sK0,sK2)) | m1_connsp_2(sK2,sK0,sK1)),
% 0.37/0.67    inference(resolution,[],[f205,f168])).
% 0.37/0.67  fof(f168,plain,(
% 0.37/0.67    m2_connsp_2(sK2,sK0,k1_tarski(sK1)) | m1_connsp_2(sK2,sK0,sK1)),
% 0.37/0.67    inference(backward_demodulation,[],[f29,f166])).
% 0.37/0.67  fof(f166,plain,(
% 0.37/0.67    k6_domain_1(u1_struct_0(sK0),sK1) = k1_tarski(sK1)),
% 0.37/0.67    inference(resolution,[],[f165,f51])).
% 0.37/0.67  fof(f51,plain,(
% 0.37/0.67    v1_xboole_0(u1_struct_0(sK0)) | k6_domain_1(u1_struct_0(sK0),sK1) = k1_tarski(sK1)),
% 0.37/0.67    inference(resolution,[],[f40,f32])).
% 0.37/0.67  fof(f40,plain,(
% 0.37/0.67    ( ! [X0,X1] : (~m1_subset_1(X1,X0) | v1_xboole_0(X0) | k6_domain_1(X0,X1) = k1_tarski(X1)) )),
% 0.37/0.67    inference(cnf_transformation,[],[f19])).
% 0.37/0.67  fof(f19,plain,(
% 0.37/0.67    ! [X0,X1] : (k6_domain_1(X0,X1) = k1_tarski(X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0))),
% 0.37/0.67    inference(flattening,[],[f18])).
% 0.37/0.67  fof(f18,plain,(
% 0.37/0.67    ! [X0,X1] : (k6_domain_1(X0,X1) = k1_tarski(X1) | (~m1_subset_1(X1,X0) | v1_xboole_0(X0)))),
% 0.37/0.67    inference(ennf_transformation,[],[f4])).
% 0.37/0.67  fof(f4,axiom,(
% 0.37/0.67    ! [X0,X1] : ((m1_subset_1(X1,X0) & ~v1_xboole_0(X0)) => k6_domain_1(X0,X1) = k1_tarski(X1))),
% 0.37/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_domain_1)).
% 0.37/0.67  fof(f165,plain,(
% 0.37/0.67    ~v1_xboole_0(u1_struct_0(sK0))),
% 0.37/0.67    inference(subsumption_resolution,[],[f164,f35])).
% 0.37/0.67  fof(f164,plain,(
% 0.37/0.67    ~l1_pre_topc(sK0) | ~v1_xboole_0(u1_struct_0(sK0))),
% 0.37/0.67    inference(subsumption_resolution,[],[f163,f34])).
% 0.37/0.67  fof(f163,plain,(
% 0.37/0.67    ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | ~v1_xboole_0(u1_struct_0(sK0))),
% 0.37/0.67    inference(subsumption_resolution,[],[f162,f33])).
% 0.37/0.67  fof(f162,plain,(
% 0.37/0.67    v2_struct_0(sK0) | ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | ~v1_xboole_0(u1_struct_0(sK0))),
% 0.37/0.67    inference(resolution,[],[f161,f32])).
% 0.37/0.67  fof(f161,plain,(
% 0.37/0.67    ( ! [X0,X1] : (~m1_subset_1(X0,u1_struct_0(X1)) | v2_struct_0(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | ~v1_xboole_0(u1_struct_0(X1))) )),
% 0.37/0.67    inference(duplicate_literal_removal,[],[f160])).
% 0.37/0.67  fof(f160,plain,(
% 0.37/0.67    ( ! [X0,X1] : (~m1_subset_1(X0,u1_struct_0(X1)) | v2_struct_0(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | ~m1_subset_1(X0,u1_struct_0(X1)) | ~v1_xboole_0(u1_struct_0(X1)) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | ~m1_subset_1(X0,u1_struct_0(X1)) | v2_struct_0(X1)) )),
% 0.37/0.67    inference(resolution,[],[f158,f43])).
% 0.37/0.67  fof(f43,plain,(
% 0.37/0.67    ( ! [X0,X1] : (m1_connsp_2(sK3(X0,X1),X0,X1) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | v2_struct_0(X0)) )),
% 0.37/0.67    inference(cnf_transformation,[],[f25])).
% 0.37/0.67  fof(f25,plain,(
% 0.37/0.67    ! [X0,X1] : (? [X2] : m1_connsp_2(X2,X0,X1) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.37/0.67    inference(flattening,[],[f24])).
% 0.37/0.67  fof(f24,plain,(
% 0.37/0.67    ! [X0,X1] : (? [X2] : m1_connsp_2(X2,X0,X1) | (~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.37/0.67    inference(ennf_transformation,[],[f9])).
% 0.37/0.67  fof(f9,axiom,(
% 0.37/0.67    ! [X0,X1] : ((m1_subset_1(X1,u1_struct_0(X0)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ? [X2] : m1_connsp_2(X2,X0,X1))),
% 0.37/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',existence_m1_connsp_2)).
% 0.37/0.67  fof(f158,plain,(
% 0.37/0.67    ( ! [X4,X5,X3] : (~m1_connsp_2(sK3(X3,X5),X3,X4) | ~m1_subset_1(X4,u1_struct_0(X3)) | v2_struct_0(X3) | ~v2_pre_topc(X3) | ~l1_pre_topc(X3) | ~m1_subset_1(X5,u1_struct_0(X3)) | ~v1_xboole_0(u1_struct_0(X3))) )),
% 0.37/0.67    inference(duplicate_literal_removal,[],[f157])).
% 0.37/0.67  fof(f157,plain,(
% 0.37/0.67    ( ! [X4,X5,X3] : (~l1_pre_topc(X3) | ~m1_subset_1(X4,u1_struct_0(X3)) | v2_struct_0(X3) | ~v2_pre_topc(X3) | ~m1_connsp_2(sK3(X3,X5),X3,X4) | ~m1_subset_1(X5,u1_struct_0(X3)) | ~m1_subset_1(X5,u1_struct_0(X3)) | v2_struct_0(X3) | ~v2_pre_topc(X3) | ~l1_pre_topc(X3) | ~v1_xboole_0(u1_struct_0(X3))) )),
% 0.37/0.67    inference(resolution,[],[f133,f68])).
% 0.37/0.67  fof(f68,plain,(
% 0.37/0.67    ( ! [X2,X0,X1] : (~r2_hidden(X2,k1_tops_1(X0,sK3(X0,X1))) | ~m1_subset_1(X1,u1_struct_0(X0)) | v2_struct_0(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~v1_xboole_0(u1_struct_0(X0))) )),
% 0.37/0.67    inference(duplicate_literal_removal,[],[f65])).
% 0.37/0.67  fof(f65,plain,(
% 0.37/0.67    ( ! [X2,X0,X1] : (~l1_pre_topc(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | v2_struct_0(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~r2_hidden(X2,k1_tops_1(X0,sK3(X0,X1))) | ~v1_xboole_0(u1_struct_0(X0))) )),
% 0.37/0.67    inference(resolution,[],[f64,f56])).
% 0.37/0.67  fof(f56,plain,(
% 0.37/0.67    ( ! [X2,X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_pre_topc(X1) | ~r2_hidden(X2,k1_tops_1(X1,X0)) | ~v1_xboole_0(u1_struct_0(X1))) )),
% 0.37/0.67    inference(resolution,[],[f44,f47])).
% 0.37/0.67  fof(f47,plain,(
% 0.37/0.67    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1) | ~v1_xboole_0(X2)) )),
% 0.37/0.67    inference(cnf_transformation,[],[f28])).
% 0.37/0.67  fof(f28,plain,(
% 0.37/0.67    ! [X0,X1,X2] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 0.37/0.67    inference(ennf_transformation,[],[f2])).
% 0.37/0.67  fof(f2,axiom,(
% 0.37/0.67    ! [X0,X1,X2] : ~(v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1))),
% 0.37/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).
% 0.37/0.67  fof(f44,plain,(
% 0.37/0.67    ( ! [X0,X1] : (m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.37/0.67    inference(cnf_transformation,[],[f27])).
% 0.37/0.67  fof(f27,plain,(
% 0.37/0.67    ! [X0,X1] : (m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 0.37/0.67    inference(flattening,[],[f26])).
% 0.37/0.67  fof(f26,plain,(
% 0.37/0.67    ! [X0,X1] : (m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 0.37/0.67    inference(ennf_transformation,[],[f5])).
% 0.37/0.67  fof(f5,axiom,(
% 0.37/0.67    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 0.37/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_tops_1)).
% 0.37/0.67  fof(f64,plain,(
% 0.37/0.67    ( ! [X0,X1] : (m1_subset_1(sK3(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | v2_struct_0(X0) | ~v2_pre_topc(X0)) )),
% 0.37/0.67    inference(duplicate_literal_removal,[],[f63])).
% 0.37/0.67  fof(f63,plain,(
% 0.37/0.67    ( ! [X0,X1] : (~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | v2_struct_0(X0) | m1_subset_1(sK3(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | v2_struct_0(X0)) )),
% 0.37/0.67    inference(resolution,[],[f42,f43])).
% 0.37/0.67  fof(f42,plain,(
% 0.37/0.67    ( ! [X2,X0,X1] : (~m1_connsp_2(X2,X0,X1) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | v2_struct_0(X0) | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) )),
% 0.37/0.67    inference(cnf_transformation,[],[f23])).
% 0.37/0.67  fof(f23,plain,(
% 0.37/0.67    ! [X0,X1] : (! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_connsp_2(X2,X0,X1)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.37/0.67    inference(flattening,[],[f22])).
% 0.37/0.67  fof(f22,plain,(
% 0.37/0.67    ! [X0,X1] : (! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_connsp_2(X2,X0,X1)) | (~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.37/0.67    inference(ennf_transformation,[],[f8])).
% 0.37/0.67  fof(f8,axiom,(
% 0.37/0.67    ! [X0,X1] : ((m1_subset_1(X1,u1_struct_0(X0)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X2] : (m1_connsp_2(X2,X0,X1) => m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))))),
% 0.37/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_connsp_2)).
% 0.37/0.67  fof(f133,plain,(
% 0.37/0.67    ( ! [X8,X7,X9] : (r2_hidden(X8,k1_tops_1(X7,sK3(X7,X9))) | ~l1_pre_topc(X7) | ~m1_subset_1(X8,u1_struct_0(X7)) | v2_struct_0(X7) | ~v2_pre_topc(X7) | ~m1_connsp_2(sK3(X7,X9),X7,X8) | ~m1_subset_1(X9,u1_struct_0(X7))) )),
% 0.37/0.67    inference(duplicate_literal_removal,[],[f132])).
% 0.37/0.67  fof(f132,plain,(
% 0.37/0.67    ( ! [X8,X7,X9] : (~v2_pre_topc(X7) | ~l1_pre_topc(X7) | ~m1_subset_1(X8,u1_struct_0(X7)) | v2_struct_0(X7) | r2_hidden(X8,k1_tops_1(X7,sK3(X7,X9))) | ~m1_connsp_2(sK3(X7,X9),X7,X8) | ~l1_pre_topc(X7) | ~m1_subset_1(X9,u1_struct_0(X7)) | v2_struct_0(X7) | ~v2_pre_topc(X7)) )),
% 0.37/0.67    inference(resolution,[],[f37,f64])).
% 0.37/0.67  fof(f37,plain,(
% 0.37/0.67    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | v2_struct_0(X0) | r2_hidden(X1,k1_tops_1(X0,X2)) | ~m1_connsp_2(X2,X0,X1)) )),
% 0.37/0.67    inference(cnf_transformation,[],[f15])).
% 0.37/0.67  fof(f29,plain,(
% 0.37/0.67    m2_connsp_2(sK2,sK0,k6_domain_1(u1_struct_0(sK0),sK1)) | m1_connsp_2(sK2,sK0,sK1)),
% 0.37/0.67    inference(cnf_transformation,[],[f13])).
% 0.37/0.67  fof(f205,plain,(
% 0.37/0.67    ~m2_connsp_2(sK2,sK0,k1_tarski(sK1)) | r2_hidden(sK1,k1_tops_1(sK0,sK2))),
% 0.37/0.67    inference(resolution,[],[f175,f46])).
% 0.37/0.67  fof(f46,plain,(
% 0.37/0.67    ( ! [X0,X1] : (~r1_tarski(k1_tarski(X0),X1) | r2_hidden(X0,X1)) )),
% 0.37/0.67    inference(cnf_transformation,[],[f1])).
% 0.37/0.67  fof(f1,axiom,(
% 0.37/0.67    ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) <=> r2_hidden(X0,X1))),
% 0.37/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l1_zfmisc_1)).
% 0.37/0.67  fof(f175,plain,(
% 0.37/0.67    r1_tarski(k1_tarski(sK1),k1_tops_1(sK0,sK2)) | ~m2_connsp_2(sK2,sK0,k1_tarski(sK1))),
% 0.37/0.67    inference(subsumption_resolution,[],[f174,f165])).
% 0.37/0.67  fof(f174,plain,(
% 0.37/0.67    r1_tarski(k1_tarski(sK1),k1_tops_1(sK0,sK2)) | ~m2_connsp_2(sK2,sK0,k1_tarski(sK1)) | v1_xboole_0(u1_struct_0(sK0))),
% 0.37/0.67    inference(subsumption_resolution,[],[f171,f32])).
% 0.37/0.67  fof(f171,plain,(
% 0.37/0.67    r1_tarski(k1_tarski(sK1),k1_tops_1(sK0,sK2)) | ~m2_connsp_2(sK2,sK0,k1_tarski(sK1)) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | v1_xboole_0(u1_struct_0(sK0))),
% 0.37/0.67    inference(superposition,[],[f98,f166])).
% 0.37/0.67  fof(f98,plain,(
% 0.37/0.67    ( ! [X0] : (r1_tarski(k6_domain_1(u1_struct_0(sK0),X0),k1_tops_1(sK0,sK2)) | ~m2_connsp_2(sK2,sK0,k6_domain_1(u1_struct_0(sK0),X0)) | ~m1_subset_1(X0,u1_struct_0(sK0)) | v1_xboole_0(u1_struct_0(sK0))) )),
% 0.37/0.67    inference(resolution,[],[f97,f41])).
% 0.37/0.67  fof(f41,plain,(
% 0.37/0.67    ( ! [X0,X1] : (m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 0.37/0.67    inference(cnf_transformation,[],[f21])).
% 0.37/0.67  fof(f21,plain,(
% 0.37/0.67    ! [X0,X1] : (m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0))),
% 0.37/0.67    inference(flattening,[],[f20])).
% 0.37/0.67  fof(f20,plain,(
% 0.37/0.67    ! [X0,X1] : (m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) | (~m1_subset_1(X1,X0) | v1_xboole_0(X0)))),
% 0.37/0.67    inference(ennf_transformation,[],[f3])).
% 0.37/0.67  fof(f3,axiom,(
% 0.37/0.67    ! [X0,X1] : ((m1_subset_1(X1,X0) & ~v1_xboole_0(X0)) => m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)))),
% 0.37/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_domain_1)).
% 0.37/0.67  fof(f97,plain,(
% 0.37/0.67    ( ! [X6] : (~m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(sK0))) | r1_tarski(X6,k1_tops_1(sK0,sK2)) | ~m2_connsp_2(sK2,sK0,X6)) )),
% 0.37/0.67    inference(subsumption_resolution,[],[f96,f34])).
% 0.37/0.67  fof(f96,plain,(
% 0.37/0.67    ( ! [X6] : (~m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(sK0))) | ~v2_pre_topc(sK0) | r1_tarski(X6,k1_tops_1(sK0,sK2)) | ~m2_connsp_2(sK2,sK0,X6)) )),
% 0.37/0.67    inference(subsumption_resolution,[],[f92,f35])).
% 0.37/0.67  fof(f92,plain,(
% 0.37/0.67    ( ! [X6] : (~l1_pre_topc(sK0) | ~m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(sK0))) | ~v2_pre_topc(sK0) | r1_tarski(X6,k1_tops_1(sK0,sK2)) | ~m2_connsp_2(sK2,sK0,X6)) )),
% 0.37/0.67    inference(resolution,[],[f39,f31])).
% 0.37/0.67  fof(f39,plain,(
% 0.37/0.67    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v2_pre_topc(X0) | r1_tarski(X1,k1_tops_1(X0,X2)) | ~m2_connsp_2(X2,X0,X1)) )),
% 0.37/0.67    inference(cnf_transformation,[],[f17])).
% 0.37/0.67  fof(f17,plain,(
% 0.37/0.67    ! [X0] : (! [X1] : (! [X2] : ((m2_connsp_2(X2,X0,X1) <=> r1_tarski(X1,k1_tops_1(X0,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.37/0.67    inference(flattening,[],[f16])).
% 0.37/0.67  fof(f16,plain,(
% 0.37/0.67    ! [X0] : (! [X1] : (! [X2] : ((m2_connsp_2(X2,X0,X1) <=> r1_tarski(X1,k1_tops_1(X0,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 0.37/0.67    inference(ennf_transformation,[],[f7])).
% 0.37/0.67  fof(f7,axiom,(
% 0.37/0.67    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (m2_connsp_2(X2,X0,X1) <=> r1_tarski(X1,k1_tops_1(X0,X2))))))),
% 0.37/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_connsp_2)).
% 0.37/0.67  fof(f215,plain,(
% 0.37/0.67    ~m1_connsp_2(sK2,sK0,sK1)),
% 0.37/0.67    inference(subsumption_resolution,[],[f214,f32])).
% 0.37/0.67  fof(f214,plain,(
% 0.37/0.67    ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~m1_connsp_2(sK2,sK0,sK1)),
% 0.37/0.67    inference(resolution,[],[f213,f137])).
% 0.37/0.67  % (24321)lrs+1011_7_afp=100000:afq=1.0:amm=sco:anc=all_dependent:bs=unit_only:bsr=on:ep=RS:fde=none:gsp=input_only:gs=on:gsem=off:lwlo=on:nm=4:nwc=1:stl=120:sos=theory:sp=occurrence:uhcvi=on_412 on theBenchmark
% 0.37/0.67  fof(f137,plain,(
% 0.37/0.67    ( ! [X6] : (r2_hidden(X6,k1_tops_1(sK0,sK2)) | ~m1_subset_1(X6,u1_struct_0(sK0)) | ~m1_connsp_2(sK2,sK0,X6)) )),
% 0.37/0.67    inference(subsumption_resolution,[],[f136,f33])).
% 0.37/0.67  fof(f136,plain,(
% 0.37/0.67    ( ! [X6] : (~m1_subset_1(X6,u1_struct_0(sK0)) | v2_struct_0(sK0) | r2_hidden(X6,k1_tops_1(sK0,sK2)) | ~m1_connsp_2(sK2,sK0,X6)) )),
% 0.37/0.67    inference(subsumption_resolution,[],[f135,f35])).
% 0.37/0.67  fof(f135,plain,(
% 0.37/0.67    ( ! [X6] : (~l1_pre_topc(sK0) | ~m1_subset_1(X6,u1_struct_0(sK0)) | v2_struct_0(sK0) | r2_hidden(X6,k1_tops_1(sK0,sK2)) | ~m1_connsp_2(sK2,sK0,X6)) )),
% 0.37/0.67    inference(subsumption_resolution,[],[f131,f34])).
% 0.37/0.67  fof(f131,plain,(
% 0.37/0.67    ( ! [X6] : (~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | ~m1_subset_1(X6,u1_struct_0(sK0)) | v2_struct_0(sK0) | r2_hidden(X6,k1_tops_1(sK0,sK2)) | ~m1_connsp_2(sK2,sK0,X6)) )),
% 0.37/0.67    inference(resolution,[],[f37,f31])).
% 0.37/0.67  fof(f213,plain,(
% 0.37/0.67    ~r2_hidden(sK1,k1_tops_1(sK0,sK2))),
% 0.37/0.67    inference(global_subsumption,[],[f169,f209,f212])).
% 0.37/0.67  fof(f212,plain,(
% 0.37/0.67    m2_connsp_2(sK2,sK0,k1_tarski(sK1)) | ~r2_hidden(sK1,k1_tops_1(sK0,sK2))),
% 0.37/0.67    inference(resolution,[],[f177,f45])).
% 0.37/0.67  fof(f45,plain,(
% 0.37/0.67    ( ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) )),
% 0.37/0.67    inference(cnf_transformation,[],[f1])).
% 0.37/0.67  fof(f177,plain,(
% 0.37/0.67    ~r1_tarski(k1_tarski(sK1),k1_tops_1(sK0,sK2)) | m2_connsp_2(sK2,sK0,k1_tarski(sK1))),
% 0.37/0.67    inference(subsumption_resolution,[],[f176,f165])).
% 0.37/0.67  fof(f176,plain,(
% 0.37/0.67    ~r1_tarski(k1_tarski(sK1),k1_tops_1(sK0,sK2)) | m2_connsp_2(sK2,sK0,k1_tarski(sK1)) | v1_xboole_0(u1_struct_0(sK0))),
% 0.37/0.67    inference(subsumption_resolution,[],[f172,f32])).
% 0.37/0.67  fof(f172,plain,(
% 0.37/0.67    ~r1_tarski(k1_tarski(sK1),k1_tops_1(sK0,sK2)) | m2_connsp_2(sK2,sK0,k1_tarski(sK1)) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | v1_xboole_0(u1_struct_0(sK0))),
% 0.37/0.67    inference(superposition,[],[f82,f166])).
% 0.37/0.67  % (24300)Refutation not found, incomplete strategy% (24300)------------------------------
% 0.37/0.67  % (24300)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.37/0.67  % (24300)Termination reason: Refutation not found, incomplete strategy
% 0.37/0.67  
% 0.37/0.67  % (24300)Memory used [KB]: 10618
% 0.37/0.67  % (24300)Time elapsed: 0.087 s
% 0.37/0.67  % (24300)------------------------------
% 0.37/0.67  % (24300)------------------------------
% 0.37/0.67  fof(f82,plain,(
% 0.37/0.67    ( ! [X0] : (~r1_tarski(k6_domain_1(u1_struct_0(sK0),X0),k1_tops_1(sK0,sK2)) | m2_connsp_2(sK2,sK0,k6_domain_1(u1_struct_0(sK0),X0)) | ~m1_subset_1(X0,u1_struct_0(sK0)) | v1_xboole_0(u1_struct_0(sK0))) )),
% 0.37/0.67    inference(resolution,[],[f81,f41])).
% 0.37/0.67  fof(f81,plain,(
% 0.37/0.67    ( ! [X6] : (~m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(sK0))) | ~r1_tarski(X6,k1_tops_1(sK0,sK2)) | m2_connsp_2(sK2,sK0,X6)) )),
% 0.37/0.67    inference(subsumption_resolution,[],[f80,f34])).
% 0.37/0.67  fof(f80,plain,(
% 0.37/0.67    ( ! [X6] : (~m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(sK0))) | ~v2_pre_topc(sK0) | ~r1_tarski(X6,k1_tops_1(sK0,sK2)) | m2_connsp_2(sK2,sK0,X6)) )),
% 0.37/0.67    inference(subsumption_resolution,[],[f76,f35])).
% 0.37/0.67  fof(f76,plain,(
% 0.37/0.67    ( ! [X6] : (~l1_pre_topc(sK0) | ~m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(sK0))) | ~v2_pre_topc(sK0) | ~r1_tarski(X6,k1_tops_1(sK0,sK2)) | m2_connsp_2(sK2,sK0,X6)) )),
% 0.37/0.67    inference(resolution,[],[f38,f31])).
% 0.37/0.67  fof(f38,plain,(
% 0.37/0.67    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v2_pre_topc(X0) | ~r1_tarski(X1,k1_tops_1(X0,X2)) | m2_connsp_2(X2,X0,X1)) )),
% 0.37/0.67    inference(cnf_transformation,[],[f17])).
% 0.37/0.67  fof(f169,plain,(
% 0.37/0.67    ~m2_connsp_2(sK2,sK0,k1_tarski(sK1)) | ~m1_connsp_2(sK2,sK0,sK1)),
% 0.37/0.67    inference(backward_demodulation,[],[f30,f166])).
% 0.37/0.67  fof(f30,plain,(
% 0.37/0.67    ~m2_connsp_2(sK2,sK0,k6_domain_1(u1_struct_0(sK0),sK1)) | ~m1_connsp_2(sK2,sK0,sK1)),
% 0.37/0.67    inference(cnf_transformation,[],[f13])).
% 0.37/0.67  % SZS output end Proof for theBenchmark
% 0.37/0.67  % (24310)------------------------------
% 0.37/0.67  % (24310)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.37/0.67  % (24310)Termination reason: Refutation
% 0.37/0.67  
% 0.37/0.67  % (24310)Memory used [KB]: 6396
% 0.37/0.67  % (24310)Time elapsed: 0.091 s
% 0.37/0.67  % (24310)------------------------------
% 0.37/0.67  % (24310)------------------------------
% 0.37/0.67  % (24106)Success in time 0.308 s
%------------------------------------------------------------------------------
