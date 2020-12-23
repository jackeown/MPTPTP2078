%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1392+1.002 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n028.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:49:52 EST 2020

% Result     : Theorem 2.70s
% Output     : Refutation 2.70s
% Verified   : 
% Statistics : Number of formulae       :  134 ( 348 expanded)
%              Number of leaves         :   16 (  66 expanded)
%              Depth                    :   41
%              Number of atoms          :  605 (1756 expanded)
%              Number of equality atoms :   31 (  38 expanded)
%              Maximal formula depth    :   16 (   7 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f523,plain,(
    $false ),
    inference(subsumption_resolution,[],[f522,f47])).

fof(f47,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ v3_pre_topc(X1,X0)
          & v3_connsp_1(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & v1_connsp_2(X0)
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ v3_pre_topc(X1,X0)
          & v3_connsp_1(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & v1_connsp_2(X0)
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ( v1_connsp_2(X0)
         => ! [X1] :
              ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
             => ( v3_connsp_1(X1,X0)
               => v3_pre_topc(X1,X0) ) ) ) ) ),
    inference(negated_conjecture,[],[f18])).

fof(f18,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( v1_connsp_2(X0)
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( v3_connsp_1(X1,X0)
             => v3_pre_topc(X1,X0) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_connsp_2)).

fof(f522,plain,(
    ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(subsumption_resolution,[],[f491,f49])).

fof(f49,plain,(
    ~ v3_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f21])).

fof(f491,plain,
    ( v3_pre_topc(sK1,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(superposition,[],[f122,f480])).

fof(f480,plain,(
    sK1 = k1_tops_1(sK0,sK1) ),
    inference(subsumption_resolution,[],[f479,f47])).

fof(f479,plain,
    ( sK1 = k1_tops_1(sK0,sK1)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(resolution,[],[f462,f82])).

fof(f82,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(f462,plain,
    ( ~ r1_tarski(sK1,u1_struct_0(sK0))
    | sK1 = k1_tops_1(sK0,sK1) ),
    inference(subsumption_resolution,[],[f461,f47])).

fof(f461,plain,
    ( ~ r1_tarski(sK1,u1_struct_0(sK0))
    | sK1 = k1_tops_1(sK0,sK1)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(duplicate_literal_removal,[],[f458])).

fof(f458,plain,
    ( ~ r1_tarski(sK1,u1_struct_0(sK0))
    | sK1 = k1_tops_1(sK0,sK1)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | sK1 = k1_tops_1(sK0,sK1) ),
    inference(resolution,[],[f455,f132])).

fof(f132,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,k1_tops_1(sK0,X0))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | k1_tops_1(sK0,X0) = X0 ) ),
    inference(resolution,[],[f88,f77])).

fof(f77,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r1_tarski(X1,X0)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f88,plain,(
    ! [X0] :
      ( r1_tarski(k1_tops_1(sK0,X0),X0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(resolution,[],[f52,f56])).

fof(f56,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | r1_tarski(k1_tops_1(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k1_tops_1(X0,X1),X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => r1_tarski(k1_tops_1(X0,X1),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_tops_1)).

fof(f52,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f21])).

fof(f455,plain,
    ( r1_tarski(sK1,k1_tops_1(sK0,sK1))
    | ~ r1_tarski(sK1,u1_struct_0(sK0))
    | sK1 = k1_tops_1(sK0,sK1) ),
    inference(resolution,[],[f454,f79])).

fof(f79,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK5(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(f454,plain,(
    ! [X2] :
      ( ~ r2_hidden(sK5(sK1,k1_tops_1(sK0,sK1)),X2)
      | sK1 = k1_tops_1(sK0,sK1)
      | ~ r1_tarski(X2,u1_struct_0(sK0)) ) ),
    inference(subsumption_resolution,[],[f452,f86])).

fof(f86,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f75])).

fof(f75,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f452,plain,(
    ! [X2] :
      ( sK1 = k1_tops_1(sK0,sK1)
      | ~ r2_hidden(sK5(sK1,k1_tops_1(sK0,sK1)),X2)
      | ~ r1_tarski(X2,u1_struct_0(sK0))
      | ~ r1_tarski(u1_struct_0(sK0),u1_struct_0(sK0)) ) ),
    inference(resolution,[],[f450,f81])).

fof(f81,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f450,plain,(
    ! [X2] :
      ( ~ m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
      | sK1 = k1_tops_1(sK0,sK1)
      | ~ r2_hidden(sK5(sK1,k1_tops_1(sK0,sK1)),X2)
      | ~ r1_tarski(X2,u1_struct_0(sK0)) ) ),
    inference(subsumption_resolution,[],[f449,f47])).

fof(f449,plain,(
    ! [X2] :
      ( ~ m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
      | sK1 = k1_tops_1(sK0,sK1)
      | ~ r2_hidden(sK5(sK1,k1_tops_1(sK0,sK1)),X2)
      | ~ r1_tarski(X2,u1_struct_0(sK0))
      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(resolution,[],[f447,f82])).

fof(f447,plain,(
    ! [X0] :
      ( ~ r1_tarski(sK1,u1_struct_0(sK0))
      | ~ m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
      | sK1 = k1_tops_1(sK0,sK1)
      | ~ r2_hidden(sK5(sK1,k1_tops_1(sK0,sK1)),X0)
      | ~ r1_tarski(X0,u1_struct_0(sK0)) ) ),
    inference(resolution,[],[f440,f78])).

fof(f78,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X2,X1)
      | ~ r2_hidden(X2,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f440,plain,
    ( ~ r2_hidden(sK5(sK1,k1_tops_1(sK0,sK1)),u1_struct_0(sK0))
    | ~ r1_tarski(sK1,u1_struct_0(sK0))
    | ~ m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | sK1 = k1_tops_1(sK0,sK1) ),
    inference(resolution,[],[f437,f130])).

fof(f130,plain,(
    v3_pre_topc(u1_struct_0(sK0),sK0) ),
    inference(subsumption_resolution,[],[f129,f51])).

fof(f51,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f21])).

fof(f129,plain,
    ( v3_pre_topc(u1_struct_0(sK0),sK0)
    | ~ v2_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f128,f52])).

fof(f128,plain,
    ( v3_pre_topc(u1_struct_0(sK0),sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0) ),
    inference(superposition,[],[f71,f127])).

fof(f127,plain,(
    u1_struct_0(sK0) = k2_struct_0(sK0) ),
    inference(resolution,[],[f87,f54])).

fof(f54,plain,(
    ! [X0] :
      ( ~ l1_struct_0(X0)
      | u1_struct_0(X0) = k2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( u1_struct_0(X0) = k2_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => u1_struct_0(X0) = k2_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).

fof(f87,plain,(
    l1_struct_0(sK0) ),
    inference(resolution,[],[f52,f55])).

fof(f55,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(f71,plain,(
    ! [X0] :
      ( v3_pre_topc(k2_struct_0(X0),X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0] :
      ( v3_pre_topc(k2_struct_0(X0),X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f35])).

fof(f35,plain,(
    ! [X0] :
      ( v3_pre_topc(k2_struct_0(X0),X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => v3_pre_topc(k2_struct_0(X0),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc10_tops_1)).

fof(f437,plain,(
    ! [X1] :
      ( ~ v3_pre_topc(X1,sK0)
      | sK1 = k1_tops_1(sK0,sK1)
      | ~ r1_tarski(sK1,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r2_hidden(sK5(sK1,k1_tops_1(sK0,sK1)),X1) ) ),
    inference(duplicate_literal_removal,[],[f435])).

fof(f435,plain,(
    ! [X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | sK1 = k1_tops_1(sK0,sK1)
      | ~ r1_tarski(sK1,X1)
      | ~ v3_pre_topc(X1,sK0)
      | ~ r2_hidden(sK5(sK1,k1_tops_1(sK0,sK1)),X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(resolution,[],[f433,f117])).

fof(f117,plain,(
    ! [X12,X13] :
      ( m1_connsp_2(X12,sK0,X13)
      | ~ v3_pre_topc(X12,sK0)
      | ~ r2_hidden(X13,X12)
      | ~ m1_subset_1(X12,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(subsumption_resolution,[],[f116,f83])).

fof(f83,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f44])).

fof(f44,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).

fof(f116,plain,(
    ! [X12,X13] :
      ( ~ m1_subset_1(X12,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X13,u1_struct_0(sK0))
      | ~ v3_pre_topc(X12,sK0)
      | ~ r2_hidden(X13,X12)
      | m1_connsp_2(X12,sK0,X13) ) ),
    inference(subsumption_resolution,[],[f115,f50])).

fof(f50,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f21])).

fof(f115,plain,(
    ! [X12,X13] :
      ( v2_struct_0(sK0)
      | ~ m1_subset_1(X12,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X13,u1_struct_0(sK0))
      | ~ v3_pre_topc(X12,sK0)
      | ~ r2_hidden(X13,X12)
      | m1_connsp_2(X12,sK0,X13) ) ),
    inference(subsumption_resolution,[],[f96,f51])).

fof(f96,plain,(
    ! [X12,X13] :
      ( ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0)
      | ~ m1_subset_1(X12,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X13,u1_struct_0(sK0))
      | ~ v3_pre_topc(X12,sK0)
      | ~ r2_hidden(X13,X12)
      | m1_connsp_2(X12,sK0,X13) ) ),
    inference(resolution,[],[f52,f69])).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ v3_pre_topc(X1,X0)
      | ~ r2_hidden(X2,X1)
      | m1_connsp_2(X1,X0,X2) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_connsp_2(X1,X0,X2)
              | ~ r2_hidden(X2,X1)
              | ~ v3_pre_topc(X1,X0)
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_connsp_2(X1,X0,X2)
              | ~ r2_hidden(X2,X1)
              | ~ v3_pre_topc(X1,X0)
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( ( r2_hidden(X2,X1)
                  & v3_pre_topc(X1,X0) )
               => m1_connsp_2(X1,X0,X2) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_connsp_2)).

fof(f433,plain,(
    ! [X0] :
      ( ~ m1_connsp_2(X0,sK0,sK5(sK1,k1_tops_1(sK0,sK1)))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | sK1 = k1_tops_1(sK0,sK1)
      | ~ r1_tarski(sK1,X0) ) ),
    inference(subsumption_resolution,[],[f432,f47])).

fof(f432,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_connsp_2(X0,sK0,sK5(sK1,k1_tops_1(sK0,sK1)))
      | sK1 = k1_tops_1(sK0,sK1)
      | ~ r1_tarski(sK1,X0)
      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(duplicate_literal_removal,[],[f429])).

fof(f429,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_connsp_2(X0,sK0,sK5(sK1,k1_tops_1(sK0,sK1)))
      | sK1 = k1_tops_1(sK0,sK1)
      | ~ r1_tarski(sK1,X0)
      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
      | sK1 = k1_tops_1(sK0,sK1) ) ),
    inference(resolution,[],[f427,f132])).

fof(f427,plain,(
    ! [X0] :
      ( r1_tarski(sK1,k1_tops_1(sK0,sK1))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_connsp_2(X0,sK0,sK5(sK1,k1_tops_1(sK0,sK1)))
      | sK1 = k1_tops_1(sK0,sK1)
      | ~ r1_tarski(sK1,X0) ) ),
    inference(subsumption_resolution,[],[f424,f47])).

fof(f424,plain,(
    ! [X0] :
      ( ~ r1_tarski(sK1,X0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_connsp_2(X0,sK0,sK5(sK1,k1_tops_1(sK0,sK1)))
      | sK1 = k1_tops_1(sK0,sK1)
      | r1_tarski(sK1,k1_tops_1(sK0,sK1)) ) ),
    inference(resolution,[],[f297,f79])).

fof(f297,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK5(sK1,k1_tops_1(sK0,sK1)),X1)
      | ~ r1_tarski(sK1,X0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_connsp_2(X0,sK0,sK5(sK1,k1_tops_1(sK0,sK1)))
      | sK1 = k1_tops_1(sK0,sK1) ) ),
    inference(subsumption_resolution,[],[f295,f47])).

fof(f295,plain,(
    ! [X0,X1] :
      ( ~ m1_connsp_2(X0,sK0,sK5(sK1,k1_tops_1(sK0,sK1)))
      | ~ r1_tarski(sK1,X0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r2_hidden(sK5(sK1,k1_tops_1(sK0,sK1)),X1)
      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
      | sK1 = k1_tops_1(sK0,sK1) ) ),
    inference(resolution,[],[f263,f132])).

fof(f263,plain,(
    ! [X0,X1] :
      ( r1_tarski(sK1,k1_tops_1(sK0,sK1))
      | ~ m1_connsp_2(X0,sK0,sK5(sK1,k1_tops_1(sK0,sK1)))
      | ~ r1_tarski(sK1,X0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r2_hidden(sK5(sK1,k1_tops_1(sK0,sK1)),X1) ) ),
    inference(duplicate_literal_removal,[],[f261])).

fof(f261,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_connsp_2(X0,sK0,sK5(sK1,k1_tops_1(sK0,sK1)))
      | ~ r1_tarski(sK1,X0)
      | r1_tarski(sK1,k1_tops_1(sK0,sK1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r2_hidden(sK5(sK1,k1_tops_1(sK0,sK1)),X1)
      | r1_tarski(sK1,k1_tops_1(sK0,sK1)) ) ),
    inference(resolution,[],[f236,f79])).

fof(f236,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(sK5(X0,k1_tops_1(sK0,sK1)),sK1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_connsp_2(X1,sK0,sK5(X0,k1_tops_1(sK0,sK1)))
      | ~ r1_tarski(sK1,X1)
      | r1_tarski(X0,k1_tops_1(sK0,sK1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r2_hidden(sK5(X0,k1_tops_1(sK0,sK1)),X2) ) ),
    inference(resolution,[],[f235,f143])).

fof(f143,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_connsp_2(X0,sK0,sK5(X1,k1_tops_1(sK0,X0)))
      | r1_tarski(X1,k1_tops_1(sK0,X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r2_hidden(sK5(X1,k1_tops_1(sK0,X0)),X2) ) ),
    inference(resolution,[],[f137,f83])).

fof(f137,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(sK5(X0,k1_tops_1(sK0,X1)),u1_struct_0(sK0))
      | ~ m1_connsp_2(X1,sK0,sK5(X0,k1_tops_1(sK0,X1)))
      | r1_tarski(X0,k1_tops_1(sK0,X1)) ) ),
    inference(resolution,[],[f136,f80])).

fof(f80,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK5(X0,X1),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f136,plain,(
    ! [X10,X11] :
      ( r2_hidden(X10,k1_tops_1(sK0,X11))
      | ~ m1_subset_1(X10,u1_struct_0(sK0))
      | ~ m1_connsp_2(X11,sK0,X10) ) ),
    inference(subsumption_resolution,[],[f114,f121])).

fof(f121,plain,(
    ! [X17,X16] :
      ( m1_subset_1(X17,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_connsp_2(X17,sK0,X16)
      | ~ m1_subset_1(X16,u1_struct_0(sK0)) ) ),
    inference(subsumption_resolution,[],[f120,f50])).

fof(f120,plain,(
    ! [X17,X16] :
      ( v2_struct_0(sK0)
      | ~ m1_subset_1(X16,u1_struct_0(sK0))
      | ~ m1_connsp_2(X17,sK0,X16)
      | m1_subset_1(X17,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(subsumption_resolution,[],[f98,f51])).

fof(f98,plain,(
    ! [X17,X16] :
      ( ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0)
      | ~ m1_subset_1(X16,u1_struct_0(sK0))
      | ~ m1_connsp_2(X17,sK0,X16)
      | m1_subset_1(X17,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(resolution,[],[f52,f73])).

fof(f73,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_connsp_2(X2,X0,X1)
      | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_connsp_2(X2,X0,X1) )
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_connsp_2(X2,X0,X1) )
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,u1_struct_0(X0))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X2] :
          ( m1_connsp_2(X2,X0,X1)
         => m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_connsp_2)).

fof(f114,plain,(
    ! [X10,X11] :
      ( ~ m1_subset_1(X10,u1_struct_0(sK0))
      | ~ m1_subset_1(X11,k1_zfmisc_1(u1_struct_0(sK0)))
      | r2_hidden(X10,k1_tops_1(sK0,X11))
      | ~ m1_connsp_2(X11,sK0,X10) ) ),
    inference(subsumption_resolution,[],[f113,f50])).

fof(f113,plain,(
    ! [X10,X11] :
      ( v2_struct_0(sK0)
      | ~ m1_subset_1(X10,u1_struct_0(sK0))
      | ~ m1_subset_1(X11,k1_zfmisc_1(u1_struct_0(sK0)))
      | r2_hidden(X10,k1_tops_1(sK0,X11))
      | ~ m1_connsp_2(X11,sK0,X10) ) ),
    inference(subsumption_resolution,[],[f95,f51])).

fof(f95,plain,(
    ! [X10,X11] :
      ( ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0)
      | ~ m1_subset_1(X10,u1_struct_0(sK0))
      | ~ m1_subset_1(X11,k1_zfmisc_1(u1_struct_0(sK0)))
      | r2_hidden(X10,k1_tops_1(sK0,X11))
      | ~ m1_connsp_2(X11,sK0,X10) ) ),
    inference(resolution,[],[f52,f68])).

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | r2_hidden(X1,k1_tops_1(X0,X2))
      | ~ m1_connsp_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
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
    inference(flattening,[],[f29])).

fof(f29,plain,(
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
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
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

fof(f235,plain,(
    ! [X0,X1] :
      ( m1_connsp_2(sK1,sK0,X0)
      | ~ r2_hidden(X0,sK1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_connsp_2(X1,sK0,X0)
      | ~ r1_tarski(sK1,X1) ) ),
    inference(subsumption_resolution,[],[f234,f47])).

fof(f234,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r2_hidden(X0,sK1)
      | m1_connsp_2(sK1,sK0,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_connsp_2(X1,sK0,X0)
      | ~ r1_tarski(sK1,X1) ) ),
    inference(resolution,[],[f193,f48])).

fof(f48,plain,(
    v3_connsp_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f21])).

fof(f193,plain,(
    ! [X2,X0,X1] :
      ( ~ v3_connsp_1(X2,sK0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r2_hidden(X1,X2)
      | m1_connsp_2(X2,sK0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_connsp_2(X0,sK0,X1)
      | ~ r1_tarski(X2,X0) ) ),
    inference(duplicate_literal_removal,[],[f192])).

fof(f192,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_connsp_2(X0,sK0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r2_hidden(X1,X2)
      | m1_connsp_2(X2,sK0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v3_connsp_1(X2,sK0)
      | ~ r1_tarski(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(resolution,[],[f168,f119])).

fof(f119,plain,(
    ! [X14,X15] :
      ( r3_connsp_1(sK0,X15,X14)
      | ~ m1_subset_1(X15,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v3_connsp_1(X14,sK0)
      | ~ r1_tarski(X14,X15)
      | ~ m1_subset_1(X14,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(subsumption_resolution,[],[f118,f50])).

fof(f118,plain,(
    ! [X14,X15] :
      ( v2_struct_0(sK0)
      | ~ m1_subset_1(X14,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X15,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v3_connsp_1(X14,sK0)
      | ~ r1_tarski(X14,X15)
      | r3_connsp_1(sK0,X15,X14) ) ),
    inference(subsumption_resolution,[],[f97,f51])).

fof(f97,plain,(
    ! [X14,X15] :
      ( ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0)
      | ~ m1_subset_1(X14,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X15,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v3_connsp_1(X14,sK0)
      | ~ r1_tarski(X14,X15)
      | r3_connsp_1(sK0,X15,X14) ) ),
    inference(resolution,[],[f52,f70])).

fof(f70,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v3_connsp_1(X1,X0)
      | ~ r1_tarski(X1,X2)
      | r3_connsp_1(X0,X2,X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r3_connsp_1(X0,X2,X1)
              | ~ r1_tarski(X1,X2)
              | ~ v3_connsp_1(X1,X0)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f33])).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r3_connsp_1(X0,X2,X1)
              | ~ r1_tarski(X1,X2)
              | ~ v3_connsp_1(X1,X0)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( ( r1_tarski(X1,X2)
                  & v3_connsp_1(X1,X0) )
               => r3_connsp_1(X0,X2,X1) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t13_connsp_2)).

fof(f168,plain,(
    ! [X2,X0,X1] :
      ( ~ r3_connsp_1(sK0,X1,X0)
      | ~ m1_connsp_2(X1,sK0,X2)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r2_hidden(X2,X0)
      | m1_connsp_2(X0,sK0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(subsumption_resolution,[],[f167,f83])).

fof(f167,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_connsp_2(X1,sK0,X2)
      | ~ r3_connsp_1(sK0,X1,X0)
      | ~ r2_hidden(X2,X0)
      | m1_connsp_2(X0,sK0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X2,u1_struct_0(sK0)) ) ),
    inference(resolution,[],[f110,f126])).

fof(f126,plain,(
    ! [X0] :
      ( r1_connsp_2(sK0,X0)
      | ~ m1_subset_1(X0,u1_struct_0(sK0)) ) ),
    inference(subsumption_resolution,[],[f125,f50])).

fof(f125,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK0))
      | r1_connsp_2(sK0,X0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f124,f52])).

fof(f124,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(sK0)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | r1_connsp_2(sK0,X0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f123,f51])).

fof(f123,plain,(
    ! [X0] :
      ( ~ v2_pre_topc(sK0)
      | ~ l1_pre_topc(sK0)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | r1_connsp_2(sK0,X0)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f53,f57])).

fof(f57,plain,(
    ! [X0,X1] :
      ( ~ v1_connsp_2(X0)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | r1_connsp_2(X0,X1)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ( v1_connsp_2(X0)
      <=> ! [X1] :
            ( r1_connsp_2(X0,X1)
            | ~ m1_subset_1(X1,u1_struct_0(X0)) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ( v1_connsp_2(X0)
      <=> ! [X1] :
            ( r1_connsp_2(X0,X1)
            | ~ m1_subset_1(X1,u1_struct_0(X0)) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( v1_connsp_2(X0)
      <=> ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => r1_connsp_2(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_connsp_2)).

fof(f53,plain,(
    v1_connsp_2(sK0) ),
    inference(cnf_transformation,[],[f21])).

fof(f110,plain,(
    ! [X6,X7,X5] :
      ( ~ r1_connsp_2(sK0,X5)
      | ~ m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_connsp_2(X6,sK0,X5)
      | ~ r3_connsp_1(sK0,X6,X7)
      | ~ r2_hidden(X5,X7)
      | m1_connsp_2(X7,sK0,X5)
      | ~ m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(subsumption_resolution,[],[f109,f83])).

fof(f109,plain,(
    ! [X6,X7,X5] :
      ( ~ m1_subset_1(X5,u1_struct_0(sK0))
      | ~ m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_connsp_2(X6,sK0,X5)
      | ~ r3_connsp_1(sK0,X6,X7)
      | ~ r2_hidden(X5,X7)
      | m1_connsp_2(X7,sK0,X5)
      | ~ r1_connsp_2(sK0,X5) ) ),
    inference(subsumption_resolution,[],[f108,f50])).

fof(f108,plain,(
    ! [X6,X7,X5] :
      ( v2_struct_0(sK0)
      | ~ m1_subset_1(X5,u1_struct_0(sK0))
      | ~ m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_connsp_2(X6,sK0,X5)
      | ~ r3_connsp_1(sK0,X6,X7)
      | ~ r2_hidden(X5,X7)
      | m1_connsp_2(X7,sK0,X5)
      | ~ r1_connsp_2(sK0,X5) ) ),
    inference(subsumption_resolution,[],[f93,f51])).

fof(f93,plain,(
    ! [X6,X7,X5] :
      ( ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0)
      | ~ m1_subset_1(X5,u1_struct_0(sK0))
      | ~ m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_connsp_2(X6,sK0,X5)
      | ~ r3_connsp_1(sK0,X6,X7)
      | ~ r2_hidden(X5,X7)
      | m1_connsp_2(X7,sK0,X5)
      | ~ r1_connsp_2(sK0,X5) ) ),
    inference(resolution,[],[f52,f65])).

fof(f65,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_connsp_2(X2,X0,X1)
      | ~ r3_connsp_1(X0,X2,X3)
      | ~ r2_hidden(X1,X3)
      | m1_connsp_2(X3,X0,X1)
      | ~ r1_connsp_2(X0,X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_connsp_2(X0,X1)
          <=> ! [X2] :
                ( ! [X3] :
                    ( m1_connsp_2(X3,X0,X1)
                    | ~ r2_hidden(X1,X3)
                    | ~ r3_connsp_1(X0,X2,X3)
                    | ~ m1_connsp_2(X2,X0,X1)
                    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_connsp_2(X0,X1)
          <=> ! [X2] :
                ( ! [X3] :
                    ( m1_connsp_2(X3,X0,X1)
                    | ~ r2_hidden(X1,X3)
                    | ~ r3_connsp_1(X0,X2,X3)
                    | ~ m1_connsp_2(X2,X0,X1)
                    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ( r1_connsp_2(X0,X1)
          <=> ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => ! [X3] :
                    ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                   => ( ( r2_hidden(X1,X3)
                        & r3_connsp_1(X0,X2,X3)
                        & m1_connsp_2(X2,X0,X1) )
                     => m1_connsp_2(X3,X0,X1) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t19_connsp_2)).

fof(f122,plain,(
    ! [X18] :
      ( v3_pre_topc(k1_tops_1(sK0,X18),sK0)
      | ~ m1_subset_1(X18,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(subsumption_resolution,[],[f99,f51])).

fof(f99,plain,(
    ! [X18] :
      ( ~ v2_pre_topc(sK0)
      | ~ m1_subset_1(X18,k1_zfmisc_1(u1_struct_0(sK0)))
      | v3_pre_topc(k1_tops_1(sK0,X18),sK0) ) ),
    inference(resolution,[],[f52,f74])).

fof(f74,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v3_pre_topc(k1_tops_1(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(k1_tops_1(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(k1_tops_1(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => v3_pre_topc(k1_tops_1(X0,X1),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc9_tops_1)).

%------------------------------------------------------------------------------
