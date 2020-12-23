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
% DateTime   : Thu Dec  3 13:11:20 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   74 (1016 expanded)
%              Number of leaves         :    6 ( 191 expanded)
%              Depth                    :   36
%              Number of atoms          :  277 (5915 expanded)
%              Number of equality atoms :   18 ( 136 expanded)
%              Maximal formula depth    :   13 (   6 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f234,plain,(
    $false ),
    inference(subsumption_resolution,[],[f233,f228])).

fof(f228,plain,(
    ~ r2_hidden(sK2,sK1) ),
    inference(subsumption_resolution,[],[f227,f26])).

fof(f26,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v3_pre_topc(X1,X0)
          <~> ! [X2] :
                ( r2_hidden(X2,X1)
              <=> ? [X3] :
                    ( r2_hidden(X2,X3)
                    & r1_tarski(X3,X1)
                    & v3_pre_topc(X3,X0)
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) ) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f8])).

fof(f8,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v3_pre_topc(X1,X0)
          <~> ! [X2] :
                ( r2_hidden(X2,X1)
              <=> ? [X3] :
                    ( r2_hidden(X2,X3)
                    & r1_tarski(X3,X1)
                    & v3_pre_topc(X3,X0)
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) ) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( v3_pre_topc(X1,X0)
            <=> ! [X2] :
                  ( r2_hidden(X2,X1)
                <=> ? [X3] :
                      ( r2_hidden(X2,X3)
                      & r1_tarski(X3,X1)
                      & v3_pre_topc(X3,X0)
                      & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f6])).

fof(f6,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v3_pre_topc(X1,X0)
          <=> ! [X2] :
                ( r2_hidden(X2,X1)
              <=> ? [X3] :
                    ( r2_hidden(X2,X3)
                    & r1_tarski(X3,X1)
                    & v3_pre_topc(X3,X0)
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t57_tops_1)).

fof(f227,plain,
    ( ~ r2_hidden(sK2,sK1)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(subsumption_resolution,[],[f226,f39])).

fof(f39,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f226,plain,
    ( ~ r1_tarski(sK1,sK1)
    | ~ r2_hidden(sK2,sK1)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(resolution,[],[f207,f197])).

fof(f197,plain,(
    v3_pre_topc(sK1,sK0) ),
    inference(resolution,[],[f196,f26])).

fof(f196,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | v3_pre_topc(sK1,sK0) ) ),
    inference(resolution,[],[f195,f28])).

fof(f28,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f9])).

fof(f195,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v3_pre_topc(sK1,sK0) ) ),
    inference(subsumption_resolution,[],[f194,f27])).

fof(f27,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f9])).

fof(f194,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v2_pre_topc(sK0)
      | v3_pre_topc(sK1,sK0) ) ),
    inference(subsumption_resolution,[],[f193,f26])).

fof(f193,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v2_pre_topc(sK0)
      | v3_pre_topc(sK1,sK0) ) ),
    inference(subsumption_resolution,[],[f192,f28])).

fof(f192,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(sK0)
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v2_pre_topc(sK0)
      | v3_pre_topc(sK1,sK0) ) ),
    inference(trivial_inequality_removal,[],[f191])).

fof(f191,plain,(
    ! [X0,X1] :
      ( sK1 != sK1
      | ~ l1_pre_topc(sK0)
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v2_pre_topc(sK0)
      | v3_pre_topc(sK1,sK0) ) ),
    inference(superposition,[],[f31,f164])).

fof(f164,plain,(
    sK1 = k1_tops_1(sK0,sK1) ),
    inference(subsumption_resolution,[],[f163,f51])).

fof(f51,plain,
    ( ~ r1_tarski(sK1,k1_tops_1(sK0,sK1))
    | sK1 = k1_tops_1(sK0,sK1) ),
    inference(resolution,[],[f49,f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f2])).

fof(f49,plain,(
    r1_tarski(k1_tops_1(sK0,sK1),sK1) ),
    inference(resolution,[],[f48,f26])).

fof(f48,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | r1_tarski(k1_tops_1(sK0,X0),X0) ) ),
    inference(resolution,[],[f29,f28])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | r1_tarski(k1_tops_1(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k1_tops_1(X0,X1),X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => r1_tarski(k1_tops_1(X0,X1),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_tops_1)).

fof(f163,plain,
    ( sK1 = k1_tops_1(sK0,sK1)
    | r1_tarski(sK1,k1_tops_1(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f162,f26])).

fof(f162,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | sK1 = k1_tops_1(sK0,sK1)
    | r1_tarski(sK1,k1_tops_1(sK0,sK1)) ),
    inference(resolution,[],[f131,f39])).

fof(f131,plain,(
    ! [X2] :
      ( ~ r1_tarski(sK1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
      | sK1 = k1_tops_1(sK0,sK1)
      | r1_tarski(sK1,k1_tops_1(sK0,X2)) ) ),
    inference(subsumption_resolution,[],[f128,f26])).

fof(f128,plain,(
    ! [X2] :
      ( sK1 = k1_tops_1(sK0,sK1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r1_tarski(sK1,X2)
      | r1_tarski(sK1,k1_tops_1(sK0,X2)) ) ),
    inference(resolution,[],[f116,f83])).

fof(f83,plain,(
    ! [X0,X1] :
      ( ~ v3_pre_topc(X0,sK0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r1_tarski(X0,X1)
      | r1_tarski(X0,k1_tops_1(sK0,X1)) ) ),
    inference(resolution,[],[f30,f28])).

fof(f30,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v3_pre_topc(X1,X0)
      | ~ r1_tarski(X1,X2)
      | r1_tarski(X1,k1_tops_1(X0,X2)) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(X1,k1_tops_1(X0,X2))
              | ~ r1_tarski(X1,X2)
              | ~ v3_pre_topc(X1,X0)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(X1,k1_tops_1(X0,X2))
              | ~ r1_tarski(X1,X2)
              | ~ v3_pre_topc(X1,X0)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( ( r1_tarski(X1,X2)
                  & v3_pre_topc(X1,X0) )
               => r1_tarski(X1,k1_tops_1(X0,X2)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t56_tops_1)).

fof(f116,plain,
    ( v3_pre_topc(sK1,sK0)
    | sK1 = k1_tops_1(sK0,sK1) ),
    inference(resolution,[],[f115,f51])).

fof(f115,plain,
    ( r1_tarski(sK1,k1_tops_1(sK0,sK1))
    | v3_pre_topc(sK1,sK0) ),
    inference(duplicate_literal_removal,[],[f113])).

fof(f113,plain,
    ( v3_pre_topc(sK1,sK0)
    | r1_tarski(sK1,k1_tops_1(sK0,sK1))
    | r1_tarski(sK1,k1_tops_1(sK0,sK1)) ),
    inference(resolution,[],[f111,f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK5(X0,X1),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(f111,plain,(
    ! [X0] :
      ( r2_hidden(sK5(sK1,X0),k1_tops_1(sK0,sK1))
      | v3_pre_topc(sK1,sK0)
      | r1_tarski(sK1,X0) ) ),
    inference(subsumption_resolution,[],[f110,f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK5(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f110,plain,(
    ! [X0] :
      ( ~ r2_hidden(sK5(sK1,X0),sK1)
      | v3_pre_topc(sK1,sK0)
      | r2_hidden(sK5(sK1,X0),k1_tops_1(sK0,sK1))
      | r1_tarski(sK1,X0) ) ),
    inference(duplicate_literal_removal,[],[f104])).

% (22251)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
fof(f104,plain,(
    ! [X0] :
      ( ~ r2_hidden(sK5(sK1,X0),sK1)
      | v3_pre_topc(sK1,sK0)
      | r2_hidden(sK5(sK1,X0),k1_tops_1(sK0,sK1))
      | v3_pre_topc(sK1,sK0)
      | r1_tarski(sK1,X0) ) ),
    inference(resolution,[],[f103,f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(sK4(sK5(sK1,X0)),X1)
      | r2_hidden(sK5(sK1,X0),X1)
      | v3_pre_topc(sK1,sK0)
      | r1_tarski(sK1,X0) ) ),
    inference(resolution,[],[f45,f37])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,sK1)
      | ~ r1_tarski(sK4(X0),X1)
      | r2_hidden(X0,X1)
      | v3_pre_topc(sK1,sK0) ) ),
    inference(resolution,[],[f36,f19])).

fof(f19,plain,(
    ! [X2] :
      ( r2_hidden(X2,sK4(X2))
      | ~ r2_hidden(X2,sK1)
      | v3_pre_topc(sK1,sK0) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f36,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,X0)
      | r2_hidden(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f103,plain,(
    ! [X0] :
      ( r1_tarski(sK4(X0),k1_tops_1(sK0,sK1))
      | ~ r2_hidden(X0,sK1)
      | v3_pre_topc(sK1,sK0) ) ),
    inference(subsumption_resolution,[],[f100,f18])).

fof(f18,plain,(
    ! [X2] :
      ( r1_tarski(sK4(X2),sK1)
      | ~ r2_hidden(X2,sK1)
      | v3_pre_topc(sK1,sK0) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f100,plain,(
    ! [X0] :
      ( ~ r1_tarski(sK4(X0),sK1)
      | r1_tarski(sK4(X0),k1_tops_1(sK0,sK1))
      | ~ r2_hidden(X0,sK1)
      | v3_pre_topc(sK1,sK0) ) ),
    inference(resolution,[],[f99,f26])).

fof(f99,plain,(
    ! [X2,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r1_tarski(sK4(X2),X1)
      | r1_tarski(sK4(X2),k1_tops_1(sK0,X1))
      | ~ r2_hidden(X2,sK1)
      | v3_pre_topc(sK1,sK0) ) ),
    inference(subsumption_resolution,[],[f97,f16])).

fof(f16,plain,(
    ! [X2] :
      ( m1_subset_1(sK4(X2),k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r2_hidden(X2,sK1)
      | v3_pre_topc(sK1,sK0) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f97,plain,(
    ! [X2,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(sK4(X2),k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r1_tarski(sK4(X2),X1)
      | r1_tarski(sK4(X2),k1_tops_1(sK0,X1))
      | ~ r2_hidden(X2,sK1)
      | v3_pre_topc(sK1,sK0) ) ),
    inference(resolution,[],[f83,f17])).

fof(f17,plain,(
    ! [X2] :
      ( v3_pre_topc(sK4(X2),sK0)
      | ~ r2_hidden(X2,sK1)
      | v3_pre_topc(sK1,sK0) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f31,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_tops_1(X0,X2) != X2
      | ~ l1_pre_topc(X0)
      | ~ l1_pre_topc(X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ v2_pre_topc(X0)
      | v3_pre_topc(X2,X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ( v3_pre_topc(X2,X0)
                      | k1_tops_1(X0,X2) != X2 )
                    & ( k1_tops_1(X1,X3) = X3
                      | ~ v3_pre_topc(X3,X1) ) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ( v3_pre_topc(X2,X0)
                      | k1_tops_1(X0,X2) != X2 )
                    & ( k1_tops_1(X1,X3) = X3
                      | ~ v3_pre_topc(X3,X1) ) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( l1_pre_topc(X1)
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ! [X3] :
                  ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
                 => ( ( k1_tops_1(X0,X2) = X2
                     => v3_pre_topc(X2,X0) )
                    & ( v3_pre_topc(X3,X1)
                     => k1_tops_1(X1,X3) = X3 ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_tops_1)).

fof(f207,plain,(
    ! [X1] :
      ( ~ v3_pre_topc(X1,sK0)
      | ~ r1_tarski(X1,sK1)
      | ~ r2_hidden(sK2,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(subsumption_resolution,[],[f201,f36])).

fof(f201,plain,(
    ! [X1] :
      ( ~ v3_pre_topc(X1,sK0)
      | ~ r1_tarski(X1,sK1)
      | ~ r2_hidden(sK2,X1)
      | ~ r2_hidden(sK2,sK1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(resolution,[],[f197,f21])).

fof(f21,plain,(
    ! [X3] :
      ( ~ v3_pre_topc(sK1,sK0)
      | ~ v3_pre_topc(X3,sK0)
      | ~ r1_tarski(X3,sK1)
      | ~ r2_hidden(sK2,X3)
      | ~ r2_hidden(sK2,sK1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f233,plain,(
    r2_hidden(sK2,sK1) ),
    inference(duplicate_literal_removal,[],[f230])).

fof(f230,plain,
    ( r2_hidden(sK2,sK1)
    | r2_hidden(sK2,sK1) ),
    inference(resolution,[],[f229,f211])).

fof(f211,plain,(
    ! [X0] :
      ( ~ r1_tarski(sK3,X0)
      | r2_hidden(sK2,X0)
      | r2_hidden(sK2,sK1) ) ),
    inference(resolution,[],[f203,f36])).

fof(f203,plain,
    ( r2_hidden(sK2,sK3)
    | r2_hidden(sK2,sK1) ),
    inference(resolution,[],[f197,f25])).

fof(f25,plain,
    ( ~ v3_pre_topc(sK1,sK0)
    | r2_hidden(sK2,sK1)
    | r2_hidden(sK2,sK3) ),
    inference(cnf_transformation,[],[f9])).

fof(f229,plain,(
    r1_tarski(sK3,sK1) ),
    inference(resolution,[],[f228,f204])).

fof(f204,plain,
    ( r2_hidden(sK2,sK1)
    | r1_tarski(sK3,sK1) ),
    inference(resolution,[],[f197,f24])).

fof(f24,plain,
    ( ~ v3_pre_topc(sK1,sK0)
    | r2_hidden(sK2,sK1)
    | r1_tarski(sK3,sK1) ),
    inference(cnf_transformation,[],[f9])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 15:10:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.48  % (22253)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.20/0.51  % (22270)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.20/0.51  % (22262)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.20/0.51  % (22261)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.20/0.51  % (22266)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.20/0.51  % (22254)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.20/0.51  % (22249)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.20/0.52  % (22274)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.20/0.52  % (22248)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.20/0.52  % (22259)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.20/0.52  % (22269)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.20/0.53  % (22258)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.20/0.53  % (22254)Refutation found. Thanks to Tanya!
% 0.20/0.53  % SZS status Theorem for theBenchmark
% 0.20/0.53  % SZS output start Proof for theBenchmark
% 0.20/0.53  fof(f234,plain,(
% 0.20/0.53    $false),
% 0.20/0.53    inference(subsumption_resolution,[],[f233,f228])).
% 0.20/0.53  fof(f228,plain,(
% 0.20/0.53    ~r2_hidden(sK2,sK1)),
% 0.20/0.53    inference(subsumption_resolution,[],[f227,f26])).
% 0.20/0.53  fof(f26,plain,(
% 0.20/0.53    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.20/0.53    inference(cnf_transformation,[],[f9])).
% 0.20/0.53  fof(f9,plain,(
% 0.20/0.53    ? [X0] : (? [X1] : ((v3_pre_topc(X1,X0) <~> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (r2_hidden(X2,X3) & r1_tarski(X3,X1) & v3_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 0.20/0.53    inference(flattening,[],[f8])).
% 0.20/0.53  fof(f8,plain,(
% 0.20/0.53    ? [X0] : (? [X1] : ((v3_pre_topc(X1,X0) <~> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (r2_hidden(X2,X3) & r1_tarski(X3,X1) & v3_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_pre_topc(X0) & v2_pre_topc(X0)))),
% 0.20/0.53    inference(ennf_transformation,[],[f7])).
% 0.20/0.53  fof(f7,negated_conjecture,(
% 0.20/0.53    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_pre_topc(X1,X0) <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (r2_hidden(X2,X3) & r1_tarski(X3,X1) & v3_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))))))),
% 0.20/0.53    inference(negated_conjecture,[],[f6])).
% 0.20/0.53  fof(f6,conjecture,(
% 0.20/0.53    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_pre_topc(X1,X0) <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (r2_hidden(X2,X3) & r1_tarski(X3,X1) & v3_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))))))),
% 0.20/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t57_tops_1)).
% 0.20/0.53  fof(f227,plain,(
% 0.20/0.53    ~r2_hidden(sK2,sK1) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.20/0.53    inference(subsumption_resolution,[],[f226,f39])).
% 0.20/0.53  fof(f39,plain,(
% 0.20/0.53    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 0.20/0.53    inference(equality_resolution,[],[f34])).
% 0.20/0.53  fof(f34,plain,(
% 0.20/0.53    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 0.20/0.53    inference(cnf_transformation,[],[f2])).
% 0.20/0.53  fof(f2,axiom,(
% 0.20/0.53    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.20/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.20/0.53  fof(f226,plain,(
% 0.20/0.53    ~r1_tarski(sK1,sK1) | ~r2_hidden(sK2,sK1) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.20/0.53    inference(resolution,[],[f207,f197])).
% 0.20/0.53  fof(f197,plain,(
% 0.20/0.53    v3_pre_topc(sK1,sK0)),
% 0.20/0.53    inference(resolution,[],[f196,f26])).
% 0.20/0.53  fof(f196,plain,(
% 0.20/0.53    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | v3_pre_topc(sK1,sK0)) )),
% 0.20/0.53    inference(resolution,[],[f195,f28])).
% 0.20/0.53  fof(f28,plain,(
% 0.20/0.53    l1_pre_topc(sK0)),
% 0.20/0.53    inference(cnf_transformation,[],[f9])).
% 0.20/0.53  fof(f195,plain,(
% 0.20/0.53    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v3_pre_topc(sK1,sK0)) )),
% 0.20/0.53    inference(subsumption_resolution,[],[f194,f27])).
% 0.20/0.53  fof(f27,plain,(
% 0.20/0.53    v2_pre_topc(sK0)),
% 0.20/0.53    inference(cnf_transformation,[],[f9])).
% 0.20/0.53  fof(f194,plain,(
% 0.20/0.53    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v2_pre_topc(sK0) | v3_pre_topc(sK1,sK0)) )),
% 0.20/0.53    inference(subsumption_resolution,[],[f193,f26])).
% 0.20/0.53  fof(f193,plain,(
% 0.20/0.53    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v2_pre_topc(sK0) | v3_pre_topc(sK1,sK0)) )),
% 0.20/0.53    inference(subsumption_resolution,[],[f192,f28])).
% 0.20/0.53  fof(f192,plain,(
% 0.20/0.53    ( ! [X0,X1] : (~l1_pre_topc(sK0) | ~l1_pre_topc(X0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v2_pre_topc(sK0) | v3_pre_topc(sK1,sK0)) )),
% 0.20/0.53    inference(trivial_inequality_removal,[],[f191])).
% 0.20/0.53  fof(f191,plain,(
% 0.20/0.53    ( ! [X0,X1] : (sK1 != sK1 | ~l1_pre_topc(sK0) | ~l1_pre_topc(X0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v2_pre_topc(sK0) | v3_pre_topc(sK1,sK0)) )),
% 0.20/0.53    inference(superposition,[],[f31,f164])).
% 0.20/0.53  fof(f164,plain,(
% 0.20/0.53    sK1 = k1_tops_1(sK0,sK1)),
% 0.20/0.53    inference(subsumption_resolution,[],[f163,f51])).
% 0.20/0.53  fof(f51,plain,(
% 0.20/0.53    ~r1_tarski(sK1,k1_tops_1(sK0,sK1)) | sK1 = k1_tops_1(sK0,sK1)),
% 0.20/0.53    inference(resolution,[],[f49,f35])).
% 0.20/0.53  fof(f35,plain,(
% 0.20/0.53    ( ! [X0,X1] : (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1) | X0 = X1) )),
% 0.20/0.53    inference(cnf_transformation,[],[f2])).
% 0.20/0.53  fof(f49,plain,(
% 0.20/0.53    r1_tarski(k1_tops_1(sK0,sK1),sK1)),
% 0.20/0.53    inference(resolution,[],[f48,f26])).
% 0.20/0.53  fof(f48,plain,(
% 0.20/0.53    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | r1_tarski(k1_tops_1(sK0,X0),X0)) )),
% 0.20/0.53    inference(resolution,[],[f29,f28])).
% 0.20/0.53  fof(f29,plain,(
% 0.20/0.53    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | r1_tarski(k1_tops_1(X0,X1),X1)) )),
% 0.20/0.53    inference(cnf_transformation,[],[f10])).
% 0.20/0.53  fof(f10,plain,(
% 0.20/0.53    ! [X0] : (! [X1] : (r1_tarski(k1_tops_1(X0,X1),X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.20/0.53    inference(ennf_transformation,[],[f3])).
% 0.20/0.53  fof(f3,axiom,(
% 0.20/0.53    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => r1_tarski(k1_tops_1(X0,X1),X1)))),
% 0.20/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_tops_1)).
% 0.20/0.53  fof(f163,plain,(
% 0.20/0.53    sK1 = k1_tops_1(sK0,sK1) | r1_tarski(sK1,k1_tops_1(sK0,sK1))),
% 0.20/0.53    inference(subsumption_resolution,[],[f162,f26])).
% 0.20/0.53  fof(f162,plain,(
% 0.20/0.53    ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | sK1 = k1_tops_1(sK0,sK1) | r1_tarski(sK1,k1_tops_1(sK0,sK1))),
% 0.20/0.53    inference(resolution,[],[f131,f39])).
% 0.20/0.53  fof(f131,plain,(
% 0.20/0.53    ( ! [X2] : (~r1_tarski(sK1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) | sK1 = k1_tops_1(sK0,sK1) | r1_tarski(sK1,k1_tops_1(sK0,X2))) )),
% 0.20/0.53    inference(subsumption_resolution,[],[f128,f26])).
% 0.20/0.53  fof(f128,plain,(
% 0.20/0.53    ( ! [X2] : (sK1 = k1_tops_1(sK0,sK1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~r1_tarski(sK1,X2) | r1_tarski(sK1,k1_tops_1(sK0,X2))) )),
% 0.20/0.53    inference(resolution,[],[f116,f83])).
% 0.20/0.53  fof(f83,plain,(
% 0.20/0.53    ( ! [X0,X1] : (~v3_pre_topc(X0,sK0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~r1_tarski(X0,X1) | r1_tarski(X0,k1_tops_1(sK0,X1))) )),
% 0.20/0.53    inference(resolution,[],[f30,f28])).
% 0.20/0.53  fof(f30,plain,(
% 0.20/0.53    ( ! [X2,X0,X1] : (~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~v3_pre_topc(X1,X0) | ~r1_tarski(X1,X2) | r1_tarski(X1,k1_tops_1(X0,X2))) )),
% 0.20/0.53    inference(cnf_transformation,[],[f12])).
% 0.20/0.53  fof(f12,plain,(
% 0.20/0.53    ! [X0] : (! [X1] : (! [X2] : (r1_tarski(X1,k1_tops_1(X0,X2)) | ~r1_tarski(X1,X2) | ~v3_pre_topc(X1,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.20/0.53    inference(flattening,[],[f11])).
% 0.20/0.53  fof(f11,plain,(
% 0.20/0.53    ! [X0] : (! [X1] : (! [X2] : ((r1_tarski(X1,k1_tops_1(X0,X2)) | (~r1_tarski(X1,X2) | ~v3_pre_topc(X1,X0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.20/0.53    inference(ennf_transformation,[],[f5])).
% 0.20/0.53  fof(f5,axiom,(
% 0.20/0.53    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((r1_tarski(X1,X2) & v3_pre_topc(X1,X0)) => r1_tarski(X1,k1_tops_1(X0,X2))))))),
% 0.20/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t56_tops_1)).
% 0.20/0.53  fof(f116,plain,(
% 0.20/0.53    v3_pre_topc(sK1,sK0) | sK1 = k1_tops_1(sK0,sK1)),
% 0.20/0.53    inference(resolution,[],[f115,f51])).
% 0.20/0.53  fof(f115,plain,(
% 0.20/0.53    r1_tarski(sK1,k1_tops_1(sK0,sK1)) | v3_pre_topc(sK1,sK0)),
% 0.20/0.53    inference(duplicate_literal_removal,[],[f113])).
% 0.20/0.53  fof(f113,plain,(
% 0.20/0.53    v3_pre_topc(sK1,sK0) | r1_tarski(sK1,k1_tops_1(sK0,sK1)) | r1_tarski(sK1,k1_tops_1(sK0,sK1))),
% 0.20/0.53    inference(resolution,[],[f111,f38])).
% 0.20/0.53  fof(f38,plain,(
% 0.20/0.53    ( ! [X0,X1] : (~r2_hidden(sK5(X0,X1),X1) | r1_tarski(X0,X1)) )),
% 0.20/0.53    inference(cnf_transformation,[],[f15])).
% 0.20/0.53  fof(f15,plain,(
% 0.20/0.53    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 0.20/0.53    inference(ennf_transformation,[],[f1])).
% 0.20/0.53  fof(f1,axiom,(
% 0.20/0.53    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 0.20/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).
% 0.20/0.53  fof(f111,plain,(
% 0.20/0.53    ( ! [X0] : (r2_hidden(sK5(sK1,X0),k1_tops_1(sK0,sK1)) | v3_pre_topc(sK1,sK0) | r1_tarski(sK1,X0)) )),
% 0.20/0.53    inference(subsumption_resolution,[],[f110,f37])).
% 0.20/0.53  fof(f37,plain,(
% 0.20/0.53    ( ! [X0,X1] : (r2_hidden(sK5(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 0.20/0.53    inference(cnf_transformation,[],[f15])).
% 0.20/0.53  fof(f110,plain,(
% 0.20/0.53    ( ! [X0] : (~r2_hidden(sK5(sK1,X0),sK1) | v3_pre_topc(sK1,sK0) | r2_hidden(sK5(sK1,X0),k1_tops_1(sK0,sK1)) | r1_tarski(sK1,X0)) )),
% 0.20/0.53    inference(duplicate_literal_removal,[],[f104])).
% 0.20/0.53  % (22251)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.20/0.53  fof(f104,plain,(
% 0.20/0.53    ( ! [X0] : (~r2_hidden(sK5(sK1,X0),sK1) | v3_pre_topc(sK1,sK0) | r2_hidden(sK5(sK1,X0),k1_tops_1(sK0,sK1)) | v3_pre_topc(sK1,sK0) | r1_tarski(sK1,X0)) )),
% 0.20/0.53    inference(resolution,[],[f103,f47])).
% 0.20/0.53  fof(f47,plain,(
% 0.20/0.53    ( ! [X0,X1] : (~r1_tarski(sK4(sK5(sK1,X0)),X1) | r2_hidden(sK5(sK1,X0),X1) | v3_pre_topc(sK1,sK0) | r1_tarski(sK1,X0)) )),
% 0.20/0.53    inference(resolution,[],[f45,f37])).
% 0.20/0.53  fof(f45,plain,(
% 0.20/0.53    ( ! [X0,X1] : (~r2_hidden(X0,sK1) | ~r1_tarski(sK4(X0),X1) | r2_hidden(X0,X1) | v3_pre_topc(sK1,sK0)) )),
% 0.20/0.53    inference(resolution,[],[f36,f19])).
% 0.20/0.53  fof(f19,plain,(
% 0.20/0.53    ( ! [X2] : (r2_hidden(X2,sK4(X2)) | ~r2_hidden(X2,sK1) | v3_pre_topc(sK1,sK0)) )),
% 0.20/0.53    inference(cnf_transformation,[],[f9])).
% 0.20/0.53  fof(f36,plain,(
% 0.20/0.53    ( ! [X2,X0,X1] : (~r2_hidden(X2,X0) | r2_hidden(X2,X1) | ~r1_tarski(X0,X1)) )),
% 0.20/0.53    inference(cnf_transformation,[],[f15])).
% 0.20/0.53  fof(f103,plain,(
% 0.20/0.53    ( ! [X0] : (r1_tarski(sK4(X0),k1_tops_1(sK0,sK1)) | ~r2_hidden(X0,sK1) | v3_pre_topc(sK1,sK0)) )),
% 0.20/0.53    inference(subsumption_resolution,[],[f100,f18])).
% 0.20/0.53  fof(f18,plain,(
% 0.20/0.53    ( ! [X2] : (r1_tarski(sK4(X2),sK1) | ~r2_hidden(X2,sK1) | v3_pre_topc(sK1,sK0)) )),
% 0.20/0.53    inference(cnf_transformation,[],[f9])).
% 0.20/0.53  fof(f100,plain,(
% 0.20/0.53    ( ! [X0] : (~r1_tarski(sK4(X0),sK1) | r1_tarski(sK4(X0),k1_tops_1(sK0,sK1)) | ~r2_hidden(X0,sK1) | v3_pre_topc(sK1,sK0)) )),
% 0.20/0.53    inference(resolution,[],[f99,f26])).
% 0.20/0.53  fof(f99,plain,(
% 0.20/0.53    ( ! [X2,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | ~r1_tarski(sK4(X2),X1) | r1_tarski(sK4(X2),k1_tops_1(sK0,X1)) | ~r2_hidden(X2,sK1) | v3_pre_topc(sK1,sK0)) )),
% 0.20/0.53    inference(subsumption_resolution,[],[f97,f16])).
% 0.20/0.53  fof(f16,plain,(
% 0.20/0.53    ( ! [X2] : (m1_subset_1(sK4(X2),k1_zfmisc_1(u1_struct_0(sK0))) | ~r2_hidden(X2,sK1) | v3_pre_topc(sK1,sK0)) )),
% 0.20/0.53    inference(cnf_transformation,[],[f9])).
% 0.20/0.53  fof(f97,plain,(
% 0.20/0.53    ( ! [X2,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(sK4(X2),k1_zfmisc_1(u1_struct_0(sK0))) | ~r1_tarski(sK4(X2),X1) | r1_tarski(sK4(X2),k1_tops_1(sK0,X1)) | ~r2_hidden(X2,sK1) | v3_pre_topc(sK1,sK0)) )),
% 0.20/0.53    inference(resolution,[],[f83,f17])).
% 0.20/0.53  fof(f17,plain,(
% 0.20/0.53    ( ! [X2] : (v3_pre_topc(sK4(X2),sK0) | ~r2_hidden(X2,sK1) | v3_pre_topc(sK1,sK0)) )),
% 0.20/0.53    inference(cnf_transformation,[],[f9])).
% 0.20/0.53  fof(f31,plain,(
% 0.20/0.53    ( ! [X2,X0,X3,X1] : (k1_tops_1(X0,X2) != X2 | ~l1_pre_topc(X0) | ~l1_pre_topc(X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) | ~v2_pre_topc(X0) | v3_pre_topc(X2,X0)) )),
% 0.20/0.53    inference(cnf_transformation,[],[f14])).
% 0.20/0.53  fof(f14,plain,(
% 0.20/0.53    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((v3_pre_topc(X2,X0) | k1_tops_1(X0,X2) != X2) & (k1_tops_1(X1,X3) = X3 | ~v3_pre_topc(X3,X1))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.20/0.53    inference(flattening,[],[f13])).
% 0.20/0.53  fof(f13,plain,(
% 0.20/0.53    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((v3_pre_topc(X2,X0) | k1_tops_1(X0,X2) != X2) & (k1_tops_1(X1,X3) = X3 | ~v3_pre_topc(X3,X1))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X1)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 0.20/0.53    inference(ennf_transformation,[],[f4])).
% 0.20/0.53  fof(f4,axiom,(
% 0.20/0.53    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (l1_pre_topc(X1) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) => ((k1_tops_1(X0,X2) = X2 => v3_pre_topc(X2,X0)) & (v3_pre_topc(X3,X1) => k1_tops_1(X1,X3) = X3))))))),
% 0.20/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_tops_1)).
% 0.20/0.53  fof(f207,plain,(
% 0.20/0.53    ( ! [X1] : (~v3_pre_topc(X1,sK0) | ~r1_tarski(X1,sK1) | ~r2_hidden(sK2,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) )),
% 0.20/0.53    inference(subsumption_resolution,[],[f201,f36])).
% 0.20/0.53  fof(f201,plain,(
% 0.20/0.53    ( ! [X1] : (~v3_pre_topc(X1,sK0) | ~r1_tarski(X1,sK1) | ~r2_hidden(sK2,X1) | ~r2_hidden(sK2,sK1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) )),
% 0.20/0.53    inference(resolution,[],[f197,f21])).
% 0.20/0.53  fof(f21,plain,(
% 0.20/0.53    ( ! [X3] : (~v3_pre_topc(sK1,sK0) | ~v3_pre_topc(X3,sK0) | ~r1_tarski(X3,sK1) | ~r2_hidden(sK2,X3) | ~r2_hidden(sK2,sK1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))) )),
% 0.20/0.53    inference(cnf_transformation,[],[f9])).
% 0.20/0.53  fof(f233,plain,(
% 0.20/0.53    r2_hidden(sK2,sK1)),
% 0.20/0.53    inference(duplicate_literal_removal,[],[f230])).
% 0.20/0.53  fof(f230,plain,(
% 0.20/0.53    r2_hidden(sK2,sK1) | r2_hidden(sK2,sK1)),
% 0.20/0.53    inference(resolution,[],[f229,f211])).
% 0.20/0.53  fof(f211,plain,(
% 0.20/0.53    ( ! [X0] : (~r1_tarski(sK3,X0) | r2_hidden(sK2,X0) | r2_hidden(sK2,sK1)) )),
% 0.20/0.53    inference(resolution,[],[f203,f36])).
% 0.20/0.53  fof(f203,plain,(
% 0.20/0.53    r2_hidden(sK2,sK3) | r2_hidden(sK2,sK1)),
% 0.20/0.53    inference(resolution,[],[f197,f25])).
% 0.20/0.53  fof(f25,plain,(
% 0.20/0.53    ~v3_pre_topc(sK1,sK0) | r2_hidden(sK2,sK1) | r2_hidden(sK2,sK3)),
% 0.20/0.53    inference(cnf_transformation,[],[f9])).
% 0.20/0.53  fof(f229,plain,(
% 0.20/0.53    r1_tarski(sK3,sK1)),
% 0.20/0.53    inference(resolution,[],[f228,f204])).
% 0.20/0.53  fof(f204,plain,(
% 0.20/0.53    r2_hidden(sK2,sK1) | r1_tarski(sK3,sK1)),
% 0.20/0.53    inference(resolution,[],[f197,f24])).
% 0.20/0.53  fof(f24,plain,(
% 0.20/0.53    ~v3_pre_topc(sK1,sK0) | r2_hidden(sK2,sK1) | r1_tarski(sK3,sK1)),
% 0.20/0.53    inference(cnf_transformation,[],[f9])).
% 0.20/0.53  % SZS output end Proof for theBenchmark
% 0.20/0.53  % (22254)------------------------------
% 0.20/0.53  % (22254)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.53  % (22254)Termination reason: Refutation
% 0.20/0.53  
% 0.20/0.53  % (22254)Memory used [KB]: 6396
% 0.20/0.53  % (22254)Time elapsed: 0.087 s
% 0.20/0.53  % (22254)------------------------------
% 0.20/0.53  % (22254)------------------------------
% 0.20/0.53  % (22268)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.20/0.53  % (22271)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.20/0.54  % (22244)Success in time 0.178 s
%------------------------------------------------------------------------------
