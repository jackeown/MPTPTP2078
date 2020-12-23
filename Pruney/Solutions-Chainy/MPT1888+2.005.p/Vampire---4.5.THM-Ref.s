%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:22:09 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  106 ( 806 expanded)
%              Number of leaves         :   13 ( 151 expanded)
%              Depth                    :   27
%              Number of atoms          :  336 (3664 expanded)
%              Number of equality atoms :   33 ( 387 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f472,plain,(
    $false ),
    inference(subsumption_resolution,[],[f471,f133])).

fof(f133,plain,(
    ~ r2_hidden(sK2,k2_pre_topc(sK0,k1_tarski(sK1))) ),
    inference(forward_demodulation,[],[f132,f96])).

fof(f96,plain,(
    k6_domain_1(u1_struct_0(sK0),sK1) = k1_tarski(sK1) ),
    inference(subsumption_resolution,[],[f90,f75])).

fof(f75,plain,(
    ~ v1_xboole_0(u1_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f74,f42])).

fof(f42,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2)) != k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X1))
              & ~ r1_xboole_0(k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X1)),k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2)))
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_pre_topc(X0)
      & v3_tdlat_3(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2)) != k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X1))
              & ~ r1_xboole_0(k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X1)),k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2)))
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_pre_topc(X0)
      & v3_tdlat_3(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v3_tdlat_3(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => ( k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2)) = k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X1))
                  | r1_xboole_0(k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X1)),k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2))) ) ) ) ) ),
    inference(negated_conjecture,[],[f14])).

fof(f14,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v3_tdlat_3(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2)) = k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X1))
                | r1_xboole_0(k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X1)),k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2))) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t56_tex_2)).

fof(f74,plain,
    ( v2_struct_0(sK0)
    | ~ v1_xboole_0(u1_struct_0(sK0)) ),
    inference(resolution,[],[f73,f61])).

fof(f61,plain,(
    ! [X0] :
      ( ~ l1_struct_0(X0)
      | v2_struct_0(X0)
      | ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_struct_0)).

fof(f73,plain,(
    l1_struct_0(sK0) ),
    inference(resolution,[],[f45,f67])).

fof(f67,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(f45,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f18])).

fof(f90,plain,
    ( v1_xboole_0(u1_struct_0(sK0))
    | k6_domain_1(u1_struct_0(sK0),sK1) = k1_tarski(sK1) ),
    inference(resolution,[],[f41,f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0)
      | k6_domain_1(X0,X1) = k1_tarski(X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( k6_domain_1(X0,X1) = k1_tarski(X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( k6_domain_1(X0,X1) = k1_tarski(X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,X0)
        & ~ v1_xboole_0(X0) )
     => k6_domain_1(X0,X1) = k1_tarski(X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

fof(f41,plain,(
    m1_subset_1(sK1,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f18])).

fof(f132,plain,(
    ~ r2_hidden(sK2,k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK1))) ),
    inference(subsumption_resolution,[],[f131,f98])).

fof(f98,plain,(
    k2_pre_topc(sK0,k1_tarski(sK2)) != k2_pre_topc(sK0,k1_tarski(sK1)) ),
    inference(backward_demodulation,[],[f87,f96])).

fof(f87,plain,(
    k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK1)) != k2_pre_topc(sK0,k1_tarski(sK2)) ),
    inference(backward_demodulation,[],[f40,f84])).

fof(f84,plain,(
    k6_domain_1(u1_struct_0(sK0),sK2) = k1_tarski(sK2) ),
    inference(subsumption_resolution,[],[f78,f75])).

fof(f78,plain,
    ( v1_xboole_0(u1_struct_0(sK0))
    | k6_domain_1(u1_struct_0(sK0),sK2) = k1_tarski(sK2) ),
    inference(resolution,[],[f38,f50])).

fof(f38,plain,(
    m1_subset_1(sK2,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f18])).

fof(f40,plain,(
    k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK1)) != k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK2)) ),
    inference(cnf_transformation,[],[f18])).

fof(f131,plain,
    ( k2_pre_topc(sK0,k1_tarski(sK2)) = k2_pre_topc(sK0,k1_tarski(sK1))
    | ~ r2_hidden(sK2,k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK1))) ),
    inference(forward_demodulation,[],[f130,f96])).

fof(f130,plain,
    ( k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK1)) = k2_pre_topc(sK0,k1_tarski(sK2))
    | ~ r2_hidden(sK2,k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK1))) ),
    inference(resolution,[],[f85,f41])).

fof(f85,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK0))
      | k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X0)) = k2_pre_topc(sK0,k1_tarski(sK2))
      | ~ r2_hidden(sK2,k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X0))) ) ),
    inference(backward_demodulation,[],[f82,f84])).

fof(f82,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ r2_hidden(sK2,k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X0)))
      | k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK2)) = k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X0)) ) ),
    inference(subsumption_resolution,[],[f81,f42])).

fof(f81,plain,(
    ! [X0] :
      ( v2_struct_0(sK0)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ r2_hidden(sK2,k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X0)))
      | k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK2)) = k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X0)) ) ),
    inference(subsumption_resolution,[],[f80,f45])).

fof(f80,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(sK0)
      | v2_struct_0(sK0)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ r2_hidden(sK2,k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X0)))
      | k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK2)) = k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X0)) ) ),
    inference(subsumption_resolution,[],[f79,f44])).

fof(f44,plain,(
    v3_tdlat_3(sK0) ),
    inference(cnf_transformation,[],[f18])).

fof(f79,plain,(
    ! [X0] :
      ( ~ v3_tdlat_3(sK0)
      | ~ l1_pre_topc(sK0)
      | v2_struct_0(sK0)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ r2_hidden(sK2,k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X0)))
      | k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK2)) = k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X0)) ) ),
    inference(subsumption_resolution,[],[f76,f43])).

fof(f43,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f18])).

fof(f76,plain,(
    ! [X0] :
      ( ~ v2_pre_topc(sK0)
      | ~ v3_tdlat_3(sK0)
      | ~ l1_pre_topc(sK0)
      | v2_struct_0(sK0)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ r2_hidden(sK2,k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X0)))
      | k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK2)) = k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X0)) ) ),
    inference(resolution,[],[f38,f51])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ v2_pre_topc(X0)
      | ~ v3_tdlat_3(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ r2_hidden(X1,k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2)))
      | k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2)) = k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X1)) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2)) = k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X1))
              | ~ r2_hidden(X1,k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2)))
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v3_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2)) = k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X1))
              | ~ r2_hidden(X1,k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2)))
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v3_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v3_tdlat_3(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( r2_hidden(X1,k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2)))
               => k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2)) = k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X1)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_tex_2)).

fof(f471,plain,(
    r2_hidden(sK2,k2_pre_topc(sK0,k1_tarski(sK1))) ),
    inference(backward_demodulation,[],[f461,f467])).

fof(f467,plain,(
    sK2 = sK4(k2_pre_topc(sK0,k1_tarski(sK1)),k1_tarski(sK2)) ),
    inference(resolution,[],[f462,f68])).

fof(f68,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,k1_tarski(X0))
      | X0 = X2 ) ),
    inference(equality_resolution,[],[f47])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( X0 = X2
      | ~ r2_hidden(X2,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).

fof(f462,plain,(
    r2_hidden(sK4(k2_pre_topc(sK0,k1_tarski(sK1)),k1_tarski(sK2)),k1_tarski(sK2)) ),
    inference(resolution,[],[f460,f54])).

fof(f54,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | r2_hidden(sK4(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X3] :
              ~ ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X2] :
              ~ ( r2_hidden(X2,X1)
                & r2_hidden(X2,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_0)).

fof(f460,plain,(
    ~ r1_xboole_0(k2_pre_topc(sK0,k1_tarski(sK1)),k1_tarski(sK2)) ),
    inference(subsumption_resolution,[],[f446,f99])).

fof(f99,plain,(
    ~ r1_xboole_0(k2_pre_topc(sK0,k1_tarski(sK1)),k2_pre_topc(sK0,k1_tarski(sK2))) ),
    inference(backward_demodulation,[],[f86,f96])).

fof(f86,plain,(
    ~ r1_xboole_0(k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK1)),k2_pre_topc(sK0,k1_tarski(sK2))) ),
    inference(backward_demodulation,[],[f39,f84])).

fof(f39,plain,(
    ~ r1_xboole_0(k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK1)),k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK2))) ),
    inference(cnf_transformation,[],[f18])).

fof(f446,plain,
    ( ~ r1_xboole_0(k2_pre_topc(sK0,k1_tarski(sK1)),k1_tarski(sK2))
    | r1_xboole_0(k2_pre_topc(sK0,k1_tarski(sK1)),k2_pre_topc(sK0,k1_tarski(sK2))) ),
    inference(resolution,[],[f157,f101])).

fof(f101,plain,(
    m1_subset_1(k1_tarski(sK2),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(resolution,[],[f83,f63])).

fof(f63,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_subset_1)).

fof(f83,plain,(
    r2_hidden(sK2,u1_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f77,f75])).

fof(f77,plain,
    ( v1_xboole_0(u1_struct_0(sK0))
    | r2_hidden(sK2,u1_struct_0(sK0)) ),
    inference(resolution,[],[f38,f62])).

fof(f62,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,X1)
      | v1_xboole_0(X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

fof(f157,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r1_xboole_0(k2_pre_topc(sK0,k1_tarski(sK1)),X0)
      | r1_xboole_0(k2_pre_topc(sK0,k1_tarski(sK1)),k2_pre_topc(sK0,X0)) ) ),
    inference(subsumption_resolution,[],[f156,f43])).

fof(f156,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r1_xboole_0(k2_pre_topc(sK0,k1_tarski(sK1)),X0)
      | ~ v2_pre_topc(sK0)
      | r1_xboole_0(k2_pre_topc(sK0,k1_tarski(sK1)),k2_pre_topc(sK0,X0)) ) ),
    inference(subsumption_resolution,[],[f155,f119])).

fof(f119,plain,(
    m1_subset_1(k2_pre_topc(sK0,k1_tarski(sK1)),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(subsumption_resolution,[],[f114,f45])).

fof(f114,plain,
    ( ~ l1_pre_topc(sK0)
    | m1_subset_1(k2_pre_topc(sK0,k1_tarski(sK1)),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(resolution,[],[f103,f56])).

fof(f56,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_pre_topc)).

fof(f103,plain,(
    m1_subset_1(k1_tarski(sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(resolution,[],[f95,f63])).

fof(f95,plain,(
    r2_hidden(sK1,u1_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f89,f75])).

fof(f89,plain,
    ( v1_xboole_0(u1_struct_0(sK0))
    | r2_hidden(sK1,u1_struct_0(sK0)) ),
    inference(resolution,[],[f41,f62])).

fof(f155,plain,(
    ! [X0] :
      ( ~ m1_subset_1(k2_pre_topc(sK0,k1_tarski(sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r1_xboole_0(k2_pre_topc(sK0,k1_tarski(sK1)),X0)
      | ~ v2_pre_topc(sK0)
      | r1_xboole_0(k2_pre_topc(sK0,k1_tarski(sK1)),k2_pre_topc(sK0,X0)) ) ),
    inference(subsumption_resolution,[],[f154,f45])).

fof(f154,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(sK0)
      | ~ m1_subset_1(k2_pre_topc(sK0,k1_tarski(sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r1_xboole_0(k2_pre_topc(sK0,k1_tarski(sK1)),X0)
      | ~ v2_pre_topc(sK0)
      | r1_xboole_0(k2_pre_topc(sK0,k1_tarski(sK1)),k2_pre_topc(sK0,X0)) ) ),
    inference(resolution,[],[f145,f55])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( ~ v3_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ r1_xboole_0(X1,X2)
      | ~ v2_pre_topc(X0)
      | r1_xboole_0(X1,k2_pre_topc(X0,X2)) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_xboole_0(X1,k2_pre_topc(X0,X2))
              | ~ v3_pre_topc(X1,X0)
              | ~ r1_xboole_0(X1,X2)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_xboole_0(X1,k2_pre_topc(X0,X2))
              | ~ v3_pre_topc(X1,X0)
              | ~ r1_xboole_0(X1,X2)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( ( v3_pre_topc(X1,X0)
                  & r1_xboole_0(X1,X2) )
               => r1_xboole_0(X1,k2_pre_topc(X0,X2)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t40_tsep_1)).

fof(f145,plain,(
    v3_pre_topc(k2_pre_topc(sK0,k1_tarski(sK1)),sK0) ),
    inference(subsumption_resolution,[],[f144,f44])).

fof(f144,plain,
    ( v3_pre_topc(k2_pre_topc(sK0,k1_tarski(sK1)),sK0)
    | ~ v3_tdlat_3(sK0) ),
    inference(subsumption_resolution,[],[f143,f43])).

fof(f143,plain,
    ( ~ v2_pre_topc(sK0)
    | v3_pre_topc(k2_pre_topc(sK0,k1_tarski(sK1)),sK0)
    | ~ v3_tdlat_3(sK0) ),
    inference(subsumption_resolution,[],[f142,f119])).

fof(f142,plain,
    ( ~ m1_subset_1(k2_pre_topc(sK0,k1_tarski(sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v2_pre_topc(sK0)
    | v3_pre_topc(k2_pre_topc(sK0,k1_tarski(sK1)),sK0)
    | ~ v3_tdlat_3(sK0) ),
    inference(subsumption_resolution,[],[f141,f45])).

fof(f141,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ m1_subset_1(k2_pre_topc(sK0,k1_tarski(sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v2_pre_topc(sK0)
    | v3_pre_topc(k2_pre_topc(sK0,k1_tarski(sK1)),sK0)
    | ~ v3_tdlat_3(sK0) ),
    inference(resolution,[],[f118,f57])).

fof(f57,plain,(
    ! [X0,X1] :
      ( ~ v4_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v2_pre_topc(X0)
      | v3_pre_topc(X1,X0)
      | ~ v3_tdlat_3(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ( v3_tdlat_3(X0)
      <=> ! [X1] :
            ( v3_pre_topc(X1,X0)
            | ~ v4_pre_topc(X1,X0)
            | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ( v3_tdlat_3(X0)
      <=> ! [X1] :
            ( v3_pre_topc(X1,X0)
            | ~ v4_pre_topc(X1,X0)
            | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ( v3_tdlat_3(X0)
      <=> ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( v4_pre_topc(X1,X0)
             => v3_pre_topc(X1,X0) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t24_tdlat_3)).

fof(f118,plain,(
    v4_pre_topc(k2_pre_topc(sK0,k1_tarski(sK1)),sK0) ),
    inference(subsumption_resolution,[],[f117,f43])).

fof(f117,plain,
    ( ~ v2_pre_topc(sK0)
    | v4_pre_topc(k2_pre_topc(sK0,k1_tarski(sK1)),sK0) ),
    inference(subsumption_resolution,[],[f113,f45])).

fof(f113,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v4_pre_topc(k2_pre_topc(sK0,k1_tarski(sK1)),sK0) ),
    inference(resolution,[],[f103,f66])).

fof(f66,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v4_pre_topc(k2_pre_topc(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( v4_pre_topc(k2_pre_topc(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( v4_pre_topc(k2_pre_topc(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => v4_pre_topc(k2_pre_topc(X0,X1),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_tops_1)).

fof(f461,plain,(
    r2_hidden(sK4(k2_pre_topc(sK0,k1_tarski(sK1)),k1_tarski(sK2)),k2_pre_topc(sK0,k1_tarski(sK1))) ),
    inference(resolution,[],[f460,f53])).

fof(f53,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | r2_hidden(sK4(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f23])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 20:53:39 EST 2020
% 0.20/0.34  % CPUTime    : 
% 0.22/0.49  % (12104)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 0.22/0.50  % (12120)dis+2_128_add=large:afp=100000:afq=1.4:amm=sco:anc=none:lma=on:nm=2:newcnf=on:nwc=1:nicw=on:sas=z3:sos=theory:sac=on:updr=off_288 on theBenchmark
% 0.22/0.50  % (12118)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 0.22/0.50  % (12102)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 0.22/0.51  % (12098)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.22/0.51  % (12110)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.22/0.51  % (12102)Refutation not found, incomplete strategy% (12102)------------------------------
% 0.22/0.51  % (12102)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.51  % (12102)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.51  
% 0.22/0.51  % (12102)Memory used [KB]: 10618
% 0.22/0.51  % (12102)Time elapsed: 0.037 s
% 0.22/0.51  % (12102)------------------------------
% 0.22/0.51  % (12102)------------------------------
% 0.22/0.51  % (12101)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.22/0.51  % (12113)lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_145 on theBenchmark
% 0.22/0.52  % (12107)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 0.22/0.52  % (12109)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 0.22/0.52  % (12097)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 0.22/0.52  % (12097)Refutation not found, incomplete strategy% (12097)------------------------------
% 0.22/0.52  % (12097)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.52  % (12097)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.52  
% 0.22/0.52  % (12097)Memory used [KB]: 10618
% 0.22/0.52  % (12097)Time elapsed: 0.096 s
% 0.22/0.52  % (12097)------------------------------
% 0.22/0.52  % (12097)------------------------------
% 0.22/0.52  % (12096)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 0.22/0.52  % (12099)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.22/0.53  % (12114)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 0.22/0.53  % (12105)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
% 0.22/0.53  % (12117)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 0.22/0.53  % (12119)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 0.22/0.53  % (12108)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 0.22/0.54  % (12115)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 0.22/0.54  % (12101)Refutation found. Thanks to Tanya!
% 0.22/0.54  % SZS status Theorem for theBenchmark
% 0.22/0.54  % SZS output start Proof for theBenchmark
% 0.22/0.54  fof(f472,plain,(
% 0.22/0.54    $false),
% 0.22/0.54    inference(subsumption_resolution,[],[f471,f133])).
% 0.22/0.54  fof(f133,plain,(
% 0.22/0.54    ~r2_hidden(sK2,k2_pre_topc(sK0,k1_tarski(sK1)))),
% 0.22/0.54    inference(forward_demodulation,[],[f132,f96])).
% 0.22/0.54  fof(f96,plain,(
% 0.22/0.54    k6_domain_1(u1_struct_0(sK0),sK1) = k1_tarski(sK1)),
% 0.22/0.54    inference(subsumption_resolution,[],[f90,f75])).
% 0.22/0.54  fof(f75,plain,(
% 0.22/0.54    ~v1_xboole_0(u1_struct_0(sK0))),
% 0.22/0.54    inference(subsumption_resolution,[],[f74,f42])).
% 0.22/0.54  fof(f42,plain,(
% 0.22/0.54    ~v2_struct_0(sK0)),
% 0.22/0.54    inference(cnf_transformation,[],[f18])).
% 0.22/0.54  fof(f18,plain,(
% 0.22/0.54    ? [X0] : (? [X1] : (? [X2] : (k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2)) != k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X1)) & ~r1_xboole_0(k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X1)),k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2))) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_pre_topc(X0) & v3_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.22/0.54    inference(flattening,[],[f17])).
% 0.22/0.54  fof(f17,plain,(
% 0.22/0.54    ? [X0] : (? [X1] : (? [X2] : ((k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2)) != k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X1)) & ~r1_xboole_0(k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X1)),k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2)))) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) & (l1_pre_topc(X0) & v3_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 0.22/0.54    inference(ennf_transformation,[],[f15])).
% 0.22/0.54  fof(f15,negated_conjecture,(
% 0.22/0.54    ~! [X0] : ((l1_pre_topc(X0) & v3_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2)) = k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X1)) | r1_xboole_0(k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X1)),k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2)))))))),
% 0.22/0.54    inference(negated_conjecture,[],[f14])).
% 0.22/0.54  fof(f14,conjecture,(
% 0.22/0.54    ! [X0] : ((l1_pre_topc(X0) & v3_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2)) = k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X1)) | r1_xboole_0(k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X1)),k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2)))))))),
% 0.22/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t56_tex_2)).
% 0.22/0.54  fof(f74,plain,(
% 0.22/0.54    v2_struct_0(sK0) | ~v1_xboole_0(u1_struct_0(sK0))),
% 0.22/0.54    inference(resolution,[],[f73,f61])).
% 0.22/0.54  fof(f61,plain,(
% 0.22/0.54    ( ! [X0] : (~l1_struct_0(X0) | v2_struct_0(X0) | ~v1_xboole_0(u1_struct_0(X0))) )),
% 0.22/0.54    inference(cnf_transformation,[],[f31])).
% 0.22/0.54  fof(f31,plain,(
% 0.22/0.54    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 0.22/0.54    inference(flattening,[],[f30])).
% 0.22/0.54  fof(f30,plain,(
% 0.22/0.54    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 0.22/0.54    inference(ennf_transformation,[],[f8])).
% 0.22/0.54  fof(f8,axiom,(
% 0.22/0.54    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ~v1_xboole_0(u1_struct_0(X0)))),
% 0.22/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_struct_0)).
% 0.22/0.54  fof(f73,plain,(
% 0.22/0.54    l1_struct_0(sK0)),
% 0.22/0.54    inference(resolution,[],[f45,f67])).
% 0.22/0.54  fof(f67,plain,(
% 0.22/0.54    ( ! [X0] : (~l1_pre_topc(X0) | l1_struct_0(X0)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f37])).
% 0.22/0.54  fof(f37,plain,(
% 0.22/0.54    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 0.22/0.54    inference(ennf_transformation,[],[f7])).
% 0.22/0.54  fof(f7,axiom,(
% 0.22/0.54    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 0.22/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).
% 0.22/0.54  fof(f45,plain,(
% 0.22/0.54    l1_pre_topc(sK0)),
% 0.22/0.54    inference(cnf_transformation,[],[f18])).
% 0.22/0.54  fof(f90,plain,(
% 0.22/0.54    v1_xboole_0(u1_struct_0(sK0)) | k6_domain_1(u1_struct_0(sK0),sK1) = k1_tarski(sK1)),
% 0.22/0.54    inference(resolution,[],[f41,f50])).
% 0.22/0.54  fof(f50,plain,(
% 0.22/0.54    ( ! [X0,X1] : (~m1_subset_1(X1,X0) | v1_xboole_0(X0) | k6_domain_1(X0,X1) = k1_tarski(X1)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f20])).
% 0.22/0.54  fof(f20,plain,(
% 0.22/0.54    ! [X0,X1] : (k6_domain_1(X0,X1) = k1_tarski(X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0))),
% 0.22/0.54    inference(flattening,[],[f19])).
% 0.22/0.54  fof(f19,plain,(
% 0.22/0.54    ! [X0,X1] : (k6_domain_1(X0,X1) = k1_tarski(X1) | (~m1_subset_1(X1,X0) | v1_xboole_0(X0)))),
% 0.22/0.54    inference(ennf_transformation,[],[f9])).
% 0.22/0.54  fof(f9,axiom,(
% 0.22/0.54    ! [X0,X1] : ((m1_subset_1(X1,X0) & ~v1_xboole_0(X0)) => k6_domain_1(X0,X1) = k1_tarski(X1))),
% 0.22/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_domain_1)).
% 0.22/0.54  fof(f41,plain,(
% 0.22/0.54    m1_subset_1(sK1,u1_struct_0(sK0))),
% 0.22/0.54    inference(cnf_transformation,[],[f18])).
% 0.22/0.54  fof(f132,plain,(
% 0.22/0.54    ~r2_hidden(sK2,k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK1)))),
% 0.22/0.54    inference(subsumption_resolution,[],[f131,f98])).
% 0.22/0.54  fof(f98,plain,(
% 0.22/0.54    k2_pre_topc(sK0,k1_tarski(sK2)) != k2_pre_topc(sK0,k1_tarski(sK1))),
% 0.22/0.54    inference(backward_demodulation,[],[f87,f96])).
% 0.22/0.54  fof(f87,plain,(
% 0.22/0.54    k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK1)) != k2_pre_topc(sK0,k1_tarski(sK2))),
% 0.22/0.54    inference(backward_demodulation,[],[f40,f84])).
% 0.22/0.54  fof(f84,plain,(
% 0.22/0.54    k6_domain_1(u1_struct_0(sK0),sK2) = k1_tarski(sK2)),
% 0.22/0.54    inference(subsumption_resolution,[],[f78,f75])).
% 0.22/0.54  fof(f78,plain,(
% 0.22/0.54    v1_xboole_0(u1_struct_0(sK0)) | k6_domain_1(u1_struct_0(sK0),sK2) = k1_tarski(sK2)),
% 0.22/0.54    inference(resolution,[],[f38,f50])).
% 0.22/0.54  fof(f38,plain,(
% 0.22/0.54    m1_subset_1(sK2,u1_struct_0(sK0))),
% 0.22/0.54    inference(cnf_transformation,[],[f18])).
% 0.22/0.54  fof(f40,plain,(
% 0.22/0.54    k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK1)) != k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK2))),
% 0.22/0.54    inference(cnf_transformation,[],[f18])).
% 0.22/0.54  fof(f131,plain,(
% 0.22/0.54    k2_pre_topc(sK0,k1_tarski(sK2)) = k2_pre_topc(sK0,k1_tarski(sK1)) | ~r2_hidden(sK2,k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK1)))),
% 0.22/0.54    inference(forward_demodulation,[],[f130,f96])).
% 0.22/0.54  fof(f130,plain,(
% 0.22/0.54    k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK1)) = k2_pre_topc(sK0,k1_tarski(sK2)) | ~r2_hidden(sK2,k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK1)))),
% 0.22/0.54    inference(resolution,[],[f85,f41])).
% 0.22/0.54  fof(f85,plain,(
% 0.22/0.54    ( ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK0)) | k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X0)) = k2_pre_topc(sK0,k1_tarski(sK2)) | ~r2_hidden(sK2,k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X0)))) )),
% 0.22/0.54    inference(backward_demodulation,[],[f82,f84])).
% 0.22/0.54  fof(f82,plain,(
% 0.22/0.54    ( ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK0)) | ~r2_hidden(sK2,k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X0))) | k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK2)) = k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X0))) )),
% 0.22/0.54    inference(subsumption_resolution,[],[f81,f42])).
% 0.22/0.54  fof(f81,plain,(
% 0.22/0.54    ( ! [X0] : (v2_struct_0(sK0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~r2_hidden(sK2,k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X0))) | k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK2)) = k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X0))) )),
% 0.22/0.54    inference(subsumption_resolution,[],[f80,f45])).
% 0.22/0.54  fof(f80,plain,(
% 0.22/0.54    ( ! [X0] : (~l1_pre_topc(sK0) | v2_struct_0(sK0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~r2_hidden(sK2,k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X0))) | k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK2)) = k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X0))) )),
% 0.22/0.54    inference(subsumption_resolution,[],[f79,f44])).
% 0.22/0.54  fof(f44,plain,(
% 0.22/0.54    v3_tdlat_3(sK0)),
% 0.22/0.54    inference(cnf_transformation,[],[f18])).
% 0.22/0.54  fof(f79,plain,(
% 0.22/0.54    ( ! [X0] : (~v3_tdlat_3(sK0) | ~l1_pre_topc(sK0) | v2_struct_0(sK0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~r2_hidden(sK2,k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X0))) | k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK2)) = k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X0))) )),
% 0.22/0.54    inference(subsumption_resolution,[],[f76,f43])).
% 0.22/0.54  fof(f43,plain,(
% 0.22/0.54    v2_pre_topc(sK0)),
% 0.22/0.54    inference(cnf_transformation,[],[f18])).
% 0.22/0.54  fof(f76,plain,(
% 0.22/0.54    ( ! [X0] : (~v2_pre_topc(sK0) | ~v3_tdlat_3(sK0) | ~l1_pre_topc(sK0) | v2_struct_0(sK0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~r2_hidden(sK2,k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X0))) | k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK2)) = k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X0))) )),
% 0.22/0.54    inference(resolution,[],[f38,f51])).
% 0.22/0.54  fof(f51,plain,(
% 0.22/0.54    ( ! [X2,X0,X1] : (~m1_subset_1(X1,u1_struct_0(X0)) | ~v2_pre_topc(X0) | ~v3_tdlat_3(X0) | ~l1_pre_topc(X0) | v2_struct_0(X0) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~r2_hidden(X1,k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2))) | k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2)) = k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X1))) )),
% 0.22/0.54    inference(cnf_transformation,[],[f22])).
% 0.22/0.54  fof(f22,plain,(
% 0.22/0.54    ! [X0] : (! [X1] : (! [X2] : (k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2)) = k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X1)) | ~r2_hidden(X1,k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v3_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.22/0.54    inference(flattening,[],[f21])).
% 0.22/0.54  fof(f21,plain,(
% 0.22/0.54    ! [X0] : (! [X1] : (! [X2] : ((k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2)) = k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X1)) | ~r2_hidden(X1,k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2)))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_pre_topc(X0) | ~v3_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.22/0.54    inference(ennf_transformation,[],[f13])).
% 0.22/0.54  fof(f13,axiom,(
% 0.22/0.54    ! [X0] : ((l1_pre_topc(X0) & v3_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r2_hidden(X1,k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2))) => k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2)) = k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X1))))))),
% 0.22/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_tex_2)).
% 0.22/0.54  fof(f471,plain,(
% 0.22/0.54    r2_hidden(sK2,k2_pre_topc(sK0,k1_tarski(sK1)))),
% 0.22/0.54    inference(backward_demodulation,[],[f461,f467])).
% 0.22/0.54  fof(f467,plain,(
% 0.22/0.54    sK2 = sK4(k2_pre_topc(sK0,k1_tarski(sK1)),k1_tarski(sK2))),
% 0.22/0.54    inference(resolution,[],[f462,f68])).
% 0.22/0.54  fof(f68,plain,(
% 0.22/0.54    ( ! [X2,X0] : (~r2_hidden(X2,k1_tarski(X0)) | X0 = X2) )),
% 0.22/0.54    inference(equality_resolution,[],[f47])).
% 0.22/0.54  fof(f47,plain,(
% 0.22/0.54    ( ! [X2,X0,X1] : (X0 = X2 | ~r2_hidden(X2,X1) | k1_tarski(X0) != X1) )),
% 0.22/0.54    inference(cnf_transformation,[],[f3])).
% 0.22/0.54  fof(f3,axiom,(
% 0.22/0.54    ! [X0,X1] : (k1_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> X0 = X2))),
% 0.22/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).
% 0.22/0.54  fof(f462,plain,(
% 0.22/0.54    r2_hidden(sK4(k2_pre_topc(sK0,k1_tarski(sK1)),k1_tarski(sK2)),k1_tarski(sK2))),
% 0.22/0.54    inference(resolution,[],[f460,f54])).
% 0.22/0.54  fof(f54,plain,(
% 0.22/0.54    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | r2_hidden(sK4(X0,X1),X1)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f23])).
% 0.22/0.54  fof(f23,plain,(
% 0.22/0.54    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r1_xboole_0(X0,X1)))),
% 0.22/0.54    inference(ennf_transformation,[],[f16])).
% 0.22/0.54  fof(f16,plain,(
% 0.22/0.54    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X3] : ~(r2_hidden(X3,X1) & r2_hidden(X3,X0)) & ~r1_xboole_0(X0,X1)))),
% 0.22/0.54    inference(rectify,[],[f2])).
% 0.22/0.54  fof(f2,axiom,(
% 0.22/0.54    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X2] : ~(r2_hidden(X2,X1) & r2_hidden(X2,X0)) & ~r1_xboole_0(X0,X1)))),
% 0.22/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_0)).
% 0.22/0.54  fof(f460,plain,(
% 0.22/0.54    ~r1_xboole_0(k2_pre_topc(sK0,k1_tarski(sK1)),k1_tarski(sK2))),
% 0.22/0.54    inference(subsumption_resolution,[],[f446,f99])).
% 0.22/0.54  fof(f99,plain,(
% 0.22/0.54    ~r1_xboole_0(k2_pre_topc(sK0,k1_tarski(sK1)),k2_pre_topc(sK0,k1_tarski(sK2)))),
% 0.22/0.54    inference(backward_demodulation,[],[f86,f96])).
% 0.22/0.54  fof(f86,plain,(
% 0.22/0.54    ~r1_xboole_0(k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK1)),k2_pre_topc(sK0,k1_tarski(sK2)))),
% 0.22/0.54    inference(backward_demodulation,[],[f39,f84])).
% 0.22/0.54  fof(f39,plain,(
% 0.22/0.54    ~r1_xboole_0(k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK1)),k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK2)))),
% 0.22/0.54    inference(cnf_transformation,[],[f18])).
% 0.22/0.54  fof(f446,plain,(
% 0.22/0.54    ~r1_xboole_0(k2_pre_topc(sK0,k1_tarski(sK1)),k1_tarski(sK2)) | r1_xboole_0(k2_pre_topc(sK0,k1_tarski(sK1)),k2_pre_topc(sK0,k1_tarski(sK2)))),
% 0.22/0.54    inference(resolution,[],[f157,f101])).
% 0.22/0.54  fof(f101,plain,(
% 0.22/0.54    m1_subset_1(k1_tarski(sK2),k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.22/0.54    inference(resolution,[],[f83,f63])).
% 0.22/0.54  fof(f63,plain,(
% 0.22/0.54    ( ! [X0,X1] : (~r2_hidden(X0,X1) | m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1))) )),
% 0.22/0.54    inference(cnf_transformation,[],[f34])).
% 0.22/0.54  fof(f34,plain,(
% 0.22/0.54    ! [X0,X1] : (m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1)) | ~r2_hidden(X0,X1))),
% 0.22/0.54    inference(ennf_transformation,[],[f4])).
% 0.22/0.54  fof(f4,axiom,(
% 0.22/0.54    ! [X0,X1] : (r2_hidden(X0,X1) => m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1)))),
% 0.22/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_subset_1)).
% 0.22/0.54  fof(f83,plain,(
% 0.22/0.54    r2_hidden(sK2,u1_struct_0(sK0))),
% 0.22/0.54    inference(subsumption_resolution,[],[f77,f75])).
% 0.22/0.54  fof(f77,plain,(
% 0.22/0.54    v1_xboole_0(u1_struct_0(sK0)) | r2_hidden(sK2,u1_struct_0(sK0))),
% 0.22/0.54    inference(resolution,[],[f38,f62])).
% 0.22/0.54  fof(f62,plain,(
% 0.22/0.54    ( ! [X0,X1] : (~m1_subset_1(X0,X1) | v1_xboole_0(X1) | r2_hidden(X0,X1)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f33])).
% 0.22/0.54  fof(f33,plain,(
% 0.22/0.54    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 0.22/0.54    inference(flattening,[],[f32])).
% 0.22/0.54  fof(f32,plain,(
% 0.22/0.54    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 0.22/0.54    inference(ennf_transformation,[],[f5])).
% 0.22/0.54  fof(f5,axiom,(
% 0.22/0.54    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 0.22/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).
% 0.22/0.54  fof(f157,plain,(
% 0.22/0.54    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~r1_xboole_0(k2_pre_topc(sK0,k1_tarski(sK1)),X0) | r1_xboole_0(k2_pre_topc(sK0,k1_tarski(sK1)),k2_pre_topc(sK0,X0))) )),
% 0.22/0.54    inference(subsumption_resolution,[],[f156,f43])).
% 0.22/0.54  fof(f156,plain,(
% 0.22/0.54    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~r1_xboole_0(k2_pre_topc(sK0,k1_tarski(sK1)),X0) | ~v2_pre_topc(sK0) | r1_xboole_0(k2_pre_topc(sK0,k1_tarski(sK1)),k2_pre_topc(sK0,X0))) )),
% 0.22/0.54    inference(subsumption_resolution,[],[f155,f119])).
% 0.22/0.54  fof(f119,plain,(
% 0.22/0.54    m1_subset_1(k2_pre_topc(sK0,k1_tarski(sK1)),k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.22/0.54    inference(subsumption_resolution,[],[f114,f45])).
% 0.22/0.54  fof(f114,plain,(
% 0.22/0.54    ~l1_pre_topc(sK0) | m1_subset_1(k2_pre_topc(sK0,k1_tarski(sK1)),k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.22/0.54    inference(resolution,[],[f103,f56])).
% 0.22/0.54  fof(f56,plain,(
% 0.22/0.54    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))) )),
% 0.22/0.54    inference(cnf_transformation,[],[f27])).
% 0.22/0.54  fof(f27,plain,(
% 0.22/0.54    ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 0.22/0.54    inference(flattening,[],[f26])).
% 0.22/0.54  fof(f26,plain,(
% 0.22/0.54    ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 0.22/0.54    inference(ennf_transformation,[],[f6])).
% 0.22/0.54  fof(f6,axiom,(
% 0.22/0.54    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 0.22/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_pre_topc)).
% 0.22/0.54  fof(f103,plain,(
% 0.22/0.54    m1_subset_1(k1_tarski(sK1),k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.22/0.54    inference(resolution,[],[f95,f63])).
% 0.22/0.54  fof(f95,plain,(
% 0.22/0.54    r2_hidden(sK1,u1_struct_0(sK0))),
% 0.22/0.54    inference(subsumption_resolution,[],[f89,f75])).
% 0.22/0.54  fof(f89,plain,(
% 0.22/0.54    v1_xboole_0(u1_struct_0(sK0)) | r2_hidden(sK1,u1_struct_0(sK0))),
% 0.22/0.54    inference(resolution,[],[f41,f62])).
% 0.22/0.54  fof(f155,plain,(
% 0.22/0.54    ( ! [X0] : (~m1_subset_1(k2_pre_topc(sK0,k1_tarski(sK1)),k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~r1_xboole_0(k2_pre_topc(sK0,k1_tarski(sK1)),X0) | ~v2_pre_topc(sK0) | r1_xboole_0(k2_pre_topc(sK0,k1_tarski(sK1)),k2_pre_topc(sK0,X0))) )),
% 0.22/0.54    inference(subsumption_resolution,[],[f154,f45])).
% 0.22/0.54  fof(f154,plain,(
% 0.22/0.54    ( ! [X0] : (~l1_pre_topc(sK0) | ~m1_subset_1(k2_pre_topc(sK0,k1_tarski(sK1)),k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~r1_xboole_0(k2_pre_topc(sK0,k1_tarski(sK1)),X0) | ~v2_pre_topc(sK0) | r1_xboole_0(k2_pre_topc(sK0,k1_tarski(sK1)),k2_pre_topc(sK0,X0))) )),
% 0.22/0.54    inference(resolution,[],[f145,f55])).
% 0.22/0.54  fof(f55,plain,(
% 0.22/0.54    ( ! [X2,X0,X1] : (~v3_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~r1_xboole_0(X1,X2) | ~v2_pre_topc(X0) | r1_xboole_0(X1,k2_pre_topc(X0,X2))) )),
% 0.22/0.54    inference(cnf_transformation,[],[f25])).
% 0.22/0.54  fof(f25,plain,(
% 0.22/0.54    ! [X0] : (! [X1] : (! [X2] : (r1_xboole_0(X1,k2_pre_topc(X0,X2)) | ~v3_pre_topc(X1,X0) | ~r1_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.22/0.54    inference(flattening,[],[f24])).
% 0.22/0.54  fof(f24,plain,(
% 0.22/0.54    ! [X0] : (! [X1] : (! [X2] : ((r1_xboole_0(X1,k2_pre_topc(X0,X2)) | (~v3_pre_topc(X1,X0) | ~r1_xboole_0(X1,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 0.22/0.54    inference(ennf_transformation,[],[f12])).
% 0.22/0.54  fof(f12,axiom,(
% 0.22/0.54    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((v3_pre_topc(X1,X0) & r1_xboole_0(X1,X2)) => r1_xboole_0(X1,k2_pre_topc(X0,X2))))))),
% 0.22/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t40_tsep_1)).
% 0.22/0.54  fof(f145,plain,(
% 0.22/0.54    v3_pre_topc(k2_pre_topc(sK0,k1_tarski(sK1)),sK0)),
% 0.22/0.54    inference(subsumption_resolution,[],[f144,f44])).
% 0.22/0.54  fof(f144,plain,(
% 0.22/0.54    v3_pre_topc(k2_pre_topc(sK0,k1_tarski(sK1)),sK0) | ~v3_tdlat_3(sK0)),
% 0.22/0.54    inference(subsumption_resolution,[],[f143,f43])).
% 0.22/0.54  fof(f143,plain,(
% 0.22/0.54    ~v2_pre_topc(sK0) | v3_pre_topc(k2_pre_topc(sK0,k1_tarski(sK1)),sK0) | ~v3_tdlat_3(sK0)),
% 0.22/0.54    inference(subsumption_resolution,[],[f142,f119])).
% 0.22/0.54  fof(f142,plain,(
% 0.22/0.54    ~m1_subset_1(k2_pre_topc(sK0,k1_tarski(sK1)),k1_zfmisc_1(u1_struct_0(sK0))) | ~v2_pre_topc(sK0) | v3_pre_topc(k2_pre_topc(sK0,k1_tarski(sK1)),sK0) | ~v3_tdlat_3(sK0)),
% 0.22/0.54    inference(subsumption_resolution,[],[f141,f45])).
% 0.22/0.54  fof(f141,plain,(
% 0.22/0.54    ~l1_pre_topc(sK0) | ~m1_subset_1(k2_pre_topc(sK0,k1_tarski(sK1)),k1_zfmisc_1(u1_struct_0(sK0))) | ~v2_pre_topc(sK0) | v3_pre_topc(k2_pre_topc(sK0,k1_tarski(sK1)),sK0) | ~v3_tdlat_3(sK0)),
% 0.22/0.54    inference(resolution,[],[f118,f57])).
% 0.22/0.54  fof(f57,plain,(
% 0.22/0.54    ( ! [X0,X1] : (~v4_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v2_pre_topc(X0) | v3_pre_topc(X1,X0) | ~v3_tdlat_3(X0)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f29])).
% 0.22/0.54  fof(f29,plain,(
% 0.22/0.54    ! [X0] : ((v3_tdlat_3(X0) <=> ! [X1] : (v3_pre_topc(X1,X0) | ~v4_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.22/0.54    inference(flattening,[],[f28])).
% 0.22/0.54  fof(f28,plain,(
% 0.22/0.54    ! [X0] : ((v3_tdlat_3(X0) <=> ! [X1] : ((v3_pre_topc(X1,X0) | ~v4_pre_topc(X1,X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 0.22/0.54    inference(ennf_transformation,[],[f11])).
% 0.22/0.54  fof(f11,axiom,(
% 0.22/0.54    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => (v3_tdlat_3(X0) <=> ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_pre_topc(X1,X0) => v3_pre_topc(X1,X0)))))),
% 0.22/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t24_tdlat_3)).
% 0.22/0.54  fof(f118,plain,(
% 0.22/0.54    v4_pre_topc(k2_pre_topc(sK0,k1_tarski(sK1)),sK0)),
% 0.22/0.54    inference(subsumption_resolution,[],[f117,f43])).
% 0.22/0.54  fof(f117,plain,(
% 0.22/0.54    ~v2_pre_topc(sK0) | v4_pre_topc(k2_pre_topc(sK0,k1_tarski(sK1)),sK0)),
% 0.22/0.54    inference(subsumption_resolution,[],[f113,f45])).
% 0.22/0.54  fof(f113,plain,(
% 0.22/0.54    ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v4_pre_topc(k2_pre_topc(sK0,k1_tarski(sK1)),sK0)),
% 0.22/0.54    inference(resolution,[],[f103,f66])).
% 0.22/0.54  fof(f66,plain,(
% 0.22/0.54    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v4_pre_topc(k2_pre_topc(X0,X1),X0)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f36])).
% 0.22/0.54  fof(f36,plain,(
% 0.22/0.54    ! [X0,X1] : (v4_pre_topc(k2_pre_topc(X0,X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.22/0.54    inference(flattening,[],[f35])).
% 0.22/0.54  fof(f35,plain,(
% 0.22/0.54    ! [X0,X1] : (v4_pre_topc(k2_pre_topc(X0,X1),X0) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 0.22/0.54    inference(ennf_transformation,[],[f10])).
% 0.22/0.54  fof(f10,axiom,(
% 0.22/0.54    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0)) => v4_pre_topc(k2_pre_topc(X0,X1),X0))),
% 0.22/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_tops_1)).
% 0.22/0.54  fof(f461,plain,(
% 0.22/0.54    r2_hidden(sK4(k2_pre_topc(sK0,k1_tarski(sK1)),k1_tarski(sK2)),k2_pre_topc(sK0,k1_tarski(sK1)))),
% 0.22/0.54    inference(resolution,[],[f460,f53])).
% 0.22/0.54  fof(f53,plain,(
% 0.22/0.54    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | r2_hidden(sK4(X0,X1),X0)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f23])).
% 0.22/0.54  % SZS output end Proof for theBenchmark
% 0.22/0.54  % (12101)------------------------------
% 0.22/0.54  % (12101)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.54  % (12101)Termination reason: Refutation
% 0.22/0.54  
% 0.22/0.54  % (12101)Memory used [KB]: 6524
% 0.22/0.54  % (12101)Time elapsed: 0.115 s
% 0.22/0.54  % (12101)------------------------------
% 0.22/0.54  % (12101)------------------------------
% 0.22/0.54  % (12095)Success in time 0.18 s
%------------------------------------------------------------------------------
