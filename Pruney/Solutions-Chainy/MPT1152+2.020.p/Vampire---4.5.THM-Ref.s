%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:09:50 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  113 ( 999 expanded)
%              Number of leaves         :   15 ( 249 expanded)
%              Depth                    :   34
%              Number of atoms          :  514 (4876 expanded)
%              Number of equality atoms :   59 ( 750 expanded)
%              Maximal formula depth    :   15 (   6 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2367,plain,(
    $false ),
    inference(subsumption_resolution,[],[f2366,f465])).

fof(f465,plain,(
    m1_subset_1(sK1(k2_struct_0(sK0),k2_orders_2(sK0,k2_struct_0(sK0))),k2_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f462,f47])).

fof(f47,plain,(
    k1_xboole_0 != k2_orders_2(sK0,k2_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,
    ( k1_xboole_0 != k2_orders_2(sK0,k2_struct_0(sK0))
    & l1_orders_2(sK0)
    & v5_orders_2(sK0)
    & v4_orders_2(sK0)
    & v3_orders_2(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f14,f31])).

fof(f31,plain,
    ( ? [X0] :
        ( k1_xboole_0 != k2_orders_2(X0,k2_struct_0(X0))
        & l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
   => ( k1_xboole_0 != k2_orders_2(sK0,k2_struct_0(sK0))
      & l1_orders_2(sK0)
      & v5_orders_2(sK0)
      & v4_orders_2(sK0)
      & v3_orders_2(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f14,plain,(
    ? [X0] :
      ( k1_xboole_0 != k2_orders_2(X0,k2_struct_0(X0))
      & l1_orders_2(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ? [X0] :
      ( k1_xboole_0 != k2_orders_2(X0,k2_struct_0(X0))
      & l1_orders_2(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_orders_2(X0)
          & v5_orders_2(X0)
          & v4_orders_2(X0)
          & v3_orders_2(X0)
          & ~ v2_struct_0(X0) )
       => k1_xboole_0 = k2_orders_2(X0,k2_struct_0(X0)) ) ),
    inference(negated_conjecture,[],[f11])).

fof(f11,conjecture,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => k1_xboole_0 = k2_orders_2(X0,k2_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_orders_2)).

fof(f462,plain,
    ( k1_xboole_0 = k2_orders_2(sK0,k2_struct_0(sK0))
    | m1_subset_1(sK1(k2_struct_0(sK0),k2_orders_2(sK0,k2_struct_0(sK0))),k2_struct_0(sK0)) ),
    inference(resolution,[],[f146,f57])).

fof(f57,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k1_xboole_0 = X1
      | m1_subset_1(sK1(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( r2_hidden(sK1(X0,X1),X1)
        & m1_subset_1(sK1(X0,X1),X0) )
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f26,f35])).

fof(f35,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( r2_hidden(X2,X1)
          & m1_subset_1(X2,X0) )
     => ( r2_hidden(sK1(X0,X1),X1)
        & m1_subset_1(sK1(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( r2_hidden(X2,X1)
          & m1_subset_1(X2,X0) )
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( r2_hidden(X2,X1)
          & m1_subset_1(X2,X0) )
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ~ ( ! [X2] :
              ( m1_subset_1(X2,X0)
             => ~ r2_hidden(X2,X1) )
          & k1_xboole_0 != X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_subset_1)).

fof(f146,plain,(
    m1_subset_1(k2_orders_2(sK0,k2_struct_0(sK0)),k1_zfmisc_1(k2_struct_0(sK0))) ),
    inference(resolution,[],[f89,f74])).

fof(f74,plain,(
    m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0))) ),
    inference(forward_demodulation,[],[f73,f72])).

fof(f72,plain,(
    k2_struct_0(sK0) = u1_struct_0(sK0) ),
    inference(resolution,[],[f48,f71])).

fof(f71,plain,(
    l1_struct_0(sK0) ),
    inference(resolution,[],[f50,f46])).

fof(f46,plain,(
    l1_orders_2(sK0) ),
    inference(cnf_transformation,[],[f32])).

fof(f50,plain,(
    ! [X0] :
      ( ~ l1_orders_2(X0)
      | l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_orders_2)).

fof(f48,plain,(
    ! [X0] :
      ( ~ l1_struct_0(X0)
      | k2_struct_0(X0) = u1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k2_struct_0(X0) = u1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).

fof(f73,plain,(
    m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(resolution,[],[f49,f71])).

fof(f49,plain,(
    ! [X0] :
      ( ~ l1_struct_0(X0)
      | m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_struct_0)).

fof(f89,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))
      | m1_subset_1(k2_orders_2(sK0,X0),k1_zfmisc_1(k2_struct_0(sK0))) ) ),
    inference(subsumption_resolution,[],[f88,f42])).

fof(f42,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f32])).

fof(f88,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))
      | m1_subset_1(k2_orders_2(sK0,X0),k1_zfmisc_1(k2_struct_0(sK0)))
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f87,f43])).

fof(f43,plain,(
    v3_orders_2(sK0) ),
    inference(cnf_transformation,[],[f32])).

fof(f87,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))
      | m1_subset_1(k2_orders_2(sK0,X0),k1_zfmisc_1(k2_struct_0(sK0)))
      | ~ v3_orders_2(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f86,f44])).

fof(f44,plain,(
    v4_orders_2(sK0) ),
    inference(cnf_transformation,[],[f32])).

fof(f86,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))
      | m1_subset_1(k2_orders_2(sK0,X0),k1_zfmisc_1(k2_struct_0(sK0)))
      | ~ v4_orders_2(sK0)
      | ~ v3_orders_2(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f85,f45])).

fof(f45,plain,(
    v5_orders_2(sK0) ),
    inference(cnf_transformation,[],[f32])).

fof(f85,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))
      | m1_subset_1(k2_orders_2(sK0,X0),k1_zfmisc_1(k2_struct_0(sK0)))
      | ~ v5_orders_2(sK0)
      | ~ v4_orders_2(sK0)
      | ~ v3_orders_2(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f84,f46])).

fof(f84,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))
      | m1_subset_1(k2_orders_2(sK0,X0),k1_zfmisc_1(k2_struct_0(sK0)))
      | ~ l1_orders_2(sK0)
      | ~ v5_orders_2(sK0)
      | ~ v4_orders_2(sK0)
      | ~ v3_orders_2(sK0)
      | v2_struct_0(sK0) ) ),
    inference(superposition,[],[f59,f72])).

fof(f59,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | m1_subset_1(k2_orders_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_orders_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_orders_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => m1_subset_1(k2_orders_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_orders_2)).

fof(f2366,plain,(
    ~ m1_subset_1(sK1(k2_struct_0(sK0),k2_orders_2(sK0,k2_struct_0(sK0))),k2_struct_0(sK0)) ),
    inference(forward_demodulation,[],[f2365,f72])).

fof(f2365,plain,(
    ~ m1_subset_1(sK1(k2_struct_0(sK0),k2_orders_2(sK0,k2_struct_0(sK0))),u1_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f2362,f46])).

fof(f2362,plain,
    ( ~ m1_subset_1(sK1(k2_struct_0(sK0),k2_orders_2(sK0,k2_struct_0(sK0))),u1_struct_0(sK0))
    | ~ l1_orders_2(sK0) ),
    inference(resolution,[],[f2189,f70])).

fof(f70,plain,(
    ! [X2,X0] :
      ( ~ r2_orders_2(X0,X2,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(duplicate_literal_removal,[],[f66])).

fof(f66,plain,(
    ! [X2,X0] :
      ( ~ r2_orders_2(X0,X2,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(equality_resolution,[],[f52])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( X1 != X2
      | ~ r2_orders_2(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( r2_orders_2(X0,X1,X2)
                  | X1 = X2
                  | ~ r1_orders_2(X0,X1,X2) )
                & ( ( X1 != X2
                    & r1_orders_2(X0,X1,X2) )
                  | ~ r2_orders_2(X0,X1,X2) ) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f33])).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( r2_orders_2(X0,X1,X2)
                  | X1 = X2
                  | ~ r1_orders_2(X0,X1,X2) )
                & ( ( X1 != X2
                    & r1_orders_2(X0,X1,X2) )
                  | ~ r2_orders_2(X0,X1,X2) ) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(nnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r2_orders_2(X0,X1,X2)
              <=> ( X1 != X2
                  & r1_orders_2(X0,X1,X2) ) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( r2_orders_2(X0,X1,X2)
              <=> ( X1 != X2
                  & r1_orders_2(X0,X1,X2) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_orders_2)).

fof(f2189,plain,(
    r2_orders_2(sK0,sK1(k2_struct_0(sK0),k2_orders_2(sK0,k2_struct_0(sK0))),sK1(k2_struct_0(sK0),k2_orders_2(sK0,k2_struct_0(sK0)))) ),
    inference(forward_demodulation,[],[f2184,f630])).

fof(f630,plain,(
    sK1(k2_struct_0(sK0),k2_orders_2(sK0,k2_struct_0(sK0))) = sK3(sK1(k2_struct_0(sK0),k2_orders_2(sK0,k2_struct_0(sK0))),sK0,k2_struct_0(sK0)) ),
    inference(resolution,[],[f483,f464])).

fof(f464,plain,(
    r2_hidden(sK1(k2_struct_0(sK0),k2_orders_2(sK0,k2_struct_0(sK0))),k2_orders_2(sK0,k2_struct_0(sK0))) ),
    inference(subsumption_resolution,[],[f461,f47])).

fof(f461,plain,
    ( k1_xboole_0 = k2_orders_2(sK0,k2_struct_0(sK0))
    | r2_hidden(sK1(k2_struct_0(sK0),k2_orders_2(sK0,k2_struct_0(sK0))),k2_orders_2(sK0,k2_struct_0(sK0))) ),
    inference(resolution,[],[f146,f58])).

fof(f58,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k1_xboole_0 = X1
      | r2_hidden(sK1(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f483,plain,(
    ! [X1] :
      ( ~ r2_hidden(X1,k2_orders_2(sK0,k2_struct_0(sK0)))
      | sK3(X1,sK0,k2_struct_0(sK0)) = X1 ) ),
    inference(subsumption_resolution,[],[f482,f74])).

fof(f482,plain,(
    ! [X1] :
      ( ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0)))
      | ~ r2_hidden(X1,k2_orders_2(sK0,k2_struct_0(sK0)))
      | sK3(X1,sK0,k2_struct_0(sK0)) = X1 ) ),
    inference(forward_demodulation,[],[f481,f72])).

fof(f481,plain,(
    ! [X1] :
      ( ~ r2_hidden(X1,k2_orders_2(sK0,k2_struct_0(sK0)))
      | sK3(X1,sK0,k2_struct_0(sK0)) = X1
      | ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(subsumption_resolution,[],[f480,f42])).

fof(f480,plain,(
    ! [X1] :
      ( ~ r2_hidden(X1,k2_orders_2(sK0,k2_struct_0(sK0)))
      | sK3(X1,sK0,k2_struct_0(sK0)) = X1
      | ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f479,f43])).

fof(f479,plain,(
    ! [X1] :
      ( ~ r2_hidden(X1,k2_orders_2(sK0,k2_struct_0(sK0)))
      | sK3(X1,sK0,k2_struct_0(sK0)) = X1
      | ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v3_orders_2(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f478,f44])).

fof(f478,plain,(
    ! [X1] :
      ( ~ r2_hidden(X1,k2_orders_2(sK0,k2_struct_0(sK0)))
      | sK3(X1,sK0,k2_struct_0(sK0)) = X1
      | ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v4_orders_2(sK0)
      | ~ v3_orders_2(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f477,f45])).

fof(f477,plain,(
    ! [X1] :
      ( ~ r2_hidden(X1,k2_orders_2(sK0,k2_struct_0(sK0)))
      | sK3(X1,sK0,k2_struct_0(sK0)) = X1
      | ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v5_orders_2(sK0)
      | ~ v4_orders_2(sK0)
      | ~ v3_orders_2(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f468,f46])).

fof(f468,plain,(
    ! [X1] :
      ( ~ r2_hidden(X1,k2_orders_2(sK0,k2_struct_0(sK0)))
      | sK3(X1,sK0,k2_struct_0(sK0)) = X1
      | ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ l1_orders_2(sK0)
      | ~ v5_orders_2(sK0)
      | ~ v4_orders_2(sK0)
      | ~ v3_orders_2(sK0)
      | v2_struct_0(sK0) ) ),
    inference(superposition,[],[f61,f143])).

fof(f143,plain,(
    k2_orders_2(sK0,k2_struct_0(sK0)) = a_2_1_orders_2(sK0,k2_struct_0(sK0)) ),
    inference(resolution,[],[f83,f74])).

fof(f83,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))
      | k2_orders_2(sK0,X0) = a_2_1_orders_2(sK0,X0) ) ),
    inference(subsumption_resolution,[],[f82,f42])).

fof(f82,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))
      | k2_orders_2(sK0,X0) = a_2_1_orders_2(sK0,X0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f81,f43])).

fof(f81,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))
      | k2_orders_2(sK0,X0) = a_2_1_orders_2(sK0,X0)
      | ~ v3_orders_2(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f80,f44])).

fof(f80,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))
      | k2_orders_2(sK0,X0) = a_2_1_orders_2(sK0,X0)
      | ~ v4_orders_2(sK0)
      | ~ v3_orders_2(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f79,f45])).

fof(f79,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))
      | k2_orders_2(sK0,X0) = a_2_1_orders_2(sK0,X0)
      | ~ v5_orders_2(sK0)
      | ~ v4_orders_2(sK0)
      | ~ v3_orders_2(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f78,f46])).

fof(f78,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))
      | k2_orders_2(sK0,X0) = a_2_1_orders_2(sK0,X0)
      | ~ l1_orders_2(sK0)
      | ~ v5_orders_2(sK0)
      | ~ v4_orders_2(sK0)
      | ~ v3_orders_2(sK0)
      | v2_struct_0(sK0) ) ),
    inference(superposition,[],[f54,f72])).

fof(f54,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | k2_orders_2(X0,X1) = a_2_1_orders_2(X0,X1)
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_orders_2(X0,X1) = a_2_1_orders_2(X0,X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_orders_2(X0,X1) = a_2_1_orders_2(X0,X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k2_orders_2(X0,X1) = a_2_1_orders_2(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d13_orders_2)).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,a_2_1_orders_2(X1,X2))
      | sK3(X0,X1,X2) = X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_orders_2(X1)
      | ~ v5_orders_2(X1)
      | ~ v4_orders_2(X1)
      | ~ v3_orders_2(X1)
      | v2_struct_0(X1) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,a_2_1_orders_2(X1,X2))
          | ! [X3] :
              ( ( ~ r2_orders_2(X1,X3,sK2(X1,X2,X3))
                & r2_hidden(sK2(X1,X2,X3),X2)
                & m1_subset_1(sK2(X1,X2,X3),u1_struct_0(X1)) )
              | X0 != X3
              | ~ m1_subset_1(X3,u1_struct_0(X1)) ) )
        & ( ( ! [X6] :
                ( r2_orders_2(X1,sK3(X0,X1,X2),X6)
                | ~ r2_hidden(X6,X2)
                | ~ m1_subset_1(X6,u1_struct_0(X1)) )
            & sK3(X0,X1,X2) = X0
            & m1_subset_1(sK3(X0,X1,X2),u1_struct_0(X1)) )
          | ~ r2_hidden(X0,a_2_1_orders_2(X1,X2)) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_orders_2(X1)
      | ~ v5_orders_2(X1)
      | ~ v4_orders_2(X1)
      | ~ v3_orders_2(X1)
      | v2_struct_0(X1) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f38,f40,f39])).

fof(f39,plain,(
    ! [X3,X2,X1] :
      ( ? [X4] :
          ( ~ r2_orders_2(X1,X3,X4)
          & r2_hidden(X4,X2)
          & m1_subset_1(X4,u1_struct_0(X1)) )
     => ( ~ r2_orders_2(X1,X3,sK2(X1,X2,X3))
        & r2_hidden(sK2(X1,X2,X3),X2)
        & m1_subset_1(sK2(X1,X2,X3),u1_struct_0(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f40,plain,(
    ! [X2,X1,X0] :
      ( ? [X5] :
          ( ! [X6] :
              ( r2_orders_2(X1,X5,X6)
              | ~ r2_hidden(X6,X2)
              | ~ m1_subset_1(X6,u1_struct_0(X1)) )
          & X0 = X5
          & m1_subset_1(X5,u1_struct_0(X1)) )
     => ( ! [X6] :
            ( r2_orders_2(X1,sK3(X0,X1,X2),X6)
            | ~ r2_hidden(X6,X2)
            | ~ m1_subset_1(X6,u1_struct_0(X1)) )
        & sK3(X0,X1,X2) = X0
        & m1_subset_1(sK3(X0,X1,X2),u1_struct_0(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f38,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,a_2_1_orders_2(X1,X2))
          | ! [X3] :
              ( ? [X4] :
                  ( ~ r2_orders_2(X1,X3,X4)
                  & r2_hidden(X4,X2)
                  & m1_subset_1(X4,u1_struct_0(X1)) )
              | X0 != X3
              | ~ m1_subset_1(X3,u1_struct_0(X1)) ) )
        & ( ? [X5] :
              ( ! [X6] :
                  ( r2_orders_2(X1,X5,X6)
                  | ~ r2_hidden(X6,X2)
                  | ~ m1_subset_1(X6,u1_struct_0(X1)) )
              & X0 = X5
              & m1_subset_1(X5,u1_struct_0(X1)) )
          | ~ r2_hidden(X0,a_2_1_orders_2(X1,X2)) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_orders_2(X1)
      | ~ v5_orders_2(X1)
      | ~ v4_orders_2(X1)
      | ~ v3_orders_2(X1)
      | v2_struct_0(X1) ) ),
    inference(rectify,[],[f37])).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,a_2_1_orders_2(X1,X2))
          | ! [X3] :
              ( ? [X4] :
                  ( ~ r2_orders_2(X1,X3,X4)
                  & r2_hidden(X4,X2)
                  & m1_subset_1(X4,u1_struct_0(X1)) )
              | X0 != X3
              | ~ m1_subset_1(X3,u1_struct_0(X1)) ) )
        & ( ? [X3] :
              ( ! [X4] :
                  ( r2_orders_2(X1,X3,X4)
                  | ~ r2_hidden(X4,X2)
                  | ~ m1_subset_1(X4,u1_struct_0(X1)) )
              & X0 = X3
              & m1_subset_1(X3,u1_struct_0(X1)) )
          | ~ r2_hidden(X0,a_2_1_orders_2(X1,X2)) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_orders_2(X1)
      | ~ v5_orders_2(X1)
      | ~ v4_orders_2(X1)
      | ~ v3_orders_2(X1)
      | v2_struct_0(X1) ) ),
    inference(nnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,a_2_1_orders_2(X1,X2))
      <=> ? [X3] :
            ( ! [X4] :
                ( r2_orders_2(X1,X3,X4)
                | ~ r2_hidden(X4,X2)
                | ~ m1_subset_1(X4,u1_struct_0(X1)) )
            & X0 = X3
            & m1_subset_1(X3,u1_struct_0(X1)) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_orders_2(X1)
      | ~ v5_orders_2(X1)
      | ~ v4_orders_2(X1)
      | ~ v3_orders_2(X1)
      | v2_struct_0(X1) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,a_2_1_orders_2(X1,X2))
      <=> ? [X3] :
            ( ! [X4] :
                ( r2_orders_2(X1,X3,X4)
                | ~ r2_hidden(X4,X2)
                | ~ m1_subset_1(X4,u1_struct_0(X1)) )
            & X0 = X3
            & m1_subset_1(X3,u1_struct_0(X1)) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_orders_2(X1)
      | ~ v5_orders_2(X1)
      | ~ v4_orders_2(X1)
      | ~ v3_orders_2(X1)
      | v2_struct_0(X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
        & l1_orders_2(X1)
        & v5_orders_2(X1)
        & v4_orders_2(X1)
        & v3_orders_2(X1)
        & ~ v2_struct_0(X1) )
     => ( r2_hidden(X0,a_2_1_orders_2(X1,X2))
      <=> ? [X3] :
            ( ! [X4] :
                ( m1_subset_1(X4,u1_struct_0(X1))
               => ( r2_hidden(X4,X2)
                 => r2_orders_2(X1,X3,X4) ) )
            & X0 = X3
            & m1_subset_1(X3,u1_struct_0(X1)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fraenkel_a_2_1_orders_2)).

fof(f2184,plain,(
    r2_orders_2(sK0,sK3(sK1(k2_struct_0(sK0),k2_orders_2(sK0,k2_struct_0(sK0))),sK0,k2_struct_0(sK0)),sK1(k2_struct_0(sK0),k2_orders_2(sK0,k2_struct_0(sK0)))) ),
    inference(resolution,[],[f1963,f464])).

fof(f1963,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k2_orders_2(sK0,k2_struct_0(sK0)))
      | r2_orders_2(sK0,sK3(X0,sK0,k2_struct_0(sK0)),sK1(k2_struct_0(sK0),k2_orders_2(sK0,k2_struct_0(sK0)))) ) ),
    inference(forward_demodulation,[],[f1962,f143])).

fof(f1962,plain,(
    ! [X0] :
      ( r2_orders_2(sK0,sK3(X0,sK0,k2_struct_0(sK0)),sK1(k2_struct_0(sK0),k2_orders_2(sK0,k2_struct_0(sK0))))
      | ~ r2_hidden(X0,a_2_1_orders_2(sK0,k2_struct_0(sK0))) ) ),
    inference(subsumption_resolution,[],[f1961,f42])).

fof(f1961,plain,(
    ! [X0] :
      ( r2_orders_2(sK0,sK3(X0,sK0,k2_struct_0(sK0)),sK1(k2_struct_0(sK0),k2_orders_2(sK0,k2_struct_0(sK0))))
      | ~ r2_hidden(X0,a_2_1_orders_2(sK0,k2_struct_0(sK0)))
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f1960,f43])).

fof(f1960,plain,(
    ! [X0] :
      ( r2_orders_2(sK0,sK3(X0,sK0,k2_struct_0(sK0)),sK1(k2_struct_0(sK0),k2_orders_2(sK0,k2_struct_0(sK0))))
      | ~ r2_hidden(X0,a_2_1_orders_2(sK0,k2_struct_0(sK0)))
      | ~ v3_orders_2(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f1959,f44])).

fof(f1959,plain,(
    ! [X0] :
      ( r2_orders_2(sK0,sK3(X0,sK0,k2_struct_0(sK0)),sK1(k2_struct_0(sK0),k2_orders_2(sK0,k2_struct_0(sK0))))
      | ~ r2_hidden(X0,a_2_1_orders_2(sK0,k2_struct_0(sK0)))
      | ~ v4_orders_2(sK0)
      | ~ v3_orders_2(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f1958,f45])).

fof(f1958,plain,(
    ! [X0] :
      ( r2_orders_2(sK0,sK3(X0,sK0,k2_struct_0(sK0)),sK1(k2_struct_0(sK0),k2_orders_2(sK0,k2_struct_0(sK0))))
      | ~ r2_hidden(X0,a_2_1_orders_2(sK0,k2_struct_0(sK0)))
      | ~ v5_orders_2(sK0)
      | ~ v4_orders_2(sK0)
      | ~ v3_orders_2(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f1957,f46])).

fof(f1957,plain,(
    ! [X0] :
      ( r2_orders_2(sK0,sK3(X0,sK0,k2_struct_0(sK0)),sK1(k2_struct_0(sK0),k2_orders_2(sK0,k2_struct_0(sK0))))
      | ~ r2_hidden(X0,a_2_1_orders_2(sK0,k2_struct_0(sK0)))
      | ~ l1_orders_2(sK0)
      | ~ v5_orders_2(sK0)
      | ~ v4_orders_2(sK0)
      | ~ v3_orders_2(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f1956,f74])).

fof(f1956,plain,(
    ! [X0] :
      ( r2_orders_2(sK0,sK3(X0,sK0,k2_struct_0(sK0)),sK1(k2_struct_0(sK0),k2_orders_2(sK0,k2_struct_0(sK0))))
      | ~ r2_hidden(X0,a_2_1_orders_2(sK0,k2_struct_0(sK0)))
      | ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0)))
      | ~ l1_orders_2(sK0)
      | ~ v5_orders_2(sK0)
      | ~ v4_orders_2(sK0)
      | ~ v3_orders_2(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f1955,f465])).

fof(f1955,plain,(
    ! [X0] :
      ( ~ m1_subset_1(sK1(k2_struct_0(sK0),k2_orders_2(sK0,k2_struct_0(sK0))),k2_struct_0(sK0))
      | r2_orders_2(sK0,sK3(X0,sK0,k2_struct_0(sK0)),sK1(k2_struct_0(sK0),k2_orders_2(sK0,k2_struct_0(sK0))))
      | ~ r2_hidden(X0,a_2_1_orders_2(sK0,k2_struct_0(sK0)))
      | ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0)))
      | ~ l1_orders_2(sK0)
      | ~ v5_orders_2(sK0)
      | ~ v4_orders_2(sK0)
      | ~ v3_orders_2(sK0)
      | v2_struct_0(sK0) ) ),
    inference(superposition,[],[f876,f72])).

fof(f876,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(sK1(k2_struct_0(sK0),k2_orders_2(sK0,k2_struct_0(sK0))),u1_struct_0(X0))
      | r2_orders_2(X0,sK3(X1,X0,k2_struct_0(sK0)),sK1(k2_struct_0(sK0),k2_orders_2(sK0,k2_struct_0(sK0))))
      | ~ r2_hidden(X1,a_2_1_orders_2(X0,k2_struct_0(sK0)))
      | ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(resolution,[],[f594,f62])).

fof(f62,plain,(
    ! [X6,X2,X0,X1] :
      ( ~ r2_hidden(X6,X2)
      | r2_orders_2(X1,sK3(X0,X1,X2),X6)
      | ~ m1_subset_1(X6,u1_struct_0(X1))
      | ~ r2_hidden(X0,a_2_1_orders_2(X1,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_orders_2(X1)
      | ~ v5_orders_2(X1)
      | ~ v4_orders_2(X1)
      | ~ v3_orders_2(X1)
      | v2_struct_0(X1) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f594,plain,(
    r2_hidden(sK1(k2_struct_0(sK0),k2_orders_2(sK0,k2_struct_0(sK0))),k2_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f586,f77])).

fof(f77,plain,(
    ~ v1_xboole_0(k2_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f76,f42])).

fof(f76,plain,
    ( ~ v1_xboole_0(k2_struct_0(sK0))
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f75,f71])).

fof(f75,plain,
    ( ~ v1_xboole_0(k2_struct_0(sK0))
    | ~ l1_struct_0(sK0)
    | v2_struct_0(sK0) ),
    inference(superposition,[],[f55,f72])).

fof(f55,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_struct_0)).

fof(f586,plain,
    ( v1_xboole_0(k2_struct_0(sK0))
    | r2_hidden(sK1(k2_struct_0(sK0),k2_orders_2(sK0,k2_struct_0(sK0))),k2_struct_0(sK0)) ),
    inference(resolution,[],[f465,f56])).

fof(f56,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,X1)
      | v1_xboole_0(X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n005.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 17:09:47 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.43  % (20541)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 0.21/0.49  % (20541)Refutation found. Thanks to Tanya!
% 0.21/0.49  % SZS status Theorem for theBenchmark
% 0.21/0.49  % SZS output start Proof for theBenchmark
% 0.21/0.49  fof(f2367,plain,(
% 0.21/0.49    $false),
% 0.21/0.49    inference(subsumption_resolution,[],[f2366,f465])).
% 0.21/0.49  fof(f465,plain,(
% 0.21/0.49    m1_subset_1(sK1(k2_struct_0(sK0),k2_orders_2(sK0,k2_struct_0(sK0))),k2_struct_0(sK0))),
% 0.21/0.49    inference(subsumption_resolution,[],[f462,f47])).
% 0.21/0.49  fof(f47,plain,(
% 0.21/0.49    k1_xboole_0 != k2_orders_2(sK0,k2_struct_0(sK0))),
% 0.21/0.49    inference(cnf_transformation,[],[f32])).
% 0.21/0.49  fof(f32,plain,(
% 0.21/0.49    k1_xboole_0 != k2_orders_2(sK0,k2_struct_0(sK0)) & l1_orders_2(sK0) & v5_orders_2(sK0) & v4_orders_2(sK0) & v3_orders_2(sK0) & ~v2_struct_0(sK0)),
% 0.21/0.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f14,f31])).
% 0.21/0.49  fof(f31,plain,(
% 0.21/0.49    ? [X0] : (k1_xboole_0 != k2_orders_2(X0,k2_struct_0(X0)) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => (k1_xboole_0 != k2_orders_2(sK0,k2_struct_0(sK0)) & l1_orders_2(sK0) & v5_orders_2(sK0) & v4_orders_2(sK0) & v3_orders_2(sK0) & ~v2_struct_0(sK0))),
% 0.21/0.49    introduced(choice_axiom,[])).
% 0.21/0.49  fof(f14,plain,(
% 0.21/0.49    ? [X0] : (k1_xboole_0 != k2_orders_2(X0,k2_struct_0(X0)) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0))),
% 0.21/0.49    inference(flattening,[],[f13])).
% 0.21/0.49  fof(f13,plain,(
% 0.21/0.49    ? [X0] : (k1_xboole_0 != k2_orders_2(X0,k2_struct_0(X0)) & (l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)))),
% 0.21/0.49    inference(ennf_transformation,[],[f12])).
% 0.21/0.49  fof(f12,negated_conjecture,(
% 0.21/0.49    ~! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => k1_xboole_0 = k2_orders_2(X0,k2_struct_0(X0)))),
% 0.21/0.49    inference(negated_conjecture,[],[f11])).
% 0.21/0.49  fof(f11,conjecture,(
% 0.21/0.49    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => k1_xboole_0 = k2_orders_2(X0,k2_struct_0(X0)))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_orders_2)).
% 0.21/0.49  fof(f462,plain,(
% 0.21/0.49    k1_xboole_0 = k2_orders_2(sK0,k2_struct_0(sK0)) | m1_subset_1(sK1(k2_struct_0(sK0),k2_orders_2(sK0,k2_struct_0(sK0))),k2_struct_0(sK0))),
% 0.21/0.49    inference(resolution,[],[f146,f57])).
% 0.21/0.49  fof(f57,plain,(
% 0.21/0.49    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k1_xboole_0 = X1 | m1_subset_1(sK1(X0,X1),X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f36])).
% 0.21/0.49  fof(f36,plain,(
% 0.21/0.49    ! [X0,X1] : ((r2_hidden(sK1(X0,X1),X1) & m1_subset_1(sK1(X0,X1),X0)) | k1_xboole_0 = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.21/0.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f26,f35])).
% 0.21/0.49  fof(f35,plain,(
% 0.21/0.49    ! [X1,X0] : (? [X2] : (r2_hidden(X2,X1) & m1_subset_1(X2,X0)) => (r2_hidden(sK1(X0,X1),X1) & m1_subset_1(sK1(X0,X1),X0)))),
% 0.21/0.49    introduced(choice_axiom,[])).
% 0.21/0.49  fof(f26,plain,(
% 0.21/0.49    ! [X0,X1] : (? [X2] : (r2_hidden(X2,X1) & m1_subset_1(X2,X0)) | k1_xboole_0 = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.21/0.49    inference(flattening,[],[f25])).
% 0.21/0.49  fof(f25,plain,(
% 0.21/0.49    ! [X0,X1] : ((? [X2] : (r2_hidden(X2,X1) & m1_subset_1(X2,X0)) | k1_xboole_0 = X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.21/0.49    inference(ennf_transformation,[],[f1])).
% 0.21/0.49  fof(f1,axiom,(
% 0.21/0.49    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ~(! [X2] : (m1_subset_1(X2,X0) => ~r2_hidden(X2,X1)) & k1_xboole_0 != X1))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_subset_1)).
% 0.21/0.49  fof(f146,plain,(
% 0.21/0.49    m1_subset_1(k2_orders_2(sK0,k2_struct_0(sK0)),k1_zfmisc_1(k2_struct_0(sK0)))),
% 0.21/0.49    inference(resolution,[],[f89,f74])).
% 0.21/0.49  fof(f74,plain,(
% 0.21/0.49    m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0)))),
% 0.21/0.49    inference(forward_demodulation,[],[f73,f72])).
% 0.21/0.49  fof(f72,plain,(
% 0.21/0.49    k2_struct_0(sK0) = u1_struct_0(sK0)),
% 0.21/0.49    inference(resolution,[],[f48,f71])).
% 0.21/0.49  fof(f71,plain,(
% 0.21/0.49    l1_struct_0(sK0)),
% 0.21/0.49    inference(resolution,[],[f50,f46])).
% 0.21/0.49  fof(f46,plain,(
% 0.21/0.49    l1_orders_2(sK0)),
% 0.21/0.49    inference(cnf_transformation,[],[f32])).
% 0.21/0.49  fof(f50,plain,(
% 0.21/0.49    ( ! [X0] : (~l1_orders_2(X0) | l1_struct_0(X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f17])).
% 0.21/0.49  fof(f17,plain,(
% 0.21/0.49    ! [X0] : (l1_struct_0(X0) | ~l1_orders_2(X0))),
% 0.21/0.49    inference(ennf_transformation,[],[f9])).
% 0.21/0.49  fof(f9,axiom,(
% 0.21/0.49    ! [X0] : (l1_orders_2(X0) => l1_struct_0(X0))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_orders_2)).
% 0.21/0.49  fof(f48,plain,(
% 0.21/0.49    ( ! [X0] : (~l1_struct_0(X0) | k2_struct_0(X0) = u1_struct_0(X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f15])).
% 0.21/0.49  fof(f15,plain,(
% 0.21/0.49    ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0))),
% 0.21/0.49    inference(ennf_transformation,[],[f3])).
% 0.21/0.49  fof(f3,axiom,(
% 0.21/0.49    ! [X0] : (l1_struct_0(X0) => k2_struct_0(X0) = u1_struct_0(X0))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).
% 0.21/0.49  fof(f73,plain,(
% 0.21/0.49    m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.21/0.49    inference(resolution,[],[f49,f71])).
% 0.21/0.49  fof(f49,plain,(
% 0.21/0.49    ( ! [X0] : (~l1_struct_0(X0) | m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0)))) )),
% 0.21/0.49    inference(cnf_transformation,[],[f16])).
% 0.21/0.49  fof(f16,plain,(
% 0.21/0.49    ! [X0] : (m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0))) | ~l1_struct_0(X0))),
% 0.21/0.49    inference(ennf_transformation,[],[f4])).
% 0.21/0.49  fof(f4,axiom,(
% 0.21/0.49    ! [X0] : (l1_struct_0(X0) => m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0))))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_struct_0)).
% 0.21/0.49  fof(f89,plain,(
% 0.21/0.49    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) | m1_subset_1(k2_orders_2(sK0,X0),k1_zfmisc_1(k2_struct_0(sK0)))) )),
% 0.21/0.49    inference(subsumption_resolution,[],[f88,f42])).
% 0.21/0.49  fof(f42,plain,(
% 0.21/0.49    ~v2_struct_0(sK0)),
% 0.21/0.49    inference(cnf_transformation,[],[f32])).
% 0.21/0.49  fof(f88,plain,(
% 0.21/0.49    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) | m1_subset_1(k2_orders_2(sK0,X0),k1_zfmisc_1(k2_struct_0(sK0))) | v2_struct_0(sK0)) )),
% 0.21/0.49    inference(subsumption_resolution,[],[f87,f43])).
% 0.21/0.49  fof(f43,plain,(
% 0.21/0.49    v3_orders_2(sK0)),
% 0.21/0.49    inference(cnf_transformation,[],[f32])).
% 0.21/0.49  fof(f87,plain,(
% 0.21/0.49    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) | m1_subset_1(k2_orders_2(sK0,X0),k1_zfmisc_1(k2_struct_0(sK0))) | ~v3_orders_2(sK0) | v2_struct_0(sK0)) )),
% 0.21/0.49    inference(subsumption_resolution,[],[f86,f44])).
% 0.21/0.49  fof(f44,plain,(
% 0.21/0.49    v4_orders_2(sK0)),
% 0.21/0.49    inference(cnf_transformation,[],[f32])).
% 0.21/0.49  fof(f86,plain,(
% 0.21/0.49    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) | m1_subset_1(k2_orders_2(sK0,X0),k1_zfmisc_1(k2_struct_0(sK0))) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0)) )),
% 0.21/0.49    inference(subsumption_resolution,[],[f85,f45])).
% 0.21/0.49  fof(f45,plain,(
% 0.21/0.49    v5_orders_2(sK0)),
% 0.21/0.49    inference(cnf_transformation,[],[f32])).
% 0.21/0.49  fof(f85,plain,(
% 0.21/0.49    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) | m1_subset_1(k2_orders_2(sK0,X0),k1_zfmisc_1(k2_struct_0(sK0))) | ~v5_orders_2(sK0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0)) )),
% 0.21/0.49    inference(subsumption_resolution,[],[f84,f46])).
% 0.21/0.49  fof(f84,plain,(
% 0.21/0.49    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) | m1_subset_1(k2_orders_2(sK0,X0),k1_zfmisc_1(k2_struct_0(sK0))) | ~l1_orders_2(sK0) | ~v5_orders_2(sK0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0)) )),
% 0.21/0.49    inference(superposition,[],[f59,f72])).
% 0.21/0.49  fof(f59,plain,(
% 0.21/0.49    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | m1_subset_1(k2_orders_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f28])).
% 0.21/0.49  fof(f28,plain,(
% 0.21/0.49    ! [X0,X1] : (m1_subset_1(k2_orders_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 0.21/0.49    inference(flattening,[],[f27])).
% 0.21/0.49  fof(f27,plain,(
% 0.21/0.49    ! [X0,X1] : (m1_subset_1(k2_orders_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 0.21/0.49    inference(ennf_transformation,[],[f8])).
% 0.21/0.49  fof(f8,axiom,(
% 0.21/0.49    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => m1_subset_1(k2_orders_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_orders_2)).
% 0.21/0.49  fof(f2366,plain,(
% 0.21/0.49    ~m1_subset_1(sK1(k2_struct_0(sK0),k2_orders_2(sK0,k2_struct_0(sK0))),k2_struct_0(sK0))),
% 0.21/0.49    inference(forward_demodulation,[],[f2365,f72])).
% 0.21/0.49  fof(f2365,plain,(
% 0.21/0.49    ~m1_subset_1(sK1(k2_struct_0(sK0),k2_orders_2(sK0,k2_struct_0(sK0))),u1_struct_0(sK0))),
% 0.21/0.49    inference(subsumption_resolution,[],[f2362,f46])).
% 0.21/0.49  fof(f2362,plain,(
% 0.21/0.49    ~m1_subset_1(sK1(k2_struct_0(sK0),k2_orders_2(sK0,k2_struct_0(sK0))),u1_struct_0(sK0)) | ~l1_orders_2(sK0)),
% 0.21/0.49    inference(resolution,[],[f2189,f70])).
% 0.21/0.49  fof(f70,plain,(
% 0.21/0.49    ( ! [X2,X0] : (~r2_orders_2(X0,X2,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 0.21/0.49    inference(duplicate_literal_removal,[],[f66])).
% 0.21/0.49  fof(f66,plain,(
% 0.21/0.49    ( ! [X2,X0] : (~r2_orders_2(X0,X2,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 0.21/0.49    inference(equality_resolution,[],[f52])).
% 0.21/0.49  fof(f52,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (X1 != X2 | ~r2_orders_2(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f34])).
% 0.21/0.49  fof(f34,plain,(
% 0.21/0.49    ! [X0] : (! [X1] : (! [X2] : (((r2_orders_2(X0,X1,X2) | X1 = X2 | ~r1_orders_2(X0,X1,X2)) & ((X1 != X2 & r1_orders_2(X0,X1,X2)) | ~r2_orders_2(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 0.21/0.49    inference(flattening,[],[f33])).
% 0.21/0.49  fof(f33,plain,(
% 0.21/0.49    ! [X0] : (! [X1] : (! [X2] : (((r2_orders_2(X0,X1,X2) | (X1 = X2 | ~r1_orders_2(X0,X1,X2))) & ((X1 != X2 & r1_orders_2(X0,X1,X2)) | ~r2_orders_2(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 0.21/0.49    inference(nnf_transformation,[],[f18])).
% 0.21/0.49  fof(f18,plain,(
% 0.21/0.49    ! [X0] : (! [X1] : (! [X2] : ((r2_orders_2(X0,X1,X2) <=> (X1 != X2 & r1_orders_2(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 0.21/0.49    inference(ennf_transformation,[],[f6])).
% 0.21/0.49  fof(f6,axiom,(
% 0.21/0.49    ! [X0] : (l1_orders_2(X0) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r2_orders_2(X0,X1,X2) <=> (X1 != X2 & r1_orders_2(X0,X1,X2))))))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_orders_2)).
% 0.21/0.49  fof(f2189,plain,(
% 0.21/0.49    r2_orders_2(sK0,sK1(k2_struct_0(sK0),k2_orders_2(sK0,k2_struct_0(sK0))),sK1(k2_struct_0(sK0),k2_orders_2(sK0,k2_struct_0(sK0))))),
% 0.21/0.49    inference(forward_demodulation,[],[f2184,f630])).
% 0.21/0.49  fof(f630,plain,(
% 0.21/0.49    sK1(k2_struct_0(sK0),k2_orders_2(sK0,k2_struct_0(sK0))) = sK3(sK1(k2_struct_0(sK0),k2_orders_2(sK0,k2_struct_0(sK0))),sK0,k2_struct_0(sK0))),
% 0.21/0.49    inference(resolution,[],[f483,f464])).
% 0.21/0.49  fof(f464,plain,(
% 0.21/0.49    r2_hidden(sK1(k2_struct_0(sK0),k2_orders_2(sK0,k2_struct_0(sK0))),k2_orders_2(sK0,k2_struct_0(sK0)))),
% 0.21/0.49    inference(subsumption_resolution,[],[f461,f47])).
% 0.21/0.49  fof(f461,plain,(
% 0.21/0.49    k1_xboole_0 = k2_orders_2(sK0,k2_struct_0(sK0)) | r2_hidden(sK1(k2_struct_0(sK0),k2_orders_2(sK0,k2_struct_0(sK0))),k2_orders_2(sK0,k2_struct_0(sK0)))),
% 0.21/0.49    inference(resolution,[],[f146,f58])).
% 0.21/0.49  fof(f58,plain,(
% 0.21/0.49    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k1_xboole_0 = X1 | r2_hidden(sK1(X0,X1),X1)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f36])).
% 0.21/0.49  fof(f483,plain,(
% 0.21/0.49    ( ! [X1] : (~r2_hidden(X1,k2_orders_2(sK0,k2_struct_0(sK0))) | sK3(X1,sK0,k2_struct_0(sK0)) = X1) )),
% 0.21/0.49    inference(subsumption_resolution,[],[f482,f74])).
% 0.21/0.49  fof(f482,plain,(
% 0.21/0.49    ( ! [X1] : (~m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0))) | ~r2_hidden(X1,k2_orders_2(sK0,k2_struct_0(sK0))) | sK3(X1,sK0,k2_struct_0(sK0)) = X1) )),
% 0.21/0.49    inference(forward_demodulation,[],[f481,f72])).
% 0.21/0.49  fof(f481,plain,(
% 0.21/0.49    ( ! [X1] : (~r2_hidden(X1,k2_orders_2(sK0,k2_struct_0(sK0))) | sK3(X1,sK0,k2_struct_0(sK0)) = X1 | ~m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))) )),
% 0.21/0.49    inference(subsumption_resolution,[],[f480,f42])).
% 0.21/0.49  fof(f480,plain,(
% 0.21/0.49    ( ! [X1] : (~r2_hidden(X1,k2_orders_2(sK0,k2_struct_0(sK0))) | sK3(X1,sK0,k2_struct_0(sK0)) = X1 | ~m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) | v2_struct_0(sK0)) )),
% 0.21/0.49    inference(subsumption_resolution,[],[f479,f43])).
% 0.21/0.49  fof(f479,plain,(
% 0.21/0.49    ( ! [X1] : (~r2_hidden(X1,k2_orders_2(sK0,k2_struct_0(sK0))) | sK3(X1,sK0,k2_struct_0(sK0)) = X1 | ~m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) | ~v3_orders_2(sK0) | v2_struct_0(sK0)) )),
% 0.21/0.49    inference(subsumption_resolution,[],[f478,f44])).
% 0.21/0.49  fof(f478,plain,(
% 0.21/0.49    ( ! [X1] : (~r2_hidden(X1,k2_orders_2(sK0,k2_struct_0(sK0))) | sK3(X1,sK0,k2_struct_0(sK0)) = X1 | ~m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0)) )),
% 0.21/0.49    inference(subsumption_resolution,[],[f477,f45])).
% 0.21/0.49  fof(f477,plain,(
% 0.21/0.49    ( ! [X1] : (~r2_hidden(X1,k2_orders_2(sK0,k2_struct_0(sK0))) | sK3(X1,sK0,k2_struct_0(sK0)) = X1 | ~m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) | ~v5_orders_2(sK0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0)) )),
% 0.21/0.49    inference(subsumption_resolution,[],[f468,f46])).
% 0.21/0.49  fof(f468,plain,(
% 0.21/0.49    ( ! [X1] : (~r2_hidden(X1,k2_orders_2(sK0,k2_struct_0(sK0))) | sK3(X1,sK0,k2_struct_0(sK0)) = X1 | ~m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_orders_2(sK0) | ~v5_orders_2(sK0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0)) )),
% 0.21/0.49    inference(superposition,[],[f61,f143])).
% 0.21/0.49  fof(f143,plain,(
% 0.21/0.49    k2_orders_2(sK0,k2_struct_0(sK0)) = a_2_1_orders_2(sK0,k2_struct_0(sK0))),
% 0.21/0.49    inference(resolution,[],[f83,f74])).
% 0.21/0.49  fof(f83,plain,(
% 0.21/0.49    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) | k2_orders_2(sK0,X0) = a_2_1_orders_2(sK0,X0)) )),
% 0.21/0.49    inference(subsumption_resolution,[],[f82,f42])).
% 0.21/0.49  fof(f82,plain,(
% 0.21/0.49    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) | k2_orders_2(sK0,X0) = a_2_1_orders_2(sK0,X0) | v2_struct_0(sK0)) )),
% 0.21/0.49    inference(subsumption_resolution,[],[f81,f43])).
% 0.21/0.49  fof(f81,plain,(
% 0.21/0.49    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) | k2_orders_2(sK0,X0) = a_2_1_orders_2(sK0,X0) | ~v3_orders_2(sK0) | v2_struct_0(sK0)) )),
% 0.21/0.49    inference(subsumption_resolution,[],[f80,f44])).
% 0.21/0.49  fof(f80,plain,(
% 0.21/0.49    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) | k2_orders_2(sK0,X0) = a_2_1_orders_2(sK0,X0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0)) )),
% 0.21/0.49    inference(subsumption_resolution,[],[f79,f45])).
% 0.21/0.49  fof(f79,plain,(
% 0.21/0.49    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) | k2_orders_2(sK0,X0) = a_2_1_orders_2(sK0,X0) | ~v5_orders_2(sK0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0)) )),
% 0.21/0.49    inference(subsumption_resolution,[],[f78,f46])).
% 0.21/0.49  fof(f78,plain,(
% 0.21/0.49    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) | k2_orders_2(sK0,X0) = a_2_1_orders_2(sK0,X0) | ~l1_orders_2(sK0) | ~v5_orders_2(sK0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0)) )),
% 0.21/0.49    inference(superposition,[],[f54,f72])).
% 0.21/0.49  fof(f54,plain,(
% 0.21/0.49    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | k2_orders_2(X0,X1) = a_2_1_orders_2(X0,X1) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f20])).
% 0.21/0.49  fof(f20,plain,(
% 0.21/0.49    ! [X0] : (! [X1] : (k2_orders_2(X0,X1) = a_2_1_orders_2(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 0.21/0.49    inference(flattening,[],[f19])).
% 0.21/0.49  fof(f19,plain,(
% 0.21/0.49    ! [X0] : (! [X1] : (k2_orders_2(X0,X1) = a_2_1_orders_2(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 0.21/0.49    inference(ennf_transformation,[],[f7])).
% 0.21/0.49  fof(f7,axiom,(
% 0.21/0.49    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k2_orders_2(X0,X1) = a_2_1_orders_2(X0,X1)))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d13_orders_2)).
% 0.21/0.49  fof(f61,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (~r2_hidden(X0,a_2_1_orders_2(X1,X2)) | sK3(X0,X1,X2) = X0 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_orders_2(X1) | ~v5_orders_2(X1) | ~v4_orders_2(X1) | ~v3_orders_2(X1) | v2_struct_0(X1)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f41])).
% 0.21/0.49  fof(f41,plain,(
% 0.21/0.49    ! [X0,X1,X2] : (((r2_hidden(X0,a_2_1_orders_2(X1,X2)) | ! [X3] : ((~r2_orders_2(X1,X3,sK2(X1,X2,X3)) & r2_hidden(sK2(X1,X2,X3),X2) & m1_subset_1(sK2(X1,X2,X3),u1_struct_0(X1))) | X0 != X3 | ~m1_subset_1(X3,u1_struct_0(X1)))) & ((! [X6] : (r2_orders_2(X1,sK3(X0,X1,X2),X6) | ~r2_hidden(X6,X2) | ~m1_subset_1(X6,u1_struct_0(X1))) & sK3(X0,X1,X2) = X0 & m1_subset_1(sK3(X0,X1,X2),u1_struct_0(X1))) | ~r2_hidden(X0,a_2_1_orders_2(X1,X2)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_orders_2(X1) | ~v5_orders_2(X1) | ~v4_orders_2(X1) | ~v3_orders_2(X1) | v2_struct_0(X1))),
% 0.21/0.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f38,f40,f39])).
% 0.21/0.49  fof(f39,plain,(
% 0.21/0.49    ! [X3,X2,X1] : (? [X4] : (~r2_orders_2(X1,X3,X4) & r2_hidden(X4,X2) & m1_subset_1(X4,u1_struct_0(X1))) => (~r2_orders_2(X1,X3,sK2(X1,X2,X3)) & r2_hidden(sK2(X1,X2,X3),X2) & m1_subset_1(sK2(X1,X2,X3),u1_struct_0(X1))))),
% 0.21/0.49    introduced(choice_axiom,[])).
% 0.21/0.49  fof(f40,plain,(
% 0.21/0.49    ! [X2,X1,X0] : (? [X5] : (! [X6] : (r2_orders_2(X1,X5,X6) | ~r2_hidden(X6,X2) | ~m1_subset_1(X6,u1_struct_0(X1))) & X0 = X5 & m1_subset_1(X5,u1_struct_0(X1))) => (! [X6] : (r2_orders_2(X1,sK3(X0,X1,X2),X6) | ~r2_hidden(X6,X2) | ~m1_subset_1(X6,u1_struct_0(X1))) & sK3(X0,X1,X2) = X0 & m1_subset_1(sK3(X0,X1,X2),u1_struct_0(X1))))),
% 0.21/0.49    introduced(choice_axiom,[])).
% 0.21/0.49  fof(f38,plain,(
% 0.21/0.49    ! [X0,X1,X2] : (((r2_hidden(X0,a_2_1_orders_2(X1,X2)) | ! [X3] : (? [X4] : (~r2_orders_2(X1,X3,X4) & r2_hidden(X4,X2) & m1_subset_1(X4,u1_struct_0(X1))) | X0 != X3 | ~m1_subset_1(X3,u1_struct_0(X1)))) & (? [X5] : (! [X6] : (r2_orders_2(X1,X5,X6) | ~r2_hidden(X6,X2) | ~m1_subset_1(X6,u1_struct_0(X1))) & X0 = X5 & m1_subset_1(X5,u1_struct_0(X1))) | ~r2_hidden(X0,a_2_1_orders_2(X1,X2)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_orders_2(X1) | ~v5_orders_2(X1) | ~v4_orders_2(X1) | ~v3_orders_2(X1) | v2_struct_0(X1))),
% 0.21/0.49    inference(rectify,[],[f37])).
% 0.21/0.49  fof(f37,plain,(
% 0.21/0.49    ! [X0,X1,X2] : (((r2_hidden(X0,a_2_1_orders_2(X1,X2)) | ! [X3] : (? [X4] : (~r2_orders_2(X1,X3,X4) & r2_hidden(X4,X2) & m1_subset_1(X4,u1_struct_0(X1))) | X0 != X3 | ~m1_subset_1(X3,u1_struct_0(X1)))) & (? [X3] : (! [X4] : (r2_orders_2(X1,X3,X4) | ~r2_hidden(X4,X2) | ~m1_subset_1(X4,u1_struct_0(X1))) & X0 = X3 & m1_subset_1(X3,u1_struct_0(X1))) | ~r2_hidden(X0,a_2_1_orders_2(X1,X2)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_orders_2(X1) | ~v5_orders_2(X1) | ~v4_orders_2(X1) | ~v3_orders_2(X1) | v2_struct_0(X1))),
% 0.21/0.49    inference(nnf_transformation,[],[f30])).
% 0.21/0.49  fof(f30,plain,(
% 0.21/0.49    ! [X0,X1,X2] : ((r2_hidden(X0,a_2_1_orders_2(X1,X2)) <=> ? [X3] : (! [X4] : (r2_orders_2(X1,X3,X4) | ~r2_hidden(X4,X2) | ~m1_subset_1(X4,u1_struct_0(X1))) & X0 = X3 & m1_subset_1(X3,u1_struct_0(X1)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_orders_2(X1) | ~v5_orders_2(X1) | ~v4_orders_2(X1) | ~v3_orders_2(X1) | v2_struct_0(X1))),
% 0.21/0.49    inference(flattening,[],[f29])).
% 0.21/0.49  fof(f29,plain,(
% 0.21/0.49    ! [X0,X1,X2] : ((r2_hidden(X0,a_2_1_orders_2(X1,X2)) <=> ? [X3] : (! [X4] : ((r2_orders_2(X1,X3,X4) | ~r2_hidden(X4,X2)) | ~m1_subset_1(X4,u1_struct_0(X1))) & X0 = X3 & m1_subset_1(X3,u1_struct_0(X1)))) | (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_orders_2(X1) | ~v5_orders_2(X1) | ~v4_orders_2(X1) | ~v3_orders_2(X1) | v2_struct_0(X1)))),
% 0.21/0.49    inference(ennf_transformation,[],[f10])).
% 0.21/0.49  fof(f10,axiom,(
% 0.21/0.49    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) & l1_orders_2(X1) & v5_orders_2(X1) & v4_orders_2(X1) & v3_orders_2(X1) & ~v2_struct_0(X1)) => (r2_hidden(X0,a_2_1_orders_2(X1,X2)) <=> ? [X3] : (! [X4] : (m1_subset_1(X4,u1_struct_0(X1)) => (r2_hidden(X4,X2) => r2_orders_2(X1,X3,X4))) & X0 = X3 & m1_subset_1(X3,u1_struct_0(X1)))))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fraenkel_a_2_1_orders_2)).
% 0.21/0.49  fof(f2184,plain,(
% 0.21/0.49    r2_orders_2(sK0,sK3(sK1(k2_struct_0(sK0),k2_orders_2(sK0,k2_struct_0(sK0))),sK0,k2_struct_0(sK0)),sK1(k2_struct_0(sK0),k2_orders_2(sK0,k2_struct_0(sK0))))),
% 0.21/0.49    inference(resolution,[],[f1963,f464])).
% 0.21/0.49  fof(f1963,plain,(
% 0.21/0.49    ( ! [X0] : (~r2_hidden(X0,k2_orders_2(sK0,k2_struct_0(sK0))) | r2_orders_2(sK0,sK3(X0,sK0,k2_struct_0(sK0)),sK1(k2_struct_0(sK0),k2_orders_2(sK0,k2_struct_0(sK0))))) )),
% 0.21/0.49    inference(forward_demodulation,[],[f1962,f143])).
% 0.21/0.49  fof(f1962,plain,(
% 0.21/0.49    ( ! [X0] : (r2_orders_2(sK0,sK3(X0,sK0,k2_struct_0(sK0)),sK1(k2_struct_0(sK0),k2_orders_2(sK0,k2_struct_0(sK0)))) | ~r2_hidden(X0,a_2_1_orders_2(sK0,k2_struct_0(sK0)))) )),
% 0.21/0.49    inference(subsumption_resolution,[],[f1961,f42])).
% 0.21/0.49  fof(f1961,plain,(
% 0.21/0.49    ( ! [X0] : (r2_orders_2(sK0,sK3(X0,sK0,k2_struct_0(sK0)),sK1(k2_struct_0(sK0),k2_orders_2(sK0,k2_struct_0(sK0)))) | ~r2_hidden(X0,a_2_1_orders_2(sK0,k2_struct_0(sK0))) | v2_struct_0(sK0)) )),
% 0.21/0.49    inference(subsumption_resolution,[],[f1960,f43])).
% 0.21/0.49  fof(f1960,plain,(
% 0.21/0.49    ( ! [X0] : (r2_orders_2(sK0,sK3(X0,sK0,k2_struct_0(sK0)),sK1(k2_struct_0(sK0),k2_orders_2(sK0,k2_struct_0(sK0)))) | ~r2_hidden(X0,a_2_1_orders_2(sK0,k2_struct_0(sK0))) | ~v3_orders_2(sK0) | v2_struct_0(sK0)) )),
% 0.21/0.49    inference(subsumption_resolution,[],[f1959,f44])).
% 0.21/0.49  fof(f1959,plain,(
% 0.21/0.49    ( ! [X0] : (r2_orders_2(sK0,sK3(X0,sK0,k2_struct_0(sK0)),sK1(k2_struct_0(sK0),k2_orders_2(sK0,k2_struct_0(sK0)))) | ~r2_hidden(X0,a_2_1_orders_2(sK0,k2_struct_0(sK0))) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0)) )),
% 0.21/0.49    inference(subsumption_resolution,[],[f1958,f45])).
% 0.21/0.49  fof(f1958,plain,(
% 0.21/0.49    ( ! [X0] : (r2_orders_2(sK0,sK3(X0,sK0,k2_struct_0(sK0)),sK1(k2_struct_0(sK0),k2_orders_2(sK0,k2_struct_0(sK0)))) | ~r2_hidden(X0,a_2_1_orders_2(sK0,k2_struct_0(sK0))) | ~v5_orders_2(sK0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0)) )),
% 0.21/0.49    inference(subsumption_resolution,[],[f1957,f46])).
% 0.21/0.49  fof(f1957,plain,(
% 0.21/0.49    ( ! [X0] : (r2_orders_2(sK0,sK3(X0,sK0,k2_struct_0(sK0)),sK1(k2_struct_0(sK0),k2_orders_2(sK0,k2_struct_0(sK0)))) | ~r2_hidden(X0,a_2_1_orders_2(sK0,k2_struct_0(sK0))) | ~l1_orders_2(sK0) | ~v5_orders_2(sK0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0)) )),
% 0.21/0.49    inference(subsumption_resolution,[],[f1956,f74])).
% 0.21/0.49  fof(f1956,plain,(
% 0.21/0.49    ( ! [X0] : (r2_orders_2(sK0,sK3(X0,sK0,k2_struct_0(sK0)),sK1(k2_struct_0(sK0),k2_orders_2(sK0,k2_struct_0(sK0)))) | ~r2_hidden(X0,a_2_1_orders_2(sK0,k2_struct_0(sK0))) | ~m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0))) | ~l1_orders_2(sK0) | ~v5_orders_2(sK0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0)) )),
% 0.21/0.49    inference(subsumption_resolution,[],[f1955,f465])).
% 0.21/0.49  fof(f1955,plain,(
% 0.21/0.49    ( ! [X0] : (~m1_subset_1(sK1(k2_struct_0(sK0),k2_orders_2(sK0,k2_struct_0(sK0))),k2_struct_0(sK0)) | r2_orders_2(sK0,sK3(X0,sK0,k2_struct_0(sK0)),sK1(k2_struct_0(sK0),k2_orders_2(sK0,k2_struct_0(sK0)))) | ~r2_hidden(X0,a_2_1_orders_2(sK0,k2_struct_0(sK0))) | ~m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0))) | ~l1_orders_2(sK0) | ~v5_orders_2(sK0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0)) )),
% 0.21/0.49    inference(superposition,[],[f876,f72])).
% 0.21/0.49  fof(f876,plain,(
% 0.21/0.49    ( ! [X0,X1] : (~m1_subset_1(sK1(k2_struct_0(sK0),k2_orders_2(sK0,k2_struct_0(sK0))),u1_struct_0(X0)) | r2_orders_2(X0,sK3(X1,X0,k2_struct_0(sK0)),sK1(k2_struct_0(sK0),k2_orders_2(sK0,k2_struct_0(sK0)))) | ~r2_hidden(X1,a_2_1_orders_2(X0,k2_struct_0(sK0))) | ~m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 0.21/0.49    inference(resolution,[],[f594,f62])).
% 0.21/0.49  fof(f62,plain,(
% 0.21/0.49    ( ! [X6,X2,X0,X1] : (~r2_hidden(X6,X2) | r2_orders_2(X1,sK3(X0,X1,X2),X6) | ~m1_subset_1(X6,u1_struct_0(X1)) | ~r2_hidden(X0,a_2_1_orders_2(X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_orders_2(X1) | ~v5_orders_2(X1) | ~v4_orders_2(X1) | ~v3_orders_2(X1) | v2_struct_0(X1)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f41])).
% 0.21/0.49  fof(f594,plain,(
% 0.21/0.49    r2_hidden(sK1(k2_struct_0(sK0),k2_orders_2(sK0,k2_struct_0(sK0))),k2_struct_0(sK0))),
% 0.21/0.49    inference(subsumption_resolution,[],[f586,f77])).
% 0.21/0.49  fof(f77,plain,(
% 0.21/0.49    ~v1_xboole_0(k2_struct_0(sK0))),
% 0.21/0.49    inference(subsumption_resolution,[],[f76,f42])).
% 0.21/0.49  fof(f76,plain,(
% 0.21/0.49    ~v1_xboole_0(k2_struct_0(sK0)) | v2_struct_0(sK0)),
% 0.21/0.49    inference(subsumption_resolution,[],[f75,f71])).
% 0.21/0.49  fof(f75,plain,(
% 0.21/0.49    ~v1_xboole_0(k2_struct_0(sK0)) | ~l1_struct_0(sK0) | v2_struct_0(sK0)),
% 0.21/0.49    inference(superposition,[],[f55,f72])).
% 0.21/0.49  fof(f55,plain,(
% 0.21/0.49    ( ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f22])).
% 0.21/0.49  fof(f22,plain,(
% 0.21/0.49    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 0.21/0.49    inference(flattening,[],[f21])).
% 0.21/0.49  fof(f21,plain,(
% 0.21/0.49    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 0.21/0.49    inference(ennf_transformation,[],[f5])).
% 0.21/0.49  fof(f5,axiom,(
% 0.21/0.49    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ~v1_xboole_0(u1_struct_0(X0)))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_struct_0)).
% 0.21/0.49  fof(f586,plain,(
% 0.21/0.49    v1_xboole_0(k2_struct_0(sK0)) | r2_hidden(sK1(k2_struct_0(sK0),k2_orders_2(sK0,k2_struct_0(sK0))),k2_struct_0(sK0))),
% 0.21/0.49    inference(resolution,[],[f465,f56])).
% 0.21/0.49  fof(f56,plain,(
% 0.21/0.49    ( ! [X0,X1] : (~m1_subset_1(X0,X1) | v1_xboole_0(X1) | r2_hidden(X0,X1)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f24])).
% 0.21/0.49  fof(f24,plain,(
% 0.21/0.49    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 0.21/0.49    inference(flattening,[],[f23])).
% 0.21/0.49  fof(f23,plain,(
% 0.21/0.49    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 0.21/0.49    inference(ennf_transformation,[],[f2])).
% 0.21/0.49  fof(f2,axiom,(
% 0.21/0.49    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).
% 0.21/0.49  % SZS output end Proof for theBenchmark
% 0.21/0.49  % (20541)------------------------------
% 0.21/0.49  % (20541)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.49  % (20541)Termination reason: Refutation
% 0.21/0.49  
% 0.21/0.49  % (20541)Memory used [KB]: 11769
% 0.21/0.49  % (20541)Time elapsed: 0.089 s
% 0.21/0.49  % (20541)------------------------------
% 0.21/0.49  % (20541)------------------------------
% 0.21/0.49  % (20530)Success in time 0.139 s
%------------------------------------------------------------------------------
