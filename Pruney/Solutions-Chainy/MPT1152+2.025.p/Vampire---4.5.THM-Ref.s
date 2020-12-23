%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:09:51 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 1.22s
% Verified   : 
% Statistics : Number of formulae       :  126 (3164 expanded)
%              Number of leaves         :   17 ( 805 expanded)
%              Depth                    :   30
%              Number of atoms          :  494 (15268 expanded)
%              Number of equality atoms :   67 (2514 expanded)
%              Maximal formula depth    :   12 (   6 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f193,plain,(
    $false ),
    inference(subsumption_resolution,[],[f143,f189])).

fof(f189,plain,(
    ! [X1] : ~ r2_hidden(X1,k2_orders_2(sK2,k2_struct_0(sK2))) ),
    inference(resolution,[],[f187,f151])).

fof(f151,plain,(
    m1_subset_1(k2_orders_2(sK2,k2_struct_0(sK2)),k1_zfmisc_1(k2_struct_0(sK2))) ),
    inference(resolution,[],[f149,f81])).

fof(f81,plain,(
    m1_subset_1(k2_struct_0(sK2),k1_zfmisc_1(k2_struct_0(sK2))) ),
    inference(subsumption_resolution,[],[f80,f78])).

fof(f78,plain,(
    l1_struct_0(sK2) ),
    inference(resolution,[],[f53,f49])).

fof(f49,plain,(
    l1_orders_2(sK2) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,
    ( k1_xboole_0 != k2_orders_2(sK2,k2_struct_0(sK2))
    & l1_orders_2(sK2)
    & v5_orders_2(sK2)
    & v4_orders_2(sK2)
    & v3_orders_2(sK2)
    & ~ v2_struct_0(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f14,f32])).

fof(f32,plain,
    ( ? [X0] :
        ( k1_xboole_0 != k2_orders_2(X0,k2_struct_0(X0))
        & l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
   => ( k1_xboole_0 != k2_orders_2(sK2,k2_struct_0(sK2))
      & l1_orders_2(sK2)
      & v5_orders_2(sK2)
      & v4_orders_2(sK2)
      & v3_orders_2(sK2)
      & ~ v2_struct_0(sK2) ) ),
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_orders_2)).

fof(f53,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_orders_2)).

fof(f80,plain,
    ( m1_subset_1(k2_struct_0(sK2),k1_zfmisc_1(k2_struct_0(sK2)))
    | ~ l1_struct_0(sK2) ),
    inference(superposition,[],[f52,f79])).

fof(f79,plain,(
    k2_struct_0(sK2) = u1_struct_0(sK2) ),
    inference(resolution,[],[f51,f78])).

fof(f51,plain,(
    ! [X0] :
      ( ~ l1_struct_0(X0)
      | k2_struct_0(X0) = u1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k2_struct_0(X0) = u1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).

fof(f52,plain,(
    ! [X0] :
      ( m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_struct_0)).

fof(f149,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK2)))
      | m1_subset_1(k2_orders_2(sK2,X0),k1_zfmisc_1(k2_struct_0(sK2))) ) ),
    inference(subsumption_resolution,[],[f148,f45])).

% (27118)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
fof(f45,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f33])).

fof(f148,plain,(
    ! [X0] :
      ( m1_subset_1(k2_orders_2(sK2,X0),k1_zfmisc_1(k2_struct_0(sK2)))
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK2)))
      | v2_struct_0(sK2) ) ),
    inference(subsumption_resolution,[],[f147,f46])).

fof(f46,plain,(
    v3_orders_2(sK2) ),
    inference(cnf_transformation,[],[f33])).

fof(f147,plain,(
    ! [X0] :
      ( m1_subset_1(k2_orders_2(sK2,X0),k1_zfmisc_1(k2_struct_0(sK2)))
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK2)))
      | ~ v3_orders_2(sK2)
      | v2_struct_0(sK2) ) ),
    inference(subsumption_resolution,[],[f146,f47])).

fof(f47,plain,(
    v4_orders_2(sK2) ),
    inference(cnf_transformation,[],[f33])).

fof(f146,plain,(
    ! [X0] :
      ( m1_subset_1(k2_orders_2(sK2,X0),k1_zfmisc_1(k2_struct_0(sK2)))
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK2)))
      | ~ v4_orders_2(sK2)
      | ~ v3_orders_2(sK2)
      | v2_struct_0(sK2) ) ),
    inference(subsumption_resolution,[],[f145,f48])).

fof(f48,plain,(
    v5_orders_2(sK2) ),
    inference(cnf_transformation,[],[f33])).

fof(f145,plain,(
    ! [X0] :
      ( m1_subset_1(k2_orders_2(sK2,X0),k1_zfmisc_1(k2_struct_0(sK2)))
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK2)))
      | ~ v5_orders_2(sK2)
      | ~ v4_orders_2(sK2)
      | ~ v3_orders_2(sK2)
      | v2_struct_0(sK2) ) ),
    inference(subsumption_resolution,[],[f144,f49])).

fof(f144,plain,(
    ! [X0] :
      ( m1_subset_1(k2_orders_2(sK2,X0),k1_zfmisc_1(k2_struct_0(sK2)))
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK2)))
      | ~ l1_orders_2(sK2)
      | ~ v5_orders_2(sK2)
      | ~ v4_orders_2(sK2)
      | ~ v3_orders_2(sK2)
      | v2_struct_0(sK2) ) ),
    inference(superposition,[],[f62,f79])).

fof(f62,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_orders_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_orders_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_orders_2)).

fof(f187,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK2)))
      | ~ r2_hidden(X1,X0) ) ),
    inference(resolution,[],[f186,f72])).

fof(f72,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).

fof(f186,plain,(
    v1_xboole_0(k2_struct_0(sK2)) ),
    inference(subsumption_resolution,[],[f185,f128])).

fof(f128,plain,(
    m1_subset_1(sK3(k2_orders_2(sK2,k2_struct_0(sK2))),k2_struct_0(sK2)) ),
    inference(forward_demodulation,[],[f127,f122])).

fof(f122,plain,(
    sK3(k2_orders_2(sK2,k2_struct_0(sK2))) = sK5(sK2,k2_struct_0(sK2),sK3(k2_orders_2(sK2,k2_struct_0(sK2)))) ),
    inference(forward_demodulation,[],[f121,f108])).

fof(f108,plain,(
    k2_orders_2(sK2,k2_struct_0(sK2)) = a_2_1_orders_2(sK2,k2_struct_0(sK2)) ),
    inference(resolution,[],[f107,f81])).

fof(f107,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK2)))
      | k2_orders_2(sK2,X0) = a_2_1_orders_2(sK2,X0) ) ),
    inference(forward_demodulation,[],[f106,f79])).

fof(f106,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
      | k2_orders_2(sK2,X0) = a_2_1_orders_2(sK2,X0) ) ),
    inference(subsumption_resolution,[],[f105,f45])).

fof(f105,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
      | k2_orders_2(sK2,X0) = a_2_1_orders_2(sK2,X0)
      | v2_struct_0(sK2) ) ),
    inference(subsumption_resolution,[],[f104,f46])).

fof(f104,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
      | k2_orders_2(sK2,X0) = a_2_1_orders_2(sK2,X0)
      | ~ v3_orders_2(sK2)
      | v2_struct_0(sK2) ) ),
    inference(subsumption_resolution,[],[f103,f47])).

fof(f103,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
      | k2_orders_2(sK2,X0) = a_2_1_orders_2(sK2,X0)
      | ~ v4_orders_2(sK2)
      | ~ v3_orders_2(sK2)
      | v2_struct_0(sK2) ) ),
    inference(subsumption_resolution,[],[f102,f49])).

fof(f102,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
      | ~ l1_orders_2(sK2)
      | k2_orders_2(sK2,X0) = a_2_1_orders_2(sK2,X0)
      | ~ v4_orders_2(sK2)
      | ~ v3_orders_2(sK2)
      | v2_struct_0(sK2) ) ),
    inference(resolution,[],[f57,f48])).

fof(f57,plain,(
    ! [X0,X1] :
      ( ~ v5_orders_2(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | k2_orders_2(X0,X1) = a_2_1_orders_2(X0,X1)
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d13_orders_2)).

fof(f121,plain,(
    sK3(a_2_1_orders_2(sK2,k2_struct_0(sK2))) = sK5(sK2,k2_struct_0(sK2),sK3(a_2_1_orders_2(sK2,k2_struct_0(sK2)))) ),
    inference(subsumption_resolution,[],[f113,f50])).

fof(f50,plain,(
    k1_xboole_0 != k2_orders_2(sK2,k2_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f33])).

fof(f113,plain,
    ( k1_xboole_0 = k2_orders_2(sK2,k2_struct_0(sK2))
    | sK3(a_2_1_orders_2(sK2,k2_struct_0(sK2))) = sK5(sK2,k2_struct_0(sK2),sK3(a_2_1_orders_2(sK2,k2_struct_0(sK2)))) ),
    inference(backward_demodulation,[],[f97,f108])).

fof(f97,plain,
    ( sK3(a_2_1_orders_2(sK2,k2_struct_0(sK2))) = sK5(sK2,k2_struct_0(sK2),sK3(a_2_1_orders_2(sK2,k2_struct_0(sK2))))
    | k1_xboole_0 = a_2_1_orders_2(sK2,k2_struct_0(sK2)) ),
    inference(resolution,[],[f91,f66])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( ~ sP0(X0,X1,X2)
      | sK5(X0,X1,X2) = X2 ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0,X1,X2] :
      ( ( sP0(X0,X1,X2)
        | ! [X3] :
            ( ( ~ r2_orders_2(X0,X3,sK4(X0,X1,X3))
              & r2_hidden(sK4(X0,X1,X3),X1)
              & m1_subset_1(sK4(X0,X1,X3),u1_struct_0(X0)) )
            | X2 != X3
            | ~ m1_subset_1(X3,u1_struct_0(X0)) ) )
      & ( ( ! [X6] :
              ( r2_orders_2(X0,sK5(X0,X1,X2),X6)
              | ~ r2_hidden(X6,X1)
              | ~ m1_subset_1(X6,u1_struct_0(X0)) )
          & sK5(X0,X1,X2) = X2
          & m1_subset_1(sK5(X0,X1,X2),u1_struct_0(X0)) )
        | ~ sP0(X0,X1,X2) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f41,f43,f42])).

fof(f42,plain,(
    ! [X3,X1,X0] :
      ( ? [X4] :
          ( ~ r2_orders_2(X0,X3,X4)
          & r2_hidden(X4,X1)
          & m1_subset_1(X4,u1_struct_0(X0)) )
     => ( ~ r2_orders_2(X0,X3,sK4(X0,X1,X3))
        & r2_hidden(sK4(X0,X1,X3),X1)
        & m1_subset_1(sK4(X0,X1,X3),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f43,plain,(
    ! [X2,X1,X0] :
      ( ? [X5] :
          ( ! [X6] :
              ( r2_orders_2(X0,X5,X6)
              | ~ r2_hidden(X6,X1)
              | ~ m1_subset_1(X6,u1_struct_0(X0)) )
          & X2 = X5
          & m1_subset_1(X5,u1_struct_0(X0)) )
     => ( ! [X6] :
            ( r2_orders_2(X0,sK5(X0,X1,X2),X6)
            | ~ r2_hidden(X6,X1)
            | ~ m1_subset_1(X6,u1_struct_0(X0)) )
        & sK5(X0,X1,X2) = X2
        & m1_subset_1(sK5(X0,X1,X2),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f41,plain,(
    ! [X0,X1,X2] :
      ( ( sP0(X0,X1,X2)
        | ! [X3] :
            ( ? [X4] :
                ( ~ r2_orders_2(X0,X3,X4)
                & r2_hidden(X4,X1)
                & m1_subset_1(X4,u1_struct_0(X0)) )
            | X2 != X3
            | ~ m1_subset_1(X3,u1_struct_0(X0)) ) )
      & ( ? [X5] :
            ( ! [X6] :
                ( r2_orders_2(X0,X5,X6)
                | ~ r2_hidden(X6,X1)
                | ~ m1_subset_1(X6,u1_struct_0(X0)) )
            & X2 = X5
            & m1_subset_1(X5,u1_struct_0(X0)) )
        | ~ sP0(X0,X1,X2) ) ) ),
    inference(rectify,[],[f40])).

fof(f40,plain,(
    ! [X1,X2,X0] :
      ( ( sP0(X1,X2,X0)
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
        | ~ sP0(X1,X2,X0) ) ) ),
    inference(nnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X1,X2,X0] :
      ( sP0(X1,X2,X0)
    <=> ? [X3] :
          ( ! [X4] :
              ( r2_orders_2(X1,X3,X4)
              | ~ r2_hidden(X4,X2)
              | ~ m1_subset_1(X4,u1_struct_0(X1)) )
          & X0 = X3
          & m1_subset_1(X3,u1_struct_0(X1)) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f91,plain,
    ( sP0(sK2,k2_struct_0(sK2),sK3(a_2_1_orders_2(sK2,k2_struct_0(sK2))))
    | k1_xboole_0 = a_2_1_orders_2(sK2,k2_struct_0(sK2)) ),
    inference(resolution,[],[f90,f58])).

fof(f58,plain,(
    ! [X0] :
      ( r2_hidden(sK3(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0] :
      ( ( ! [X2,X3] :
            ( k4_tarski(X2,X3) != sK3(X0)
            | ( ~ r2_hidden(X3,X0)
              & ~ r2_hidden(X2,X0) ) )
        & r2_hidden(sK3(X0),X0) )
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f21,f36])).

fof(f36,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ! [X2,X3] :
              ( k4_tarski(X2,X3) != X1
              | ( ~ r2_hidden(X3,X0)
                & ~ r2_hidden(X2,X0) ) )
          & r2_hidden(X1,X0) )
     => ( ! [X3,X2] :
            ( k4_tarski(X2,X3) != sK3(X0)
            | ( ~ r2_hidden(X3,X0)
              & ~ r2_hidden(X2,X0) ) )
        & r2_hidden(sK3(X0),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ! [X2,X3] :
              ( k4_tarski(X2,X3) != X1
              | ( ~ r2_hidden(X3,X0)
                & ~ r2_hidden(X2,X0) ) )
          & r2_hidden(X1,X0) )
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ~ ( ! [X1] :
            ~ ( ! [X2,X3] :
                  ~ ( k4_tarski(X2,X3) = X1
                    & ( r2_hidden(X3,X0)
                      | r2_hidden(X2,X0) ) )
              & r2_hidden(X1,X0) )
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t9_mcart_1)).

fof(f90,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,a_2_1_orders_2(sK2,k2_struct_0(sK2)))
      | sP0(sK2,k2_struct_0(sK2),X0) ) ),
    inference(resolution,[],[f89,f63])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( ~ sP1(X0,X1,X2)
      | ~ r2_hidden(X0,a_2_1_orders_2(X2,X1))
      | sP0(X2,X1,X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,a_2_1_orders_2(X2,X1))
          | ~ sP0(X2,X1,X0) )
        & ( sP0(X2,X1,X0)
          | ~ r2_hidden(X0,a_2_1_orders_2(X2,X1)) ) )
      | ~ sP1(X0,X1,X2) ) ),
    inference(rectify,[],[f38])).

fof(f38,plain,(
    ! [X0,X2,X1] :
      ( ( ( r2_hidden(X0,a_2_1_orders_2(X1,X2))
          | ~ sP0(X1,X2,X0) )
        & ( sP0(X1,X2,X0)
          | ~ r2_hidden(X0,a_2_1_orders_2(X1,X2)) ) )
      | ~ sP1(X0,X2,X1) ) ),
    inference(nnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X2,X1] :
      ( ( r2_hidden(X0,a_2_1_orders_2(X1,X2))
      <=> sP0(X1,X2,X0) )
      | ~ sP1(X0,X2,X1) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f89,plain,(
    ! [X0] : sP1(X0,k2_struct_0(sK2),sK2) ),
    inference(resolution,[],[f88,f81])).

fof(f88,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK2)))
      | sP1(X1,X0,sK2) ) ),
    inference(forward_demodulation,[],[f87,f79])).

fof(f87,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
      | sP1(X1,X0,sK2) ) ),
    inference(subsumption_resolution,[],[f86,f45])).

fof(f86,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
      | sP1(X1,X0,sK2)
      | v2_struct_0(sK2) ) ),
    inference(subsumption_resolution,[],[f85,f46])).

fof(f85,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
      | sP1(X1,X0,sK2)
      | ~ v3_orders_2(sK2)
      | v2_struct_0(sK2) ) ),
    inference(subsumption_resolution,[],[f84,f47])).

fof(f84,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
      | sP1(X1,X0,sK2)
      | ~ v4_orders_2(sK2)
      | ~ v3_orders_2(sK2)
      | v2_struct_0(sK2) ) ),
    inference(subsumption_resolution,[],[f83,f49])).

fof(f83,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
      | ~ l1_orders_2(sK2)
      | sP1(X1,X0,sK2)
      | ~ v4_orders_2(sK2)
      | ~ v3_orders_2(sK2)
      | v2_struct_0(sK2) ) ),
    inference(resolution,[],[f71,f48])).

fof(f71,plain,(
    ! [X2,X0,X1] :
      ( ~ v5_orders_2(X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_orders_2(X1)
      | sP1(X0,X2,X1)
      | ~ v4_orders_2(X1)
      | ~ v3_orders_2(X1)
      | v2_struct_0(X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( sP1(X0,X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_orders_2(X1)
      | ~ v5_orders_2(X1)
      | ~ v4_orders_2(X1)
      | ~ v3_orders_2(X1)
      | v2_struct_0(X1) ) ),
    inference(definition_folding,[],[f27,f30,f29])).

fof(f27,plain,(
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
    inference(flattening,[],[f26])).

fof(f26,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fraenkel_a_2_1_orders_2)).

fof(f127,plain,(
    m1_subset_1(sK5(sK2,k2_struct_0(sK2),sK3(k2_orders_2(sK2,k2_struct_0(sK2)))),k2_struct_0(sK2)) ),
    inference(forward_demodulation,[],[f126,f108])).

fof(f126,plain,(
    m1_subset_1(sK5(sK2,k2_struct_0(sK2),sK3(a_2_1_orders_2(sK2,k2_struct_0(sK2)))),k2_struct_0(sK2)) ),
    inference(subsumption_resolution,[],[f115,f50])).

fof(f115,plain,
    ( k1_xboole_0 = k2_orders_2(sK2,k2_struct_0(sK2))
    | m1_subset_1(sK5(sK2,k2_struct_0(sK2),sK3(a_2_1_orders_2(sK2,k2_struct_0(sK2)))),k2_struct_0(sK2)) ),
    inference(backward_demodulation,[],[f99,f108])).

fof(f99,plain,
    ( m1_subset_1(sK5(sK2,k2_struct_0(sK2),sK3(a_2_1_orders_2(sK2,k2_struct_0(sK2)))),k2_struct_0(sK2))
    | k1_xboole_0 = a_2_1_orders_2(sK2,k2_struct_0(sK2)) ),
    inference(forward_demodulation,[],[f96,f79])).

fof(f96,plain,
    ( k1_xboole_0 = a_2_1_orders_2(sK2,k2_struct_0(sK2))
    | m1_subset_1(sK5(sK2,k2_struct_0(sK2),sK3(a_2_1_orders_2(sK2,k2_struct_0(sK2)))),u1_struct_0(sK2)) ),
    inference(resolution,[],[f91,f65])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( ~ sP0(X0,X1,X2)
      | m1_subset_1(sK5(X0,X1,X2),u1_struct_0(X0)) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f185,plain,
    ( v1_xboole_0(k2_struct_0(sK2))
    | ~ m1_subset_1(sK3(k2_orders_2(sK2,k2_struct_0(sK2))),k2_struct_0(sK2)) ),
    inference(resolution,[],[f182,f61])).

fof(f61,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

fof(f182,plain,(
    ~ r2_hidden(sK3(k2_orders_2(sK2,k2_struct_0(sK2))),k2_struct_0(sK2)) ),
    inference(subsumption_resolution,[],[f181,f128])).

fof(f181,plain,
    ( ~ m1_subset_1(sK3(k2_orders_2(sK2,k2_struct_0(sK2))),k2_struct_0(sK2))
    | ~ r2_hidden(sK3(k2_orders_2(sK2,k2_struct_0(sK2))),k2_struct_0(sK2)) ),
    inference(forward_demodulation,[],[f180,f79])).

fof(f180,plain,
    ( ~ r2_hidden(sK3(k2_orders_2(sK2,k2_struct_0(sK2))),k2_struct_0(sK2))
    | ~ m1_subset_1(sK3(k2_orders_2(sK2,k2_struct_0(sK2))),u1_struct_0(sK2)) ),
    inference(subsumption_resolution,[],[f179,f49])).

fof(f179,plain,
    ( ~ r2_hidden(sK3(k2_orders_2(sK2,k2_struct_0(sK2))),k2_struct_0(sK2))
    | ~ m1_subset_1(sK3(k2_orders_2(sK2,k2_struct_0(sK2))),u1_struct_0(sK2))
    | ~ l1_orders_2(sK2) ),
    inference(subsumption_resolution,[],[f177,f128])).

fof(f177,plain,
    ( ~ m1_subset_1(sK3(k2_orders_2(sK2,k2_struct_0(sK2))),k2_struct_0(sK2))
    | ~ r2_hidden(sK3(k2_orders_2(sK2,k2_struct_0(sK2))),k2_struct_0(sK2))
    | ~ m1_subset_1(sK3(k2_orders_2(sK2,k2_struct_0(sK2))),u1_struct_0(sK2))
    | ~ l1_orders_2(sK2) ),
    inference(resolution,[],[f125,f77])).

fof(f77,plain,(
    ! [X2,X0] :
      ( ~ r2_orders_2(X0,X2,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(duplicate_literal_removal,[],[f73])).

fof(f73,plain,(
    ! [X2,X0] :
      ( ~ r2_orders_2(X0,X2,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(equality_resolution,[],[f55])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( X1 != X2
      | ~ r2_orders_2(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
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
    inference(flattening,[],[f34])).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_orders_2)).

fof(f125,plain,(
    ! [X0] :
      ( r2_orders_2(sK2,sK3(k2_orders_2(sK2,k2_struct_0(sK2))),X0)
      | ~ m1_subset_1(X0,k2_struct_0(sK2))
      | ~ r2_hidden(X0,k2_struct_0(sK2)) ) ),
    inference(forward_demodulation,[],[f124,f122])).

fof(f124,plain,(
    ! [X0] :
      ( r2_orders_2(sK2,sK5(sK2,k2_struct_0(sK2),sK3(k2_orders_2(sK2,k2_struct_0(sK2)))),X0)
      | ~ m1_subset_1(X0,k2_struct_0(sK2))
      | ~ r2_hidden(X0,k2_struct_0(sK2)) ) ),
    inference(forward_demodulation,[],[f123,f108])).

fof(f123,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k2_struct_0(sK2))
      | ~ r2_hidden(X0,k2_struct_0(sK2))
      | r2_orders_2(sK2,sK5(sK2,k2_struct_0(sK2),sK3(a_2_1_orders_2(sK2,k2_struct_0(sK2)))),X0) ) ),
    inference(subsumption_resolution,[],[f114,f50])).

fof(f114,plain,(
    ! [X0] :
      ( k1_xboole_0 = k2_orders_2(sK2,k2_struct_0(sK2))
      | ~ m1_subset_1(X0,k2_struct_0(sK2))
      | ~ r2_hidden(X0,k2_struct_0(sK2))
      | r2_orders_2(sK2,sK5(sK2,k2_struct_0(sK2),sK3(a_2_1_orders_2(sK2,k2_struct_0(sK2)))),X0) ) ),
    inference(backward_demodulation,[],[f98,f108])).

fof(f98,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k2_struct_0(sK2))
      | k1_xboole_0 = a_2_1_orders_2(sK2,k2_struct_0(sK2))
      | ~ r2_hidden(X0,k2_struct_0(sK2))
      | r2_orders_2(sK2,sK5(sK2,k2_struct_0(sK2),sK3(a_2_1_orders_2(sK2,k2_struct_0(sK2)))),X0) ) ),
    inference(forward_demodulation,[],[f95,f79])).

fof(f95,plain,(
    ! [X0] :
      ( k1_xboole_0 = a_2_1_orders_2(sK2,k2_struct_0(sK2))
      | ~ r2_hidden(X0,k2_struct_0(sK2))
      | ~ m1_subset_1(X0,u1_struct_0(sK2))
      | r2_orders_2(sK2,sK5(sK2,k2_struct_0(sK2),sK3(a_2_1_orders_2(sK2,k2_struct_0(sK2)))),X0) ) ),
    inference(resolution,[],[f91,f67])).

fof(f67,plain,(
    ! [X6,X2,X0,X1] :
      ( ~ sP0(X0,X1,X2)
      | ~ r2_hidden(X6,X1)
      | ~ m1_subset_1(X6,u1_struct_0(X0))
      | r2_orders_2(X0,sK5(X0,X1,X2),X6) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f143,plain,(
    r2_hidden(sK3(k2_orders_2(sK2,k2_struct_0(sK2))),k2_orders_2(sK2,k2_struct_0(sK2))) ),
    inference(resolution,[],[f132,f118])).

fof(f118,plain,(
    sP0(sK2,k2_struct_0(sK2),sK3(k2_orders_2(sK2,k2_struct_0(sK2)))) ),
    inference(subsumption_resolution,[],[f117,f50])).

fof(f117,plain,
    ( k1_xboole_0 = k2_orders_2(sK2,k2_struct_0(sK2))
    | sP0(sK2,k2_struct_0(sK2),sK3(k2_orders_2(sK2,k2_struct_0(sK2)))) ),
    inference(forward_demodulation,[],[f110,f108])).

fof(f110,plain,
    ( sP0(sK2,k2_struct_0(sK2),sK3(k2_orders_2(sK2,k2_struct_0(sK2))))
    | k1_xboole_0 = a_2_1_orders_2(sK2,k2_struct_0(sK2)) ),
    inference(backward_demodulation,[],[f91,f108])).

fof(f132,plain,(
    ! [X0] :
      ( ~ sP0(sK2,k2_struct_0(sK2),X0)
      | r2_hidden(X0,k2_orders_2(sK2,k2_struct_0(sK2))) ) ),
    inference(subsumption_resolution,[],[f131,f89])).

fof(f131,plain,(
    ! [X0] :
      ( r2_hidden(X0,k2_orders_2(sK2,k2_struct_0(sK2)))
      | ~ sP0(sK2,k2_struct_0(sK2),X0)
      | ~ sP1(X0,k2_struct_0(sK2),sK2) ) ),
    inference(superposition,[],[f64,f108])).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,a_2_1_orders_2(X2,X1))
      | ~ sP0(X2,X1,X0)
      | ~ sP1(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f39])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n002.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 19:13:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.47  % (27122)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
% 0.20/0.48  % (27135)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 0.20/0.48  % (27127)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.20/0.49  % (27130)lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_145 on theBenchmark
% 0.20/0.49  % (27121)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 0.20/0.49  % (27116)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.20/0.50  % (27117)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.20/0.50  % (27114)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 0.20/0.51  % (27124)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 0.20/0.51  % (27116)Refutation found. Thanks to Tanya!
% 0.20/0.51  % SZS status Theorem for theBenchmark
% 0.20/0.51  % SZS output start Proof for theBenchmark
% 0.20/0.51  fof(f193,plain,(
% 0.20/0.51    $false),
% 0.20/0.51    inference(subsumption_resolution,[],[f143,f189])).
% 0.20/0.51  fof(f189,plain,(
% 0.20/0.51    ( ! [X1] : (~r2_hidden(X1,k2_orders_2(sK2,k2_struct_0(sK2)))) )),
% 0.20/0.51    inference(resolution,[],[f187,f151])).
% 0.20/0.51  fof(f151,plain,(
% 0.20/0.51    m1_subset_1(k2_orders_2(sK2,k2_struct_0(sK2)),k1_zfmisc_1(k2_struct_0(sK2)))),
% 0.20/0.51    inference(resolution,[],[f149,f81])).
% 0.20/0.51  fof(f81,plain,(
% 0.20/0.51    m1_subset_1(k2_struct_0(sK2),k1_zfmisc_1(k2_struct_0(sK2)))),
% 0.20/0.51    inference(subsumption_resolution,[],[f80,f78])).
% 0.20/0.51  fof(f78,plain,(
% 0.20/0.51    l1_struct_0(sK2)),
% 0.20/0.51    inference(resolution,[],[f53,f49])).
% 0.20/0.51  fof(f49,plain,(
% 0.20/0.51    l1_orders_2(sK2)),
% 0.20/0.51    inference(cnf_transformation,[],[f33])).
% 0.20/0.51  fof(f33,plain,(
% 0.20/0.51    k1_xboole_0 != k2_orders_2(sK2,k2_struct_0(sK2)) & l1_orders_2(sK2) & v5_orders_2(sK2) & v4_orders_2(sK2) & v3_orders_2(sK2) & ~v2_struct_0(sK2)),
% 0.20/0.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f14,f32])).
% 0.20/0.51  fof(f32,plain,(
% 0.20/0.51    ? [X0] : (k1_xboole_0 != k2_orders_2(X0,k2_struct_0(X0)) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => (k1_xboole_0 != k2_orders_2(sK2,k2_struct_0(sK2)) & l1_orders_2(sK2) & v5_orders_2(sK2) & v4_orders_2(sK2) & v3_orders_2(sK2) & ~v2_struct_0(sK2))),
% 0.20/0.51    introduced(choice_axiom,[])).
% 0.20/0.51  fof(f14,plain,(
% 0.20/0.51    ? [X0] : (k1_xboole_0 != k2_orders_2(X0,k2_struct_0(X0)) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0))),
% 0.20/0.51    inference(flattening,[],[f13])).
% 0.20/0.51  fof(f13,plain,(
% 0.20/0.51    ? [X0] : (k1_xboole_0 != k2_orders_2(X0,k2_struct_0(X0)) & (l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)))),
% 0.20/0.51    inference(ennf_transformation,[],[f12])).
% 0.20/0.51  fof(f12,negated_conjecture,(
% 0.20/0.51    ~! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => k1_xboole_0 = k2_orders_2(X0,k2_struct_0(X0)))),
% 0.20/0.51    inference(negated_conjecture,[],[f11])).
% 0.20/0.51  fof(f11,conjecture,(
% 0.20/0.51    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => k1_xboole_0 = k2_orders_2(X0,k2_struct_0(X0)))),
% 0.20/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_orders_2)).
% 0.20/0.51  fof(f53,plain,(
% 0.20/0.51    ( ! [X0] : (~l1_orders_2(X0) | l1_struct_0(X0)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f17])).
% 0.20/0.51  fof(f17,plain,(
% 0.20/0.51    ! [X0] : (l1_struct_0(X0) | ~l1_orders_2(X0))),
% 0.20/0.51    inference(ennf_transformation,[],[f9])).
% 0.20/0.51  fof(f9,axiom,(
% 0.20/0.51    ! [X0] : (l1_orders_2(X0) => l1_struct_0(X0))),
% 0.20/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_orders_2)).
% 0.20/0.51  fof(f80,plain,(
% 0.20/0.51    m1_subset_1(k2_struct_0(sK2),k1_zfmisc_1(k2_struct_0(sK2))) | ~l1_struct_0(sK2)),
% 0.20/0.51    inference(superposition,[],[f52,f79])).
% 0.20/0.51  fof(f79,plain,(
% 0.20/0.51    k2_struct_0(sK2) = u1_struct_0(sK2)),
% 0.20/0.51    inference(resolution,[],[f51,f78])).
% 0.20/0.51  fof(f51,plain,(
% 0.20/0.51    ( ! [X0] : (~l1_struct_0(X0) | k2_struct_0(X0) = u1_struct_0(X0)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f15])).
% 0.20/0.51  fof(f15,plain,(
% 0.20/0.51    ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0))),
% 0.20/0.51    inference(ennf_transformation,[],[f4])).
% 0.20/0.51  fof(f4,axiom,(
% 0.20/0.51    ! [X0] : (l1_struct_0(X0) => k2_struct_0(X0) = u1_struct_0(X0))),
% 0.20/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).
% 0.20/0.51  fof(f52,plain,(
% 0.20/0.51    ( ! [X0] : (m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0))) | ~l1_struct_0(X0)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f16])).
% 0.20/0.51  fof(f16,plain,(
% 0.20/0.51    ! [X0] : (m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0))) | ~l1_struct_0(X0))),
% 0.20/0.51    inference(ennf_transformation,[],[f5])).
% 0.20/0.51  fof(f5,axiom,(
% 0.20/0.51    ! [X0] : (l1_struct_0(X0) => m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0))))),
% 0.20/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_struct_0)).
% 0.20/0.51  fof(f149,plain,(
% 0.20/0.51    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK2))) | m1_subset_1(k2_orders_2(sK2,X0),k1_zfmisc_1(k2_struct_0(sK2)))) )),
% 0.20/0.51    inference(subsumption_resolution,[],[f148,f45])).
% 0.20/0.51  % (27118)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.20/0.51  fof(f45,plain,(
% 0.20/0.51    ~v2_struct_0(sK2)),
% 0.20/0.51    inference(cnf_transformation,[],[f33])).
% 0.20/0.51  fof(f148,plain,(
% 0.20/0.51    ( ! [X0] : (m1_subset_1(k2_orders_2(sK2,X0),k1_zfmisc_1(k2_struct_0(sK2))) | ~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK2))) | v2_struct_0(sK2)) )),
% 0.20/0.51    inference(subsumption_resolution,[],[f147,f46])).
% 0.20/0.51  fof(f46,plain,(
% 0.20/0.51    v3_orders_2(sK2)),
% 0.20/0.51    inference(cnf_transformation,[],[f33])).
% 0.20/0.51  fof(f147,plain,(
% 0.20/0.51    ( ! [X0] : (m1_subset_1(k2_orders_2(sK2,X0),k1_zfmisc_1(k2_struct_0(sK2))) | ~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK2))) | ~v3_orders_2(sK2) | v2_struct_0(sK2)) )),
% 0.20/0.51    inference(subsumption_resolution,[],[f146,f47])).
% 0.20/0.51  fof(f47,plain,(
% 0.20/0.51    v4_orders_2(sK2)),
% 0.20/0.51    inference(cnf_transformation,[],[f33])).
% 0.20/0.51  fof(f146,plain,(
% 0.20/0.51    ( ! [X0] : (m1_subset_1(k2_orders_2(sK2,X0),k1_zfmisc_1(k2_struct_0(sK2))) | ~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK2))) | ~v4_orders_2(sK2) | ~v3_orders_2(sK2) | v2_struct_0(sK2)) )),
% 0.20/0.51    inference(subsumption_resolution,[],[f145,f48])).
% 0.20/0.51  fof(f48,plain,(
% 0.20/0.51    v5_orders_2(sK2)),
% 0.20/0.51    inference(cnf_transformation,[],[f33])).
% 0.20/0.51  fof(f145,plain,(
% 0.20/0.51    ( ! [X0] : (m1_subset_1(k2_orders_2(sK2,X0),k1_zfmisc_1(k2_struct_0(sK2))) | ~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK2))) | ~v5_orders_2(sK2) | ~v4_orders_2(sK2) | ~v3_orders_2(sK2) | v2_struct_0(sK2)) )),
% 0.20/0.51    inference(subsumption_resolution,[],[f144,f49])).
% 0.20/0.51  fof(f144,plain,(
% 0.20/0.51    ( ! [X0] : (m1_subset_1(k2_orders_2(sK2,X0),k1_zfmisc_1(k2_struct_0(sK2))) | ~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK2))) | ~l1_orders_2(sK2) | ~v5_orders_2(sK2) | ~v4_orders_2(sK2) | ~v3_orders_2(sK2) | v2_struct_0(sK2)) )),
% 0.20/0.51    inference(superposition,[],[f62,f79])).
% 0.20/0.51  fof(f62,plain,(
% 0.20/0.51    ( ! [X0,X1] : (m1_subset_1(k2_orders_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f25])).
% 0.20/0.51  fof(f25,plain,(
% 0.20/0.51    ! [X0,X1] : (m1_subset_1(k2_orders_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 0.20/0.51    inference(flattening,[],[f24])).
% 0.20/0.51  fof(f24,plain,(
% 0.20/0.51    ! [X0,X1] : (m1_subset_1(k2_orders_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 0.20/0.51    inference(ennf_transformation,[],[f8])).
% 0.20/0.51  fof(f8,axiom,(
% 0.20/0.51    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => m1_subset_1(k2_orders_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 0.20/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_orders_2)).
% 0.20/0.51  fof(f187,plain,(
% 0.20/0.51    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK2))) | ~r2_hidden(X1,X0)) )),
% 0.20/0.51    inference(resolution,[],[f186,f72])).
% 0.20/0.51  fof(f72,plain,(
% 0.20/0.51    ( ! [X2,X0,X1] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f28])).
% 0.20/0.51  fof(f28,plain,(
% 0.20/0.51    ! [X0,X1,X2] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 0.20/0.51    inference(ennf_transformation,[],[f2])).
% 0.20/0.51  fof(f2,axiom,(
% 0.20/0.51    ! [X0,X1,X2] : ~(v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1))),
% 0.20/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).
% 0.20/0.51  fof(f186,plain,(
% 0.20/0.51    v1_xboole_0(k2_struct_0(sK2))),
% 0.20/0.51    inference(subsumption_resolution,[],[f185,f128])).
% 0.20/0.51  fof(f128,plain,(
% 0.20/0.51    m1_subset_1(sK3(k2_orders_2(sK2,k2_struct_0(sK2))),k2_struct_0(sK2))),
% 0.20/0.51    inference(forward_demodulation,[],[f127,f122])).
% 0.20/0.51  fof(f122,plain,(
% 0.20/0.51    sK3(k2_orders_2(sK2,k2_struct_0(sK2))) = sK5(sK2,k2_struct_0(sK2),sK3(k2_orders_2(sK2,k2_struct_0(sK2))))),
% 0.20/0.51    inference(forward_demodulation,[],[f121,f108])).
% 0.20/0.51  fof(f108,plain,(
% 0.20/0.51    k2_orders_2(sK2,k2_struct_0(sK2)) = a_2_1_orders_2(sK2,k2_struct_0(sK2))),
% 0.20/0.51    inference(resolution,[],[f107,f81])).
% 0.20/0.51  fof(f107,plain,(
% 0.20/0.51    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK2))) | k2_orders_2(sK2,X0) = a_2_1_orders_2(sK2,X0)) )),
% 0.20/0.51    inference(forward_demodulation,[],[f106,f79])).
% 0.20/0.51  fof(f106,plain,(
% 0.20/0.51    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) | k2_orders_2(sK2,X0) = a_2_1_orders_2(sK2,X0)) )),
% 0.20/0.51    inference(subsumption_resolution,[],[f105,f45])).
% 0.20/0.51  fof(f105,plain,(
% 0.20/0.51    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) | k2_orders_2(sK2,X0) = a_2_1_orders_2(sK2,X0) | v2_struct_0(sK2)) )),
% 0.20/0.51    inference(subsumption_resolution,[],[f104,f46])).
% 0.20/0.51  fof(f104,plain,(
% 0.20/0.51    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) | k2_orders_2(sK2,X0) = a_2_1_orders_2(sK2,X0) | ~v3_orders_2(sK2) | v2_struct_0(sK2)) )),
% 0.20/0.51    inference(subsumption_resolution,[],[f103,f47])).
% 0.20/0.51  fof(f103,plain,(
% 0.20/0.51    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) | k2_orders_2(sK2,X0) = a_2_1_orders_2(sK2,X0) | ~v4_orders_2(sK2) | ~v3_orders_2(sK2) | v2_struct_0(sK2)) )),
% 0.20/0.51    inference(subsumption_resolution,[],[f102,f49])).
% 0.20/0.51  fof(f102,plain,(
% 0.20/0.51    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) | ~l1_orders_2(sK2) | k2_orders_2(sK2,X0) = a_2_1_orders_2(sK2,X0) | ~v4_orders_2(sK2) | ~v3_orders_2(sK2) | v2_struct_0(sK2)) )),
% 0.20/0.51    inference(resolution,[],[f57,f48])).
% 0.20/0.51  fof(f57,plain,(
% 0.20/0.51    ( ! [X0,X1] : (~v5_orders_2(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | k2_orders_2(X0,X1) = a_2_1_orders_2(X0,X1) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f20])).
% 0.20/0.51  fof(f20,plain,(
% 0.20/0.51    ! [X0] : (! [X1] : (k2_orders_2(X0,X1) = a_2_1_orders_2(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 0.20/0.51    inference(flattening,[],[f19])).
% 0.20/0.51  fof(f19,plain,(
% 0.20/0.51    ! [X0] : (! [X1] : (k2_orders_2(X0,X1) = a_2_1_orders_2(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 0.20/0.51    inference(ennf_transformation,[],[f7])).
% 0.20/0.51  fof(f7,axiom,(
% 0.20/0.51    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k2_orders_2(X0,X1) = a_2_1_orders_2(X0,X1)))),
% 0.20/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d13_orders_2)).
% 0.20/0.51  fof(f121,plain,(
% 0.20/0.51    sK3(a_2_1_orders_2(sK2,k2_struct_0(sK2))) = sK5(sK2,k2_struct_0(sK2),sK3(a_2_1_orders_2(sK2,k2_struct_0(sK2))))),
% 0.20/0.51    inference(subsumption_resolution,[],[f113,f50])).
% 0.20/0.51  fof(f50,plain,(
% 0.20/0.51    k1_xboole_0 != k2_orders_2(sK2,k2_struct_0(sK2))),
% 0.20/0.51    inference(cnf_transformation,[],[f33])).
% 0.20/0.51  fof(f113,plain,(
% 0.20/0.51    k1_xboole_0 = k2_orders_2(sK2,k2_struct_0(sK2)) | sK3(a_2_1_orders_2(sK2,k2_struct_0(sK2))) = sK5(sK2,k2_struct_0(sK2),sK3(a_2_1_orders_2(sK2,k2_struct_0(sK2))))),
% 0.20/0.51    inference(backward_demodulation,[],[f97,f108])).
% 0.20/0.51  fof(f97,plain,(
% 0.20/0.51    sK3(a_2_1_orders_2(sK2,k2_struct_0(sK2))) = sK5(sK2,k2_struct_0(sK2),sK3(a_2_1_orders_2(sK2,k2_struct_0(sK2)))) | k1_xboole_0 = a_2_1_orders_2(sK2,k2_struct_0(sK2))),
% 0.20/0.51    inference(resolution,[],[f91,f66])).
% 0.20/0.51  fof(f66,plain,(
% 0.20/0.51    ( ! [X2,X0,X1] : (~sP0(X0,X1,X2) | sK5(X0,X1,X2) = X2) )),
% 0.20/0.51    inference(cnf_transformation,[],[f44])).
% 0.20/0.51  fof(f44,plain,(
% 0.20/0.51    ! [X0,X1,X2] : ((sP0(X0,X1,X2) | ! [X3] : ((~r2_orders_2(X0,X3,sK4(X0,X1,X3)) & r2_hidden(sK4(X0,X1,X3),X1) & m1_subset_1(sK4(X0,X1,X3),u1_struct_0(X0))) | X2 != X3 | ~m1_subset_1(X3,u1_struct_0(X0)))) & ((! [X6] : (r2_orders_2(X0,sK5(X0,X1,X2),X6) | ~r2_hidden(X6,X1) | ~m1_subset_1(X6,u1_struct_0(X0))) & sK5(X0,X1,X2) = X2 & m1_subset_1(sK5(X0,X1,X2),u1_struct_0(X0))) | ~sP0(X0,X1,X2)))),
% 0.20/0.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f41,f43,f42])).
% 0.20/0.51  fof(f42,plain,(
% 0.20/0.51    ! [X3,X1,X0] : (? [X4] : (~r2_orders_2(X0,X3,X4) & r2_hidden(X4,X1) & m1_subset_1(X4,u1_struct_0(X0))) => (~r2_orders_2(X0,X3,sK4(X0,X1,X3)) & r2_hidden(sK4(X0,X1,X3),X1) & m1_subset_1(sK4(X0,X1,X3),u1_struct_0(X0))))),
% 0.20/0.51    introduced(choice_axiom,[])).
% 0.20/0.51  fof(f43,plain,(
% 0.20/0.51    ! [X2,X1,X0] : (? [X5] : (! [X6] : (r2_orders_2(X0,X5,X6) | ~r2_hidden(X6,X1) | ~m1_subset_1(X6,u1_struct_0(X0))) & X2 = X5 & m1_subset_1(X5,u1_struct_0(X0))) => (! [X6] : (r2_orders_2(X0,sK5(X0,X1,X2),X6) | ~r2_hidden(X6,X1) | ~m1_subset_1(X6,u1_struct_0(X0))) & sK5(X0,X1,X2) = X2 & m1_subset_1(sK5(X0,X1,X2),u1_struct_0(X0))))),
% 0.20/0.51    introduced(choice_axiom,[])).
% 0.20/0.51  fof(f41,plain,(
% 0.20/0.51    ! [X0,X1,X2] : ((sP0(X0,X1,X2) | ! [X3] : (? [X4] : (~r2_orders_2(X0,X3,X4) & r2_hidden(X4,X1) & m1_subset_1(X4,u1_struct_0(X0))) | X2 != X3 | ~m1_subset_1(X3,u1_struct_0(X0)))) & (? [X5] : (! [X6] : (r2_orders_2(X0,X5,X6) | ~r2_hidden(X6,X1) | ~m1_subset_1(X6,u1_struct_0(X0))) & X2 = X5 & m1_subset_1(X5,u1_struct_0(X0))) | ~sP0(X0,X1,X2)))),
% 0.20/0.51    inference(rectify,[],[f40])).
% 0.20/0.51  fof(f40,plain,(
% 0.20/0.51    ! [X1,X2,X0] : ((sP0(X1,X2,X0) | ! [X3] : (? [X4] : (~r2_orders_2(X1,X3,X4) & r2_hidden(X4,X2) & m1_subset_1(X4,u1_struct_0(X1))) | X0 != X3 | ~m1_subset_1(X3,u1_struct_0(X1)))) & (? [X3] : (! [X4] : (r2_orders_2(X1,X3,X4) | ~r2_hidden(X4,X2) | ~m1_subset_1(X4,u1_struct_0(X1))) & X0 = X3 & m1_subset_1(X3,u1_struct_0(X1))) | ~sP0(X1,X2,X0)))),
% 0.20/0.51    inference(nnf_transformation,[],[f29])).
% 0.20/0.51  fof(f29,plain,(
% 0.20/0.51    ! [X1,X2,X0] : (sP0(X1,X2,X0) <=> ? [X3] : (! [X4] : (r2_orders_2(X1,X3,X4) | ~r2_hidden(X4,X2) | ~m1_subset_1(X4,u1_struct_0(X1))) & X0 = X3 & m1_subset_1(X3,u1_struct_0(X1))))),
% 0.20/0.51    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 0.20/0.51  fof(f91,plain,(
% 0.20/0.51    sP0(sK2,k2_struct_0(sK2),sK3(a_2_1_orders_2(sK2,k2_struct_0(sK2)))) | k1_xboole_0 = a_2_1_orders_2(sK2,k2_struct_0(sK2))),
% 0.20/0.51    inference(resolution,[],[f90,f58])).
% 0.20/0.51  fof(f58,plain,(
% 0.20/0.51    ( ! [X0] : (r2_hidden(sK3(X0),X0) | k1_xboole_0 = X0) )),
% 0.20/0.51    inference(cnf_transformation,[],[f37])).
% 0.20/0.51  fof(f37,plain,(
% 0.20/0.51    ! [X0] : ((! [X2,X3] : (k4_tarski(X2,X3) != sK3(X0) | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(sK3(X0),X0)) | k1_xboole_0 = X0)),
% 0.20/0.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f21,f36])).
% 0.20/0.51  fof(f36,plain,(
% 0.20/0.51    ! [X0] : (? [X1] : (! [X2,X3] : (k4_tarski(X2,X3) != X1 | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(X1,X0)) => (! [X3,X2] : (k4_tarski(X2,X3) != sK3(X0) | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(sK3(X0),X0)))),
% 0.20/0.51    introduced(choice_axiom,[])).
% 0.20/0.51  fof(f21,plain,(
% 0.20/0.51    ! [X0] : (? [X1] : (! [X2,X3] : (k4_tarski(X2,X3) != X1 | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(X1,X0)) | k1_xboole_0 = X0)),
% 0.20/0.51    inference(ennf_transformation,[],[f3])).
% 0.20/0.51  fof(f3,axiom,(
% 0.20/0.51    ! [X0] : ~(! [X1] : ~(! [X2,X3] : ~(k4_tarski(X2,X3) = X1 & (r2_hidden(X3,X0) | r2_hidden(X2,X0))) & r2_hidden(X1,X0)) & k1_xboole_0 != X0)),
% 0.20/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t9_mcart_1)).
% 0.20/0.51  fof(f90,plain,(
% 0.20/0.51    ( ! [X0] : (~r2_hidden(X0,a_2_1_orders_2(sK2,k2_struct_0(sK2))) | sP0(sK2,k2_struct_0(sK2),X0)) )),
% 0.20/0.51    inference(resolution,[],[f89,f63])).
% 0.20/0.51  fof(f63,plain,(
% 0.20/0.51    ( ! [X2,X0,X1] : (~sP1(X0,X1,X2) | ~r2_hidden(X0,a_2_1_orders_2(X2,X1)) | sP0(X2,X1,X0)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f39])).
% 0.20/0.51  fof(f39,plain,(
% 0.20/0.51    ! [X0,X1,X2] : (((r2_hidden(X0,a_2_1_orders_2(X2,X1)) | ~sP0(X2,X1,X0)) & (sP0(X2,X1,X0) | ~r2_hidden(X0,a_2_1_orders_2(X2,X1)))) | ~sP1(X0,X1,X2))),
% 0.20/0.51    inference(rectify,[],[f38])).
% 0.20/0.51  fof(f38,plain,(
% 0.20/0.51    ! [X0,X2,X1] : (((r2_hidden(X0,a_2_1_orders_2(X1,X2)) | ~sP0(X1,X2,X0)) & (sP0(X1,X2,X0) | ~r2_hidden(X0,a_2_1_orders_2(X1,X2)))) | ~sP1(X0,X2,X1))),
% 0.20/0.51    inference(nnf_transformation,[],[f30])).
% 0.20/0.51  fof(f30,plain,(
% 0.20/0.51    ! [X0,X2,X1] : ((r2_hidden(X0,a_2_1_orders_2(X1,X2)) <=> sP0(X1,X2,X0)) | ~sP1(X0,X2,X1))),
% 0.20/0.51    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 0.20/0.51  fof(f89,plain,(
% 0.20/0.51    ( ! [X0] : (sP1(X0,k2_struct_0(sK2),sK2)) )),
% 0.20/0.51    inference(resolution,[],[f88,f81])).
% 0.20/0.51  fof(f88,plain,(
% 0.20/0.51    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK2))) | sP1(X1,X0,sK2)) )),
% 0.20/0.51    inference(forward_demodulation,[],[f87,f79])).
% 0.20/0.51  fof(f87,plain,(
% 0.20/0.51    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) | sP1(X1,X0,sK2)) )),
% 0.20/0.51    inference(subsumption_resolution,[],[f86,f45])).
% 0.20/0.51  fof(f86,plain,(
% 0.20/0.51    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) | sP1(X1,X0,sK2) | v2_struct_0(sK2)) )),
% 0.20/0.51    inference(subsumption_resolution,[],[f85,f46])).
% 0.20/0.51  fof(f85,plain,(
% 0.20/0.51    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) | sP1(X1,X0,sK2) | ~v3_orders_2(sK2) | v2_struct_0(sK2)) )),
% 0.20/0.51    inference(subsumption_resolution,[],[f84,f47])).
% 0.20/0.51  fof(f84,plain,(
% 0.20/0.51    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) | sP1(X1,X0,sK2) | ~v4_orders_2(sK2) | ~v3_orders_2(sK2) | v2_struct_0(sK2)) )),
% 0.20/0.51    inference(subsumption_resolution,[],[f83,f49])).
% 0.20/0.51  fof(f83,plain,(
% 0.20/0.51    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) | ~l1_orders_2(sK2) | sP1(X1,X0,sK2) | ~v4_orders_2(sK2) | ~v3_orders_2(sK2) | v2_struct_0(sK2)) )),
% 0.20/0.51    inference(resolution,[],[f71,f48])).
% 0.20/0.51  fof(f71,plain,(
% 0.20/0.51    ( ! [X2,X0,X1] : (~v5_orders_2(X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_orders_2(X1) | sP1(X0,X2,X1) | ~v4_orders_2(X1) | ~v3_orders_2(X1) | v2_struct_0(X1)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f31])).
% 0.20/0.51  fof(f31,plain,(
% 0.20/0.51    ! [X0,X1,X2] : (sP1(X0,X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_orders_2(X1) | ~v5_orders_2(X1) | ~v4_orders_2(X1) | ~v3_orders_2(X1) | v2_struct_0(X1))),
% 0.20/0.51    inference(definition_folding,[],[f27,f30,f29])).
% 0.20/0.51  fof(f27,plain,(
% 0.20/0.51    ! [X0,X1,X2] : ((r2_hidden(X0,a_2_1_orders_2(X1,X2)) <=> ? [X3] : (! [X4] : (r2_orders_2(X1,X3,X4) | ~r2_hidden(X4,X2) | ~m1_subset_1(X4,u1_struct_0(X1))) & X0 = X3 & m1_subset_1(X3,u1_struct_0(X1)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_orders_2(X1) | ~v5_orders_2(X1) | ~v4_orders_2(X1) | ~v3_orders_2(X1) | v2_struct_0(X1))),
% 0.20/0.51    inference(flattening,[],[f26])).
% 0.20/0.51  fof(f26,plain,(
% 0.20/0.51    ! [X0,X1,X2] : ((r2_hidden(X0,a_2_1_orders_2(X1,X2)) <=> ? [X3] : (! [X4] : ((r2_orders_2(X1,X3,X4) | ~r2_hidden(X4,X2)) | ~m1_subset_1(X4,u1_struct_0(X1))) & X0 = X3 & m1_subset_1(X3,u1_struct_0(X1)))) | (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_orders_2(X1) | ~v5_orders_2(X1) | ~v4_orders_2(X1) | ~v3_orders_2(X1) | v2_struct_0(X1)))),
% 0.20/0.51    inference(ennf_transformation,[],[f10])).
% 0.20/0.51  fof(f10,axiom,(
% 0.20/0.51    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) & l1_orders_2(X1) & v5_orders_2(X1) & v4_orders_2(X1) & v3_orders_2(X1) & ~v2_struct_0(X1)) => (r2_hidden(X0,a_2_1_orders_2(X1,X2)) <=> ? [X3] : (! [X4] : (m1_subset_1(X4,u1_struct_0(X1)) => (r2_hidden(X4,X2) => r2_orders_2(X1,X3,X4))) & X0 = X3 & m1_subset_1(X3,u1_struct_0(X1)))))),
% 0.20/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fraenkel_a_2_1_orders_2)).
% 0.20/0.51  fof(f127,plain,(
% 0.20/0.51    m1_subset_1(sK5(sK2,k2_struct_0(sK2),sK3(k2_orders_2(sK2,k2_struct_0(sK2)))),k2_struct_0(sK2))),
% 0.20/0.51    inference(forward_demodulation,[],[f126,f108])).
% 0.20/0.51  fof(f126,plain,(
% 0.20/0.51    m1_subset_1(sK5(sK2,k2_struct_0(sK2),sK3(a_2_1_orders_2(sK2,k2_struct_0(sK2)))),k2_struct_0(sK2))),
% 0.20/0.51    inference(subsumption_resolution,[],[f115,f50])).
% 0.20/0.51  fof(f115,plain,(
% 0.20/0.51    k1_xboole_0 = k2_orders_2(sK2,k2_struct_0(sK2)) | m1_subset_1(sK5(sK2,k2_struct_0(sK2),sK3(a_2_1_orders_2(sK2,k2_struct_0(sK2)))),k2_struct_0(sK2))),
% 0.20/0.51    inference(backward_demodulation,[],[f99,f108])).
% 0.20/0.51  fof(f99,plain,(
% 0.20/0.51    m1_subset_1(sK5(sK2,k2_struct_0(sK2),sK3(a_2_1_orders_2(sK2,k2_struct_0(sK2)))),k2_struct_0(sK2)) | k1_xboole_0 = a_2_1_orders_2(sK2,k2_struct_0(sK2))),
% 0.20/0.51    inference(forward_demodulation,[],[f96,f79])).
% 0.20/0.51  fof(f96,plain,(
% 0.20/0.51    k1_xboole_0 = a_2_1_orders_2(sK2,k2_struct_0(sK2)) | m1_subset_1(sK5(sK2,k2_struct_0(sK2),sK3(a_2_1_orders_2(sK2,k2_struct_0(sK2)))),u1_struct_0(sK2))),
% 0.20/0.51    inference(resolution,[],[f91,f65])).
% 1.22/0.51  fof(f65,plain,(
% 1.22/0.51    ( ! [X2,X0,X1] : (~sP0(X0,X1,X2) | m1_subset_1(sK5(X0,X1,X2),u1_struct_0(X0))) )),
% 1.22/0.51    inference(cnf_transformation,[],[f44])).
% 1.22/0.51  fof(f185,plain,(
% 1.22/0.51    v1_xboole_0(k2_struct_0(sK2)) | ~m1_subset_1(sK3(k2_orders_2(sK2,k2_struct_0(sK2))),k2_struct_0(sK2))),
% 1.22/0.51    inference(resolution,[],[f182,f61])).
% 1.22/0.51  fof(f61,plain,(
% 1.22/0.51    ( ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1)) )),
% 1.22/0.51    inference(cnf_transformation,[],[f23])).
% 1.22/0.51  fof(f23,plain,(
% 1.22/0.51    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 1.22/0.51    inference(flattening,[],[f22])).
% 1.22/0.51  fof(f22,plain,(
% 1.22/0.51    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 1.22/0.51    inference(ennf_transformation,[],[f1])).
% 1.22/0.51  fof(f1,axiom,(
% 1.22/0.51    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 1.22/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).
% 1.22/0.51  fof(f182,plain,(
% 1.22/0.51    ~r2_hidden(sK3(k2_orders_2(sK2,k2_struct_0(sK2))),k2_struct_0(sK2))),
% 1.22/0.51    inference(subsumption_resolution,[],[f181,f128])).
% 1.22/0.51  fof(f181,plain,(
% 1.22/0.51    ~m1_subset_1(sK3(k2_orders_2(sK2,k2_struct_0(sK2))),k2_struct_0(sK2)) | ~r2_hidden(sK3(k2_orders_2(sK2,k2_struct_0(sK2))),k2_struct_0(sK2))),
% 1.22/0.51    inference(forward_demodulation,[],[f180,f79])).
% 1.22/0.51  fof(f180,plain,(
% 1.22/0.51    ~r2_hidden(sK3(k2_orders_2(sK2,k2_struct_0(sK2))),k2_struct_0(sK2)) | ~m1_subset_1(sK3(k2_orders_2(sK2,k2_struct_0(sK2))),u1_struct_0(sK2))),
% 1.22/0.51    inference(subsumption_resolution,[],[f179,f49])).
% 1.22/0.51  fof(f179,plain,(
% 1.22/0.51    ~r2_hidden(sK3(k2_orders_2(sK2,k2_struct_0(sK2))),k2_struct_0(sK2)) | ~m1_subset_1(sK3(k2_orders_2(sK2,k2_struct_0(sK2))),u1_struct_0(sK2)) | ~l1_orders_2(sK2)),
% 1.22/0.51    inference(subsumption_resolution,[],[f177,f128])).
% 1.22/0.51  fof(f177,plain,(
% 1.22/0.51    ~m1_subset_1(sK3(k2_orders_2(sK2,k2_struct_0(sK2))),k2_struct_0(sK2)) | ~r2_hidden(sK3(k2_orders_2(sK2,k2_struct_0(sK2))),k2_struct_0(sK2)) | ~m1_subset_1(sK3(k2_orders_2(sK2,k2_struct_0(sK2))),u1_struct_0(sK2)) | ~l1_orders_2(sK2)),
% 1.22/0.51    inference(resolution,[],[f125,f77])).
% 1.22/0.51  fof(f77,plain,(
% 1.22/0.51    ( ! [X2,X0] : (~r2_orders_2(X0,X2,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 1.22/0.51    inference(duplicate_literal_removal,[],[f73])).
% 1.22/0.51  fof(f73,plain,(
% 1.22/0.51    ( ! [X2,X0] : (~r2_orders_2(X0,X2,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 1.22/0.51    inference(equality_resolution,[],[f55])).
% 1.22/0.51  fof(f55,plain,(
% 1.22/0.51    ( ! [X2,X0,X1] : (X1 != X2 | ~r2_orders_2(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 1.22/0.51    inference(cnf_transformation,[],[f35])).
% 1.22/0.51  fof(f35,plain,(
% 1.22/0.51    ! [X0] : (! [X1] : (! [X2] : (((r2_orders_2(X0,X1,X2) | X1 = X2 | ~r1_orders_2(X0,X1,X2)) & ((X1 != X2 & r1_orders_2(X0,X1,X2)) | ~r2_orders_2(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 1.22/0.51    inference(flattening,[],[f34])).
% 1.22/0.51  fof(f34,plain,(
% 1.22/0.51    ! [X0] : (! [X1] : (! [X2] : (((r2_orders_2(X0,X1,X2) | (X1 = X2 | ~r1_orders_2(X0,X1,X2))) & ((X1 != X2 & r1_orders_2(X0,X1,X2)) | ~r2_orders_2(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 1.22/0.51    inference(nnf_transformation,[],[f18])).
% 1.22/0.51  fof(f18,plain,(
% 1.22/0.51    ! [X0] : (! [X1] : (! [X2] : ((r2_orders_2(X0,X1,X2) <=> (X1 != X2 & r1_orders_2(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 1.22/0.51    inference(ennf_transformation,[],[f6])).
% 1.22/0.51  fof(f6,axiom,(
% 1.22/0.51    ! [X0] : (l1_orders_2(X0) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r2_orders_2(X0,X1,X2) <=> (X1 != X2 & r1_orders_2(X0,X1,X2))))))),
% 1.22/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_orders_2)).
% 1.22/0.51  fof(f125,plain,(
% 1.22/0.51    ( ! [X0] : (r2_orders_2(sK2,sK3(k2_orders_2(sK2,k2_struct_0(sK2))),X0) | ~m1_subset_1(X0,k2_struct_0(sK2)) | ~r2_hidden(X0,k2_struct_0(sK2))) )),
% 1.22/0.51    inference(forward_demodulation,[],[f124,f122])).
% 1.22/0.51  fof(f124,plain,(
% 1.22/0.51    ( ! [X0] : (r2_orders_2(sK2,sK5(sK2,k2_struct_0(sK2),sK3(k2_orders_2(sK2,k2_struct_0(sK2)))),X0) | ~m1_subset_1(X0,k2_struct_0(sK2)) | ~r2_hidden(X0,k2_struct_0(sK2))) )),
% 1.22/0.51    inference(forward_demodulation,[],[f123,f108])).
% 1.22/0.51  fof(f123,plain,(
% 1.22/0.51    ( ! [X0] : (~m1_subset_1(X0,k2_struct_0(sK2)) | ~r2_hidden(X0,k2_struct_0(sK2)) | r2_orders_2(sK2,sK5(sK2,k2_struct_0(sK2),sK3(a_2_1_orders_2(sK2,k2_struct_0(sK2)))),X0)) )),
% 1.22/0.51    inference(subsumption_resolution,[],[f114,f50])).
% 1.22/0.51  fof(f114,plain,(
% 1.22/0.51    ( ! [X0] : (k1_xboole_0 = k2_orders_2(sK2,k2_struct_0(sK2)) | ~m1_subset_1(X0,k2_struct_0(sK2)) | ~r2_hidden(X0,k2_struct_0(sK2)) | r2_orders_2(sK2,sK5(sK2,k2_struct_0(sK2),sK3(a_2_1_orders_2(sK2,k2_struct_0(sK2)))),X0)) )),
% 1.22/0.51    inference(backward_demodulation,[],[f98,f108])).
% 1.22/0.51  fof(f98,plain,(
% 1.22/0.51    ( ! [X0] : (~m1_subset_1(X0,k2_struct_0(sK2)) | k1_xboole_0 = a_2_1_orders_2(sK2,k2_struct_0(sK2)) | ~r2_hidden(X0,k2_struct_0(sK2)) | r2_orders_2(sK2,sK5(sK2,k2_struct_0(sK2),sK3(a_2_1_orders_2(sK2,k2_struct_0(sK2)))),X0)) )),
% 1.22/0.51    inference(forward_demodulation,[],[f95,f79])).
% 1.22/0.51  fof(f95,plain,(
% 1.22/0.51    ( ! [X0] : (k1_xboole_0 = a_2_1_orders_2(sK2,k2_struct_0(sK2)) | ~r2_hidden(X0,k2_struct_0(sK2)) | ~m1_subset_1(X0,u1_struct_0(sK2)) | r2_orders_2(sK2,sK5(sK2,k2_struct_0(sK2),sK3(a_2_1_orders_2(sK2,k2_struct_0(sK2)))),X0)) )),
% 1.22/0.51    inference(resolution,[],[f91,f67])).
% 1.22/0.51  fof(f67,plain,(
% 1.22/0.51    ( ! [X6,X2,X0,X1] : (~sP0(X0,X1,X2) | ~r2_hidden(X6,X1) | ~m1_subset_1(X6,u1_struct_0(X0)) | r2_orders_2(X0,sK5(X0,X1,X2),X6)) )),
% 1.22/0.51    inference(cnf_transformation,[],[f44])).
% 1.22/0.51  fof(f143,plain,(
% 1.22/0.51    r2_hidden(sK3(k2_orders_2(sK2,k2_struct_0(sK2))),k2_orders_2(sK2,k2_struct_0(sK2)))),
% 1.22/0.51    inference(resolution,[],[f132,f118])).
% 1.22/0.51  fof(f118,plain,(
% 1.22/0.51    sP0(sK2,k2_struct_0(sK2),sK3(k2_orders_2(sK2,k2_struct_0(sK2))))),
% 1.22/0.51    inference(subsumption_resolution,[],[f117,f50])).
% 1.22/0.51  fof(f117,plain,(
% 1.22/0.51    k1_xboole_0 = k2_orders_2(sK2,k2_struct_0(sK2)) | sP0(sK2,k2_struct_0(sK2),sK3(k2_orders_2(sK2,k2_struct_0(sK2))))),
% 1.22/0.51    inference(forward_demodulation,[],[f110,f108])).
% 1.22/0.51  fof(f110,plain,(
% 1.22/0.51    sP0(sK2,k2_struct_0(sK2),sK3(k2_orders_2(sK2,k2_struct_0(sK2)))) | k1_xboole_0 = a_2_1_orders_2(sK2,k2_struct_0(sK2))),
% 1.22/0.51    inference(backward_demodulation,[],[f91,f108])).
% 1.22/0.51  fof(f132,plain,(
% 1.22/0.51    ( ! [X0] : (~sP0(sK2,k2_struct_0(sK2),X0) | r2_hidden(X0,k2_orders_2(sK2,k2_struct_0(sK2)))) )),
% 1.22/0.51    inference(subsumption_resolution,[],[f131,f89])).
% 1.22/0.51  fof(f131,plain,(
% 1.22/0.51    ( ! [X0] : (r2_hidden(X0,k2_orders_2(sK2,k2_struct_0(sK2))) | ~sP0(sK2,k2_struct_0(sK2),X0) | ~sP1(X0,k2_struct_0(sK2),sK2)) )),
% 1.22/0.51    inference(superposition,[],[f64,f108])).
% 1.22/0.51  fof(f64,plain,(
% 1.22/0.51    ( ! [X2,X0,X1] : (r2_hidden(X0,a_2_1_orders_2(X2,X1)) | ~sP0(X2,X1,X0) | ~sP1(X0,X1,X2)) )),
% 1.22/0.51    inference(cnf_transformation,[],[f39])).
% 1.22/0.51  % SZS output end Proof for theBenchmark
% 1.22/0.51  % (27116)------------------------------
% 1.22/0.51  % (27116)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.22/0.51  % (27116)Termination reason: Refutation
% 1.22/0.51  
% 1.22/0.51  % (27116)Memory used [KB]: 6268
% 1.22/0.51  % (27116)Time elapsed: 0.106 s
% 1.22/0.51  % (27116)------------------------------
% 1.22/0.51  % (27116)------------------------------
% 1.22/0.51  % (27112)Success in time 0.15 s
%------------------------------------------------------------------------------
