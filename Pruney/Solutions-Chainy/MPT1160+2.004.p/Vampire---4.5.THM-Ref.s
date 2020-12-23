%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:10:05 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  120 ( 680 expanded)
%              Number of leaves         :   16 ( 204 expanded)
%              Depth                    :   34
%              Number of atoms          :  602 (3652 expanded)
%              Number of equality atoms :   63 ( 573 expanded)
%              Maximal formula depth    :   15 (   7 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f386,plain,(
    $false ),
    inference(trivial_inequality_removal,[],[f374])).

fof(f374,plain,(
    k1_xboole_0 != k1_xboole_0 ),
    inference(superposition,[],[f73,f373])).

fof(f373,plain,(
    k1_xboole_0 = k3_orders_2(sK0,k1_xboole_0,sK1) ),
    inference(resolution,[],[f369,f71])).

fof(f71,plain,(
    l1_struct_0(sK0) ),
    inference(resolution,[],[f55,f51])).

fof(f51,plain,(
    l1_orders_2(sK0) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,
    ( k1_xboole_0 != k3_orders_2(sK0,k1_struct_0(sK0),sK1)
    & m1_subset_1(sK1,u1_struct_0(sK0))
    & l1_orders_2(sK0)
    & v5_orders_2(sK0)
    & v4_orders_2(sK0)
    & v3_orders_2(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f18,f41,f40])).

fof(f40,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( k1_xboole_0 != k3_orders_2(X0,k1_struct_0(X0),X1)
            & m1_subset_1(X1,u1_struct_0(X0)) )
        & l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( k1_xboole_0 != k3_orders_2(sK0,k1_struct_0(sK0),X1)
          & m1_subset_1(X1,u1_struct_0(sK0)) )
      & l1_orders_2(sK0)
      & v5_orders_2(sK0)
      & v4_orders_2(sK0)
      & v3_orders_2(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f41,plain,
    ( ? [X1] :
        ( k1_xboole_0 != k3_orders_2(sK0,k1_struct_0(sK0),X1)
        & m1_subset_1(X1,u1_struct_0(sK0)) )
   => ( k1_xboole_0 != k3_orders_2(sK0,k1_struct_0(sK0),sK1)
      & m1_subset_1(sK1,u1_struct_0(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,(
    ? [X0] :
      ( ? [X1] :
          ( k1_xboole_0 != k3_orders_2(X0,k1_struct_0(X0),X1)
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_orders_2(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ? [X0] :
      ( ? [X1] :
          ( k1_xboole_0 != k3_orders_2(X0,k1_struct_0(X0),X1)
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_orders_2(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_orders_2(X0)
          & v5_orders_2(X0)
          & v4_orders_2(X0)
          & v3_orders_2(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => k1_xboole_0 = k3_orders_2(X0,k1_struct_0(X0),X1) ) ) ),
    inference(negated_conjecture,[],[f15])).

fof(f15,conjecture,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => k1_xboole_0 = k3_orders_2(X0,k1_struct_0(X0),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_orders_2)).

fof(f55,plain,(
    ! [X0] :
      ( ~ l1_orders_2(X0)
      | l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_orders_2)).

fof(f369,plain,
    ( ~ l1_struct_0(sK0)
    | k1_xboole_0 = k3_orders_2(sK0,k1_xboole_0,sK1) ),
    inference(resolution,[],[f368,f47])).

fof(f47,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f42])).

fof(f368,plain,
    ( v2_struct_0(sK0)
    | k1_xboole_0 = k3_orders_2(sK0,k1_xboole_0,sK1)
    | ~ l1_struct_0(sK0) ),
    inference(duplicate_literal_removal,[],[f367])).

fof(f367,plain,
    ( k1_xboole_0 = k3_orders_2(sK0,k1_xboole_0,sK1)
    | v2_struct_0(sK0)
    | ~ l1_struct_0(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f366,f65])).

fof(f65,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k2_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k2_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k2_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(k2_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc5_struct_0)).

fof(f366,plain,
    ( v1_xboole_0(k2_struct_0(sK0))
    | k1_xboole_0 = k3_orders_2(sK0,k1_xboole_0,sK1)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f365,f54])).

fof(f54,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

fof(f365,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_struct_0(sK0)))
    | k1_xboole_0 = k3_orders_2(sK0,k1_xboole_0,sK1)
    | v1_xboole_0(k2_struct_0(sK0))
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f364,f75])).

fof(f75,plain,(
    m1_subset_1(sK1,k2_struct_0(sK0)) ),
    inference(backward_demodulation,[],[f52,f74])).

fof(f74,plain,(
    u1_struct_0(sK0) = k2_struct_0(sK0) ),
    inference(resolution,[],[f57,f71])).

fof(f57,plain,(
    ! [X0] :
      ( ~ l1_struct_0(X0)
      | k2_struct_0(X0) = u1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k2_struct_0(X0) = u1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).

fof(f52,plain,(
    m1_subset_1(sK1,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f42])).

fof(f364,plain,
    ( ~ m1_subset_1(sK1,k2_struct_0(sK0))
    | v1_xboole_0(k2_struct_0(sK0))
    | k1_xboole_0 = k3_orders_2(sK0,k1_xboole_0,sK1)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_struct_0(sK0)))
    | v2_struct_0(sK0) ),
    inference(duplicate_literal_removal,[],[f363])).

fof(f363,plain,
    ( v2_struct_0(sK0)
    | v1_xboole_0(k2_struct_0(sK0))
    | k1_xboole_0 = k3_orders_2(sK0,k1_xboole_0,sK1)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k2_struct_0(sK0))
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f358,f130])).

fof(f130,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_orders_2(sK0,X0,X1),k1_zfmisc_1(k2_struct_0(sK0)))
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))
      | ~ m1_subset_1(X1,k2_struct_0(sK0))
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f125,f48])).

fof(f48,plain,(
    v3_orders_2(sK0) ),
    inference(cnf_transformation,[],[f42])).

fof(f125,plain,(
    ! [X0,X1] :
      ( ~ v3_orders_2(sK0)
      | m1_subset_1(k3_orders_2(sK0,X1,X0),k1_zfmisc_1(k2_struct_0(sK0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK0)))
      | ~ m1_subset_1(X0,k2_struct_0(sK0))
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f124,f49])).

fof(f49,plain,(
    v4_orders_2(sK0) ),
    inference(cnf_transformation,[],[f42])).

fof(f124,plain,(
    ! [X0,X1] :
      ( ~ v4_orders_2(sK0)
      | ~ m1_subset_1(X1,k2_struct_0(sK0))
      | m1_subset_1(k3_orders_2(sK0,X0,X1),k1_zfmisc_1(k2_struct_0(sK0)))
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))
      | ~ v3_orders_2(sK0)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f108,f50])).

fof(f50,plain,(
    v5_orders_2(sK0) ),
    inference(cnf_transformation,[],[f42])).

fof(f108,plain,(
    ! [X0,X1] :
      ( ~ v5_orders_2(sK0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK0)))
      | ~ m1_subset_1(X0,k2_struct_0(sK0))
      | m1_subset_1(k3_orders_2(sK0,X1,X0),k1_zfmisc_1(k2_struct_0(sK0)))
      | ~ v4_orders_2(sK0)
      | ~ v3_orders_2(sK0)
      | v2_struct_0(sK0) ) ),
    inference(forward_demodulation,[],[f107,f74])).

fof(f107,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK0)))
      | ~ m1_subset_1(X0,k2_struct_0(sK0))
      | m1_subset_1(k3_orders_2(sK0,X1,X0),k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v5_orders_2(sK0)
      | ~ v4_orders_2(sK0)
      | ~ v3_orders_2(sK0)
      | v2_struct_0(sK0) ) ),
    inference(forward_demodulation,[],[f106,f74])).

fof(f106,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k2_struct_0(sK0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | m1_subset_1(k3_orders_2(sK0,X1,X0),k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v5_orders_2(sK0)
      | ~ v4_orders_2(sK0)
      | ~ v3_orders_2(sK0)
      | v2_struct_0(sK0) ) ),
    inference(forward_demodulation,[],[f105,f74])).

fof(f105,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | m1_subset_1(k3_orders_2(sK0,X1,X0),k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v5_orders_2(sK0)
      | ~ v4_orders_2(sK0)
      | ~ v3_orders_2(sK0)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f69,f51])).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_orders_2(X0)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | m1_subset_1(k3_orders_2(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k3_orders_2(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f36])).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k3_orders_2(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => m1_subset_1(k3_orders_2(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_orders_2)).

fof(f358,plain,
    ( ~ m1_subset_1(k3_orders_2(sK0,k1_xboole_0,sK1),k1_zfmisc_1(k2_struct_0(sK0)))
    | v2_struct_0(sK0)
    | v1_xboole_0(k2_struct_0(sK0))
    | k1_xboole_0 = k3_orders_2(sK0,k1_xboole_0,sK1) ),
    inference(duplicate_literal_removal,[],[f352])).

fof(f352,plain,
    ( k1_xboole_0 = k3_orders_2(sK0,k1_xboole_0,sK1)
    | v2_struct_0(sK0)
    | v1_xboole_0(k2_struct_0(sK0))
    | k1_xboole_0 = k3_orders_2(sK0,k1_xboole_0,sK1)
    | ~ m1_subset_1(k3_orders_2(sK0,k1_xboole_0,sK1),k1_zfmisc_1(k2_struct_0(sK0)))
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f346,f188])).

fof(f188,plain,(
    ! [X0] :
      ( ~ r2_hidden(sK2(k2_struct_0(sK0),X0),k1_xboole_0)
      | v1_xboole_0(k2_struct_0(sK0))
      | k1_xboole_0 = X0
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f187,f71])).

fof(f187,plain,(
    ! [X0] :
      ( ~ l1_struct_0(sK0)
      | v1_xboole_0(k2_struct_0(sK0))
      | ~ r2_hidden(sK2(k2_struct_0(sK0),X0),k1_xboole_0)
      | k1_xboole_0 = X0
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f186,f79])).

fof(f79,plain,
    ( m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0)))
    | ~ l1_struct_0(sK0) ),
    inference(superposition,[],[f59,f74])).

fof(f59,plain,(
    ! [X0] :
      ( m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_struct_0)).

fof(f186,plain,(
    ! [X0] :
      ( ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0)))
      | v2_struct_0(sK0)
      | v1_xboole_0(k2_struct_0(sK0))
      | ~ r2_hidden(sK2(k2_struct_0(sK0),X0),k1_xboole_0)
      | k1_xboole_0 = X0
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) ) ),
    inference(forward_demodulation,[],[f185,f91])).

fof(f91,plain,(
    k1_xboole_0 = k2_orders_2(sK0,k2_struct_0(sK0)) ),
    inference(resolution,[],[f90,f47])).

fof(f90,plain,
    ( v2_struct_0(sK0)
    | k1_xboole_0 = k2_orders_2(sK0,k2_struct_0(sK0)) ),
    inference(resolution,[],[f89,f48])).

fof(f89,plain,
    ( ~ v3_orders_2(sK0)
    | k1_xboole_0 = k2_orders_2(sK0,k2_struct_0(sK0))
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f88,f49])).

fof(f88,plain,
    ( ~ v4_orders_2(sK0)
    | k1_xboole_0 = k2_orders_2(sK0,k2_struct_0(sK0))
    | ~ v3_orders_2(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f86,f50])).

fof(f86,plain,
    ( ~ v5_orders_2(sK0)
    | k1_xboole_0 = k2_orders_2(sK0,k2_struct_0(sK0))
    | ~ v4_orders_2(sK0)
    | ~ v3_orders_2(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f60,f51])).

fof(f60,plain,(
    ! [X0] :
      ( ~ l1_orders_2(X0)
      | k1_xboole_0 = k2_orders_2(X0,k2_struct_0(X0))
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( k1_xboole_0 = k2_orders_2(X0,k2_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( k1_xboole_0 = k2_orders_2(X0,k2_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => k1_xboole_0 = k2_orders_2(X0,k2_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_orders_2)).

fof(f185,plain,(
    ! [X0] :
      ( ~ r2_hidden(sK2(k2_struct_0(sK0),X0),k2_orders_2(sK0,k2_struct_0(sK0)))
      | v2_struct_0(sK0)
      | v1_xboole_0(k2_struct_0(sK0))
      | ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0)))
      | k1_xboole_0 = X0
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) ) ),
    inference(duplicate_literal_removal,[],[f182])).

fof(f182,plain,(
    ! [X0] :
      ( ~ r2_hidden(sK2(k2_struct_0(sK0),X0),k2_orders_2(sK0,k2_struct_0(sK0)))
      | v2_struct_0(sK0)
      | v1_xboole_0(k2_struct_0(sK0))
      | ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0)))
      | k1_xboole_0 = X0
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))
      | k1_xboole_0 = X0
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) ) ),
    inference(resolution,[],[f115,f67])).

fof(f67,plain,(
    ! [X0,X1] :
      ( m1_subset_1(sK2(X0,X1),X0)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ( r2_hidden(sK2(X0,X1),X1)
        & m1_subset_1(sK2(X0,X1),X0) )
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f35,f45])).

fof(f45,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( r2_hidden(X2,X1)
          & m1_subset_1(X2,X0) )
     => ( r2_hidden(sK2(X0,X1),X1)
        & m1_subset_1(sK2(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( r2_hidden(X2,X1)
          & m1_subset_1(X2,X0) )
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f34])).

fof(f34,plain,(
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

fof(f115,plain,(
    ! [X2,X1] :
      ( ~ m1_subset_1(sK2(k2_struct_0(sK0),X2),X1)
      | ~ r2_hidden(sK2(k2_struct_0(sK0),X2),k2_orders_2(sK0,X1))
      | v2_struct_0(sK0)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK0)))
      | k1_xboole_0 = X2
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_struct_0(sK0))) ) ),
    inference(resolution,[],[f112,f67])).

fof(f112,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k2_struct_0(sK0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK0)))
      | ~ r2_hidden(X0,k2_orders_2(sK0,X1))
      | v2_struct_0(sK0)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(resolution,[],[f111,f66])).

fof(f66,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
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
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

fof(f111,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ m1_subset_1(X0,k2_struct_0(sK0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK0)))
      | ~ r2_hidden(X0,k2_orders_2(sK0,X1))
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f110,f48])).

fof(f110,plain,(
    ! [X0,X1] :
      ( ~ v3_orders_2(sK0)
      | ~ r2_hidden(X0,k2_orders_2(sK0,X1))
      | ~ m1_subset_1(X0,k2_struct_0(sK0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK0)))
      | ~ r2_hidden(X0,X1)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f109,f49])).

fof(f109,plain,(
    ! [X0,X1] :
      ( ~ v4_orders_2(sK0)
      | ~ r2_hidden(X1,X0)
      | ~ r2_hidden(X1,k2_orders_2(sK0,X0))
      | ~ m1_subset_1(X1,k2_struct_0(sK0))
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))
      | ~ v3_orders_2(sK0)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f94,f50])).

fof(f94,plain,(
    ! [X0,X1] :
      ( ~ v5_orders_2(sK0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK0)))
      | ~ r2_hidden(X0,X1)
      | ~ r2_hidden(X0,k2_orders_2(sK0,X1))
      | ~ m1_subset_1(X0,k2_struct_0(sK0))
      | ~ v4_orders_2(sK0)
      | ~ v3_orders_2(sK0)
      | v2_struct_0(sK0) ) ),
    inference(forward_demodulation,[],[f93,f74])).

fof(f93,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK0)))
      | ~ r2_hidden(X0,X1)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ r2_hidden(X0,k2_orders_2(sK0,X1))
      | ~ v5_orders_2(sK0)
      | ~ v4_orders_2(sK0)
      | ~ v3_orders_2(sK0)
      | v2_struct_0(sK0) ) ),
    inference(forward_demodulation,[],[f92,f74])).

fof(f92,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ r2_hidden(X0,k2_orders_2(sK0,X1))
      | ~ v5_orders_2(sK0)
      | ~ v4_orders_2(sK0)
      | ~ v3_orders_2(sK0)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f64,f51])).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_orders_2(X0)
      | ~ r2_hidden(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ r2_hidden(X1,k2_orders_2(X0,X2))
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ~ r2_hidden(X1,k2_orders_2(X0,X2))
              | ~ r2_hidden(X1,X2)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ~ r2_hidden(X1,k2_orders_2(X0,X2))
              | ~ r2_hidden(X1,X2)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ~ ( r2_hidden(X1,k2_orders_2(X0,X2))
                  & r2_hidden(X1,X2) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_orders_2)).

fof(f346,plain,
    ( r2_hidden(sK2(k2_struct_0(sK0),k3_orders_2(sK0,k1_xboole_0,sK1)),k1_xboole_0)
    | k1_xboole_0 = k3_orders_2(sK0,k1_xboole_0,sK1)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f343,f54])).

fof(f343,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))
      | k1_xboole_0 = k3_orders_2(sK0,X0,sK1)
      | r2_hidden(sK2(k2_struct_0(sK0),k3_orders_2(sK0,X0,sK1)),X0)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f342,f75])).

fof(f342,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k2_struct_0(sK0))
      | v2_struct_0(sK0)
      | k1_xboole_0 = k3_orders_2(sK0,X0,X1)
      | r2_hidden(sK2(k2_struct_0(sK0),k3_orders_2(sK0,X0,X1)),X0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) ) ),
    inference(duplicate_literal_removal,[],[f341])).

fof(f341,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))
      | v2_struct_0(sK0)
      | k1_xboole_0 = k3_orders_2(sK0,X0,X1)
      | r2_hidden(sK2(k2_struct_0(sK0),k3_orders_2(sK0,X0,X1)),X0)
      | ~ m1_subset_1(X1,k2_struct_0(sK0))
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))
      | ~ m1_subset_1(X1,k2_struct_0(sK0))
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f340,f130])).

fof(f340,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(k3_orders_2(sK0,X1,X0),k1_zfmisc_1(k2_struct_0(sK0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK0)))
      | v2_struct_0(sK0)
      | k1_xboole_0 = k3_orders_2(sK0,X1,X0)
      | r2_hidden(sK2(k2_struct_0(sK0),k3_orders_2(sK0,X1,X0)),X1)
      | ~ m1_subset_1(X0,k2_struct_0(sK0)) ) ),
    inference(duplicate_literal_removal,[],[f337])).

fof(f337,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k2_struct_0(sK0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK0)))
      | v2_struct_0(sK0)
      | k1_xboole_0 = k3_orders_2(sK0,X1,X0)
      | r2_hidden(sK2(k2_struct_0(sK0),k3_orders_2(sK0,X1,X0)),X1)
      | k1_xboole_0 = k3_orders_2(sK0,X1,X0)
      | ~ m1_subset_1(k3_orders_2(sK0,X1,X0),k1_zfmisc_1(k2_struct_0(sK0))) ) ),
    inference(resolution,[],[f332,f67])).

fof(f332,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(sK2(k2_struct_0(sK0),k3_orders_2(sK0,X0,X1)),k2_struct_0(sK0))
      | ~ m1_subset_1(X1,k2_struct_0(sK0))
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))
      | v2_struct_0(sK0)
      | k1_xboole_0 = k3_orders_2(sK0,X0,X1)
      | r2_hidden(sK2(k2_struct_0(sK0),k3_orders_2(sK0,X0,X1)),X0) ) ),
    inference(duplicate_literal_removal,[],[f331])).

fof(f331,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(sK2(k2_struct_0(sK0),k3_orders_2(sK0,X0,X1)),k2_struct_0(sK0))
      | ~ m1_subset_1(X1,k2_struct_0(sK0))
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))
      | v2_struct_0(sK0)
      | k1_xboole_0 = k3_orders_2(sK0,X0,X1)
      | r2_hidden(sK2(k2_struct_0(sK0),k3_orders_2(sK0,X0,X1)),X0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))
      | ~ m1_subset_1(X1,k2_struct_0(sK0))
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f148,f130])).

fof(f148,plain,(
    ! [X4,X5,X3] :
      ( ~ m1_subset_1(k3_orders_2(sK0,X4,X5),k1_zfmisc_1(X3))
      | ~ m1_subset_1(sK2(X3,k3_orders_2(sK0,X4,X5)),k2_struct_0(sK0))
      | ~ m1_subset_1(X5,k2_struct_0(sK0))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_struct_0(sK0)))
      | v2_struct_0(sK0)
      | k1_xboole_0 = k3_orders_2(sK0,X4,X5)
      | r2_hidden(sK2(X3,k3_orders_2(sK0,X4,X5)),X4) ) ),
    inference(resolution,[],[f145,f68])).

fof(f68,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK2(X0,X1),X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f145,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k3_orders_2(sK0,X1,X2))
      | r2_hidden(X0,X1)
      | ~ m1_subset_1(X0,k2_struct_0(sK0))
      | ~ m1_subset_1(X2,k2_struct_0(sK0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK0)))
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f144,f48])).

fof(f144,plain,(
    ! [X2,X0,X1] :
      ( ~ v3_orders_2(sK0)
      | ~ r2_hidden(X1,k3_orders_2(sK0,X0,X2))
      | r2_hidden(X1,X0)
      | ~ m1_subset_1(X1,k2_struct_0(sK0))
      | ~ m1_subset_1(X2,k2_struct_0(sK0))
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f143,f49])).

fof(f143,plain,(
    ! [X2,X0,X1] :
      ( ~ v4_orders_2(sK0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK0)))
      | ~ r2_hidden(X2,k3_orders_2(sK0,X1,X0))
      | r2_hidden(X2,X1)
      | ~ m1_subset_1(X2,k2_struct_0(sK0))
      | ~ m1_subset_1(X0,k2_struct_0(sK0))
      | ~ v3_orders_2(sK0)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f120,f50])).

fof(f120,plain,(
    ! [X2,X0,X1] :
      ( ~ v5_orders_2(sK0)
      | ~ m1_subset_1(X2,k2_struct_0(sK0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK0)))
      | ~ r2_hidden(X0,k3_orders_2(sK0,X1,X2))
      | r2_hidden(X0,X1)
      | ~ m1_subset_1(X0,k2_struct_0(sK0))
      | ~ v4_orders_2(sK0)
      | ~ v3_orders_2(sK0)
      | v2_struct_0(sK0) ) ),
    inference(forward_demodulation,[],[f119,f74])).

fof(f119,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k2_struct_0(sK0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK0)))
      | ~ r2_hidden(X0,k3_orders_2(sK0,X1,X2))
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | r2_hidden(X0,X1)
      | ~ v5_orders_2(sK0)
      | ~ v4_orders_2(sK0)
      | ~ v3_orders_2(sK0)
      | v2_struct_0(sK0) ) ),
    inference(forward_demodulation,[],[f118,f74])).

fof(f118,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK0)))
      | ~ r2_hidden(X0,k3_orders_2(sK0,X1,X2))
      | ~ m1_subset_1(X2,u1_struct_0(sK0))
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | r2_hidden(X0,X1)
      | ~ v5_orders_2(sK0)
      | ~ v4_orders_2(sK0)
      | ~ v3_orders_2(sK0)
      | v2_struct_0(sK0) ) ),
    inference(forward_demodulation,[],[f117,f74])).

fof(f117,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k3_orders_2(sK0,X1,X2))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X2,u1_struct_0(sK0))
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | r2_hidden(X0,X1)
      | ~ v5_orders_2(sK0)
      | ~ v4_orders_2(sK0)
      | ~ v3_orders_2(sK0)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f62,f51])).

fof(f62,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ l1_orders_2(X0)
      | ~ r2_hidden(X1,k3_orders_2(X0,X3,X2))
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | r2_hidden(X1,X3)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ( r2_hidden(X1,k3_orders_2(X0,X3,X2))
                      | ~ r2_hidden(X1,X3)
                      | ~ r2_orders_2(X0,X1,X2) )
                    & ( ( r2_hidden(X1,X3)
                        & r2_orders_2(X0,X1,X2) )
                      | ~ r2_hidden(X1,k3_orders_2(X0,X3,X2)) ) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f43])).

fof(f43,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ( r2_hidden(X1,k3_orders_2(X0,X3,X2))
                      | ~ r2_hidden(X1,X3)
                      | ~ r2_orders_2(X0,X1,X2) )
                    & ( ( r2_hidden(X1,X3)
                        & r2_orders_2(X0,X1,X2) )
                      | ~ r2_hidden(X1,k3_orders_2(X0,X3,X2)) ) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( r2_hidden(X1,k3_orders_2(X0,X3,X2))
                  <=> ( r2_hidden(X1,X3)
                      & r2_orders_2(X0,X1,X2) ) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( r2_hidden(X1,k3_orders_2(X0,X3,X2))
                  <=> ( r2_hidden(X1,X3)
                      & r2_orders_2(X0,X1,X2) ) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ! [X3] :
                  ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                 => ( r2_hidden(X1,k3_orders_2(X0,X3,X2))
                  <=> ( r2_hidden(X1,X3)
                      & r2_orders_2(X0,X1,X2) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t57_orders_2)).

fof(f73,plain,(
    k1_xboole_0 != k3_orders_2(sK0,k1_xboole_0,sK1) ),
    inference(backward_demodulation,[],[f53,f72])).

fof(f72,plain,(
    k1_xboole_0 = k1_struct_0(sK0) ),
    inference(resolution,[],[f56,f71])).

fof(f56,plain,(
    ! [X0] :
      ( ~ l1_struct_0(X0)
      | k1_xboole_0 = k1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( k1_xboole_0 = k1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k1_xboole_0 = k1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_struct_0)).

fof(f53,plain,(
    k1_xboole_0 != k3_orders_2(sK0,k1_struct_0(sK0),sK1) ),
    inference(cnf_transformation,[],[f42])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n003.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 12:05:42 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.43  % (11238)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_142 on theBenchmark
% 0.21/0.46  % (11238)Refutation found. Thanks to Tanya!
% 0.21/0.46  % SZS status Theorem for theBenchmark
% 0.21/0.46  % SZS output start Proof for theBenchmark
% 0.21/0.46  fof(f386,plain,(
% 0.21/0.46    $false),
% 0.21/0.46    inference(trivial_inequality_removal,[],[f374])).
% 0.21/0.46  fof(f374,plain,(
% 0.21/0.46    k1_xboole_0 != k1_xboole_0),
% 0.21/0.46    inference(superposition,[],[f73,f373])).
% 0.21/0.46  fof(f373,plain,(
% 0.21/0.46    k1_xboole_0 = k3_orders_2(sK0,k1_xboole_0,sK1)),
% 0.21/0.46    inference(resolution,[],[f369,f71])).
% 0.21/0.46  fof(f71,plain,(
% 0.21/0.46    l1_struct_0(sK0)),
% 0.21/0.46    inference(resolution,[],[f55,f51])).
% 0.21/0.46  fof(f51,plain,(
% 0.21/0.46    l1_orders_2(sK0)),
% 0.21/0.46    inference(cnf_transformation,[],[f42])).
% 0.21/0.46  fof(f42,plain,(
% 0.21/0.46    (k1_xboole_0 != k3_orders_2(sK0,k1_struct_0(sK0),sK1) & m1_subset_1(sK1,u1_struct_0(sK0))) & l1_orders_2(sK0) & v5_orders_2(sK0) & v4_orders_2(sK0) & v3_orders_2(sK0) & ~v2_struct_0(sK0)),
% 0.21/0.46    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f18,f41,f40])).
% 0.21/0.46  fof(f40,plain,(
% 0.21/0.46    ? [X0] : (? [X1] : (k1_xboole_0 != k3_orders_2(X0,k1_struct_0(X0),X1) & m1_subset_1(X1,u1_struct_0(X0))) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => (? [X1] : (k1_xboole_0 != k3_orders_2(sK0,k1_struct_0(sK0),X1) & m1_subset_1(X1,u1_struct_0(sK0))) & l1_orders_2(sK0) & v5_orders_2(sK0) & v4_orders_2(sK0) & v3_orders_2(sK0) & ~v2_struct_0(sK0))),
% 0.21/0.46    introduced(choice_axiom,[])).
% 0.21/0.46  fof(f41,plain,(
% 0.21/0.46    ? [X1] : (k1_xboole_0 != k3_orders_2(sK0,k1_struct_0(sK0),X1) & m1_subset_1(X1,u1_struct_0(sK0))) => (k1_xboole_0 != k3_orders_2(sK0,k1_struct_0(sK0),sK1) & m1_subset_1(sK1,u1_struct_0(sK0)))),
% 0.21/0.46    introduced(choice_axiom,[])).
% 0.21/0.46  fof(f18,plain,(
% 0.21/0.46    ? [X0] : (? [X1] : (k1_xboole_0 != k3_orders_2(X0,k1_struct_0(X0),X1) & m1_subset_1(X1,u1_struct_0(X0))) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0))),
% 0.21/0.46    inference(flattening,[],[f17])).
% 0.21/0.46  fof(f17,plain,(
% 0.21/0.46    ? [X0] : (? [X1] : (k1_xboole_0 != k3_orders_2(X0,k1_struct_0(X0),X1) & m1_subset_1(X1,u1_struct_0(X0))) & (l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)))),
% 0.21/0.46    inference(ennf_transformation,[],[f16])).
% 0.21/0.46  fof(f16,negated_conjecture,(
% 0.21/0.46    ~! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => k1_xboole_0 = k3_orders_2(X0,k1_struct_0(X0),X1)))),
% 0.21/0.46    inference(negated_conjecture,[],[f15])).
% 0.21/0.46  fof(f15,conjecture,(
% 0.21/0.46    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => k1_xboole_0 = k3_orders_2(X0,k1_struct_0(X0),X1)))),
% 0.21/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_orders_2)).
% 0.21/0.46  fof(f55,plain,(
% 0.21/0.46    ( ! [X0] : (~l1_orders_2(X0) | l1_struct_0(X0)) )),
% 0.21/0.46    inference(cnf_transformation,[],[f19])).
% 0.21/0.46  fof(f19,plain,(
% 0.21/0.46    ! [X0] : (l1_struct_0(X0) | ~l1_orders_2(X0))),
% 0.21/0.46    inference(ennf_transformation,[],[f11])).
% 0.21/0.46  fof(f11,axiom,(
% 0.21/0.46    ! [X0] : (l1_orders_2(X0) => l1_struct_0(X0))),
% 0.21/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_orders_2)).
% 0.21/0.46  fof(f369,plain,(
% 0.21/0.46    ~l1_struct_0(sK0) | k1_xboole_0 = k3_orders_2(sK0,k1_xboole_0,sK1)),
% 0.21/0.46    inference(resolution,[],[f368,f47])).
% 0.21/0.46  fof(f47,plain,(
% 0.21/0.46    ~v2_struct_0(sK0)),
% 0.21/0.46    inference(cnf_transformation,[],[f42])).
% 0.21/0.46  fof(f368,plain,(
% 0.21/0.46    v2_struct_0(sK0) | k1_xboole_0 = k3_orders_2(sK0,k1_xboole_0,sK1) | ~l1_struct_0(sK0)),
% 0.21/0.46    inference(duplicate_literal_removal,[],[f367])).
% 0.21/0.46  fof(f367,plain,(
% 0.21/0.46    k1_xboole_0 = k3_orders_2(sK0,k1_xboole_0,sK1) | v2_struct_0(sK0) | ~l1_struct_0(sK0) | v2_struct_0(sK0)),
% 0.21/0.46    inference(resolution,[],[f366,f65])).
% 0.21/0.46  fof(f65,plain,(
% 0.21/0.46    ( ! [X0] : (~v1_xboole_0(k2_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 0.21/0.46    inference(cnf_transformation,[],[f31])).
% 0.21/0.46  fof(f31,plain,(
% 0.21/0.46    ! [X0] : (~v1_xboole_0(k2_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 0.21/0.46    inference(flattening,[],[f30])).
% 0.21/0.46  fof(f30,plain,(
% 0.21/0.46    ! [X0] : (~v1_xboole_0(k2_struct_0(X0)) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 0.21/0.46    inference(ennf_transformation,[],[f9])).
% 0.21/0.46  fof(f9,axiom,(
% 0.21/0.46    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ~v1_xboole_0(k2_struct_0(X0)))),
% 0.21/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc5_struct_0)).
% 0.21/0.46  fof(f366,plain,(
% 0.21/0.46    v1_xboole_0(k2_struct_0(sK0)) | k1_xboole_0 = k3_orders_2(sK0,k1_xboole_0,sK1) | v2_struct_0(sK0)),
% 0.21/0.46    inference(resolution,[],[f365,f54])).
% 0.21/0.46  fof(f54,plain,(
% 0.21/0.46    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 0.21/0.46    inference(cnf_transformation,[],[f2])).
% 0.21/0.46  fof(f2,axiom,(
% 0.21/0.46    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 0.21/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).
% 0.21/0.46  fof(f365,plain,(
% 0.21/0.46    ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_struct_0(sK0))) | k1_xboole_0 = k3_orders_2(sK0,k1_xboole_0,sK1) | v1_xboole_0(k2_struct_0(sK0)) | v2_struct_0(sK0)),
% 0.21/0.46    inference(resolution,[],[f364,f75])).
% 0.21/0.46  fof(f75,plain,(
% 0.21/0.46    m1_subset_1(sK1,k2_struct_0(sK0))),
% 0.21/0.46    inference(backward_demodulation,[],[f52,f74])).
% 0.21/0.46  fof(f74,plain,(
% 0.21/0.46    u1_struct_0(sK0) = k2_struct_0(sK0)),
% 0.21/0.46    inference(resolution,[],[f57,f71])).
% 0.21/0.46  fof(f57,plain,(
% 0.21/0.46    ( ! [X0] : (~l1_struct_0(X0) | k2_struct_0(X0) = u1_struct_0(X0)) )),
% 0.21/0.46    inference(cnf_transformation,[],[f21])).
% 0.21/0.46  fof(f21,plain,(
% 0.21/0.46    ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0))),
% 0.21/0.46    inference(ennf_transformation,[],[f6])).
% 0.21/0.46  fof(f6,axiom,(
% 0.21/0.46    ! [X0] : (l1_struct_0(X0) => k2_struct_0(X0) = u1_struct_0(X0))),
% 0.21/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).
% 0.21/0.46  fof(f52,plain,(
% 0.21/0.46    m1_subset_1(sK1,u1_struct_0(sK0))),
% 0.21/0.46    inference(cnf_transformation,[],[f42])).
% 0.21/0.46  fof(f364,plain,(
% 0.21/0.46    ~m1_subset_1(sK1,k2_struct_0(sK0)) | v1_xboole_0(k2_struct_0(sK0)) | k1_xboole_0 = k3_orders_2(sK0,k1_xboole_0,sK1) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_struct_0(sK0))) | v2_struct_0(sK0)),
% 0.21/0.46    inference(duplicate_literal_removal,[],[f363])).
% 0.21/0.46  fof(f363,plain,(
% 0.21/0.46    v2_struct_0(sK0) | v1_xboole_0(k2_struct_0(sK0)) | k1_xboole_0 = k3_orders_2(sK0,k1_xboole_0,sK1) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_struct_0(sK0))) | ~m1_subset_1(sK1,k2_struct_0(sK0)) | v2_struct_0(sK0)),
% 0.21/0.46    inference(resolution,[],[f358,f130])).
% 0.21/0.46  fof(f130,plain,(
% 0.21/0.46    ( ! [X0,X1] : (m1_subset_1(k3_orders_2(sK0,X0,X1),k1_zfmisc_1(k2_struct_0(sK0))) | ~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) | ~m1_subset_1(X1,k2_struct_0(sK0)) | v2_struct_0(sK0)) )),
% 0.21/0.46    inference(resolution,[],[f125,f48])).
% 0.21/0.46  fof(f48,plain,(
% 0.21/0.46    v3_orders_2(sK0)),
% 0.21/0.46    inference(cnf_transformation,[],[f42])).
% 0.21/0.46  fof(f125,plain,(
% 0.21/0.46    ( ! [X0,X1] : (~v3_orders_2(sK0) | m1_subset_1(k3_orders_2(sK0,X1,X0),k1_zfmisc_1(k2_struct_0(sK0))) | ~m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK0))) | ~m1_subset_1(X0,k2_struct_0(sK0)) | v2_struct_0(sK0)) )),
% 0.21/0.46    inference(resolution,[],[f124,f49])).
% 0.21/0.46  fof(f49,plain,(
% 0.21/0.46    v4_orders_2(sK0)),
% 0.21/0.46    inference(cnf_transformation,[],[f42])).
% 0.21/0.46  fof(f124,plain,(
% 0.21/0.46    ( ! [X0,X1] : (~v4_orders_2(sK0) | ~m1_subset_1(X1,k2_struct_0(sK0)) | m1_subset_1(k3_orders_2(sK0,X0,X1),k1_zfmisc_1(k2_struct_0(sK0))) | ~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) | ~v3_orders_2(sK0) | v2_struct_0(sK0)) )),
% 0.21/0.46    inference(resolution,[],[f108,f50])).
% 0.21/0.46  fof(f50,plain,(
% 0.21/0.46    v5_orders_2(sK0)),
% 0.21/0.46    inference(cnf_transformation,[],[f42])).
% 0.21/0.46  fof(f108,plain,(
% 0.21/0.46    ( ! [X0,X1] : (~v5_orders_2(sK0) | ~m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK0))) | ~m1_subset_1(X0,k2_struct_0(sK0)) | m1_subset_1(k3_orders_2(sK0,X1,X0),k1_zfmisc_1(k2_struct_0(sK0))) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0)) )),
% 0.21/0.46    inference(forward_demodulation,[],[f107,f74])).
% 0.21/0.46  fof(f107,plain,(
% 0.21/0.46    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK0))) | ~m1_subset_1(X0,k2_struct_0(sK0)) | m1_subset_1(k3_orders_2(sK0,X1,X0),k1_zfmisc_1(u1_struct_0(sK0))) | ~v5_orders_2(sK0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0)) )),
% 0.21/0.46    inference(forward_demodulation,[],[f106,f74])).
% 0.21/0.46  fof(f106,plain,(
% 0.21/0.46    ( ! [X0,X1] : (~m1_subset_1(X0,k2_struct_0(sK0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | m1_subset_1(k3_orders_2(sK0,X1,X0),k1_zfmisc_1(u1_struct_0(sK0))) | ~v5_orders_2(sK0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0)) )),
% 0.21/0.46    inference(forward_demodulation,[],[f105,f74])).
% 0.21/0.46  fof(f105,plain,(
% 0.21/0.46    ( ! [X0,X1] : (~m1_subset_1(X0,u1_struct_0(sK0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | m1_subset_1(k3_orders_2(sK0,X1,X0),k1_zfmisc_1(u1_struct_0(sK0))) | ~v5_orders_2(sK0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0)) )),
% 0.21/0.46    inference(resolution,[],[f69,f51])).
% 0.21/0.46  fof(f69,plain,(
% 0.21/0.46    ( ! [X2,X0,X1] : (~l1_orders_2(X0) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | m1_subset_1(k3_orders_2(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 0.21/0.46    inference(cnf_transformation,[],[f37])).
% 0.21/0.46  fof(f37,plain,(
% 0.21/0.46    ! [X0,X1,X2] : (m1_subset_1(k3_orders_2(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 0.21/0.46    inference(flattening,[],[f36])).
% 0.21/0.46  fof(f36,plain,(
% 0.21/0.46    ! [X0,X1,X2] : (m1_subset_1(k3_orders_2(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 0.21/0.46    inference(ennf_transformation,[],[f10])).
% 0.21/0.46  fof(f10,axiom,(
% 0.21/0.46    ! [X0,X1,X2] : ((m1_subset_1(X2,u1_struct_0(X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => m1_subset_1(k3_orders_2(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))))),
% 0.21/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_orders_2)).
% 0.21/0.46  fof(f358,plain,(
% 0.21/0.46    ~m1_subset_1(k3_orders_2(sK0,k1_xboole_0,sK1),k1_zfmisc_1(k2_struct_0(sK0))) | v2_struct_0(sK0) | v1_xboole_0(k2_struct_0(sK0)) | k1_xboole_0 = k3_orders_2(sK0,k1_xboole_0,sK1)),
% 0.21/0.46    inference(duplicate_literal_removal,[],[f352])).
% 0.21/0.46  fof(f352,plain,(
% 0.21/0.46    k1_xboole_0 = k3_orders_2(sK0,k1_xboole_0,sK1) | v2_struct_0(sK0) | v1_xboole_0(k2_struct_0(sK0)) | k1_xboole_0 = k3_orders_2(sK0,k1_xboole_0,sK1) | ~m1_subset_1(k3_orders_2(sK0,k1_xboole_0,sK1),k1_zfmisc_1(k2_struct_0(sK0))) | v2_struct_0(sK0)),
% 0.21/0.46    inference(resolution,[],[f346,f188])).
% 0.21/0.46  fof(f188,plain,(
% 0.21/0.46    ( ! [X0] : (~r2_hidden(sK2(k2_struct_0(sK0),X0),k1_xboole_0) | v1_xboole_0(k2_struct_0(sK0)) | k1_xboole_0 = X0 | ~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) | v2_struct_0(sK0)) )),
% 0.21/0.46    inference(resolution,[],[f187,f71])).
% 0.21/0.46  fof(f187,plain,(
% 0.21/0.46    ( ! [X0] : (~l1_struct_0(sK0) | v1_xboole_0(k2_struct_0(sK0)) | ~r2_hidden(sK2(k2_struct_0(sK0),X0),k1_xboole_0) | k1_xboole_0 = X0 | ~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) | v2_struct_0(sK0)) )),
% 0.21/0.46    inference(resolution,[],[f186,f79])).
% 0.21/0.46  fof(f79,plain,(
% 0.21/0.46    m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0))) | ~l1_struct_0(sK0)),
% 0.21/0.46    inference(superposition,[],[f59,f74])).
% 0.21/0.46  fof(f59,plain,(
% 0.21/0.46    ( ! [X0] : (m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0))) | ~l1_struct_0(X0)) )),
% 0.21/0.46    inference(cnf_transformation,[],[f23])).
% 0.21/0.46  fof(f23,plain,(
% 0.21/0.46    ! [X0] : (m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0))) | ~l1_struct_0(X0))),
% 0.21/0.46    inference(ennf_transformation,[],[f8])).
% 0.21/0.46  fof(f8,axiom,(
% 0.21/0.46    ! [X0] : (l1_struct_0(X0) => m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0))))),
% 0.21/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_struct_0)).
% 0.21/0.46  fof(f186,plain,(
% 0.21/0.46    ( ! [X0] : (~m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0))) | v2_struct_0(sK0) | v1_xboole_0(k2_struct_0(sK0)) | ~r2_hidden(sK2(k2_struct_0(sK0),X0),k1_xboole_0) | k1_xboole_0 = X0 | ~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))) )),
% 0.21/0.46    inference(forward_demodulation,[],[f185,f91])).
% 0.21/0.46  fof(f91,plain,(
% 0.21/0.46    k1_xboole_0 = k2_orders_2(sK0,k2_struct_0(sK0))),
% 0.21/0.46    inference(resolution,[],[f90,f47])).
% 0.21/0.46  fof(f90,plain,(
% 0.21/0.46    v2_struct_0(sK0) | k1_xboole_0 = k2_orders_2(sK0,k2_struct_0(sK0))),
% 0.21/0.46    inference(resolution,[],[f89,f48])).
% 0.21/0.46  fof(f89,plain,(
% 0.21/0.46    ~v3_orders_2(sK0) | k1_xboole_0 = k2_orders_2(sK0,k2_struct_0(sK0)) | v2_struct_0(sK0)),
% 0.21/0.46    inference(resolution,[],[f88,f49])).
% 0.21/0.46  fof(f88,plain,(
% 0.21/0.46    ~v4_orders_2(sK0) | k1_xboole_0 = k2_orders_2(sK0,k2_struct_0(sK0)) | ~v3_orders_2(sK0) | v2_struct_0(sK0)),
% 0.21/0.46    inference(resolution,[],[f86,f50])).
% 0.21/0.46  fof(f86,plain,(
% 0.21/0.46    ~v5_orders_2(sK0) | k1_xboole_0 = k2_orders_2(sK0,k2_struct_0(sK0)) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0)),
% 0.21/0.46    inference(resolution,[],[f60,f51])).
% 0.21/0.46  fof(f60,plain,(
% 0.21/0.46    ( ! [X0] : (~l1_orders_2(X0) | k1_xboole_0 = k2_orders_2(X0,k2_struct_0(X0)) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 0.21/0.46    inference(cnf_transformation,[],[f25])).
% 0.21/0.46  fof(f25,plain,(
% 0.21/0.46    ! [X0] : (k1_xboole_0 = k2_orders_2(X0,k2_struct_0(X0)) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 0.21/0.46    inference(flattening,[],[f24])).
% 0.21/0.46  fof(f24,plain,(
% 0.21/0.46    ! [X0] : (k1_xboole_0 = k2_orders_2(X0,k2_struct_0(X0)) | (~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 0.21/0.46    inference(ennf_transformation,[],[f12])).
% 0.21/0.46  fof(f12,axiom,(
% 0.21/0.46    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => k1_xboole_0 = k2_orders_2(X0,k2_struct_0(X0)))),
% 0.21/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_orders_2)).
% 0.21/0.46  fof(f185,plain,(
% 0.21/0.46    ( ! [X0] : (~r2_hidden(sK2(k2_struct_0(sK0),X0),k2_orders_2(sK0,k2_struct_0(sK0))) | v2_struct_0(sK0) | v1_xboole_0(k2_struct_0(sK0)) | ~m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0))) | k1_xboole_0 = X0 | ~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))) )),
% 0.21/0.46    inference(duplicate_literal_removal,[],[f182])).
% 0.21/0.46  fof(f182,plain,(
% 0.21/0.46    ( ! [X0] : (~r2_hidden(sK2(k2_struct_0(sK0),X0),k2_orders_2(sK0,k2_struct_0(sK0))) | v2_struct_0(sK0) | v1_xboole_0(k2_struct_0(sK0)) | ~m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0))) | k1_xboole_0 = X0 | ~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) | k1_xboole_0 = X0 | ~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))) )),
% 0.21/0.46    inference(resolution,[],[f115,f67])).
% 0.21/0.46  fof(f67,plain,(
% 0.21/0.46    ( ! [X0,X1] : (m1_subset_1(sK2(X0,X1),X0) | k1_xboole_0 = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.21/0.46    inference(cnf_transformation,[],[f46])).
% 0.21/0.46  fof(f46,plain,(
% 0.21/0.46    ! [X0,X1] : ((r2_hidden(sK2(X0,X1),X1) & m1_subset_1(sK2(X0,X1),X0)) | k1_xboole_0 = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.21/0.46    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f35,f45])).
% 0.21/0.46  fof(f45,plain,(
% 0.21/0.46    ! [X1,X0] : (? [X2] : (r2_hidden(X2,X1) & m1_subset_1(X2,X0)) => (r2_hidden(sK2(X0,X1),X1) & m1_subset_1(sK2(X0,X1),X0)))),
% 0.21/0.46    introduced(choice_axiom,[])).
% 0.21/0.46  fof(f35,plain,(
% 0.21/0.46    ! [X0,X1] : (? [X2] : (r2_hidden(X2,X1) & m1_subset_1(X2,X0)) | k1_xboole_0 = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.21/0.46    inference(flattening,[],[f34])).
% 0.21/0.46  fof(f34,plain,(
% 0.21/0.46    ! [X0,X1] : ((? [X2] : (r2_hidden(X2,X1) & m1_subset_1(X2,X0)) | k1_xboole_0 = X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.21/0.46    inference(ennf_transformation,[],[f1])).
% 0.21/0.46  fof(f1,axiom,(
% 0.21/0.46    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ~(! [X2] : (m1_subset_1(X2,X0) => ~r2_hidden(X2,X1)) & k1_xboole_0 != X1))),
% 0.21/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_subset_1)).
% 0.21/0.46  fof(f115,plain,(
% 0.21/0.46    ( ! [X2,X1] : (~m1_subset_1(sK2(k2_struct_0(sK0),X2),X1) | ~r2_hidden(sK2(k2_struct_0(sK0),X2),k2_orders_2(sK0,X1)) | v2_struct_0(sK0) | v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK0))) | k1_xboole_0 = X2 | ~m1_subset_1(X2,k1_zfmisc_1(k2_struct_0(sK0)))) )),
% 0.21/0.46    inference(resolution,[],[f112,f67])).
% 0.21/0.46  fof(f112,plain,(
% 0.21/0.46    ( ! [X0,X1] : (~m1_subset_1(X0,k2_struct_0(sK0)) | ~m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK0))) | ~r2_hidden(X0,k2_orders_2(sK0,X1)) | v2_struct_0(sK0) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1)) )),
% 0.21/0.46    inference(resolution,[],[f111,f66])).
% 0.21/0.46  fof(f66,plain,(
% 0.21/0.46    ( ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1)) )),
% 0.21/0.46    inference(cnf_transformation,[],[f33])).
% 0.21/0.46  fof(f33,plain,(
% 0.21/0.46    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 0.21/0.46    inference(flattening,[],[f32])).
% 0.21/0.46  fof(f32,plain,(
% 0.21/0.46    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 0.21/0.46    inference(ennf_transformation,[],[f3])).
% 0.21/0.46  fof(f3,axiom,(
% 0.21/0.46    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 0.21/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).
% 0.21/0.46  fof(f111,plain,(
% 0.21/0.46    ( ! [X0,X1] : (~r2_hidden(X0,X1) | ~m1_subset_1(X0,k2_struct_0(sK0)) | ~m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK0))) | ~r2_hidden(X0,k2_orders_2(sK0,X1)) | v2_struct_0(sK0)) )),
% 0.21/0.46    inference(resolution,[],[f110,f48])).
% 0.21/0.46  fof(f110,plain,(
% 0.21/0.46    ( ! [X0,X1] : (~v3_orders_2(sK0) | ~r2_hidden(X0,k2_orders_2(sK0,X1)) | ~m1_subset_1(X0,k2_struct_0(sK0)) | ~m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK0))) | ~r2_hidden(X0,X1) | v2_struct_0(sK0)) )),
% 0.21/0.46    inference(resolution,[],[f109,f49])).
% 0.21/0.46  fof(f109,plain,(
% 0.21/0.46    ( ! [X0,X1] : (~v4_orders_2(sK0) | ~r2_hidden(X1,X0) | ~r2_hidden(X1,k2_orders_2(sK0,X0)) | ~m1_subset_1(X1,k2_struct_0(sK0)) | ~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) | ~v3_orders_2(sK0) | v2_struct_0(sK0)) )),
% 0.21/0.46    inference(resolution,[],[f94,f50])).
% 0.21/0.46  fof(f94,plain,(
% 0.21/0.46    ( ! [X0,X1] : (~v5_orders_2(sK0) | ~m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK0))) | ~r2_hidden(X0,X1) | ~r2_hidden(X0,k2_orders_2(sK0,X1)) | ~m1_subset_1(X0,k2_struct_0(sK0)) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0)) )),
% 0.21/0.46    inference(forward_demodulation,[],[f93,f74])).
% 0.21/0.46  fof(f93,plain,(
% 0.21/0.46    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK0))) | ~r2_hidden(X0,X1) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~r2_hidden(X0,k2_orders_2(sK0,X1)) | ~v5_orders_2(sK0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0)) )),
% 0.21/0.46    inference(forward_demodulation,[],[f92,f74])).
% 0.21/0.46  fof(f92,plain,(
% 0.21/0.46    ( ! [X0,X1] : (~r2_hidden(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~r2_hidden(X0,k2_orders_2(sK0,X1)) | ~v5_orders_2(sK0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0)) )),
% 0.21/0.46    inference(resolution,[],[f64,f51])).
% 0.21/0.46  fof(f64,plain,(
% 0.21/0.46    ( ! [X2,X0,X1] : (~l1_orders_2(X0) | ~r2_hidden(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~r2_hidden(X1,k2_orders_2(X0,X2)) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 0.21/0.46    inference(cnf_transformation,[],[f29])).
% 0.21/0.46  fof(f29,plain,(
% 0.21/0.46    ! [X0] : (! [X1] : (! [X2] : (~r2_hidden(X1,k2_orders_2(X0,X2)) | ~r2_hidden(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 0.21/0.46    inference(flattening,[],[f28])).
% 0.21/0.46  fof(f28,plain,(
% 0.21/0.46    ! [X0] : (! [X1] : (! [X2] : ((~r2_hidden(X1,k2_orders_2(X0,X2)) | ~r2_hidden(X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 0.21/0.46    inference(ennf_transformation,[],[f13])).
% 0.21/0.46  fof(f13,axiom,(
% 0.21/0.46    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ~(r2_hidden(X1,k2_orders_2(X0,X2)) & r2_hidden(X1,X2)))))),
% 0.21/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_orders_2)).
% 0.21/0.46  fof(f346,plain,(
% 0.21/0.46    r2_hidden(sK2(k2_struct_0(sK0),k3_orders_2(sK0,k1_xboole_0,sK1)),k1_xboole_0) | k1_xboole_0 = k3_orders_2(sK0,k1_xboole_0,sK1) | v2_struct_0(sK0)),
% 0.21/0.46    inference(resolution,[],[f343,f54])).
% 0.21/0.46  fof(f343,plain,(
% 0.21/0.46    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) | k1_xboole_0 = k3_orders_2(sK0,X0,sK1) | r2_hidden(sK2(k2_struct_0(sK0),k3_orders_2(sK0,X0,sK1)),X0) | v2_struct_0(sK0)) )),
% 0.21/0.46    inference(resolution,[],[f342,f75])).
% 0.21/0.46  fof(f342,plain,(
% 0.21/0.46    ( ! [X0,X1] : (~m1_subset_1(X1,k2_struct_0(sK0)) | v2_struct_0(sK0) | k1_xboole_0 = k3_orders_2(sK0,X0,X1) | r2_hidden(sK2(k2_struct_0(sK0),k3_orders_2(sK0,X0,X1)),X0) | ~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))) )),
% 0.21/0.46    inference(duplicate_literal_removal,[],[f341])).
% 0.21/0.46  fof(f341,plain,(
% 0.21/0.46    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) | v2_struct_0(sK0) | k1_xboole_0 = k3_orders_2(sK0,X0,X1) | r2_hidden(sK2(k2_struct_0(sK0),k3_orders_2(sK0,X0,X1)),X0) | ~m1_subset_1(X1,k2_struct_0(sK0)) | ~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) | ~m1_subset_1(X1,k2_struct_0(sK0)) | v2_struct_0(sK0)) )),
% 0.21/0.46    inference(resolution,[],[f340,f130])).
% 0.21/0.46  fof(f340,plain,(
% 0.21/0.46    ( ! [X0,X1] : (~m1_subset_1(k3_orders_2(sK0,X1,X0),k1_zfmisc_1(k2_struct_0(sK0))) | ~m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK0))) | v2_struct_0(sK0) | k1_xboole_0 = k3_orders_2(sK0,X1,X0) | r2_hidden(sK2(k2_struct_0(sK0),k3_orders_2(sK0,X1,X0)),X1) | ~m1_subset_1(X0,k2_struct_0(sK0))) )),
% 0.21/0.46    inference(duplicate_literal_removal,[],[f337])).
% 0.21/0.46  fof(f337,plain,(
% 0.21/0.46    ( ! [X0,X1] : (~m1_subset_1(X0,k2_struct_0(sK0)) | ~m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK0))) | v2_struct_0(sK0) | k1_xboole_0 = k3_orders_2(sK0,X1,X0) | r2_hidden(sK2(k2_struct_0(sK0),k3_orders_2(sK0,X1,X0)),X1) | k1_xboole_0 = k3_orders_2(sK0,X1,X0) | ~m1_subset_1(k3_orders_2(sK0,X1,X0),k1_zfmisc_1(k2_struct_0(sK0)))) )),
% 0.21/0.46    inference(resolution,[],[f332,f67])).
% 0.21/0.46  fof(f332,plain,(
% 0.21/0.46    ( ! [X0,X1] : (~m1_subset_1(sK2(k2_struct_0(sK0),k3_orders_2(sK0,X0,X1)),k2_struct_0(sK0)) | ~m1_subset_1(X1,k2_struct_0(sK0)) | ~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) | v2_struct_0(sK0) | k1_xboole_0 = k3_orders_2(sK0,X0,X1) | r2_hidden(sK2(k2_struct_0(sK0),k3_orders_2(sK0,X0,X1)),X0)) )),
% 0.21/0.46    inference(duplicate_literal_removal,[],[f331])).
% 0.21/0.46  fof(f331,plain,(
% 0.21/0.46    ( ! [X0,X1] : (~m1_subset_1(sK2(k2_struct_0(sK0),k3_orders_2(sK0,X0,X1)),k2_struct_0(sK0)) | ~m1_subset_1(X1,k2_struct_0(sK0)) | ~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) | v2_struct_0(sK0) | k1_xboole_0 = k3_orders_2(sK0,X0,X1) | r2_hidden(sK2(k2_struct_0(sK0),k3_orders_2(sK0,X0,X1)),X0) | ~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) | ~m1_subset_1(X1,k2_struct_0(sK0)) | v2_struct_0(sK0)) )),
% 0.21/0.46    inference(resolution,[],[f148,f130])).
% 0.21/0.46  fof(f148,plain,(
% 0.21/0.46    ( ! [X4,X5,X3] : (~m1_subset_1(k3_orders_2(sK0,X4,X5),k1_zfmisc_1(X3)) | ~m1_subset_1(sK2(X3,k3_orders_2(sK0,X4,X5)),k2_struct_0(sK0)) | ~m1_subset_1(X5,k2_struct_0(sK0)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_struct_0(sK0))) | v2_struct_0(sK0) | k1_xboole_0 = k3_orders_2(sK0,X4,X5) | r2_hidden(sK2(X3,k3_orders_2(sK0,X4,X5)),X4)) )),
% 0.21/0.46    inference(resolution,[],[f145,f68])).
% 0.21/0.46  fof(f68,plain,(
% 0.21/0.46    ( ! [X0,X1] : (r2_hidden(sK2(X0,X1),X1) | k1_xboole_0 = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.21/0.46    inference(cnf_transformation,[],[f46])).
% 0.21/0.46  fof(f145,plain,(
% 0.21/0.46    ( ! [X2,X0,X1] : (~r2_hidden(X0,k3_orders_2(sK0,X1,X2)) | r2_hidden(X0,X1) | ~m1_subset_1(X0,k2_struct_0(sK0)) | ~m1_subset_1(X2,k2_struct_0(sK0)) | ~m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK0))) | v2_struct_0(sK0)) )),
% 0.21/0.46    inference(resolution,[],[f144,f48])).
% 0.21/0.46  fof(f144,plain,(
% 0.21/0.46    ( ! [X2,X0,X1] : (~v3_orders_2(sK0) | ~r2_hidden(X1,k3_orders_2(sK0,X0,X2)) | r2_hidden(X1,X0) | ~m1_subset_1(X1,k2_struct_0(sK0)) | ~m1_subset_1(X2,k2_struct_0(sK0)) | ~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) | v2_struct_0(sK0)) )),
% 0.21/0.46    inference(resolution,[],[f143,f49])).
% 0.21/0.46  fof(f143,plain,(
% 0.21/0.46    ( ! [X2,X0,X1] : (~v4_orders_2(sK0) | ~m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK0))) | ~r2_hidden(X2,k3_orders_2(sK0,X1,X0)) | r2_hidden(X2,X1) | ~m1_subset_1(X2,k2_struct_0(sK0)) | ~m1_subset_1(X0,k2_struct_0(sK0)) | ~v3_orders_2(sK0) | v2_struct_0(sK0)) )),
% 0.21/0.46    inference(resolution,[],[f120,f50])).
% 0.21/0.46  fof(f120,plain,(
% 0.21/0.46    ( ! [X2,X0,X1] : (~v5_orders_2(sK0) | ~m1_subset_1(X2,k2_struct_0(sK0)) | ~m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK0))) | ~r2_hidden(X0,k3_orders_2(sK0,X1,X2)) | r2_hidden(X0,X1) | ~m1_subset_1(X0,k2_struct_0(sK0)) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0)) )),
% 0.21/0.46    inference(forward_demodulation,[],[f119,f74])).
% 0.21/0.46  fof(f119,plain,(
% 0.21/0.46    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k2_struct_0(sK0)) | ~m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK0))) | ~r2_hidden(X0,k3_orders_2(sK0,X1,X2)) | ~m1_subset_1(X0,u1_struct_0(sK0)) | r2_hidden(X0,X1) | ~v5_orders_2(sK0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0)) )),
% 0.21/0.46    inference(forward_demodulation,[],[f118,f74])).
% 0.21/0.46  fof(f118,plain,(
% 0.21/0.46    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK0))) | ~r2_hidden(X0,k3_orders_2(sK0,X1,X2)) | ~m1_subset_1(X2,u1_struct_0(sK0)) | ~m1_subset_1(X0,u1_struct_0(sK0)) | r2_hidden(X0,X1) | ~v5_orders_2(sK0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0)) )),
% 0.21/0.46    inference(forward_demodulation,[],[f117,f74])).
% 0.21/0.46  fof(f117,plain,(
% 0.21/0.46    ( ! [X2,X0,X1] : (~r2_hidden(X0,k3_orders_2(sK0,X1,X2)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X2,u1_struct_0(sK0)) | ~m1_subset_1(X0,u1_struct_0(sK0)) | r2_hidden(X0,X1) | ~v5_orders_2(sK0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0)) )),
% 0.21/0.46    inference(resolution,[],[f62,f51])).
% 0.21/0.46  fof(f62,plain,(
% 0.21/0.46    ( ! [X2,X0,X3,X1] : (~l1_orders_2(X0) | ~r2_hidden(X1,k3_orders_2(X0,X3,X2)) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | r2_hidden(X1,X3) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 0.21/0.46    inference(cnf_transformation,[],[f44])).
% 0.21/0.46  fof(f44,plain,(
% 0.21/0.46    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((r2_hidden(X1,k3_orders_2(X0,X3,X2)) | ~r2_hidden(X1,X3) | ~r2_orders_2(X0,X1,X2)) & ((r2_hidden(X1,X3) & r2_orders_2(X0,X1,X2)) | ~r2_hidden(X1,k3_orders_2(X0,X3,X2)))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 0.21/0.46    inference(flattening,[],[f43])).
% 0.21/0.46  fof(f43,plain,(
% 0.21/0.46    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((r2_hidden(X1,k3_orders_2(X0,X3,X2)) | (~r2_hidden(X1,X3) | ~r2_orders_2(X0,X1,X2))) & ((r2_hidden(X1,X3) & r2_orders_2(X0,X1,X2)) | ~r2_hidden(X1,k3_orders_2(X0,X3,X2)))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 0.21/0.46    inference(nnf_transformation,[],[f27])).
% 0.21/0.46  fof(f27,plain,(
% 0.21/0.46    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((r2_hidden(X1,k3_orders_2(X0,X3,X2)) <=> (r2_hidden(X1,X3) & r2_orders_2(X0,X1,X2))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 0.21/0.46    inference(flattening,[],[f26])).
% 0.21/0.46  fof(f26,plain,(
% 0.21/0.46    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((r2_hidden(X1,k3_orders_2(X0,X3,X2)) <=> (r2_hidden(X1,X3) & r2_orders_2(X0,X1,X2))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 0.21/0.46    inference(ennf_transformation,[],[f14])).
% 0.21/0.46  fof(f14,axiom,(
% 0.21/0.46    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) => (r2_hidden(X1,k3_orders_2(X0,X3,X2)) <=> (r2_hidden(X1,X3) & r2_orders_2(X0,X1,X2)))))))),
% 0.21/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t57_orders_2)).
% 0.21/0.46  fof(f73,plain,(
% 0.21/0.46    k1_xboole_0 != k3_orders_2(sK0,k1_xboole_0,sK1)),
% 0.21/0.46    inference(backward_demodulation,[],[f53,f72])).
% 0.21/0.46  fof(f72,plain,(
% 0.21/0.46    k1_xboole_0 = k1_struct_0(sK0)),
% 0.21/0.46    inference(resolution,[],[f56,f71])).
% 0.21/0.46  fof(f56,plain,(
% 0.21/0.46    ( ! [X0] : (~l1_struct_0(X0) | k1_xboole_0 = k1_struct_0(X0)) )),
% 0.21/0.46    inference(cnf_transformation,[],[f20])).
% 0.21/0.46  fof(f20,plain,(
% 0.21/0.46    ! [X0] : (k1_xboole_0 = k1_struct_0(X0) | ~l1_struct_0(X0))),
% 0.21/0.46    inference(ennf_transformation,[],[f5])).
% 0.21/0.46  fof(f5,axiom,(
% 0.21/0.46    ! [X0] : (l1_struct_0(X0) => k1_xboole_0 = k1_struct_0(X0))),
% 0.21/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_struct_0)).
% 0.21/0.46  fof(f53,plain,(
% 0.21/0.46    k1_xboole_0 != k3_orders_2(sK0,k1_struct_0(sK0),sK1)),
% 0.21/0.46    inference(cnf_transformation,[],[f42])).
% 0.21/0.46  % SZS output end Proof for theBenchmark
% 0.21/0.46  % (11238)------------------------------
% 0.21/0.46  % (11238)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.46  % (11238)Termination reason: Refutation
% 0.21/0.46  
% 0.21/0.46  % (11238)Memory used [KB]: 2046
% 0.21/0.46  % (11238)Time elapsed: 0.032 s
% 0.21/0.46  % (11238)------------------------------
% 0.21/0.46  % (11238)------------------------------
% 0.21/0.46  % (11227)Success in time 0.104 s
%------------------------------------------------------------------------------
