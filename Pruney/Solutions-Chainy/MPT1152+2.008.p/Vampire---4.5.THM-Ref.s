%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:09:48 EST 2020

% Result     : Theorem 0.23s
% Output     : Refutation 0.23s
% Verified   : 
% Statistics : Number of formulae       :  126 (4091 expanded)
%              Number of leaves         :   16 (1064 expanded)
%              Depth                    :   34
%              Number of atoms          :  559 (21568 expanded)
%              Number of equality atoms :   69 (3694 expanded)
%              Maximal formula depth    :   15 (   6 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f275,plain,(
    $false ),
    inference(subsumption_resolution,[],[f273,f221])).

fof(f221,plain,(
    k1_xboole_0 != k2_orders_2(sK0,k1_xboole_0) ),
    inference(superposition,[],[f45,f218])).

fof(f218,plain,(
    k1_xboole_0 = k2_struct_0(sK0) ),
    inference(resolution,[],[f216,f54])).

fof(f54,plain,(
    ! [X0] :
      ( r2_hidden(sK1(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0] :
      ( ( ! [X2,X3,X4] :
            ( k3_mcart_1(X2,X3,X4) != sK1(X0)
            | ( ~ r2_hidden(X3,X0)
              & ~ r2_hidden(X2,X0) ) )
        & r2_hidden(sK1(X0),X0) )
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f21,f33])).

fof(f33,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ! [X2,X3,X4] :
              ( k3_mcart_1(X2,X3,X4) != X1
              | ( ~ r2_hidden(X3,X0)
                & ~ r2_hidden(X2,X0) ) )
          & r2_hidden(X1,X0) )
     => ( ! [X4,X3,X2] :
            ( k3_mcart_1(X2,X3,X4) != sK1(X0)
            | ( ~ r2_hidden(X3,X0)
              & ~ r2_hidden(X2,X0) ) )
        & r2_hidden(sK1(X0),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ! [X2,X3,X4] :
              ( k3_mcart_1(X2,X3,X4) != X1
              | ( ~ r2_hidden(X3,X0)
                & ~ r2_hidden(X2,X0) ) )
          & r2_hidden(X1,X0) )
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ~ ( ! [X1] :
            ~ ( ! [X2,X3,X4] :
                  ~ ( k3_mcart_1(X2,X3,X4) = X1
                    & ( r2_hidden(X3,X0)
                      | r2_hidden(X2,X0) ) )
              & r2_hidden(X1,X0) )
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_mcart_1)).

fof(f216,plain,(
    ! [X0] : ~ r2_hidden(X0,k2_struct_0(sK0)) ),
    inference(resolution,[],[f215,f72])).

fof(f72,plain,(
    ! [X0] : m1_subset_1(X0,k1_zfmisc_1(X0)) ),
    inference(forward_demodulation,[],[f47,f46])).

fof(f46,plain,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).

fof(f47,plain,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_subset_1)).

fof(f215,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))
      | ~ r2_hidden(X1,X0) ) ),
    inference(resolution,[],[f214,f65])).

fof(f65,plain,(
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
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).

fof(f214,plain,(
    v1_xboole_0(k2_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f213,f132])).

fof(f132,plain,(
    m1_subset_1(sK1(k2_orders_2(sK0,k2_struct_0(sK0))),k2_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f130,f45])).

fof(f130,plain,
    ( m1_subset_1(sK1(k2_orders_2(sK0,k2_struct_0(sK0))),k2_struct_0(sK0))
    | k1_xboole_0 = k2_orders_2(sK0,k2_struct_0(sK0)) ),
    inference(resolution,[],[f129,f54])).

fof(f129,plain,
    ( ~ r2_hidden(sK1(k2_orders_2(sK0,k2_struct_0(sK0))),k2_orders_2(sK0,k2_struct_0(sK0)))
    | m1_subset_1(sK1(k2_orders_2(sK0,k2_struct_0(sK0))),k2_struct_0(sK0)) ),
    inference(forward_demodulation,[],[f128,f83])).

fof(f83,plain,(
    k2_orders_2(sK0,k2_struct_0(sK0)) = a_2_1_orders_2(sK0,k2_struct_0(sK0)) ),
    inference(resolution,[],[f82,f72])).

fof(f82,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))
      | k2_orders_2(sK0,X0) = a_2_1_orders_2(sK0,X0) ) ),
    inference(forward_demodulation,[],[f81,f73])).

fof(f73,plain,(
    k2_struct_0(sK0) = u1_struct_0(sK0) ),
    inference(resolution,[],[f48,f71])).

fof(f71,plain,(
    l1_struct_0(sK0) ),
    inference(resolution,[],[f49,f44])).

fof(f44,plain,(
    l1_orders_2(sK0) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,
    ( k1_xboole_0 != k2_orders_2(sK0,k2_struct_0(sK0))
    & l1_orders_2(sK0)
    & v5_orders_2(sK0)
    & v4_orders_2(sK0)
    & v3_orders_2(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f15,f29])).

fof(f29,plain,
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

fof(f15,plain,(
    ? [X0] :
      ( k1_xboole_0 != k2_orders_2(X0,k2_struct_0(X0))
      & l1_orders_2(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ? [X0] :
      ( k1_xboole_0 != k2_orders_2(X0,k2_struct_0(X0))
      & l1_orders_2(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_orders_2(X0)
          & v5_orders_2(X0)
          & v4_orders_2(X0)
          & v3_orders_2(X0)
          & ~ v2_struct_0(X0) )
       => k1_xboole_0 = k2_orders_2(X0,k2_struct_0(X0)) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f12,conjecture,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => k1_xboole_0 = k2_orders_2(X0,k2_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_orders_2)).

fof(f49,plain,(
    ! [X0] :
      ( ~ l1_orders_2(X0)
      | l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_orders_2)).

fof(f48,plain,(
    ! [X0] :
      ( ~ l1_struct_0(X0)
      | k2_struct_0(X0) = u1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k2_struct_0(X0) = u1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).

fof(f81,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | k2_orders_2(sK0,X0) = a_2_1_orders_2(sK0,X0) ) ),
    inference(subsumption_resolution,[],[f80,f40])).

fof(f40,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f30])).

fof(f80,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | k2_orders_2(sK0,X0) = a_2_1_orders_2(sK0,X0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f79,f41])).

fof(f41,plain,(
    v3_orders_2(sK0) ),
    inference(cnf_transformation,[],[f30])).

fof(f79,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | k2_orders_2(sK0,X0) = a_2_1_orders_2(sK0,X0)
      | ~ v3_orders_2(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f78,f42])).

fof(f42,plain,(
    v4_orders_2(sK0) ),
    inference(cnf_transformation,[],[f30])).

fof(f78,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | k2_orders_2(sK0,X0) = a_2_1_orders_2(sK0,X0)
      | ~ v4_orders_2(sK0)
      | ~ v3_orders_2(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f77,f44])).

fof(f77,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ l1_orders_2(sK0)
      | k2_orders_2(sK0,X0) = a_2_1_orders_2(sK0,X0)
      | ~ v4_orders_2(sK0)
      | ~ v3_orders_2(sK0)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f53,f43])).

fof(f43,plain,(
    v5_orders_2(sK0) ),
    inference(cnf_transformation,[],[f30])).

fof(f53,plain,(
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
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
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

fof(f128,plain,
    ( m1_subset_1(sK1(k2_orders_2(sK0,k2_struct_0(sK0))),k2_struct_0(sK0))
    | ~ r2_hidden(sK1(k2_orders_2(sK0,k2_struct_0(sK0))),a_2_1_orders_2(sK0,k2_struct_0(sK0))) ),
    inference(subsumption_resolution,[],[f127,f72])).

fof(f127,plain,
    ( m1_subset_1(sK1(k2_orders_2(sK0,k2_struct_0(sK0))),k2_struct_0(sK0))
    | ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0)))
    | ~ r2_hidden(sK1(k2_orders_2(sK0,k2_struct_0(sK0))),a_2_1_orders_2(sK0,k2_struct_0(sK0))) ),
    inference(superposition,[],[f125,f108])).

fof(f108,plain,(
    sK1(k2_orders_2(sK0,k2_struct_0(sK0))) = sK3(sK1(k2_orders_2(sK0,k2_struct_0(sK0))),sK0,k2_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f106,f45])).

fof(f106,plain,
    ( sK1(k2_orders_2(sK0,k2_struct_0(sK0))) = sK3(sK1(k2_orders_2(sK0,k2_struct_0(sK0))),sK0,k2_struct_0(sK0))
    | k1_xboole_0 = k2_orders_2(sK0,k2_struct_0(sK0)) ),
    inference(resolution,[],[f105,f54])).

fof(f105,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k2_orders_2(sK0,k2_struct_0(sK0)))
      | sK3(X0,sK0,k2_struct_0(sK0)) = X0 ) ),
    inference(forward_demodulation,[],[f103,f83])).

fof(f103,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,a_2_1_orders_2(sK0,k2_struct_0(sK0)))
      | sK3(X0,sK0,k2_struct_0(sK0)) = X0 ) ),
    inference(resolution,[],[f102,f72])).

fof(f102,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK0)))
      | ~ r2_hidden(X0,a_2_1_orders_2(sK0,X1))
      | sK3(X0,sK0,X1) = X0 ) ),
    inference(forward_demodulation,[],[f101,f73])).

fof(f101,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,a_2_1_orders_2(sK0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | sK3(X0,sK0,X1) = X0 ) ),
    inference(subsumption_resolution,[],[f100,f40])).

fof(f100,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,a_2_1_orders_2(sK0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | sK3(X0,sK0,X1) = X0
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f99,f41])).

fof(f99,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,a_2_1_orders_2(sK0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | sK3(X0,sK0,X1) = X0
      | ~ v3_orders_2(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f98,f42])).

fof(f98,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,a_2_1_orders_2(sK0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | sK3(X0,sK0,X1) = X0
      | ~ v4_orders_2(sK0)
      | ~ v3_orders_2(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f97,f44])).

fof(f97,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,a_2_1_orders_2(sK0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ l1_orders_2(sK0)
      | sK3(X0,sK0,X1) = X0
      | ~ v4_orders_2(sK0)
      | ~ v3_orders_2(sK0)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f60,f43])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( ~ v5_orders_2(X1)
      | ~ r2_hidden(X0,a_2_1_orders_2(X1,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_orders_2(X1)
      | sK3(X0,X1,X2) = X0
      | ~ v4_orders_2(X1)
      | ~ v3_orders_2(X1)
      | v2_struct_0(X1) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f36,f38,f37])).

fof(f37,plain,(
    ! [X3,X2,X1] :
      ( ? [X4] :
          ( ~ r2_orders_2(X1,X3,X4)
          & r2_hidden(X4,X2)
          & m1_subset_1(X4,u1_struct_0(X1)) )
     => ( ~ r2_orders_2(X1,X3,sK2(X1,X2,X3))
        & r2_hidden(sK2(X1,X2,X3),X2)
        & m1_subset_1(sK2(X1,X2,X3),u1_struct_0(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f38,plain,(
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

fof(f36,plain,(
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
    inference(rectify,[],[f35])).

fof(f35,plain,(
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
    inference(nnf_transformation,[],[f27])).

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
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
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

fof(f125,plain,(
    ! [X0,X1] :
      ( m1_subset_1(sK3(X0,sK0,X1),k2_struct_0(sK0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK0)))
      | ~ r2_hidden(X0,a_2_1_orders_2(sK0,X1)) ) ),
    inference(forward_demodulation,[],[f124,f73])).

fof(f124,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK0)))
      | ~ r2_hidden(X0,a_2_1_orders_2(sK0,X1))
      | m1_subset_1(sK3(X0,sK0,X1),u1_struct_0(sK0)) ) ),
    inference(forward_demodulation,[],[f123,f73])).

fof(f123,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,a_2_1_orders_2(sK0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | m1_subset_1(sK3(X0,sK0,X1),u1_struct_0(sK0)) ) ),
    inference(subsumption_resolution,[],[f122,f40])).

fof(f122,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,a_2_1_orders_2(sK0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | m1_subset_1(sK3(X0,sK0,X1),u1_struct_0(sK0))
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f121,f41])).

fof(f121,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,a_2_1_orders_2(sK0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | m1_subset_1(sK3(X0,sK0,X1),u1_struct_0(sK0))
      | ~ v3_orders_2(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f120,f42])).

fof(f120,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,a_2_1_orders_2(sK0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | m1_subset_1(sK3(X0,sK0,X1),u1_struct_0(sK0))
      | ~ v4_orders_2(sK0)
      | ~ v3_orders_2(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f119,f44])).

fof(f119,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,a_2_1_orders_2(sK0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ l1_orders_2(sK0)
      | m1_subset_1(sK3(X0,sK0,X1),u1_struct_0(sK0))
      | ~ v4_orders_2(sK0)
      | ~ v3_orders_2(sK0)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f59,f43])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( ~ v5_orders_2(X1)
      | ~ r2_hidden(X0,a_2_1_orders_2(X1,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_orders_2(X1)
      | m1_subset_1(sK3(X0,X1,X2),u1_struct_0(X1))
      | ~ v4_orders_2(X1)
      | ~ v3_orders_2(X1)
      | v2_struct_0(X1) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f213,plain,
    ( v1_xboole_0(k2_struct_0(sK0))
    | ~ m1_subset_1(sK1(k2_orders_2(sK0,k2_struct_0(sK0))),k2_struct_0(sK0)) ),
    inference(resolution,[],[f204,f57])).

fof(f57,plain,(
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
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

fof(f204,plain,(
    ~ r2_hidden(sK1(k2_orders_2(sK0,k2_struct_0(sK0))),k2_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f203,f132])).

fof(f203,plain,
    ( ~ m1_subset_1(sK1(k2_orders_2(sK0,k2_struct_0(sK0))),k2_struct_0(sK0))
    | ~ r2_hidden(sK1(k2_orders_2(sK0,k2_struct_0(sK0))),k2_struct_0(sK0)) ),
    inference(forward_demodulation,[],[f202,f73])).

fof(f202,plain,
    ( ~ r2_hidden(sK1(k2_orders_2(sK0,k2_struct_0(sK0))),k2_struct_0(sK0))
    | ~ m1_subset_1(sK1(k2_orders_2(sK0,k2_struct_0(sK0))),u1_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f201,f44])).

fof(f201,plain,
    ( ~ r2_hidden(sK1(k2_orders_2(sK0,k2_struct_0(sK0))),k2_struct_0(sK0))
    | ~ m1_subset_1(sK1(k2_orders_2(sK0,k2_struct_0(sK0))),u1_struct_0(sK0))
    | ~ l1_orders_2(sK0) ),
    inference(subsumption_resolution,[],[f199,f132])).

fof(f199,plain,
    ( ~ m1_subset_1(sK1(k2_orders_2(sK0,k2_struct_0(sK0))),k2_struct_0(sK0))
    | ~ r2_hidden(sK1(k2_orders_2(sK0,k2_struct_0(sK0))),k2_struct_0(sK0))
    | ~ m1_subset_1(sK1(k2_orders_2(sK0,k2_struct_0(sK0))),u1_struct_0(sK0))
    | ~ l1_orders_2(sK0) ),
    inference(resolution,[],[f198,f70])).

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
    inference(equality_resolution,[],[f51])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( X1 != X2
      | ~ r2_orders_2(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
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
    inference(flattening,[],[f31])).

fof(f31,plain,(
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
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
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

fof(f198,plain,(
    ! [X0] :
      ( r2_orders_2(sK0,sK1(k2_orders_2(sK0,k2_struct_0(sK0))),X0)
      | ~ m1_subset_1(X0,k2_struct_0(sK0))
      | ~ r2_hidden(X0,k2_struct_0(sK0)) ) ),
    inference(forward_demodulation,[],[f197,f108])).

fof(f197,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k2_struct_0(sK0))
      | ~ r2_hidden(X0,k2_struct_0(sK0))
      | r2_orders_2(sK0,sK3(sK1(k2_orders_2(sK0,k2_struct_0(sK0))),sK0,k2_struct_0(sK0)),X0) ) ),
    inference(subsumption_resolution,[],[f194,f45])).

fof(f194,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k2_struct_0(sK0))
      | ~ r2_hidden(X0,k2_struct_0(sK0))
      | r2_orders_2(sK0,sK3(sK1(k2_orders_2(sK0,k2_struct_0(sK0))),sK0,k2_struct_0(sK0)),X0)
      | k1_xboole_0 = k2_orders_2(sK0,k2_struct_0(sK0)) ) ),
    inference(resolution,[],[f193,f54])).

fof(f193,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,k2_orders_2(sK0,k2_struct_0(sK0)))
      | ~ m1_subset_1(X0,k2_struct_0(sK0))
      | ~ r2_hidden(X0,k2_struct_0(sK0))
      | r2_orders_2(sK0,sK3(X1,sK0,k2_struct_0(sK0)),X0) ) ),
    inference(forward_demodulation,[],[f191,f83])).

fof(f191,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k2_struct_0(sK0))
      | ~ r2_hidden(X0,k2_struct_0(sK0))
      | ~ r2_hidden(X1,a_2_1_orders_2(sK0,k2_struct_0(sK0)))
      | r2_orders_2(sK0,sK3(X1,sK0,k2_struct_0(sK0)),X0) ) ),
    inference(resolution,[],[f190,f72])).

fof(f190,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK0)))
      | ~ m1_subset_1(X0,k2_struct_0(sK0))
      | ~ r2_hidden(X0,X1)
      | ~ r2_hidden(X2,a_2_1_orders_2(sK0,X1))
      | r2_orders_2(sK0,sK3(X2,sK0,X1),X0) ) ),
    inference(forward_demodulation,[],[f189,f73])).

fof(f189,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X0,k2_struct_0(sK0))
      | ~ r2_hidden(X0,X1)
      | ~ r2_hidden(X2,a_2_1_orders_2(sK0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | r2_orders_2(sK0,sK3(X2,sK0,X1),X0) ) ),
    inference(forward_demodulation,[],[f188,f73])).

fof(f188,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ r2_hidden(X2,a_2_1_orders_2(sK0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | r2_orders_2(sK0,sK3(X2,sK0,X1),X0) ) ),
    inference(subsumption_resolution,[],[f187,f40])).

fof(f187,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ r2_hidden(X2,a_2_1_orders_2(sK0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | r2_orders_2(sK0,sK3(X2,sK0,X1),X0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f186,f41])).

fof(f186,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ r2_hidden(X2,a_2_1_orders_2(sK0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | r2_orders_2(sK0,sK3(X2,sK0,X1),X0)
      | ~ v3_orders_2(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f185,f42])).

fof(f185,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ r2_hidden(X2,a_2_1_orders_2(sK0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | r2_orders_2(sK0,sK3(X2,sK0,X1),X0)
      | ~ v4_orders_2(sK0)
      | ~ v3_orders_2(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f184,f44])).

fof(f184,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ r2_hidden(X2,a_2_1_orders_2(sK0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ l1_orders_2(sK0)
      | r2_orders_2(sK0,sK3(X2,sK0,X1),X0)
      | ~ v4_orders_2(sK0)
      | ~ v3_orders_2(sK0)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f61,f43])).

fof(f61,plain,(
    ! [X6,X2,X0,X1] :
      ( ~ v5_orders_2(X1)
      | ~ r2_hidden(X6,X2)
      | ~ m1_subset_1(X6,u1_struct_0(X1))
      | ~ r2_hidden(X0,a_2_1_orders_2(X1,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_orders_2(X1)
      | r2_orders_2(X1,sK3(X0,X1,X2),X6)
      | ~ v4_orders_2(X1)
      | ~ v3_orders_2(X1)
      | v2_struct_0(X1) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f45,plain,(
    k1_xboole_0 != k2_orders_2(sK0,k2_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f30])).

fof(f273,plain,(
    k1_xboole_0 = k2_orders_2(sK0,k1_xboole_0) ),
    inference(resolution,[],[f272,f54])).

fof(f272,plain,(
    ! [X0] : ~ r2_hidden(X0,k2_orders_2(sK0,k1_xboole_0)) ),
    inference(resolution,[],[f271,f72])).

fof(f271,plain,(
    ! [X2,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k1_xboole_0))
      | ~ r2_hidden(X1,k2_orders_2(sK0,X2)) ) ),
    inference(forward_demodulation,[],[f217,f218])).

fof(f217,plain,(
    ! [X2,X1] :
      ( ~ r2_hidden(X1,k2_orders_2(sK0,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_struct_0(sK0))) ) ),
    inference(resolution,[],[f215,f89])).

fof(f89,plain,(
    ! [X0] :
      ( m1_subset_1(k2_orders_2(sK0,X0),k1_zfmisc_1(k2_struct_0(sK0)))
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) ) ),
    inference(subsumption_resolution,[],[f88,f40])).

fof(f88,plain,(
    ! [X0] :
      ( m1_subset_1(k2_orders_2(sK0,X0),k1_zfmisc_1(k2_struct_0(sK0)))
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f87,f41])).

fof(f87,plain,(
    ! [X0] :
      ( m1_subset_1(k2_orders_2(sK0,X0),k1_zfmisc_1(k2_struct_0(sK0)))
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))
      | ~ v3_orders_2(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f86,f42])).

fof(f86,plain,(
    ! [X0] :
      ( m1_subset_1(k2_orders_2(sK0,X0),k1_zfmisc_1(k2_struct_0(sK0)))
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))
      | ~ v4_orders_2(sK0)
      | ~ v3_orders_2(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f85,f43])).

fof(f85,plain,(
    ! [X0] :
      ( m1_subset_1(k2_orders_2(sK0,X0),k1_zfmisc_1(k2_struct_0(sK0)))
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))
      | ~ v5_orders_2(sK0)
      | ~ v4_orders_2(sK0)
      | ~ v3_orders_2(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f84,f44])).

fof(f84,plain,(
    ! [X0] :
      ( m1_subset_1(k2_orders_2(sK0,X0),k1_zfmisc_1(k2_struct_0(sK0)))
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))
      | ~ l1_orders_2(sK0)
      | ~ v5_orders_2(sK0)
      | ~ v4_orders_2(sK0)
      | ~ v3_orders_2(sK0)
      | v2_struct_0(sK0) ) ),
    inference(superposition,[],[f58,f73])).

fof(f58,plain,(
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
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => m1_subset_1(k2_orders_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_orders_2)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.14  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n024.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 09:40:21 EST 2020
% 0.15/0.36  % CPUTime    : 
% 0.23/0.47  % (1440)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 0.23/0.47  % (1432)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 0.23/0.48  % (1432)Refutation not found, incomplete strategy% (1432)------------------------------
% 0.23/0.48  % (1432)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.23/0.48  % (1432)Termination reason: Refutation not found, incomplete strategy
% 0.23/0.48  
% 0.23/0.48  % (1432)Memory used [KB]: 6140
% 0.23/0.48  % (1432)Time elapsed: 0.055 s
% 0.23/0.48  % (1432)------------------------------
% 0.23/0.48  % (1432)------------------------------
% 0.23/0.49  % (1440)Refutation found. Thanks to Tanya!
% 0.23/0.49  % SZS status Theorem for theBenchmark
% 0.23/0.49  % SZS output start Proof for theBenchmark
% 0.23/0.49  fof(f275,plain,(
% 0.23/0.49    $false),
% 0.23/0.49    inference(subsumption_resolution,[],[f273,f221])).
% 0.23/0.49  fof(f221,plain,(
% 0.23/0.49    k1_xboole_0 != k2_orders_2(sK0,k1_xboole_0)),
% 0.23/0.49    inference(superposition,[],[f45,f218])).
% 0.23/0.49  fof(f218,plain,(
% 0.23/0.49    k1_xboole_0 = k2_struct_0(sK0)),
% 0.23/0.49    inference(resolution,[],[f216,f54])).
% 0.23/0.49  fof(f54,plain,(
% 0.23/0.49    ( ! [X0] : (r2_hidden(sK1(X0),X0) | k1_xboole_0 = X0) )),
% 0.23/0.49    inference(cnf_transformation,[],[f34])).
% 0.23/0.49  fof(f34,plain,(
% 0.23/0.49    ! [X0] : ((! [X2,X3,X4] : (k3_mcart_1(X2,X3,X4) != sK1(X0) | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(sK1(X0),X0)) | k1_xboole_0 = X0)),
% 0.23/0.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f21,f33])).
% 0.23/0.49  fof(f33,plain,(
% 0.23/0.49    ! [X0] : (? [X1] : (! [X2,X3,X4] : (k3_mcart_1(X2,X3,X4) != X1 | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(X1,X0)) => (! [X4,X3,X2] : (k3_mcart_1(X2,X3,X4) != sK1(X0) | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(sK1(X0),X0)))),
% 0.23/0.49    introduced(choice_axiom,[])).
% 0.23/0.49  fof(f21,plain,(
% 0.23/0.49    ! [X0] : (? [X1] : (! [X2,X3,X4] : (k3_mcart_1(X2,X3,X4) != X1 | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(X1,X0)) | k1_xboole_0 = X0)),
% 0.23/0.49    inference(ennf_transformation,[],[f5])).
% 0.23/0.49  fof(f5,axiom,(
% 0.23/0.49    ! [X0] : ~(! [X1] : ~(! [X2,X3,X4] : ~(k3_mcart_1(X2,X3,X4) = X1 & (r2_hidden(X3,X0) | r2_hidden(X2,X0))) & r2_hidden(X1,X0)) & k1_xboole_0 != X0)),
% 0.23/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_mcart_1)).
% 0.23/0.49  fof(f216,plain,(
% 0.23/0.49    ( ! [X0] : (~r2_hidden(X0,k2_struct_0(sK0))) )),
% 0.23/0.49    inference(resolution,[],[f215,f72])).
% 0.23/0.49  fof(f72,plain,(
% 0.23/0.49    ( ! [X0] : (m1_subset_1(X0,k1_zfmisc_1(X0))) )),
% 0.23/0.49    inference(forward_demodulation,[],[f47,f46])).
% 0.23/0.49  fof(f46,plain,(
% 0.23/0.49    ( ! [X0] : (k2_subset_1(X0) = X0) )),
% 0.23/0.49    inference(cnf_transformation,[],[f1])).
% 0.23/0.49  fof(f1,axiom,(
% 0.23/0.49    ! [X0] : k2_subset_1(X0) = X0),
% 0.23/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).
% 0.23/0.49  fof(f47,plain,(
% 0.23/0.49    ( ! [X0] : (m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))) )),
% 0.23/0.49    inference(cnf_transformation,[],[f2])).
% 0.23/0.49  fof(f2,axiom,(
% 0.23/0.49    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))),
% 0.23/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_subset_1)).
% 0.23/0.49  fof(f215,plain,(
% 0.23/0.49    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) | ~r2_hidden(X1,X0)) )),
% 0.23/0.49    inference(resolution,[],[f214,f65])).
% 0.23/0.49  fof(f65,plain,(
% 0.23/0.49    ( ! [X2,X0,X1] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) )),
% 0.23/0.49    inference(cnf_transformation,[],[f28])).
% 0.23/0.49  fof(f28,plain,(
% 0.23/0.49    ! [X0,X1,X2] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 0.23/0.49    inference(ennf_transformation,[],[f4])).
% 0.23/0.49  fof(f4,axiom,(
% 0.23/0.49    ! [X0,X1,X2] : ~(v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1))),
% 0.23/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).
% 0.23/0.49  fof(f214,plain,(
% 0.23/0.49    v1_xboole_0(k2_struct_0(sK0))),
% 0.23/0.49    inference(subsumption_resolution,[],[f213,f132])).
% 0.23/0.49  fof(f132,plain,(
% 0.23/0.49    m1_subset_1(sK1(k2_orders_2(sK0,k2_struct_0(sK0))),k2_struct_0(sK0))),
% 0.23/0.49    inference(subsumption_resolution,[],[f130,f45])).
% 0.23/0.49  fof(f130,plain,(
% 0.23/0.49    m1_subset_1(sK1(k2_orders_2(sK0,k2_struct_0(sK0))),k2_struct_0(sK0)) | k1_xboole_0 = k2_orders_2(sK0,k2_struct_0(sK0))),
% 0.23/0.49    inference(resolution,[],[f129,f54])).
% 0.23/0.49  fof(f129,plain,(
% 0.23/0.49    ~r2_hidden(sK1(k2_orders_2(sK0,k2_struct_0(sK0))),k2_orders_2(sK0,k2_struct_0(sK0))) | m1_subset_1(sK1(k2_orders_2(sK0,k2_struct_0(sK0))),k2_struct_0(sK0))),
% 0.23/0.49    inference(forward_demodulation,[],[f128,f83])).
% 0.23/0.49  fof(f83,plain,(
% 0.23/0.49    k2_orders_2(sK0,k2_struct_0(sK0)) = a_2_1_orders_2(sK0,k2_struct_0(sK0))),
% 0.23/0.49    inference(resolution,[],[f82,f72])).
% 0.23/0.49  fof(f82,plain,(
% 0.23/0.49    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) | k2_orders_2(sK0,X0) = a_2_1_orders_2(sK0,X0)) )),
% 0.23/0.49    inference(forward_demodulation,[],[f81,f73])).
% 0.23/0.49  fof(f73,plain,(
% 0.23/0.49    k2_struct_0(sK0) = u1_struct_0(sK0)),
% 0.23/0.49    inference(resolution,[],[f48,f71])).
% 0.23/0.49  fof(f71,plain,(
% 0.23/0.49    l1_struct_0(sK0)),
% 0.23/0.49    inference(resolution,[],[f49,f44])).
% 0.23/0.49  fof(f44,plain,(
% 0.23/0.49    l1_orders_2(sK0)),
% 0.23/0.49    inference(cnf_transformation,[],[f30])).
% 0.23/0.49  fof(f30,plain,(
% 0.23/0.49    k1_xboole_0 != k2_orders_2(sK0,k2_struct_0(sK0)) & l1_orders_2(sK0) & v5_orders_2(sK0) & v4_orders_2(sK0) & v3_orders_2(sK0) & ~v2_struct_0(sK0)),
% 0.23/0.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f15,f29])).
% 0.23/0.49  fof(f29,plain,(
% 0.23/0.49    ? [X0] : (k1_xboole_0 != k2_orders_2(X0,k2_struct_0(X0)) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => (k1_xboole_0 != k2_orders_2(sK0,k2_struct_0(sK0)) & l1_orders_2(sK0) & v5_orders_2(sK0) & v4_orders_2(sK0) & v3_orders_2(sK0) & ~v2_struct_0(sK0))),
% 0.23/0.49    introduced(choice_axiom,[])).
% 0.23/0.49  fof(f15,plain,(
% 0.23/0.49    ? [X0] : (k1_xboole_0 != k2_orders_2(X0,k2_struct_0(X0)) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0))),
% 0.23/0.49    inference(flattening,[],[f14])).
% 0.23/0.49  fof(f14,plain,(
% 0.23/0.49    ? [X0] : (k1_xboole_0 != k2_orders_2(X0,k2_struct_0(X0)) & (l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)))),
% 0.23/0.49    inference(ennf_transformation,[],[f13])).
% 0.23/0.49  fof(f13,negated_conjecture,(
% 0.23/0.49    ~! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => k1_xboole_0 = k2_orders_2(X0,k2_struct_0(X0)))),
% 0.23/0.49    inference(negated_conjecture,[],[f12])).
% 0.23/0.49  fof(f12,conjecture,(
% 0.23/0.49    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => k1_xboole_0 = k2_orders_2(X0,k2_struct_0(X0)))),
% 0.23/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_orders_2)).
% 0.23/0.49  fof(f49,plain,(
% 0.23/0.49    ( ! [X0] : (~l1_orders_2(X0) | l1_struct_0(X0)) )),
% 0.23/0.49    inference(cnf_transformation,[],[f17])).
% 0.23/0.49  fof(f17,plain,(
% 0.23/0.49    ! [X0] : (l1_struct_0(X0) | ~l1_orders_2(X0))),
% 0.23/0.49    inference(ennf_transformation,[],[f10])).
% 0.23/0.49  fof(f10,axiom,(
% 0.23/0.49    ! [X0] : (l1_orders_2(X0) => l1_struct_0(X0))),
% 0.23/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_orders_2)).
% 0.23/0.49  fof(f48,plain,(
% 0.23/0.49    ( ! [X0] : (~l1_struct_0(X0) | k2_struct_0(X0) = u1_struct_0(X0)) )),
% 0.23/0.49    inference(cnf_transformation,[],[f16])).
% 0.23/0.49  fof(f16,plain,(
% 0.23/0.49    ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0))),
% 0.23/0.49    inference(ennf_transformation,[],[f6])).
% 0.23/0.49  fof(f6,axiom,(
% 0.23/0.49    ! [X0] : (l1_struct_0(X0) => k2_struct_0(X0) = u1_struct_0(X0))),
% 0.23/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).
% 0.23/0.49  fof(f81,plain,(
% 0.23/0.49    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | k2_orders_2(sK0,X0) = a_2_1_orders_2(sK0,X0)) )),
% 0.23/0.49    inference(subsumption_resolution,[],[f80,f40])).
% 0.23/0.49  fof(f40,plain,(
% 0.23/0.49    ~v2_struct_0(sK0)),
% 0.23/0.49    inference(cnf_transformation,[],[f30])).
% 0.23/0.49  fof(f80,plain,(
% 0.23/0.49    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | k2_orders_2(sK0,X0) = a_2_1_orders_2(sK0,X0) | v2_struct_0(sK0)) )),
% 0.23/0.49    inference(subsumption_resolution,[],[f79,f41])).
% 0.23/0.49  fof(f41,plain,(
% 0.23/0.49    v3_orders_2(sK0)),
% 0.23/0.49    inference(cnf_transformation,[],[f30])).
% 0.23/0.49  fof(f79,plain,(
% 0.23/0.49    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | k2_orders_2(sK0,X0) = a_2_1_orders_2(sK0,X0) | ~v3_orders_2(sK0) | v2_struct_0(sK0)) )),
% 0.23/0.49    inference(subsumption_resolution,[],[f78,f42])).
% 0.23/0.49  fof(f42,plain,(
% 0.23/0.49    v4_orders_2(sK0)),
% 0.23/0.49    inference(cnf_transformation,[],[f30])).
% 0.23/0.49  fof(f78,plain,(
% 0.23/0.49    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | k2_orders_2(sK0,X0) = a_2_1_orders_2(sK0,X0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0)) )),
% 0.23/0.49    inference(subsumption_resolution,[],[f77,f44])).
% 0.23/0.49  fof(f77,plain,(
% 0.23/0.49    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_orders_2(sK0) | k2_orders_2(sK0,X0) = a_2_1_orders_2(sK0,X0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0)) )),
% 0.23/0.49    inference(resolution,[],[f53,f43])).
% 0.23/0.49  fof(f43,plain,(
% 0.23/0.49    v5_orders_2(sK0)),
% 0.23/0.49    inference(cnf_transformation,[],[f30])).
% 0.23/0.49  fof(f53,plain,(
% 0.23/0.49    ( ! [X0,X1] : (~v5_orders_2(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | k2_orders_2(X0,X1) = a_2_1_orders_2(X0,X1) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 0.23/0.49    inference(cnf_transformation,[],[f20])).
% 0.23/0.49  fof(f20,plain,(
% 0.23/0.49    ! [X0] : (! [X1] : (k2_orders_2(X0,X1) = a_2_1_orders_2(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 0.23/0.49    inference(flattening,[],[f19])).
% 0.23/0.49  fof(f19,plain,(
% 0.23/0.49    ! [X0] : (! [X1] : (k2_orders_2(X0,X1) = a_2_1_orders_2(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 0.23/0.49    inference(ennf_transformation,[],[f8])).
% 0.23/0.49  fof(f8,axiom,(
% 0.23/0.49    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k2_orders_2(X0,X1) = a_2_1_orders_2(X0,X1)))),
% 0.23/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d13_orders_2)).
% 0.23/0.49  fof(f128,plain,(
% 0.23/0.49    m1_subset_1(sK1(k2_orders_2(sK0,k2_struct_0(sK0))),k2_struct_0(sK0)) | ~r2_hidden(sK1(k2_orders_2(sK0,k2_struct_0(sK0))),a_2_1_orders_2(sK0,k2_struct_0(sK0)))),
% 0.23/0.49    inference(subsumption_resolution,[],[f127,f72])).
% 0.23/0.49  fof(f127,plain,(
% 0.23/0.49    m1_subset_1(sK1(k2_orders_2(sK0,k2_struct_0(sK0))),k2_struct_0(sK0)) | ~m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0))) | ~r2_hidden(sK1(k2_orders_2(sK0,k2_struct_0(sK0))),a_2_1_orders_2(sK0,k2_struct_0(sK0)))),
% 0.23/0.49    inference(superposition,[],[f125,f108])).
% 0.23/0.49  fof(f108,plain,(
% 0.23/0.49    sK1(k2_orders_2(sK0,k2_struct_0(sK0))) = sK3(sK1(k2_orders_2(sK0,k2_struct_0(sK0))),sK0,k2_struct_0(sK0))),
% 0.23/0.49    inference(subsumption_resolution,[],[f106,f45])).
% 0.23/0.49  fof(f106,plain,(
% 0.23/0.49    sK1(k2_orders_2(sK0,k2_struct_0(sK0))) = sK3(sK1(k2_orders_2(sK0,k2_struct_0(sK0))),sK0,k2_struct_0(sK0)) | k1_xboole_0 = k2_orders_2(sK0,k2_struct_0(sK0))),
% 0.23/0.49    inference(resolution,[],[f105,f54])).
% 0.23/0.49  fof(f105,plain,(
% 0.23/0.49    ( ! [X0] : (~r2_hidden(X0,k2_orders_2(sK0,k2_struct_0(sK0))) | sK3(X0,sK0,k2_struct_0(sK0)) = X0) )),
% 0.23/0.49    inference(forward_demodulation,[],[f103,f83])).
% 0.23/0.49  fof(f103,plain,(
% 0.23/0.49    ( ! [X0] : (~r2_hidden(X0,a_2_1_orders_2(sK0,k2_struct_0(sK0))) | sK3(X0,sK0,k2_struct_0(sK0)) = X0) )),
% 0.23/0.49    inference(resolution,[],[f102,f72])).
% 0.23/0.49  fof(f102,plain,(
% 0.23/0.49    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK0))) | ~r2_hidden(X0,a_2_1_orders_2(sK0,X1)) | sK3(X0,sK0,X1) = X0) )),
% 0.23/0.49    inference(forward_demodulation,[],[f101,f73])).
% 0.23/0.49  fof(f101,plain,(
% 0.23/0.49    ( ! [X0,X1] : (~r2_hidden(X0,a_2_1_orders_2(sK0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | sK3(X0,sK0,X1) = X0) )),
% 0.23/0.49    inference(subsumption_resolution,[],[f100,f40])).
% 0.23/0.49  fof(f100,plain,(
% 0.23/0.49    ( ! [X0,X1] : (~r2_hidden(X0,a_2_1_orders_2(sK0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | sK3(X0,sK0,X1) = X0 | v2_struct_0(sK0)) )),
% 0.23/0.49    inference(subsumption_resolution,[],[f99,f41])).
% 0.23/0.49  fof(f99,plain,(
% 0.23/0.49    ( ! [X0,X1] : (~r2_hidden(X0,a_2_1_orders_2(sK0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | sK3(X0,sK0,X1) = X0 | ~v3_orders_2(sK0) | v2_struct_0(sK0)) )),
% 0.23/0.49    inference(subsumption_resolution,[],[f98,f42])).
% 0.23/0.49  fof(f98,plain,(
% 0.23/0.49    ( ! [X0,X1] : (~r2_hidden(X0,a_2_1_orders_2(sK0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | sK3(X0,sK0,X1) = X0 | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0)) )),
% 0.23/0.49    inference(subsumption_resolution,[],[f97,f44])).
% 0.23/0.49  fof(f97,plain,(
% 0.23/0.49    ( ! [X0,X1] : (~r2_hidden(X0,a_2_1_orders_2(sK0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_orders_2(sK0) | sK3(X0,sK0,X1) = X0 | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0)) )),
% 0.23/0.49    inference(resolution,[],[f60,f43])).
% 0.23/0.49  fof(f60,plain,(
% 0.23/0.49    ( ! [X2,X0,X1] : (~v5_orders_2(X1) | ~r2_hidden(X0,a_2_1_orders_2(X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_orders_2(X1) | sK3(X0,X1,X2) = X0 | ~v4_orders_2(X1) | ~v3_orders_2(X1) | v2_struct_0(X1)) )),
% 0.23/0.49    inference(cnf_transformation,[],[f39])).
% 0.23/0.49  fof(f39,plain,(
% 0.23/0.49    ! [X0,X1,X2] : (((r2_hidden(X0,a_2_1_orders_2(X1,X2)) | ! [X3] : ((~r2_orders_2(X1,X3,sK2(X1,X2,X3)) & r2_hidden(sK2(X1,X2,X3),X2) & m1_subset_1(sK2(X1,X2,X3),u1_struct_0(X1))) | X0 != X3 | ~m1_subset_1(X3,u1_struct_0(X1)))) & ((! [X6] : (r2_orders_2(X1,sK3(X0,X1,X2),X6) | ~r2_hidden(X6,X2) | ~m1_subset_1(X6,u1_struct_0(X1))) & sK3(X0,X1,X2) = X0 & m1_subset_1(sK3(X0,X1,X2),u1_struct_0(X1))) | ~r2_hidden(X0,a_2_1_orders_2(X1,X2)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_orders_2(X1) | ~v5_orders_2(X1) | ~v4_orders_2(X1) | ~v3_orders_2(X1) | v2_struct_0(X1))),
% 0.23/0.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f36,f38,f37])).
% 0.23/0.49  fof(f37,plain,(
% 0.23/0.49    ! [X3,X2,X1] : (? [X4] : (~r2_orders_2(X1,X3,X4) & r2_hidden(X4,X2) & m1_subset_1(X4,u1_struct_0(X1))) => (~r2_orders_2(X1,X3,sK2(X1,X2,X3)) & r2_hidden(sK2(X1,X2,X3),X2) & m1_subset_1(sK2(X1,X2,X3),u1_struct_0(X1))))),
% 0.23/0.49    introduced(choice_axiom,[])).
% 0.23/0.49  fof(f38,plain,(
% 0.23/0.49    ! [X2,X1,X0] : (? [X5] : (! [X6] : (r2_orders_2(X1,X5,X6) | ~r2_hidden(X6,X2) | ~m1_subset_1(X6,u1_struct_0(X1))) & X0 = X5 & m1_subset_1(X5,u1_struct_0(X1))) => (! [X6] : (r2_orders_2(X1,sK3(X0,X1,X2),X6) | ~r2_hidden(X6,X2) | ~m1_subset_1(X6,u1_struct_0(X1))) & sK3(X0,X1,X2) = X0 & m1_subset_1(sK3(X0,X1,X2),u1_struct_0(X1))))),
% 0.23/0.49    introduced(choice_axiom,[])).
% 0.23/0.49  fof(f36,plain,(
% 0.23/0.49    ! [X0,X1,X2] : (((r2_hidden(X0,a_2_1_orders_2(X1,X2)) | ! [X3] : (? [X4] : (~r2_orders_2(X1,X3,X4) & r2_hidden(X4,X2) & m1_subset_1(X4,u1_struct_0(X1))) | X0 != X3 | ~m1_subset_1(X3,u1_struct_0(X1)))) & (? [X5] : (! [X6] : (r2_orders_2(X1,X5,X6) | ~r2_hidden(X6,X2) | ~m1_subset_1(X6,u1_struct_0(X1))) & X0 = X5 & m1_subset_1(X5,u1_struct_0(X1))) | ~r2_hidden(X0,a_2_1_orders_2(X1,X2)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_orders_2(X1) | ~v5_orders_2(X1) | ~v4_orders_2(X1) | ~v3_orders_2(X1) | v2_struct_0(X1))),
% 0.23/0.49    inference(rectify,[],[f35])).
% 0.23/0.49  fof(f35,plain,(
% 0.23/0.49    ! [X0,X1,X2] : (((r2_hidden(X0,a_2_1_orders_2(X1,X2)) | ! [X3] : (? [X4] : (~r2_orders_2(X1,X3,X4) & r2_hidden(X4,X2) & m1_subset_1(X4,u1_struct_0(X1))) | X0 != X3 | ~m1_subset_1(X3,u1_struct_0(X1)))) & (? [X3] : (! [X4] : (r2_orders_2(X1,X3,X4) | ~r2_hidden(X4,X2) | ~m1_subset_1(X4,u1_struct_0(X1))) & X0 = X3 & m1_subset_1(X3,u1_struct_0(X1))) | ~r2_hidden(X0,a_2_1_orders_2(X1,X2)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_orders_2(X1) | ~v5_orders_2(X1) | ~v4_orders_2(X1) | ~v3_orders_2(X1) | v2_struct_0(X1))),
% 0.23/0.49    inference(nnf_transformation,[],[f27])).
% 0.23/0.49  fof(f27,plain,(
% 0.23/0.49    ! [X0,X1,X2] : ((r2_hidden(X0,a_2_1_orders_2(X1,X2)) <=> ? [X3] : (! [X4] : (r2_orders_2(X1,X3,X4) | ~r2_hidden(X4,X2) | ~m1_subset_1(X4,u1_struct_0(X1))) & X0 = X3 & m1_subset_1(X3,u1_struct_0(X1)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_orders_2(X1) | ~v5_orders_2(X1) | ~v4_orders_2(X1) | ~v3_orders_2(X1) | v2_struct_0(X1))),
% 0.23/0.49    inference(flattening,[],[f26])).
% 0.23/0.49  fof(f26,plain,(
% 0.23/0.49    ! [X0,X1,X2] : ((r2_hidden(X0,a_2_1_orders_2(X1,X2)) <=> ? [X3] : (! [X4] : ((r2_orders_2(X1,X3,X4) | ~r2_hidden(X4,X2)) | ~m1_subset_1(X4,u1_struct_0(X1))) & X0 = X3 & m1_subset_1(X3,u1_struct_0(X1)))) | (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_orders_2(X1) | ~v5_orders_2(X1) | ~v4_orders_2(X1) | ~v3_orders_2(X1) | v2_struct_0(X1)))),
% 0.23/0.49    inference(ennf_transformation,[],[f11])).
% 0.23/0.49  fof(f11,axiom,(
% 0.23/0.49    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) & l1_orders_2(X1) & v5_orders_2(X1) & v4_orders_2(X1) & v3_orders_2(X1) & ~v2_struct_0(X1)) => (r2_hidden(X0,a_2_1_orders_2(X1,X2)) <=> ? [X3] : (! [X4] : (m1_subset_1(X4,u1_struct_0(X1)) => (r2_hidden(X4,X2) => r2_orders_2(X1,X3,X4))) & X0 = X3 & m1_subset_1(X3,u1_struct_0(X1)))))),
% 0.23/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fraenkel_a_2_1_orders_2)).
% 0.23/0.49  fof(f125,plain,(
% 0.23/0.49    ( ! [X0,X1] : (m1_subset_1(sK3(X0,sK0,X1),k2_struct_0(sK0)) | ~m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK0))) | ~r2_hidden(X0,a_2_1_orders_2(sK0,X1))) )),
% 0.23/0.49    inference(forward_demodulation,[],[f124,f73])).
% 0.23/0.49  fof(f124,plain,(
% 0.23/0.49    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK0))) | ~r2_hidden(X0,a_2_1_orders_2(sK0,X1)) | m1_subset_1(sK3(X0,sK0,X1),u1_struct_0(sK0))) )),
% 0.23/0.49    inference(forward_demodulation,[],[f123,f73])).
% 0.23/0.49  fof(f123,plain,(
% 0.23/0.49    ( ! [X0,X1] : (~r2_hidden(X0,a_2_1_orders_2(sK0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | m1_subset_1(sK3(X0,sK0,X1),u1_struct_0(sK0))) )),
% 0.23/0.49    inference(subsumption_resolution,[],[f122,f40])).
% 0.23/0.49  fof(f122,plain,(
% 0.23/0.49    ( ! [X0,X1] : (~r2_hidden(X0,a_2_1_orders_2(sK0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | m1_subset_1(sK3(X0,sK0,X1),u1_struct_0(sK0)) | v2_struct_0(sK0)) )),
% 0.23/0.49    inference(subsumption_resolution,[],[f121,f41])).
% 0.23/0.49  fof(f121,plain,(
% 0.23/0.49    ( ! [X0,X1] : (~r2_hidden(X0,a_2_1_orders_2(sK0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | m1_subset_1(sK3(X0,sK0,X1),u1_struct_0(sK0)) | ~v3_orders_2(sK0) | v2_struct_0(sK0)) )),
% 0.23/0.49    inference(subsumption_resolution,[],[f120,f42])).
% 0.23/0.49  fof(f120,plain,(
% 0.23/0.49    ( ! [X0,X1] : (~r2_hidden(X0,a_2_1_orders_2(sK0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | m1_subset_1(sK3(X0,sK0,X1),u1_struct_0(sK0)) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0)) )),
% 0.23/0.49    inference(subsumption_resolution,[],[f119,f44])).
% 0.23/0.49  fof(f119,plain,(
% 0.23/0.49    ( ! [X0,X1] : (~r2_hidden(X0,a_2_1_orders_2(sK0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_orders_2(sK0) | m1_subset_1(sK3(X0,sK0,X1),u1_struct_0(sK0)) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0)) )),
% 0.23/0.49    inference(resolution,[],[f59,f43])).
% 0.23/0.49  fof(f59,plain,(
% 0.23/0.49    ( ! [X2,X0,X1] : (~v5_orders_2(X1) | ~r2_hidden(X0,a_2_1_orders_2(X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_orders_2(X1) | m1_subset_1(sK3(X0,X1,X2),u1_struct_0(X1)) | ~v4_orders_2(X1) | ~v3_orders_2(X1) | v2_struct_0(X1)) )),
% 0.23/0.49    inference(cnf_transformation,[],[f39])).
% 0.23/0.49  fof(f213,plain,(
% 0.23/0.49    v1_xboole_0(k2_struct_0(sK0)) | ~m1_subset_1(sK1(k2_orders_2(sK0,k2_struct_0(sK0))),k2_struct_0(sK0))),
% 0.23/0.49    inference(resolution,[],[f204,f57])).
% 0.23/0.49  fof(f57,plain,(
% 0.23/0.49    ( ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1)) )),
% 0.23/0.49    inference(cnf_transformation,[],[f23])).
% 0.23/0.49  fof(f23,plain,(
% 0.23/0.49    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 0.23/0.49    inference(flattening,[],[f22])).
% 0.23/0.49  fof(f22,plain,(
% 0.23/0.49    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 0.23/0.49    inference(ennf_transformation,[],[f3])).
% 0.23/0.49  fof(f3,axiom,(
% 0.23/0.49    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 0.23/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).
% 0.23/0.49  fof(f204,plain,(
% 0.23/0.49    ~r2_hidden(sK1(k2_orders_2(sK0,k2_struct_0(sK0))),k2_struct_0(sK0))),
% 0.23/0.49    inference(subsumption_resolution,[],[f203,f132])).
% 0.23/0.49  fof(f203,plain,(
% 0.23/0.49    ~m1_subset_1(sK1(k2_orders_2(sK0,k2_struct_0(sK0))),k2_struct_0(sK0)) | ~r2_hidden(sK1(k2_orders_2(sK0,k2_struct_0(sK0))),k2_struct_0(sK0))),
% 0.23/0.49    inference(forward_demodulation,[],[f202,f73])).
% 0.23/0.49  fof(f202,plain,(
% 0.23/0.49    ~r2_hidden(sK1(k2_orders_2(sK0,k2_struct_0(sK0))),k2_struct_0(sK0)) | ~m1_subset_1(sK1(k2_orders_2(sK0,k2_struct_0(sK0))),u1_struct_0(sK0))),
% 0.23/0.49    inference(subsumption_resolution,[],[f201,f44])).
% 0.23/0.49  fof(f201,plain,(
% 0.23/0.49    ~r2_hidden(sK1(k2_orders_2(sK0,k2_struct_0(sK0))),k2_struct_0(sK0)) | ~m1_subset_1(sK1(k2_orders_2(sK0,k2_struct_0(sK0))),u1_struct_0(sK0)) | ~l1_orders_2(sK0)),
% 0.23/0.49    inference(subsumption_resolution,[],[f199,f132])).
% 0.23/0.49  fof(f199,plain,(
% 0.23/0.49    ~m1_subset_1(sK1(k2_orders_2(sK0,k2_struct_0(sK0))),k2_struct_0(sK0)) | ~r2_hidden(sK1(k2_orders_2(sK0,k2_struct_0(sK0))),k2_struct_0(sK0)) | ~m1_subset_1(sK1(k2_orders_2(sK0,k2_struct_0(sK0))),u1_struct_0(sK0)) | ~l1_orders_2(sK0)),
% 0.23/0.49    inference(resolution,[],[f198,f70])).
% 0.23/0.49  fof(f70,plain,(
% 0.23/0.49    ( ! [X2,X0] : (~r2_orders_2(X0,X2,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 0.23/0.49    inference(duplicate_literal_removal,[],[f66])).
% 0.23/0.49  fof(f66,plain,(
% 0.23/0.49    ( ! [X2,X0] : (~r2_orders_2(X0,X2,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 0.23/0.49    inference(equality_resolution,[],[f51])).
% 0.23/0.49  fof(f51,plain,(
% 0.23/0.49    ( ! [X2,X0,X1] : (X1 != X2 | ~r2_orders_2(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 0.23/0.49    inference(cnf_transformation,[],[f32])).
% 0.23/0.49  fof(f32,plain,(
% 0.23/0.49    ! [X0] : (! [X1] : (! [X2] : (((r2_orders_2(X0,X1,X2) | X1 = X2 | ~r1_orders_2(X0,X1,X2)) & ((X1 != X2 & r1_orders_2(X0,X1,X2)) | ~r2_orders_2(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 0.23/0.49    inference(flattening,[],[f31])).
% 0.23/0.49  fof(f31,plain,(
% 0.23/0.49    ! [X0] : (! [X1] : (! [X2] : (((r2_orders_2(X0,X1,X2) | (X1 = X2 | ~r1_orders_2(X0,X1,X2))) & ((X1 != X2 & r1_orders_2(X0,X1,X2)) | ~r2_orders_2(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 0.23/0.49    inference(nnf_transformation,[],[f18])).
% 0.23/0.49  fof(f18,plain,(
% 0.23/0.49    ! [X0] : (! [X1] : (! [X2] : ((r2_orders_2(X0,X1,X2) <=> (X1 != X2 & r1_orders_2(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 0.23/0.49    inference(ennf_transformation,[],[f7])).
% 0.23/0.49  fof(f7,axiom,(
% 0.23/0.49    ! [X0] : (l1_orders_2(X0) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r2_orders_2(X0,X1,X2) <=> (X1 != X2 & r1_orders_2(X0,X1,X2))))))),
% 0.23/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_orders_2)).
% 0.23/0.49  fof(f198,plain,(
% 0.23/0.49    ( ! [X0] : (r2_orders_2(sK0,sK1(k2_orders_2(sK0,k2_struct_0(sK0))),X0) | ~m1_subset_1(X0,k2_struct_0(sK0)) | ~r2_hidden(X0,k2_struct_0(sK0))) )),
% 0.23/0.49    inference(forward_demodulation,[],[f197,f108])).
% 0.23/0.49  fof(f197,plain,(
% 0.23/0.49    ( ! [X0] : (~m1_subset_1(X0,k2_struct_0(sK0)) | ~r2_hidden(X0,k2_struct_0(sK0)) | r2_orders_2(sK0,sK3(sK1(k2_orders_2(sK0,k2_struct_0(sK0))),sK0,k2_struct_0(sK0)),X0)) )),
% 0.23/0.49    inference(subsumption_resolution,[],[f194,f45])).
% 0.23/0.49  fof(f194,plain,(
% 0.23/0.49    ( ! [X0] : (~m1_subset_1(X0,k2_struct_0(sK0)) | ~r2_hidden(X0,k2_struct_0(sK0)) | r2_orders_2(sK0,sK3(sK1(k2_orders_2(sK0,k2_struct_0(sK0))),sK0,k2_struct_0(sK0)),X0) | k1_xboole_0 = k2_orders_2(sK0,k2_struct_0(sK0))) )),
% 0.23/0.49    inference(resolution,[],[f193,f54])).
% 0.23/0.49  fof(f193,plain,(
% 0.23/0.49    ( ! [X0,X1] : (~r2_hidden(X1,k2_orders_2(sK0,k2_struct_0(sK0))) | ~m1_subset_1(X0,k2_struct_0(sK0)) | ~r2_hidden(X0,k2_struct_0(sK0)) | r2_orders_2(sK0,sK3(X1,sK0,k2_struct_0(sK0)),X0)) )),
% 0.23/0.49    inference(forward_demodulation,[],[f191,f83])).
% 0.23/0.49  fof(f191,plain,(
% 0.23/0.49    ( ! [X0,X1] : (~m1_subset_1(X0,k2_struct_0(sK0)) | ~r2_hidden(X0,k2_struct_0(sK0)) | ~r2_hidden(X1,a_2_1_orders_2(sK0,k2_struct_0(sK0))) | r2_orders_2(sK0,sK3(X1,sK0,k2_struct_0(sK0)),X0)) )),
% 0.23/0.49    inference(resolution,[],[f190,f72])).
% 0.23/0.49  fof(f190,plain,(
% 0.23/0.49    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK0))) | ~m1_subset_1(X0,k2_struct_0(sK0)) | ~r2_hidden(X0,X1) | ~r2_hidden(X2,a_2_1_orders_2(sK0,X1)) | r2_orders_2(sK0,sK3(X2,sK0,X1),X0)) )),
% 0.23/0.49    inference(forward_demodulation,[],[f189,f73])).
% 0.23/0.49  fof(f189,plain,(
% 0.23/0.49    ( ! [X2,X0,X1] : (~m1_subset_1(X0,k2_struct_0(sK0)) | ~r2_hidden(X0,X1) | ~r2_hidden(X2,a_2_1_orders_2(sK0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | r2_orders_2(sK0,sK3(X2,sK0,X1),X0)) )),
% 0.23/0.49    inference(forward_demodulation,[],[f188,f73])).
% 0.23/0.49  fof(f188,plain,(
% 0.23/0.49    ( ! [X2,X0,X1] : (~r2_hidden(X0,X1) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~r2_hidden(X2,a_2_1_orders_2(sK0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | r2_orders_2(sK0,sK3(X2,sK0,X1),X0)) )),
% 0.23/0.49    inference(subsumption_resolution,[],[f187,f40])).
% 0.23/0.49  fof(f187,plain,(
% 0.23/0.49    ( ! [X2,X0,X1] : (~r2_hidden(X0,X1) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~r2_hidden(X2,a_2_1_orders_2(sK0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | r2_orders_2(sK0,sK3(X2,sK0,X1),X0) | v2_struct_0(sK0)) )),
% 0.23/0.49    inference(subsumption_resolution,[],[f186,f41])).
% 0.23/0.49  fof(f186,plain,(
% 0.23/0.49    ( ! [X2,X0,X1] : (~r2_hidden(X0,X1) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~r2_hidden(X2,a_2_1_orders_2(sK0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | r2_orders_2(sK0,sK3(X2,sK0,X1),X0) | ~v3_orders_2(sK0) | v2_struct_0(sK0)) )),
% 0.23/0.49    inference(subsumption_resolution,[],[f185,f42])).
% 0.23/0.49  fof(f185,plain,(
% 0.23/0.49    ( ! [X2,X0,X1] : (~r2_hidden(X0,X1) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~r2_hidden(X2,a_2_1_orders_2(sK0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | r2_orders_2(sK0,sK3(X2,sK0,X1),X0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0)) )),
% 0.23/0.49    inference(subsumption_resolution,[],[f184,f44])).
% 0.23/0.49  fof(f184,plain,(
% 0.23/0.49    ( ! [X2,X0,X1] : (~r2_hidden(X0,X1) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~r2_hidden(X2,a_2_1_orders_2(sK0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_orders_2(sK0) | r2_orders_2(sK0,sK3(X2,sK0,X1),X0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0)) )),
% 0.23/0.49    inference(resolution,[],[f61,f43])).
% 0.23/0.49  fof(f61,plain,(
% 0.23/0.49    ( ! [X6,X2,X0,X1] : (~v5_orders_2(X1) | ~r2_hidden(X6,X2) | ~m1_subset_1(X6,u1_struct_0(X1)) | ~r2_hidden(X0,a_2_1_orders_2(X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_orders_2(X1) | r2_orders_2(X1,sK3(X0,X1,X2),X6) | ~v4_orders_2(X1) | ~v3_orders_2(X1) | v2_struct_0(X1)) )),
% 0.23/0.49    inference(cnf_transformation,[],[f39])).
% 0.23/0.49  fof(f45,plain,(
% 0.23/0.49    k1_xboole_0 != k2_orders_2(sK0,k2_struct_0(sK0))),
% 0.23/0.49    inference(cnf_transformation,[],[f30])).
% 0.23/0.49  fof(f273,plain,(
% 0.23/0.49    k1_xboole_0 = k2_orders_2(sK0,k1_xboole_0)),
% 0.23/0.49    inference(resolution,[],[f272,f54])).
% 0.23/0.49  fof(f272,plain,(
% 0.23/0.49    ( ! [X0] : (~r2_hidden(X0,k2_orders_2(sK0,k1_xboole_0))) )),
% 0.23/0.49    inference(resolution,[],[f271,f72])).
% 0.23/0.49  fof(f271,plain,(
% 0.23/0.49    ( ! [X2,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k1_xboole_0)) | ~r2_hidden(X1,k2_orders_2(sK0,X2))) )),
% 0.23/0.49    inference(forward_demodulation,[],[f217,f218])).
% 0.23/0.49  fof(f217,plain,(
% 0.23/0.49    ( ! [X2,X1] : (~r2_hidden(X1,k2_orders_2(sK0,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_struct_0(sK0)))) )),
% 0.23/0.49    inference(resolution,[],[f215,f89])).
% 0.23/0.49  fof(f89,plain,(
% 0.23/0.49    ( ! [X0] : (m1_subset_1(k2_orders_2(sK0,X0),k1_zfmisc_1(k2_struct_0(sK0))) | ~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))) )),
% 0.23/0.49    inference(subsumption_resolution,[],[f88,f40])).
% 0.23/0.49  fof(f88,plain,(
% 0.23/0.49    ( ! [X0] : (m1_subset_1(k2_orders_2(sK0,X0),k1_zfmisc_1(k2_struct_0(sK0))) | ~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) | v2_struct_0(sK0)) )),
% 0.23/0.49    inference(subsumption_resolution,[],[f87,f41])).
% 0.23/0.49  fof(f87,plain,(
% 0.23/0.49    ( ! [X0] : (m1_subset_1(k2_orders_2(sK0,X0),k1_zfmisc_1(k2_struct_0(sK0))) | ~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) | ~v3_orders_2(sK0) | v2_struct_0(sK0)) )),
% 0.23/0.49    inference(subsumption_resolution,[],[f86,f42])).
% 0.23/0.49  fof(f86,plain,(
% 0.23/0.49    ( ! [X0] : (m1_subset_1(k2_orders_2(sK0,X0),k1_zfmisc_1(k2_struct_0(sK0))) | ~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0)) )),
% 0.23/0.49    inference(subsumption_resolution,[],[f85,f43])).
% 0.23/0.49  fof(f85,plain,(
% 0.23/0.49    ( ! [X0] : (m1_subset_1(k2_orders_2(sK0,X0),k1_zfmisc_1(k2_struct_0(sK0))) | ~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) | ~v5_orders_2(sK0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0)) )),
% 0.23/0.49    inference(subsumption_resolution,[],[f84,f44])).
% 0.23/0.49  fof(f84,plain,(
% 0.23/0.49    ( ! [X0] : (m1_subset_1(k2_orders_2(sK0,X0),k1_zfmisc_1(k2_struct_0(sK0))) | ~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) | ~l1_orders_2(sK0) | ~v5_orders_2(sK0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0)) )),
% 0.23/0.49    inference(superposition,[],[f58,f73])).
% 0.23/0.49  fof(f58,plain,(
% 0.23/0.49    ( ! [X0,X1] : (m1_subset_1(k2_orders_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 0.23/0.49    inference(cnf_transformation,[],[f25])).
% 0.23/0.49  fof(f25,plain,(
% 0.23/0.49    ! [X0,X1] : (m1_subset_1(k2_orders_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 0.23/0.49    inference(flattening,[],[f24])).
% 0.23/0.49  fof(f24,plain,(
% 0.23/0.49    ! [X0,X1] : (m1_subset_1(k2_orders_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 0.23/0.49    inference(ennf_transformation,[],[f9])).
% 0.23/0.49  fof(f9,axiom,(
% 0.23/0.49    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => m1_subset_1(k2_orders_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 0.23/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_orders_2)).
% 0.23/0.49  % SZS output end Proof for theBenchmark
% 0.23/0.49  % (1440)------------------------------
% 0.23/0.49  % (1440)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.23/0.49  % (1440)Termination reason: Refutation
% 0.23/0.49  
% 0.23/0.49  % (1440)Memory used [KB]: 6396
% 0.23/0.49  % (1440)Time elapsed: 0.068 s
% 0.23/0.49  % (1440)------------------------------
% 0.23/0.49  % (1440)------------------------------
% 0.23/0.49  % (1418)Success in time 0.123 s
%------------------------------------------------------------------------------
