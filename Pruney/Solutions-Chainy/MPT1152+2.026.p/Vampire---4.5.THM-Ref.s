%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:09:51 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  120 (2376 expanded)
%              Number of leaves         :   15 ( 597 expanded)
%              Depth                    :   38
%              Number of atoms          :  537 (11946 expanded)
%              Number of equality atoms :   83 (2030 expanded)
%              Maximal formula depth    :   15 (   6 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f267,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f226,f263])).

fof(f263,plain,(
    ~ spl4_10 ),
    inference(avatar_contradiction_clause,[],[f262])).

fof(f262,plain,
    ( $false
    | ~ spl4_10 ),
    inference(subsumption_resolution,[],[f261,f184])).

fof(f184,plain,(
    m1_subset_1(sK1(k2_orders_2(sK0,k2_struct_0(sK0))),k2_struct_0(sK0)) ),
    inference(superposition,[],[f170,f174])).

fof(f174,plain,(
    sK1(k2_orders_2(sK0,k2_struct_0(sK0))) = sK3(sK1(k2_orders_2(sK0,k2_struct_0(sK0))),sK0,k2_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f173,f43])).

fof(f43,plain,(
    k1_xboole_0 != k2_orders_2(sK0,k2_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,
    ( k1_xboole_0 != k2_orders_2(sK0,k2_struct_0(sK0))
    & l1_orders_2(sK0)
    & v5_orders_2(sK0)
    & v4_orders_2(sK0)
    & v3_orders_2(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f13,f27])).

fof(f27,plain,
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

fof(f13,plain,(
    ? [X0] :
      ( k1_xboole_0 != k2_orders_2(X0,k2_struct_0(X0))
      & l1_orders_2(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ? [X0] :
      ( k1_xboole_0 != k2_orders_2(X0,k2_struct_0(X0))
      & l1_orders_2(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_orders_2(X0)
          & v5_orders_2(X0)
          & v4_orders_2(X0)
          & v3_orders_2(X0)
          & ~ v2_struct_0(X0) )
       => k1_xboole_0 = k2_orders_2(X0,k2_struct_0(X0)) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f10,conjecture,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => k1_xboole_0 = k2_orders_2(X0,k2_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_orders_2)).

fof(f173,plain,
    ( k1_xboole_0 = k2_orders_2(sK0,k2_struct_0(sK0))
    | sK1(k2_orders_2(sK0,k2_struct_0(sK0))) = sK3(sK1(k2_orders_2(sK0,k2_struct_0(sK0))),sK0,k2_struct_0(sK0)) ),
    inference(forward_demodulation,[],[f172,f128])).

fof(f128,plain,(
    k2_orders_2(sK0,k2_struct_0(sK0)) = a_2_1_orders_2(sK0,k2_struct_0(sK0)) ),
    inference(resolution,[],[f83,f70])).

fof(f70,plain,(
    m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0))) ),
    inference(forward_demodulation,[],[f69,f68])).

fof(f68,plain,(
    k2_struct_0(sK0) = u1_struct_0(sK0) ),
    inference(resolution,[],[f44,f67])).

fof(f67,plain,(
    l1_struct_0(sK0) ),
    inference(resolution,[],[f46,f42])).

fof(f42,plain,(
    l1_orders_2(sK0) ),
    inference(cnf_transformation,[],[f28])).

fof(f46,plain,(
    ! [X0] :
      ( ~ l1_orders_2(X0)
      | l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_orders_2)).

fof(f44,plain,(
    ! [X0] :
      ( ~ l1_struct_0(X0)
      | k2_struct_0(X0) = u1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k2_struct_0(X0) = u1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).

fof(f69,plain,(
    m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(resolution,[],[f45,f67])).

fof(f45,plain,(
    ! [X0] :
      ( ~ l1_struct_0(X0)
      | m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_struct_0)).

fof(f83,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))
      | k2_orders_2(sK0,X0) = a_2_1_orders_2(sK0,X0) ) ),
    inference(subsumption_resolution,[],[f82,f38])).

fof(f38,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f28])).

fof(f82,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))
      | k2_orders_2(sK0,X0) = a_2_1_orders_2(sK0,X0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f81,f39])).

fof(f39,plain,(
    v3_orders_2(sK0) ),
    inference(cnf_transformation,[],[f28])).

fof(f81,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))
      | k2_orders_2(sK0,X0) = a_2_1_orders_2(sK0,X0)
      | ~ v3_orders_2(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f80,f40])).

fof(f40,plain,(
    v4_orders_2(sK0) ),
    inference(cnf_transformation,[],[f28])).

fof(f80,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))
      | k2_orders_2(sK0,X0) = a_2_1_orders_2(sK0,X0)
      | ~ v4_orders_2(sK0)
      | ~ v3_orders_2(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f79,f41])).

fof(f41,plain,(
    v5_orders_2(sK0) ),
    inference(cnf_transformation,[],[f28])).

fof(f79,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))
      | k2_orders_2(sK0,X0) = a_2_1_orders_2(sK0,X0)
      | ~ v5_orders_2(sK0)
      | ~ v4_orders_2(sK0)
      | ~ v3_orders_2(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f78,f42])).

fof(f78,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))
      | k2_orders_2(sK0,X0) = a_2_1_orders_2(sK0,X0)
      | ~ l1_orders_2(sK0)
      | ~ v5_orders_2(sK0)
      | ~ v4_orders_2(sK0)
      | ~ v3_orders_2(sK0)
      | v2_struct_0(sK0) ) ),
    inference(superposition,[],[f50,f68])).

fof(f50,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | k2_orders_2(X0,X1) = a_2_1_orders_2(X0,X1)
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f19])).

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
    inference(flattening,[],[f18])).

fof(f18,plain,(
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

fof(f172,plain,
    ( sK1(k2_orders_2(sK0,k2_struct_0(sK0))) = sK3(sK1(k2_orders_2(sK0,k2_struct_0(sK0))),sK0,k2_struct_0(sK0))
    | k1_xboole_0 = a_2_1_orders_2(sK0,k2_struct_0(sK0)) ),
    inference(forward_demodulation,[],[f171,f128])).

fof(f171,plain,
    ( sK1(a_2_1_orders_2(sK0,k2_struct_0(sK0))) = sK3(sK1(a_2_1_orders_2(sK0,k2_struct_0(sK0))),sK0,k2_struct_0(sK0))
    | k1_xboole_0 = a_2_1_orders_2(sK0,k2_struct_0(sK0)) ),
    inference(resolution,[],[f120,f70])).

fof(f120,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))
      | sK1(a_2_1_orders_2(sK0,X0)) = sK3(sK1(a_2_1_orders_2(sK0,X0)),sK0,X0)
      | k1_xboole_0 = a_2_1_orders_2(sK0,X0) ) ),
    inference(subsumption_resolution,[],[f119,f38])).

fof(f119,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))
      | sK1(a_2_1_orders_2(sK0,X0)) = sK3(sK1(a_2_1_orders_2(sK0,X0)),sK0,X0)
      | v2_struct_0(sK0)
      | k1_xboole_0 = a_2_1_orders_2(sK0,X0) ) ),
    inference(subsumption_resolution,[],[f118,f39])).

fof(f118,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))
      | sK1(a_2_1_orders_2(sK0,X0)) = sK3(sK1(a_2_1_orders_2(sK0,X0)),sK0,X0)
      | ~ v3_orders_2(sK0)
      | v2_struct_0(sK0)
      | k1_xboole_0 = a_2_1_orders_2(sK0,X0) ) ),
    inference(subsumption_resolution,[],[f117,f40])).

fof(f117,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))
      | sK1(a_2_1_orders_2(sK0,X0)) = sK3(sK1(a_2_1_orders_2(sK0,X0)),sK0,X0)
      | ~ v4_orders_2(sK0)
      | ~ v3_orders_2(sK0)
      | v2_struct_0(sK0)
      | k1_xboole_0 = a_2_1_orders_2(sK0,X0) ) ),
    inference(subsumption_resolution,[],[f116,f41])).

fof(f116,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))
      | sK1(a_2_1_orders_2(sK0,X0)) = sK3(sK1(a_2_1_orders_2(sK0,X0)),sK0,X0)
      | ~ v5_orders_2(sK0)
      | ~ v4_orders_2(sK0)
      | ~ v3_orders_2(sK0)
      | v2_struct_0(sK0)
      | k1_xboole_0 = a_2_1_orders_2(sK0,X0) ) ),
    inference(subsumption_resolution,[],[f115,f42])).

fof(f115,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))
      | sK1(a_2_1_orders_2(sK0,X0)) = sK3(sK1(a_2_1_orders_2(sK0,X0)),sK0,X0)
      | ~ l1_orders_2(sK0)
      | ~ v5_orders_2(sK0)
      | ~ v4_orders_2(sK0)
      | ~ v3_orders_2(sK0)
      | v2_struct_0(sK0)
      | k1_xboole_0 = a_2_1_orders_2(sK0,X0) ) ),
    inference(superposition,[],[f84,f68])).

fof(f84,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | sK1(a_2_1_orders_2(X0,X1)) = sK3(sK1(a_2_1_orders_2(X0,X1)),X0,X1)
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0)
      | k1_xboole_0 = a_2_1_orders_2(X0,X1) ) ),
    inference(resolution,[],[f57,f52])).

fof(f52,plain,(
    ! [X0] :
      ( r2_hidden(sK1(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( ( ! [X2,X3,X4] :
            ( k3_mcart_1(X2,X3,X4) != sK1(X0)
            | ( ~ r2_hidden(X3,X0)
              & ~ r2_hidden(X2,X0) ) )
        & r2_hidden(sK1(X0),X0) )
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f22,f31])).

fof(f31,plain,(
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

fof(f22,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ! [X2,X3,X4] :
              ( k3_mcart_1(X2,X3,X4) != X1
              | ( ~ r2_hidden(X3,X0)
                & ~ r2_hidden(X2,X0) ) )
          & r2_hidden(X1,X0) )
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ~ ( ! [X1] :
            ~ ( ! [X2,X3,X4] :
                  ~ ( k3_mcart_1(X2,X3,X4) = X1
                    & ( r2_hidden(X3,X0)
                      | r2_hidden(X2,X0) ) )
              & r2_hidden(X1,X0) )
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_mcart_1)).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,a_2_1_orders_2(X1,X2))
      | sK3(X0,X1,X2) = X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_orders_2(X1)
      | ~ v5_orders_2(X1)
      | ~ v4_orders_2(X1)
      | ~ v3_orders_2(X1)
      | v2_struct_0(X1) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f34,f36,f35])).

fof(f35,plain,(
    ! [X3,X2,X1] :
      ( ? [X4] :
          ( ~ r2_orders_2(X1,X3,X4)
          & r2_hidden(X4,X2)
          & m1_subset_1(X4,u1_struct_0(X1)) )
     => ( ~ r2_orders_2(X1,X3,sK2(X1,X2,X3))
        & r2_hidden(sK2(X1,X2,X3),X2)
        & m1_subset_1(sK2(X1,X2,X3),u1_struct_0(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,(
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

fof(f34,plain,(
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
    inference(rectify,[],[f33])).

fof(f33,plain,(
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
    inference(nnf_transformation,[],[f26])).

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
    inference(flattening,[],[f25])).

fof(f25,plain,(
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
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
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

fof(f170,plain,(
    m1_subset_1(sK3(sK1(k2_orders_2(sK0,k2_struct_0(sK0))),sK0,k2_struct_0(sK0)),k2_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f169,f43])).

fof(f169,plain,
    ( k1_xboole_0 = k2_orders_2(sK0,k2_struct_0(sK0))
    | m1_subset_1(sK3(sK1(k2_orders_2(sK0,k2_struct_0(sK0))),sK0,k2_struct_0(sK0)),k2_struct_0(sK0)) ),
    inference(forward_demodulation,[],[f168,f128])).

fof(f168,plain,
    ( m1_subset_1(sK3(sK1(k2_orders_2(sK0,k2_struct_0(sK0))),sK0,k2_struct_0(sK0)),k2_struct_0(sK0))
    | k1_xboole_0 = a_2_1_orders_2(sK0,k2_struct_0(sK0)) ),
    inference(forward_demodulation,[],[f167,f128])).

fof(f167,plain,
    ( m1_subset_1(sK3(sK1(a_2_1_orders_2(sK0,k2_struct_0(sK0))),sK0,k2_struct_0(sK0)),k2_struct_0(sK0))
    | k1_xboole_0 = a_2_1_orders_2(sK0,k2_struct_0(sK0)) ),
    inference(resolution,[],[f114,f70])).

fof(f114,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))
      | m1_subset_1(sK3(sK1(a_2_1_orders_2(sK0,X0)),sK0,X0),k2_struct_0(sK0))
      | k1_xboole_0 = a_2_1_orders_2(sK0,X0) ) ),
    inference(subsumption_resolution,[],[f113,f38])).

fof(f113,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))
      | m1_subset_1(sK3(sK1(a_2_1_orders_2(sK0,X0)),sK0,X0),k2_struct_0(sK0))
      | v2_struct_0(sK0)
      | k1_xboole_0 = a_2_1_orders_2(sK0,X0) ) ),
    inference(subsumption_resolution,[],[f112,f39])).

fof(f112,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))
      | m1_subset_1(sK3(sK1(a_2_1_orders_2(sK0,X0)),sK0,X0),k2_struct_0(sK0))
      | ~ v3_orders_2(sK0)
      | v2_struct_0(sK0)
      | k1_xboole_0 = a_2_1_orders_2(sK0,X0) ) ),
    inference(subsumption_resolution,[],[f111,f40])).

fof(f111,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))
      | m1_subset_1(sK3(sK1(a_2_1_orders_2(sK0,X0)),sK0,X0),k2_struct_0(sK0))
      | ~ v4_orders_2(sK0)
      | ~ v3_orders_2(sK0)
      | v2_struct_0(sK0)
      | k1_xboole_0 = a_2_1_orders_2(sK0,X0) ) ),
    inference(subsumption_resolution,[],[f110,f41])).

fof(f110,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))
      | m1_subset_1(sK3(sK1(a_2_1_orders_2(sK0,X0)),sK0,X0),k2_struct_0(sK0))
      | ~ v5_orders_2(sK0)
      | ~ v4_orders_2(sK0)
      | ~ v3_orders_2(sK0)
      | v2_struct_0(sK0)
      | k1_xboole_0 = a_2_1_orders_2(sK0,X0) ) ),
    inference(subsumption_resolution,[],[f109,f42])).

fof(f109,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))
      | m1_subset_1(sK3(sK1(a_2_1_orders_2(sK0,X0)),sK0,X0),k2_struct_0(sK0))
      | ~ l1_orders_2(sK0)
      | ~ v5_orders_2(sK0)
      | ~ v4_orders_2(sK0)
      | ~ v3_orders_2(sK0)
      | v2_struct_0(sK0)
      | k1_xboole_0 = a_2_1_orders_2(sK0,X0) ) ),
    inference(superposition,[],[f85,f68])).

fof(f85,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | m1_subset_1(sK3(sK1(a_2_1_orders_2(X0,X1)),X0,X1),u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0)
      | k1_xboole_0 = a_2_1_orders_2(X0,X1) ) ),
    inference(resolution,[],[f56,f52])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,a_2_1_orders_2(X1,X2))
      | m1_subset_1(sK3(X0,X1,X2),u1_struct_0(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_orders_2(X1)
      | ~ v5_orders_2(X1)
      | ~ v4_orders_2(X1)
      | ~ v3_orders_2(X1)
      | v2_struct_0(X1) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f261,plain,
    ( ~ m1_subset_1(sK1(k2_orders_2(sK0,k2_struct_0(sK0))),k2_struct_0(sK0))
    | ~ spl4_10 ),
    inference(forward_demodulation,[],[f260,f68])).

fof(f260,plain,
    ( ~ m1_subset_1(sK1(k2_orders_2(sK0,k2_struct_0(sK0))),u1_struct_0(sK0))
    | ~ spl4_10 ),
    inference(subsumption_resolution,[],[f257,f42])).

fof(f257,plain,
    ( ~ m1_subset_1(sK1(k2_orders_2(sK0,k2_struct_0(sK0))),u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | ~ spl4_10 ),
    inference(resolution,[],[f253,f66])).

fof(f66,plain,(
    ! [X2,X0] :
      ( ~ r2_orders_2(X0,X2,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(duplicate_literal_removal,[],[f62])).

fof(f62,plain,(
    ! [X2,X0] :
      ( ~ r2_orders_2(X0,X2,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(equality_resolution,[],[f48])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( X1 != X2
      | ~ r2_orders_2(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
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
    inference(flattening,[],[f29])).

fof(f29,plain,(
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
    inference(nnf_transformation,[],[f17])).

fof(f17,plain,(
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

fof(f253,plain,
    ( r2_orders_2(sK0,sK1(k2_orders_2(sK0,k2_struct_0(sK0))),sK1(k2_orders_2(sK0,k2_struct_0(sK0))))
    | ~ spl4_10 ),
    inference(forward_demodulation,[],[f251,f174])).

fof(f251,plain,
    ( r2_orders_2(sK0,sK3(sK1(k2_orders_2(sK0,k2_struct_0(sK0))),sK0,k2_struct_0(sK0)),sK1(k2_orders_2(sK0,k2_struct_0(sK0))))
    | ~ spl4_10 ),
    inference(resolution,[],[f250,f219])).

fof(f219,plain,
    ( r2_hidden(sK1(k2_orders_2(sK0,k2_struct_0(sK0))),k2_orders_2(sK0,k2_struct_0(sK0)))
    | ~ spl4_10 ),
    inference(avatar_component_clause,[],[f217])).

fof(f217,plain,
    ( spl4_10
  <=> r2_hidden(sK1(k2_orders_2(sK0,k2_struct_0(sK0))),k2_orders_2(sK0,k2_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).

fof(f250,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k2_orders_2(sK0,k2_struct_0(sK0)))
      | r2_orders_2(sK0,sK3(X0,sK0,k2_struct_0(sK0)),sK1(k2_orders_2(sK0,k2_struct_0(sK0)))) ) ),
    inference(forward_demodulation,[],[f249,f128])).

fof(f249,plain,(
    ! [X0] :
      ( r2_orders_2(sK0,sK3(X0,sK0,k2_struct_0(sK0)),sK1(k2_orders_2(sK0,k2_struct_0(sK0))))
      | ~ r2_hidden(X0,a_2_1_orders_2(sK0,k2_struct_0(sK0))) ) ),
    inference(subsumption_resolution,[],[f248,f38])).

fof(f248,plain,(
    ! [X0] :
      ( r2_orders_2(sK0,sK3(X0,sK0,k2_struct_0(sK0)),sK1(k2_orders_2(sK0,k2_struct_0(sK0))))
      | ~ r2_hidden(X0,a_2_1_orders_2(sK0,k2_struct_0(sK0)))
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f247,f39])).

fof(f247,plain,(
    ! [X0] :
      ( r2_orders_2(sK0,sK3(X0,sK0,k2_struct_0(sK0)),sK1(k2_orders_2(sK0,k2_struct_0(sK0))))
      | ~ r2_hidden(X0,a_2_1_orders_2(sK0,k2_struct_0(sK0)))
      | ~ v3_orders_2(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f246,f40])).

fof(f246,plain,(
    ! [X0] :
      ( r2_orders_2(sK0,sK3(X0,sK0,k2_struct_0(sK0)),sK1(k2_orders_2(sK0,k2_struct_0(sK0))))
      | ~ r2_hidden(X0,a_2_1_orders_2(sK0,k2_struct_0(sK0)))
      | ~ v4_orders_2(sK0)
      | ~ v3_orders_2(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f245,f41])).

fof(f245,plain,(
    ! [X0] :
      ( r2_orders_2(sK0,sK3(X0,sK0,k2_struct_0(sK0)),sK1(k2_orders_2(sK0,k2_struct_0(sK0))))
      | ~ r2_hidden(X0,a_2_1_orders_2(sK0,k2_struct_0(sK0)))
      | ~ v5_orders_2(sK0)
      | ~ v4_orders_2(sK0)
      | ~ v3_orders_2(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f244,f42])).

fof(f244,plain,(
    ! [X0] :
      ( r2_orders_2(sK0,sK3(X0,sK0,k2_struct_0(sK0)),sK1(k2_orders_2(sK0,k2_struct_0(sK0))))
      | ~ r2_hidden(X0,a_2_1_orders_2(sK0,k2_struct_0(sK0)))
      | ~ l1_orders_2(sK0)
      | ~ v5_orders_2(sK0)
      | ~ v4_orders_2(sK0)
      | ~ v3_orders_2(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f243,f70])).

fof(f243,plain,(
    ! [X0] :
      ( r2_orders_2(sK0,sK3(X0,sK0,k2_struct_0(sK0)),sK1(k2_orders_2(sK0,k2_struct_0(sK0))))
      | ~ r2_hidden(X0,a_2_1_orders_2(sK0,k2_struct_0(sK0)))
      | ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0)))
      | ~ l1_orders_2(sK0)
      | ~ v5_orders_2(sK0)
      | ~ v4_orders_2(sK0)
      | ~ v3_orders_2(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f242,f184])).

fof(f242,plain,(
    ! [X0] :
      ( ~ m1_subset_1(sK1(k2_orders_2(sK0,k2_struct_0(sK0))),k2_struct_0(sK0))
      | r2_orders_2(sK0,sK3(X0,sK0,k2_struct_0(sK0)),sK1(k2_orders_2(sK0,k2_struct_0(sK0))))
      | ~ r2_hidden(X0,a_2_1_orders_2(sK0,k2_struct_0(sK0)))
      | ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0)))
      | ~ l1_orders_2(sK0)
      | ~ v5_orders_2(sK0)
      | ~ v4_orders_2(sK0)
      | ~ v3_orders_2(sK0)
      | v2_struct_0(sK0) ) ),
    inference(superposition,[],[f185,f68])).

fof(f185,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(sK1(k2_orders_2(sK0,k2_struct_0(sK0))),u1_struct_0(X0))
      | r2_orders_2(X0,sK3(X1,X0,k2_struct_0(sK0)),sK1(k2_orders_2(sK0,k2_struct_0(sK0))))
      | ~ r2_hidden(X1,a_2_1_orders_2(X0,k2_struct_0(sK0)))
      | ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(resolution,[],[f183,f58])).

fof(f58,plain,(
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
    inference(cnf_transformation,[],[f37])).

fof(f183,plain,(
    r2_hidden(sK1(k2_orders_2(sK0,k2_struct_0(sK0))),k2_struct_0(sK0)) ),
    inference(forward_demodulation,[],[f182,f174])).

fof(f182,plain,(
    r2_hidden(sK3(sK1(k2_orders_2(sK0,k2_struct_0(sK0))),sK0,k2_struct_0(sK0)),k2_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f177,f73])).

fof(f73,plain,(
    ~ v1_xboole_0(k2_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f72,f38])).

fof(f72,plain,
    ( ~ v1_xboole_0(k2_struct_0(sK0))
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f71,f67])).

fof(f71,plain,
    ( ~ v1_xboole_0(k2_struct_0(sK0))
    | ~ l1_struct_0(sK0)
    | v2_struct_0(sK0) ),
    inference(superposition,[],[f51,f68])).

fof(f51,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
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

fof(f177,plain,
    ( v1_xboole_0(k2_struct_0(sK0))
    | r2_hidden(sK3(sK1(k2_orders_2(sK0,k2_struct_0(sK0))),sK0,k2_struct_0(sK0)),k2_struct_0(sK0)) ),
    inference(resolution,[],[f170,f55])).

fof(f55,plain,(
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
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

fof(f226,plain,(
    spl4_10 ),
    inference(avatar_contradiction_clause,[],[f225])).

fof(f225,plain,
    ( $false
    | spl4_10 ),
    inference(subsumption_resolution,[],[f224,f43])).

fof(f224,plain,
    ( k1_xboole_0 = k2_orders_2(sK0,k2_struct_0(sK0))
    | spl4_10 ),
    inference(resolution,[],[f218,f52])).

fof(f218,plain,
    ( ~ r2_hidden(sK1(k2_orders_2(sK0,k2_struct_0(sK0))),k2_orders_2(sK0,k2_struct_0(sK0)))
    | spl4_10 ),
    inference(avatar_component_clause,[],[f217])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n017.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 14:23:16 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.20/0.47  % (23781)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 0.20/0.48  % (23781)Refutation found. Thanks to Tanya!
% 0.20/0.48  % SZS status Theorem for theBenchmark
% 0.20/0.48  % SZS output start Proof for theBenchmark
% 0.20/0.48  fof(f267,plain,(
% 0.20/0.48    $false),
% 0.20/0.48    inference(avatar_sat_refutation,[],[f226,f263])).
% 0.20/0.48  fof(f263,plain,(
% 0.20/0.48    ~spl4_10),
% 0.20/0.48    inference(avatar_contradiction_clause,[],[f262])).
% 0.20/0.48  fof(f262,plain,(
% 0.20/0.48    $false | ~spl4_10),
% 0.20/0.48    inference(subsumption_resolution,[],[f261,f184])).
% 0.20/0.48  fof(f184,plain,(
% 0.20/0.48    m1_subset_1(sK1(k2_orders_2(sK0,k2_struct_0(sK0))),k2_struct_0(sK0))),
% 0.20/0.48    inference(superposition,[],[f170,f174])).
% 0.20/0.48  fof(f174,plain,(
% 0.20/0.48    sK1(k2_orders_2(sK0,k2_struct_0(sK0))) = sK3(sK1(k2_orders_2(sK0,k2_struct_0(sK0))),sK0,k2_struct_0(sK0))),
% 0.20/0.48    inference(subsumption_resolution,[],[f173,f43])).
% 0.20/0.48  fof(f43,plain,(
% 0.20/0.48    k1_xboole_0 != k2_orders_2(sK0,k2_struct_0(sK0))),
% 0.20/0.48    inference(cnf_transformation,[],[f28])).
% 0.20/0.48  fof(f28,plain,(
% 0.20/0.48    k1_xboole_0 != k2_orders_2(sK0,k2_struct_0(sK0)) & l1_orders_2(sK0) & v5_orders_2(sK0) & v4_orders_2(sK0) & v3_orders_2(sK0) & ~v2_struct_0(sK0)),
% 0.20/0.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f13,f27])).
% 0.20/0.48  fof(f27,plain,(
% 0.20/0.48    ? [X0] : (k1_xboole_0 != k2_orders_2(X0,k2_struct_0(X0)) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => (k1_xboole_0 != k2_orders_2(sK0,k2_struct_0(sK0)) & l1_orders_2(sK0) & v5_orders_2(sK0) & v4_orders_2(sK0) & v3_orders_2(sK0) & ~v2_struct_0(sK0))),
% 0.20/0.48    introduced(choice_axiom,[])).
% 0.20/0.48  fof(f13,plain,(
% 0.20/0.48    ? [X0] : (k1_xboole_0 != k2_orders_2(X0,k2_struct_0(X0)) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0))),
% 0.20/0.48    inference(flattening,[],[f12])).
% 0.20/0.48  fof(f12,plain,(
% 0.20/0.48    ? [X0] : (k1_xboole_0 != k2_orders_2(X0,k2_struct_0(X0)) & (l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)))),
% 0.20/0.48    inference(ennf_transformation,[],[f11])).
% 0.20/0.48  fof(f11,negated_conjecture,(
% 0.20/0.48    ~! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => k1_xboole_0 = k2_orders_2(X0,k2_struct_0(X0)))),
% 0.20/0.48    inference(negated_conjecture,[],[f10])).
% 0.20/0.48  fof(f10,conjecture,(
% 0.20/0.48    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => k1_xboole_0 = k2_orders_2(X0,k2_struct_0(X0)))),
% 0.20/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_orders_2)).
% 0.20/0.48  fof(f173,plain,(
% 0.20/0.48    k1_xboole_0 = k2_orders_2(sK0,k2_struct_0(sK0)) | sK1(k2_orders_2(sK0,k2_struct_0(sK0))) = sK3(sK1(k2_orders_2(sK0,k2_struct_0(sK0))),sK0,k2_struct_0(sK0))),
% 0.20/0.48    inference(forward_demodulation,[],[f172,f128])).
% 0.20/0.48  fof(f128,plain,(
% 0.20/0.48    k2_orders_2(sK0,k2_struct_0(sK0)) = a_2_1_orders_2(sK0,k2_struct_0(sK0))),
% 0.20/0.48    inference(resolution,[],[f83,f70])).
% 0.20/0.48  fof(f70,plain,(
% 0.20/0.48    m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0)))),
% 0.20/0.48    inference(forward_demodulation,[],[f69,f68])).
% 0.20/0.48  fof(f68,plain,(
% 0.20/0.48    k2_struct_0(sK0) = u1_struct_0(sK0)),
% 0.20/0.48    inference(resolution,[],[f44,f67])).
% 0.20/0.48  fof(f67,plain,(
% 0.20/0.48    l1_struct_0(sK0)),
% 0.20/0.48    inference(resolution,[],[f46,f42])).
% 0.20/0.48  fof(f42,plain,(
% 0.20/0.48    l1_orders_2(sK0)),
% 0.20/0.48    inference(cnf_transformation,[],[f28])).
% 0.20/0.48  fof(f46,plain,(
% 0.20/0.48    ( ! [X0] : (~l1_orders_2(X0) | l1_struct_0(X0)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f16])).
% 0.20/0.48  fof(f16,plain,(
% 0.20/0.48    ! [X0] : (l1_struct_0(X0) | ~l1_orders_2(X0))),
% 0.20/0.48    inference(ennf_transformation,[],[f8])).
% 0.20/0.48  fof(f8,axiom,(
% 0.20/0.48    ! [X0] : (l1_orders_2(X0) => l1_struct_0(X0))),
% 0.20/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_orders_2)).
% 0.20/0.48  fof(f44,plain,(
% 0.20/0.48    ( ! [X0] : (~l1_struct_0(X0) | k2_struct_0(X0) = u1_struct_0(X0)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f14])).
% 0.20/0.48  fof(f14,plain,(
% 0.20/0.48    ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0))),
% 0.20/0.48    inference(ennf_transformation,[],[f3])).
% 0.20/0.48  fof(f3,axiom,(
% 0.20/0.48    ! [X0] : (l1_struct_0(X0) => k2_struct_0(X0) = u1_struct_0(X0))),
% 0.20/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).
% 0.20/0.48  fof(f69,plain,(
% 0.20/0.48    m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.20/0.48    inference(resolution,[],[f45,f67])).
% 0.20/0.48  fof(f45,plain,(
% 0.20/0.48    ( ! [X0] : (~l1_struct_0(X0) | m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0)))) )),
% 0.20/0.48    inference(cnf_transformation,[],[f15])).
% 0.20/0.48  fof(f15,plain,(
% 0.20/0.48    ! [X0] : (m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0))) | ~l1_struct_0(X0))),
% 0.20/0.48    inference(ennf_transformation,[],[f4])).
% 0.20/0.48  fof(f4,axiom,(
% 0.20/0.48    ! [X0] : (l1_struct_0(X0) => m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0))))),
% 0.20/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_struct_0)).
% 0.20/0.48  fof(f83,plain,(
% 0.20/0.48    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) | k2_orders_2(sK0,X0) = a_2_1_orders_2(sK0,X0)) )),
% 0.20/0.48    inference(subsumption_resolution,[],[f82,f38])).
% 0.20/0.48  fof(f38,plain,(
% 0.20/0.48    ~v2_struct_0(sK0)),
% 0.20/0.48    inference(cnf_transformation,[],[f28])).
% 0.20/0.48  fof(f82,plain,(
% 0.20/0.48    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) | k2_orders_2(sK0,X0) = a_2_1_orders_2(sK0,X0) | v2_struct_0(sK0)) )),
% 0.20/0.48    inference(subsumption_resolution,[],[f81,f39])).
% 0.20/0.48  fof(f39,plain,(
% 0.20/0.48    v3_orders_2(sK0)),
% 0.20/0.48    inference(cnf_transformation,[],[f28])).
% 0.20/0.48  fof(f81,plain,(
% 0.20/0.48    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) | k2_orders_2(sK0,X0) = a_2_1_orders_2(sK0,X0) | ~v3_orders_2(sK0) | v2_struct_0(sK0)) )),
% 0.20/0.48    inference(subsumption_resolution,[],[f80,f40])).
% 0.20/0.48  fof(f40,plain,(
% 0.20/0.48    v4_orders_2(sK0)),
% 0.20/0.48    inference(cnf_transformation,[],[f28])).
% 0.20/0.48  fof(f80,plain,(
% 0.20/0.48    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) | k2_orders_2(sK0,X0) = a_2_1_orders_2(sK0,X0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0)) )),
% 0.20/0.48    inference(subsumption_resolution,[],[f79,f41])).
% 0.20/0.48  fof(f41,plain,(
% 0.20/0.48    v5_orders_2(sK0)),
% 0.20/0.48    inference(cnf_transformation,[],[f28])).
% 0.20/0.48  fof(f79,plain,(
% 0.20/0.48    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) | k2_orders_2(sK0,X0) = a_2_1_orders_2(sK0,X0) | ~v5_orders_2(sK0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0)) )),
% 0.20/0.48    inference(subsumption_resolution,[],[f78,f42])).
% 0.20/0.48  fof(f78,plain,(
% 0.20/0.48    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) | k2_orders_2(sK0,X0) = a_2_1_orders_2(sK0,X0) | ~l1_orders_2(sK0) | ~v5_orders_2(sK0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0)) )),
% 0.20/0.48    inference(superposition,[],[f50,f68])).
% 0.20/0.48  fof(f50,plain,(
% 0.20/0.48    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | k2_orders_2(X0,X1) = a_2_1_orders_2(X0,X1) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f19])).
% 0.20/0.48  fof(f19,plain,(
% 0.20/0.48    ! [X0] : (! [X1] : (k2_orders_2(X0,X1) = a_2_1_orders_2(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 0.20/0.48    inference(flattening,[],[f18])).
% 0.20/0.48  fof(f18,plain,(
% 0.20/0.48    ! [X0] : (! [X1] : (k2_orders_2(X0,X1) = a_2_1_orders_2(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 0.20/0.48    inference(ennf_transformation,[],[f7])).
% 0.20/0.48  fof(f7,axiom,(
% 0.20/0.48    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k2_orders_2(X0,X1) = a_2_1_orders_2(X0,X1)))),
% 0.20/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d13_orders_2)).
% 0.20/0.48  fof(f172,plain,(
% 0.20/0.48    sK1(k2_orders_2(sK0,k2_struct_0(sK0))) = sK3(sK1(k2_orders_2(sK0,k2_struct_0(sK0))),sK0,k2_struct_0(sK0)) | k1_xboole_0 = a_2_1_orders_2(sK0,k2_struct_0(sK0))),
% 0.20/0.48    inference(forward_demodulation,[],[f171,f128])).
% 0.20/0.48  fof(f171,plain,(
% 0.20/0.48    sK1(a_2_1_orders_2(sK0,k2_struct_0(sK0))) = sK3(sK1(a_2_1_orders_2(sK0,k2_struct_0(sK0))),sK0,k2_struct_0(sK0)) | k1_xboole_0 = a_2_1_orders_2(sK0,k2_struct_0(sK0))),
% 0.20/0.48    inference(resolution,[],[f120,f70])).
% 0.20/0.48  fof(f120,plain,(
% 0.20/0.48    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) | sK1(a_2_1_orders_2(sK0,X0)) = sK3(sK1(a_2_1_orders_2(sK0,X0)),sK0,X0) | k1_xboole_0 = a_2_1_orders_2(sK0,X0)) )),
% 0.20/0.48    inference(subsumption_resolution,[],[f119,f38])).
% 0.20/0.48  fof(f119,plain,(
% 0.20/0.48    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) | sK1(a_2_1_orders_2(sK0,X0)) = sK3(sK1(a_2_1_orders_2(sK0,X0)),sK0,X0) | v2_struct_0(sK0) | k1_xboole_0 = a_2_1_orders_2(sK0,X0)) )),
% 0.20/0.48    inference(subsumption_resolution,[],[f118,f39])).
% 0.20/0.48  fof(f118,plain,(
% 0.20/0.48    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) | sK1(a_2_1_orders_2(sK0,X0)) = sK3(sK1(a_2_1_orders_2(sK0,X0)),sK0,X0) | ~v3_orders_2(sK0) | v2_struct_0(sK0) | k1_xboole_0 = a_2_1_orders_2(sK0,X0)) )),
% 0.20/0.48    inference(subsumption_resolution,[],[f117,f40])).
% 0.20/0.48  fof(f117,plain,(
% 0.20/0.48    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) | sK1(a_2_1_orders_2(sK0,X0)) = sK3(sK1(a_2_1_orders_2(sK0,X0)),sK0,X0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0) | k1_xboole_0 = a_2_1_orders_2(sK0,X0)) )),
% 0.20/0.48    inference(subsumption_resolution,[],[f116,f41])).
% 0.20/0.48  fof(f116,plain,(
% 0.20/0.48    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) | sK1(a_2_1_orders_2(sK0,X0)) = sK3(sK1(a_2_1_orders_2(sK0,X0)),sK0,X0) | ~v5_orders_2(sK0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0) | k1_xboole_0 = a_2_1_orders_2(sK0,X0)) )),
% 0.20/0.48    inference(subsumption_resolution,[],[f115,f42])).
% 0.20/0.48  fof(f115,plain,(
% 0.20/0.48    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) | sK1(a_2_1_orders_2(sK0,X0)) = sK3(sK1(a_2_1_orders_2(sK0,X0)),sK0,X0) | ~l1_orders_2(sK0) | ~v5_orders_2(sK0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0) | k1_xboole_0 = a_2_1_orders_2(sK0,X0)) )),
% 0.20/0.48    inference(superposition,[],[f84,f68])).
% 0.20/0.48  fof(f84,plain,(
% 0.20/0.48    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | sK1(a_2_1_orders_2(X0,X1)) = sK3(sK1(a_2_1_orders_2(X0,X1)),X0,X1) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0) | k1_xboole_0 = a_2_1_orders_2(X0,X1)) )),
% 0.20/0.48    inference(resolution,[],[f57,f52])).
% 0.20/0.48  fof(f52,plain,(
% 0.20/0.48    ( ! [X0] : (r2_hidden(sK1(X0),X0) | k1_xboole_0 = X0) )),
% 0.20/0.48    inference(cnf_transformation,[],[f32])).
% 0.20/0.48  fof(f32,plain,(
% 0.20/0.48    ! [X0] : ((! [X2,X3,X4] : (k3_mcart_1(X2,X3,X4) != sK1(X0) | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(sK1(X0),X0)) | k1_xboole_0 = X0)),
% 0.20/0.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f22,f31])).
% 0.20/0.48  fof(f31,plain,(
% 0.20/0.48    ! [X0] : (? [X1] : (! [X2,X3,X4] : (k3_mcart_1(X2,X3,X4) != X1 | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(X1,X0)) => (! [X4,X3,X2] : (k3_mcart_1(X2,X3,X4) != sK1(X0) | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(sK1(X0),X0)))),
% 0.20/0.48    introduced(choice_axiom,[])).
% 0.20/0.48  fof(f22,plain,(
% 0.20/0.48    ! [X0] : (? [X1] : (! [X2,X3,X4] : (k3_mcart_1(X2,X3,X4) != X1 | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(X1,X0)) | k1_xboole_0 = X0)),
% 0.20/0.48    inference(ennf_transformation,[],[f2])).
% 0.20/0.48  fof(f2,axiom,(
% 0.20/0.48    ! [X0] : ~(! [X1] : ~(! [X2,X3,X4] : ~(k3_mcart_1(X2,X3,X4) = X1 & (r2_hidden(X3,X0) | r2_hidden(X2,X0))) & r2_hidden(X1,X0)) & k1_xboole_0 != X0)),
% 0.20/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_mcart_1)).
% 0.20/0.48  fof(f57,plain,(
% 0.20/0.48    ( ! [X2,X0,X1] : (~r2_hidden(X0,a_2_1_orders_2(X1,X2)) | sK3(X0,X1,X2) = X0 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_orders_2(X1) | ~v5_orders_2(X1) | ~v4_orders_2(X1) | ~v3_orders_2(X1) | v2_struct_0(X1)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f37])).
% 0.20/0.48  fof(f37,plain,(
% 0.20/0.48    ! [X0,X1,X2] : (((r2_hidden(X0,a_2_1_orders_2(X1,X2)) | ! [X3] : ((~r2_orders_2(X1,X3,sK2(X1,X2,X3)) & r2_hidden(sK2(X1,X2,X3),X2) & m1_subset_1(sK2(X1,X2,X3),u1_struct_0(X1))) | X0 != X3 | ~m1_subset_1(X3,u1_struct_0(X1)))) & ((! [X6] : (r2_orders_2(X1,sK3(X0,X1,X2),X6) | ~r2_hidden(X6,X2) | ~m1_subset_1(X6,u1_struct_0(X1))) & sK3(X0,X1,X2) = X0 & m1_subset_1(sK3(X0,X1,X2),u1_struct_0(X1))) | ~r2_hidden(X0,a_2_1_orders_2(X1,X2)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_orders_2(X1) | ~v5_orders_2(X1) | ~v4_orders_2(X1) | ~v3_orders_2(X1) | v2_struct_0(X1))),
% 0.20/0.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f34,f36,f35])).
% 0.20/0.48  fof(f35,plain,(
% 0.20/0.48    ! [X3,X2,X1] : (? [X4] : (~r2_orders_2(X1,X3,X4) & r2_hidden(X4,X2) & m1_subset_1(X4,u1_struct_0(X1))) => (~r2_orders_2(X1,X3,sK2(X1,X2,X3)) & r2_hidden(sK2(X1,X2,X3),X2) & m1_subset_1(sK2(X1,X2,X3),u1_struct_0(X1))))),
% 0.20/0.48    introduced(choice_axiom,[])).
% 0.20/0.48  fof(f36,plain,(
% 0.20/0.48    ! [X2,X1,X0] : (? [X5] : (! [X6] : (r2_orders_2(X1,X5,X6) | ~r2_hidden(X6,X2) | ~m1_subset_1(X6,u1_struct_0(X1))) & X0 = X5 & m1_subset_1(X5,u1_struct_0(X1))) => (! [X6] : (r2_orders_2(X1,sK3(X0,X1,X2),X6) | ~r2_hidden(X6,X2) | ~m1_subset_1(X6,u1_struct_0(X1))) & sK3(X0,X1,X2) = X0 & m1_subset_1(sK3(X0,X1,X2),u1_struct_0(X1))))),
% 0.20/0.48    introduced(choice_axiom,[])).
% 0.20/0.48  fof(f34,plain,(
% 0.20/0.48    ! [X0,X1,X2] : (((r2_hidden(X0,a_2_1_orders_2(X1,X2)) | ! [X3] : (? [X4] : (~r2_orders_2(X1,X3,X4) & r2_hidden(X4,X2) & m1_subset_1(X4,u1_struct_0(X1))) | X0 != X3 | ~m1_subset_1(X3,u1_struct_0(X1)))) & (? [X5] : (! [X6] : (r2_orders_2(X1,X5,X6) | ~r2_hidden(X6,X2) | ~m1_subset_1(X6,u1_struct_0(X1))) & X0 = X5 & m1_subset_1(X5,u1_struct_0(X1))) | ~r2_hidden(X0,a_2_1_orders_2(X1,X2)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_orders_2(X1) | ~v5_orders_2(X1) | ~v4_orders_2(X1) | ~v3_orders_2(X1) | v2_struct_0(X1))),
% 0.20/0.48    inference(rectify,[],[f33])).
% 0.20/0.48  fof(f33,plain,(
% 0.20/0.48    ! [X0,X1,X2] : (((r2_hidden(X0,a_2_1_orders_2(X1,X2)) | ! [X3] : (? [X4] : (~r2_orders_2(X1,X3,X4) & r2_hidden(X4,X2) & m1_subset_1(X4,u1_struct_0(X1))) | X0 != X3 | ~m1_subset_1(X3,u1_struct_0(X1)))) & (? [X3] : (! [X4] : (r2_orders_2(X1,X3,X4) | ~r2_hidden(X4,X2) | ~m1_subset_1(X4,u1_struct_0(X1))) & X0 = X3 & m1_subset_1(X3,u1_struct_0(X1))) | ~r2_hidden(X0,a_2_1_orders_2(X1,X2)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_orders_2(X1) | ~v5_orders_2(X1) | ~v4_orders_2(X1) | ~v3_orders_2(X1) | v2_struct_0(X1))),
% 0.20/0.48    inference(nnf_transformation,[],[f26])).
% 0.20/0.48  fof(f26,plain,(
% 0.20/0.48    ! [X0,X1,X2] : ((r2_hidden(X0,a_2_1_orders_2(X1,X2)) <=> ? [X3] : (! [X4] : (r2_orders_2(X1,X3,X4) | ~r2_hidden(X4,X2) | ~m1_subset_1(X4,u1_struct_0(X1))) & X0 = X3 & m1_subset_1(X3,u1_struct_0(X1)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_orders_2(X1) | ~v5_orders_2(X1) | ~v4_orders_2(X1) | ~v3_orders_2(X1) | v2_struct_0(X1))),
% 0.20/0.48    inference(flattening,[],[f25])).
% 0.20/0.48  fof(f25,plain,(
% 0.20/0.48    ! [X0,X1,X2] : ((r2_hidden(X0,a_2_1_orders_2(X1,X2)) <=> ? [X3] : (! [X4] : ((r2_orders_2(X1,X3,X4) | ~r2_hidden(X4,X2)) | ~m1_subset_1(X4,u1_struct_0(X1))) & X0 = X3 & m1_subset_1(X3,u1_struct_0(X1)))) | (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_orders_2(X1) | ~v5_orders_2(X1) | ~v4_orders_2(X1) | ~v3_orders_2(X1) | v2_struct_0(X1)))),
% 0.20/0.48    inference(ennf_transformation,[],[f9])).
% 0.20/0.48  fof(f9,axiom,(
% 0.20/0.48    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) & l1_orders_2(X1) & v5_orders_2(X1) & v4_orders_2(X1) & v3_orders_2(X1) & ~v2_struct_0(X1)) => (r2_hidden(X0,a_2_1_orders_2(X1,X2)) <=> ? [X3] : (! [X4] : (m1_subset_1(X4,u1_struct_0(X1)) => (r2_hidden(X4,X2) => r2_orders_2(X1,X3,X4))) & X0 = X3 & m1_subset_1(X3,u1_struct_0(X1)))))),
% 0.20/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fraenkel_a_2_1_orders_2)).
% 0.20/0.48  fof(f170,plain,(
% 0.20/0.48    m1_subset_1(sK3(sK1(k2_orders_2(sK0,k2_struct_0(sK0))),sK0,k2_struct_0(sK0)),k2_struct_0(sK0))),
% 0.20/0.48    inference(subsumption_resolution,[],[f169,f43])).
% 0.20/0.48  fof(f169,plain,(
% 0.20/0.48    k1_xboole_0 = k2_orders_2(sK0,k2_struct_0(sK0)) | m1_subset_1(sK3(sK1(k2_orders_2(sK0,k2_struct_0(sK0))),sK0,k2_struct_0(sK0)),k2_struct_0(sK0))),
% 0.20/0.48    inference(forward_demodulation,[],[f168,f128])).
% 0.20/0.48  fof(f168,plain,(
% 0.20/0.48    m1_subset_1(sK3(sK1(k2_orders_2(sK0,k2_struct_0(sK0))),sK0,k2_struct_0(sK0)),k2_struct_0(sK0)) | k1_xboole_0 = a_2_1_orders_2(sK0,k2_struct_0(sK0))),
% 0.20/0.48    inference(forward_demodulation,[],[f167,f128])).
% 0.20/0.48  fof(f167,plain,(
% 0.20/0.48    m1_subset_1(sK3(sK1(a_2_1_orders_2(sK0,k2_struct_0(sK0))),sK0,k2_struct_0(sK0)),k2_struct_0(sK0)) | k1_xboole_0 = a_2_1_orders_2(sK0,k2_struct_0(sK0))),
% 0.20/0.48    inference(resolution,[],[f114,f70])).
% 0.20/0.48  fof(f114,plain,(
% 0.20/0.48    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) | m1_subset_1(sK3(sK1(a_2_1_orders_2(sK0,X0)),sK0,X0),k2_struct_0(sK0)) | k1_xboole_0 = a_2_1_orders_2(sK0,X0)) )),
% 0.20/0.48    inference(subsumption_resolution,[],[f113,f38])).
% 0.20/0.48  fof(f113,plain,(
% 0.20/0.48    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) | m1_subset_1(sK3(sK1(a_2_1_orders_2(sK0,X0)),sK0,X0),k2_struct_0(sK0)) | v2_struct_0(sK0) | k1_xboole_0 = a_2_1_orders_2(sK0,X0)) )),
% 0.20/0.48    inference(subsumption_resolution,[],[f112,f39])).
% 0.20/0.48  fof(f112,plain,(
% 0.20/0.48    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) | m1_subset_1(sK3(sK1(a_2_1_orders_2(sK0,X0)),sK0,X0),k2_struct_0(sK0)) | ~v3_orders_2(sK0) | v2_struct_0(sK0) | k1_xboole_0 = a_2_1_orders_2(sK0,X0)) )),
% 0.20/0.48    inference(subsumption_resolution,[],[f111,f40])).
% 0.20/0.48  fof(f111,plain,(
% 0.20/0.48    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) | m1_subset_1(sK3(sK1(a_2_1_orders_2(sK0,X0)),sK0,X0),k2_struct_0(sK0)) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0) | k1_xboole_0 = a_2_1_orders_2(sK0,X0)) )),
% 0.20/0.48    inference(subsumption_resolution,[],[f110,f41])).
% 0.20/0.48  fof(f110,plain,(
% 0.20/0.48    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) | m1_subset_1(sK3(sK1(a_2_1_orders_2(sK0,X0)),sK0,X0),k2_struct_0(sK0)) | ~v5_orders_2(sK0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0) | k1_xboole_0 = a_2_1_orders_2(sK0,X0)) )),
% 0.20/0.48    inference(subsumption_resolution,[],[f109,f42])).
% 0.20/0.48  fof(f109,plain,(
% 0.20/0.48    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) | m1_subset_1(sK3(sK1(a_2_1_orders_2(sK0,X0)),sK0,X0),k2_struct_0(sK0)) | ~l1_orders_2(sK0) | ~v5_orders_2(sK0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0) | k1_xboole_0 = a_2_1_orders_2(sK0,X0)) )),
% 0.20/0.48    inference(superposition,[],[f85,f68])).
% 0.20/0.48  fof(f85,plain,(
% 0.20/0.48    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | m1_subset_1(sK3(sK1(a_2_1_orders_2(X0,X1)),X0,X1),u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0) | k1_xboole_0 = a_2_1_orders_2(X0,X1)) )),
% 0.20/0.48    inference(resolution,[],[f56,f52])).
% 0.20/0.48  fof(f56,plain,(
% 0.20/0.48    ( ! [X2,X0,X1] : (~r2_hidden(X0,a_2_1_orders_2(X1,X2)) | m1_subset_1(sK3(X0,X1,X2),u1_struct_0(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_orders_2(X1) | ~v5_orders_2(X1) | ~v4_orders_2(X1) | ~v3_orders_2(X1) | v2_struct_0(X1)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f37])).
% 0.20/0.48  fof(f261,plain,(
% 0.20/0.48    ~m1_subset_1(sK1(k2_orders_2(sK0,k2_struct_0(sK0))),k2_struct_0(sK0)) | ~spl4_10),
% 0.20/0.48    inference(forward_demodulation,[],[f260,f68])).
% 0.20/0.48  fof(f260,plain,(
% 0.20/0.48    ~m1_subset_1(sK1(k2_orders_2(sK0,k2_struct_0(sK0))),u1_struct_0(sK0)) | ~spl4_10),
% 0.20/0.48    inference(subsumption_resolution,[],[f257,f42])).
% 0.20/0.48  fof(f257,plain,(
% 0.20/0.48    ~m1_subset_1(sK1(k2_orders_2(sK0,k2_struct_0(sK0))),u1_struct_0(sK0)) | ~l1_orders_2(sK0) | ~spl4_10),
% 0.20/0.48    inference(resolution,[],[f253,f66])).
% 0.20/0.48  fof(f66,plain,(
% 0.20/0.48    ( ! [X2,X0] : (~r2_orders_2(X0,X2,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 0.20/0.48    inference(duplicate_literal_removal,[],[f62])).
% 0.20/0.48  fof(f62,plain,(
% 0.20/0.48    ( ! [X2,X0] : (~r2_orders_2(X0,X2,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 0.20/0.48    inference(equality_resolution,[],[f48])).
% 0.20/0.48  fof(f48,plain,(
% 0.20/0.48    ( ! [X2,X0,X1] : (X1 != X2 | ~r2_orders_2(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f30])).
% 0.20/0.48  fof(f30,plain,(
% 0.20/0.48    ! [X0] : (! [X1] : (! [X2] : (((r2_orders_2(X0,X1,X2) | X1 = X2 | ~r1_orders_2(X0,X1,X2)) & ((X1 != X2 & r1_orders_2(X0,X1,X2)) | ~r2_orders_2(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 0.20/0.48    inference(flattening,[],[f29])).
% 0.20/0.48  fof(f29,plain,(
% 0.20/0.48    ! [X0] : (! [X1] : (! [X2] : (((r2_orders_2(X0,X1,X2) | (X1 = X2 | ~r1_orders_2(X0,X1,X2))) & ((X1 != X2 & r1_orders_2(X0,X1,X2)) | ~r2_orders_2(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 0.20/0.48    inference(nnf_transformation,[],[f17])).
% 0.20/0.48  fof(f17,plain,(
% 0.20/0.48    ! [X0] : (! [X1] : (! [X2] : ((r2_orders_2(X0,X1,X2) <=> (X1 != X2 & r1_orders_2(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 0.20/0.48    inference(ennf_transformation,[],[f6])).
% 0.20/0.48  fof(f6,axiom,(
% 0.20/0.48    ! [X0] : (l1_orders_2(X0) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r2_orders_2(X0,X1,X2) <=> (X1 != X2 & r1_orders_2(X0,X1,X2))))))),
% 0.20/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_orders_2)).
% 0.20/0.48  fof(f253,plain,(
% 0.20/0.48    r2_orders_2(sK0,sK1(k2_orders_2(sK0,k2_struct_0(sK0))),sK1(k2_orders_2(sK0,k2_struct_0(sK0)))) | ~spl4_10),
% 0.20/0.48    inference(forward_demodulation,[],[f251,f174])).
% 0.20/0.48  fof(f251,plain,(
% 0.20/0.48    r2_orders_2(sK0,sK3(sK1(k2_orders_2(sK0,k2_struct_0(sK0))),sK0,k2_struct_0(sK0)),sK1(k2_orders_2(sK0,k2_struct_0(sK0)))) | ~spl4_10),
% 0.20/0.48    inference(resolution,[],[f250,f219])).
% 0.20/0.48  fof(f219,plain,(
% 0.20/0.48    r2_hidden(sK1(k2_orders_2(sK0,k2_struct_0(sK0))),k2_orders_2(sK0,k2_struct_0(sK0))) | ~spl4_10),
% 0.20/0.48    inference(avatar_component_clause,[],[f217])).
% 0.20/0.48  fof(f217,plain,(
% 0.20/0.48    spl4_10 <=> r2_hidden(sK1(k2_orders_2(sK0,k2_struct_0(sK0))),k2_orders_2(sK0,k2_struct_0(sK0)))),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).
% 0.20/0.48  fof(f250,plain,(
% 0.20/0.48    ( ! [X0] : (~r2_hidden(X0,k2_orders_2(sK0,k2_struct_0(sK0))) | r2_orders_2(sK0,sK3(X0,sK0,k2_struct_0(sK0)),sK1(k2_orders_2(sK0,k2_struct_0(sK0))))) )),
% 0.20/0.48    inference(forward_demodulation,[],[f249,f128])).
% 0.20/0.48  fof(f249,plain,(
% 0.20/0.48    ( ! [X0] : (r2_orders_2(sK0,sK3(X0,sK0,k2_struct_0(sK0)),sK1(k2_orders_2(sK0,k2_struct_0(sK0)))) | ~r2_hidden(X0,a_2_1_orders_2(sK0,k2_struct_0(sK0)))) )),
% 0.20/0.48    inference(subsumption_resolution,[],[f248,f38])).
% 0.20/0.48  fof(f248,plain,(
% 0.20/0.48    ( ! [X0] : (r2_orders_2(sK0,sK3(X0,sK0,k2_struct_0(sK0)),sK1(k2_orders_2(sK0,k2_struct_0(sK0)))) | ~r2_hidden(X0,a_2_1_orders_2(sK0,k2_struct_0(sK0))) | v2_struct_0(sK0)) )),
% 0.20/0.48    inference(subsumption_resolution,[],[f247,f39])).
% 0.20/0.48  fof(f247,plain,(
% 0.20/0.48    ( ! [X0] : (r2_orders_2(sK0,sK3(X0,sK0,k2_struct_0(sK0)),sK1(k2_orders_2(sK0,k2_struct_0(sK0)))) | ~r2_hidden(X0,a_2_1_orders_2(sK0,k2_struct_0(sK0))) | ~v3_orders_2(sK0) | v2_struct_0(sK0)) )),
% 0.20/0.48    inference(subsumption_resolution,[],[f246,f40])).
% 0.20/0.48  fof(f246,plain,(
% 0.20/0.48    ( ! [X0] : (r2_orders_2(sK0,sK3(X0,sK0,k2_struct_0(sK0)),sK1(k2_orders_2(sK0,k2_struct_0(sK0)))) | ~r2_hidden(X0,a_2_1_orders_2(sK0,k2_struct_0(sK0))) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0)) )),
% 0.20/0.48    inference(subsumption_resolution,[],[f245,f41])).
% 0.20/0.48  fof(f245,plain,(
% 0.20/0.48    ( ! [X0] : (r2_orders_2(sK0,sK3(X0,sK0,k2_struct_0(sK0)),sK1(k2_orders_2(sK0,k2_struct_0(sK0)))) | ~r2_hidden(X0,a_2_1_orders_2(sK0,k2_struct_0(sK0))) | ~v5_orders_2(sK0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0)) )),
% 0.20/0.48    inference(subsumption_resolution,[],[f244,f42])).
% 0.20/0.48  fof(f244,plain,(
% 0.20/0.48    ( ! [X0] : (r2_orders_2(sK0,sK3(X0,sK0,k2_struct_0(sK0)),sK1(k2_orders_2(sK0,k2_struct_0(sK0)))) | ~r2_hidden(X0,a_2_1_orders_2(sK0,k2_struct_0(sK0))) | ~l1_orders_2(sK0) | ~v5_orders_2(sK0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0)) )),
% 0.20/0.48    inference(subsumption_resolution,[],[f243,f70])).
% 0.20/0.48  fof(f243,plain,(
% 0.20/0.48    ( ! [X0] : (r2_orders_2(sK0,sK3(X0,sK0,k2_struct_0(sK0)),sK1(k2_orders_2(sK0,k2_struct_0(sK0)))) | ~r2_hidden(X0,a_2_1_orders_2(sK0,k2_struct_0(sK0))) | ~m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0))) | ~l1_orders_2(sK0) | ~v5_orders_2(sK0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0)) )),
% 0.20/0.48    inference(subsumption_resolution,[],[f242,f184])).
% 0.20/0.48  fof(f242,plain,(
% 0.20/0.48    ( ! [X0] : (~m1_subset_1(sK1(k2_orders_2(sK0,k2_struct_0(sK0))),k2_struct_0(sK0)) | r2_orders_2(sK0,sK3(X0,sK0,k2_struct_0(sK0)),sK1(k2_orders_2(sK0,k2_struct_0(sK0)))) | ~r2_hidden(X0,a_2_1_orders_2(sK0,k2_struct_0(sK0))) | ~m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0))) | ~l1_orders_2(sK0) | ~v5_orders_2(sK0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0)) )),
% 0.20/0.48    inference(superposition,[],[f185,f68])).
% 0.20/0.48  fof(f185,plain,(
% 0.20/0.48    ( ! [X0,X1] : (~m1_subset_1(sK1(k2_orders_2(sK0,k2_struct_0(sK0))),u1_struct_0(X0)) | r2_orders_2(X0,sK3(X1,X0,k2_struct_0(sK0)),sK1(k2_orders_2(sK0,k2_struct_0(sK0)))) | ~r2_hidden(X1,a_2_1_orders_2(X0,k2_struct_0(sK0))) | ~m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 0.20/0.48    inference(resolution,[],[f183,f58])).
% 0.20/0.48  fof(f58,plain,(
% 0.20/0.48    ( ! [X6,X2,X0,X1] : (~r2_hidden(X6,X2) | r2_orders_2(X1,sK3(X0,X1,X2),X6) | ~m1_subset_1(X6,u1_struct_0(X1)) | ~r2_hidden(X0,a_2_1_orders_2(X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_orders_2(X1) | ~v5_orders_2(X1) | ~v4_orders_2(X1) | ~v3_orders_2(X1) | v2_struct_0(X1)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f37])).
% 0.20/0.48  fof(f183,plain,(
% 0.20/0.48    r2_hidden(sK1(k2_orders_2(sK0,k2_struct_0(sK0))),k2_struct_0(sK0))),
% 0.20/0.48    inference(forward_demodulation,[],[f182,f174])).
% 0.20/0.48  fof(f182,plain,(
% 0.20/0.48    r2_hidden(sK3(sK1(k2_orders_2(sK0,k2_struct_0(sK0))),sK0,k2_struct_0(sK0)),k2_struct_0(sK0))),
% 0.20/0.48    inference(subsumption_resolution,[],[f177,f73])).
% 0.20/0.48  fof(f73,plain,(
% 0.20/0.48    ~v1_xboole_0(k2_struct_0(sK0))),
% 0.20/0.48    inference(subsumption_resolution,[],[f72,f38])).
% 0.20/0.48  fof(f72,plain,(
% 0.20/0.48    ~v1_xboole_0(k2_struct_0(sK0)) | v2_struct_0(sK0)),
% 0.20/0.48    inference(subsumption_resolution,[],[f71,f67])).
% 0.20/0.48  fof(f71,plain,(
% 0.20/0.48    ~v1_xboole_0(k2_struct_0(sK0)) | ~l1_struct_0(sK0) | v2_struct_0(sK0)),
% 0.20/0.48    inference(superposition,[],[f51,f68])).
% 0.20/0.48  fof(f51,plain,(
% 0.20/0.48    ( ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f21])).
% 0.20/0.48  fof(f21,plain,(
% 0.20/0.48    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 0.20/0.48    inference(flattening,[],[f20])).
% 0.20/0.48  fof(f20,plain,(
% 0.20/0.48    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 0.20/0.48    inference(ennf_transformation,[],[f5])).
% 0.20/0.48  fof(f5,axiom,(
% 0.20/0.48    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ~v1_xboole_0(u1_struct_0(X0)))),
% 0.20/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_struct_0)).
% 0.20/0.48  fof(f177,plain,(
% 0.20/0.48    v1_xboole_0(k2_struct_0(sK0)) | r2_hidden(sK3(sK1(k2_orders_2(sK0,k2_struct_0(sK0))),sK0,k2_struct_0(sK0)),k2_struct_0(sK0))),
% 0.20/0.48    inference(resolution,[],[f170,f55])).
% 0.20/0.48  fof(f55,plain,(
% 0.20/0.48    ( ! [X0,X1] : (~m1_subset_1(X0,X1) | v1_xboole_0(X1) | r2_hidden(X0,X1)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f24])).
% 0.20/0.48  fof(f24,plain,(
% 0.20/0.48    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 0.20/0.48    inference(flattening,[],[f23])).
% 0.20/0.48  fof(f23,plain,(
% 0.20/0.48    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 0.20/0.48    inference(ennf_transformation,[],[f1])).
% 0.20/0.48  fof(f1,axiom,(
% 0.20/0.48    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 0.20/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).
% 0.20/0.48  fof(f226,plain,(
% 0.20/0.48    spl4_10),
% 0.20/0.48    inference(avatar_contradiction_clause,[],[f225])).
% 0.20/0.48  fof(f225,plain,(
% 0.20/0.48    $false | spl4_10),
% 0.20/0.48    inference(subsumption_resolution,[],[f224,f43])).
% 0.20/0.48  fof(f224,plain,(
% 0.20/0.48    k1_xboole_0 = k2_orders_2(sK0,k2_struct_0(sK0)) | spl4_10),
% 0.20/0.48    inference(resolution,[],[f218,f52])).
% 0.20/0.48  fof(f218,plain,(
% 0.20/0.48    ~r2_hidden(sK1(k2_orders_2(sK0,k2_struct_0(sK0))),k2_orders_2(sK0,k2_struct_0(sK0))) | spl4_10),
% 0.20/0.48    inference(avatar_component_clause,[],[f217])).
% 0.20/0.48  % SZS output end Proof for theBenchmark
% 0.20/0.48  % (23781)------------------------------
% 0.20/0.48  % (23781)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.48  % (23781)Termination reason: Refutation
% 0.20/0.48  
% 0.20/0.48  % (23781)Memory used [KB]: 10746
% 0.20/0.48  % (23781)Time elapsed: 0.040 s
% 0.20/0.48  % (23781)------------------------------
% 0.20/0.48  % (23781)------------------------------
% 0.20/0.48  % (23766)Success in time 0.119 s
%------------------------------------------------------------------------------
