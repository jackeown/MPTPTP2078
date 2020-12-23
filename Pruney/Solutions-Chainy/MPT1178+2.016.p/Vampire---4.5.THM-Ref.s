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
% DateTime   : Thu Dec  3 13:10:27 EST 2020

% Result     : Theorem 0.17s
% Output     : Refutation 0.17s
% Verified   : 
% Statistics : Number of formulae       :   87 ( 296 expanded)
%              Number of leaves         :   13 (  93 expanded)
%              Depth                    :   25
%              Number of atoms          :  395 (1767 expanded)
%              Number of equality atoms :   35 ( 251 expanded)
%              Maximal formula depth    :   14 (   6 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f116,plain,(
    $false ),
    inference(subsumption_resolution,[],[f115,f34])).

fof(f34,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,
    ( k1_xboole_0 = k3_tarski(k4_orders_2(sK0,sK1))
    & m1_orders_1(sK1,k1_orders_1(u1_struct_0(sK0)))
    & l1_orders_2(sK0)
    & v5_orders_2(sK0)
    & v4_orders_2(sK0)
    & v3_orders_2(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f12,f22,f21])).

fof(f21,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( k1_xboole_0 = k3_tarski(k4_orders_2(X0,X1))
            & m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) )
        & l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( k1_xboole_0 = k3_tarski(k4_orders_2(sK0,X1))
          & m1_orders_1(X1,k1_orders_1(u1_struct_0(sK0))) )
      & l1_orders_2(sK0)
      & v5_orders_2(sK0)
      & v4_orders_2(sK0)
      & v3_orders_2(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,
    ( ? [X1] :
        ( k1_xboole_0 = k3_tarski(k4_orders_2(sK0,X1))
        & m1_orders_1(X1,k1_orders_1(u1_struct_0(sK0))) )
   => ( k1_xboole_0 = k3_tarski(k4_orders_2(sK0,sK1))
      & m1_orders_1(sK1,k1_orders_1(u1_struct_0(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f12,plain,(
    ? [X0] :
      ( ? [X1] :
          ( k1_xboole_0 = k3_tarski(k4_orders_2(X0,X1))
          & m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) )
      & l1_orders_2(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ? [X0] :
      ( ? [X1] :
          ( k1_xboole_0 = k3_tarski(k4_orders_2(X0,X1))
          & m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) )
      & l1_orders_2(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_orders_2(X0)
          & v5_orders_2(X0)
          & v4_orders_2(X0)
          & v3_orders_2(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
           => k1_xboole_0 != k3_tarski(k4_orders_2(X0,X1)) ) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f9,conjecture,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
         => k1_xboole_0 != k3_tarski(k4_orders_2(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t87_orders_2)).

fof(f115,plain,(
    v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f114,f35])).

fof(f35,plain,(
    v3_orders_2(sK0) ),
    inference(cnf_transformation,[],[f23])).

fof(f114,plain,
    ( ~ v3_orders_2(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f113,f36])).

fof(f36,plain,(
    v4_orders_2(sK0) ),
    inference(cnf_transformation,[],[f23])).

fof(f113,plain,
    ( ~ v4_orders_2(sK0)
    | ~ v3_orders_2(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f112,f37])).

fof(f37,plain,(
    v5_orders_2(sK0) ),
    inference(cnf_transformation,[],[f23])).

fof(f112,plain,
    ( ~ v5_orders_2(sK0)
    | ~ v4_orders_2(sK0)
    | ~ v3_orders_2(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f111,f38])).

fof(f38,plain,(
    l1_orders_2(sK0) ),
    inference(cnf_transformation,[],[f23])).

fof(f111,plain,
    ( ~ l1_orders_2(sK0)
    | ~ v5_orders_2(sK0)
    | ~ v4_orders_2(sK0)
    | ~ v3_orders_2(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f109,f39])).

fof(f39,plain,(
    m1_orders_1(sK1,k1_orders_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f23])).

fof(f109,plain,
    ( ~ m1_orders_1(sK1,k1_orders_1(u1_struct_0(sK0)))
    | ~ l1_orders_2(sK0)
    | ~ v5_orders_2(sK0)
    | ~ v4_orders_2(sK0)
    | ~ v3_orders_2(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f108,f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(k4_orders_2(X0,X1))
      | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(k4_orders_2(X0,X1))
      | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(k4_orders_2(X0,X1))
      | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( ( m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
        & l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(k4_orders_2(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc9_orders_2)).

fof(f108,plain,(
    v1_xboole_0(k4_orders_2(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f107,f61])).

fof(f61,plain,(
    ! [X0] : ~ r2_hidden(X0,k1_xboole_0) ),
    inference(resolution,[],[f60,f47])).

fof(f47,plain,(
    ! [X2,X0] :
      ( ~ v1_xboole_0(X0)
      | ~ r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | r2_hidden(sK3(X0),X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f29,f30])).

fof(f30,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK3(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(rectify,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X1] : ~ r2_hidden(X1,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

fof(f60,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(resolution,[],[f59,f41])).

fof(f41,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f59,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,sK3(X0))
      | v1_xboole_0(X0) ) ),
    inference(resolution,[],[f54,f48])).

fof(f48,plain,(
    ! [X0] :
      ( r2_hidden(sK3(X0),X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f54,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ r1_tarski(X1,X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ~ ( r1_tarski(X1,X0)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).

fof(f107,plain,
    ( r2_hidden(k1_funct_1(sK1,u1_struct_0(sK0)),k1_xboole_0)
    | v1_xboole_0(k4_orders_2(sK0,sK1)) ),
    inference(resolution,[],[f106,f99])).

fof(f99,plain,
    ( m2_orders_2(k1_xboole_0,sK0,sK1)
    | v1_xboole_0(k4_orders_2(sK0,sK1)) ),
    inference(forward_demodulation,[],[f97,f83])).

fof(f83,plain,(
    k1_xboole_0 = sK3(k4_orders_2(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f82,f34])).

fof(f82,plain,
    ( v2_struct_0(sK0)
    | k1_xboole_0 = sK3(k4_orders_2(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f81,f35])).

fof(f81,plain,
    ( ~ v3_orders_2(sK0)
    | v2_struct_0(sK0)
    | k1_xboole_0 = sK3(k4_orders_2(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f80,f36])).

fof(f80,plain,
    ( ~ v4_orders_2(sK0)
    | ~ v3_orders_2(sK0)
    | v2_struct_0(sK0)
    | k1_xboole_0 = sK3(k4_orders_2(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f79,f37])).

fof(f79,plain,
    ( ~ v5_orders_2(sK0)
    | ~ v4_orders_2(sK0)
    | ~ v3_orders_2(sK0)
    | v2_struct_0(sK0)
    | k1_xboole_0 = sK3(k4_orders_2(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f78,f38])).

fof(f78,plain,
    ( ~ l1_orders_2(sK0)
    | ~ v5_orders_2(sK0)
    | ~ v4_orders_2(sK0)
    | ~ v3_orders_2(sK0)
    | v2_struct_0(sK0)
    | k1_xboole_0 = sK3(k4_orders_2(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f77,f39])).

fof(f77,plain,
    ( ~ m1_orders_1(sK1,k1_orders_1(u1_struct_0(sK0)))
    | ~ l1_orders_2(sK0)
    | ~ v5_orders_2(sK0)
    | ~ v4_orders_2(sK0)
    | ~ v3_orders_2(sK0)
    | v2_struct_0(sK0)
    | k1_xboole_0 = sK3(k4_orders_2(sK0,sK1)) ),
    inference(resolution,[],[f50,f70])).

fof(f70,plain,
    ( v1_xboole_0(k4_orders_2(sK0,sK1))
    | k1_xboole_0 = sK3(k4_orders_2(sK0,sK1)) ),
    inference(resolution,[],[f64,f65])).

fof(f65,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,k1_xboole_0)
      | k1_xboole_0 = X0 ) ),
    inference(resolution,[],[f53,f41])).

fof(f53,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r1_tarski(X1,X0)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f64,plain,
    ( r1_tarski(sK3(k4_orders_2(sK0,sK1)),k1_xboole_0)
    | v1_xboole_0(k4_orders_2(sK0,sK1)) ),
    inference(resolution,[],[f63,f48])).

fof(f63,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k4_orders_2(sK0,sK1))
      | r1_tarski(X0,k1_xboole_0) ) ),
    inference(superposition,[],[f49,f40])).

fof(f40,plain,(
    k1_xboole_0 = k3_tarski(k4_orders_2(sK0,sK1)) ),
    inference(cnf_transformation,[],[f23])).

fof(f49,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k3_tarski(X1))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k3_tarski(X1))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => r1_tarski(X0,k3_tarski(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l49_zfmisc_1)).

fof(f97,plain,
    ( m2_orders_2(sK3(k4_orders_2(sK0,sK1)),sK0,sK1)
    | v1_xboole_0(k4_orders_2(sK0,sK1)) ),
    inference(resolution,[],[f96,f48])).

fof(f96,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k4_orders_2(sK0,sK1))
      | m2_orders_2(X0,sK0,sK1) ) ),
    inference(resolution,[],[f95,f39])).

fof(f95,plain,(
    ! [X0,X1] :
      ( ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(sK0)))
      | ~ r2_hidden(X0,k4_orders_2(sK0,X1))
      | m2_orders_2(X0,sK0,X1) ) ),
    inference(subsumption_resolution,[],[f94,f34])).

fof(f94,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,k4_orders_2(sK0,X1))
      | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(sK0)))
      | m2_orders_2(X0,sK0,X1)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f93,f35])).

fof(f93,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,k4_orders_2(sK0,X1))
      | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(sK0)))
      | m2_orders_2(X0,sK0,X1)
      | ~ v3_orders_2(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f92,f36])).

fof(f92,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,k4_orders_2(sK0,X1))
      | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(sK0)))
      | m2_orders_2(X0,sK0,X1)
      | ~ v4_orders_2(sK0)
      | ~ v3_orders_2(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f91,f37])).

fof(f91,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,k4_orders_2(sK0,X1))
      | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(sK0)))
      | m2_orders_2(X0,sK0,X1)
      | ~ v5_orders_2(sK0)
      | ~ v4_orders_2(sK0)
      | ~ v3_orders_2(sK0)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f56,f38])).

fof(f56,plain,(
    ! [X4,X0,X1] :
      ( ~ l1_orders_2(X0)
      | ~ r2_hidden(X4,k4_orders_2(X0,X1))
      | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
      | m2_orders_2(X4,X0,X1)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f43])).

fof(f43,plain,(
    ! [X4,X2,X0,X1] :
      ( m2_orders_2(X4,X0,X1)
      | ~ r2_hidden(X4,X2)
      | k4_orders_2(X0,X1) != X2
      | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( k4_orders_2(X0,X1) = X2
                | ( ( ~ m2_orders_2(sK2(X0,X1,X2),X0,X1)
                    | ~ r2_hidden(sK2(X0,X1,X2),X2) )
                  & ( m2_orders_2(sK2(X0,X1,X2),X0,X1)
                    | r2_hidden(sK2(X0,X1,X2),X2) ) ) )
              & ( ! [X4] :
                    ( ( r2_hidden(X4,X2)
                      | ~ m2_orders_2(X4,X0,X1) )
                    & ( m2_orders_2(X4,X0,X1)
                      | ~ r2_hidden(X4,X2) ) )
                | k4_orders_2(X0,X1) != X2 ) )
          | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f25,f26])).

fof(f26,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ~ m2_orders_2(X3,X0,X1)
            | ~ r2_hidden(X3,X2) )
          & ( m2_orders_2(X3,X0,X1)
            | r2_hidden(X3,X2) ) )
     => ( ( ~ m2_orders_2(sK2(X0,X1,X2),X0,X1)
          | ~ r2_hidden(sK2(X0,X1,X2),X2) )
        & ( m2_orders_2(sK2(X0,X1,X2),X0,X1)
          | r2_hidden(sK2(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( k4_orders_2(X0,X1) = X2
                | ? [X3] :
                    ( ( ~ m2_orders_2(X3,X0,X1)
                      | ~ r2_hidden(X3,X2) )
                    & ( m2_orders_2(X3,X0,X1)
                      | r2_hidden(X3,X2) ) ) )
              & ( ! [X4] :
                    ( ( r2_hidden(X4,X2)
                      | ~ m2_orders_2(X4,X0,X1) )
                    & ( m2_orders_2(X4,X0,X1)
                      | ~ r2_hidden(X4,X2) ) )
                | k4_orders_2(X0,X1) != X2 ) )
          | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(rectify,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( k4_orders_2(X0,X1) = X2
                | ? [X3] :
                    ( ( ~ m2_orders_2(X3,X0,X1)
                      | ~ r2_hidden(X3,X2) )
                    & ( m2_orders_2(X3,X0,X1)
                      | r2_hidden(X3,X2) ) ) )
              & ( ! [X3] :
                    ( ( r2_hidden(X3,X2)
                      | ~ m2_orders_2(X3,X0,X1) )
                    & ( m2_orders_2(X3,X0,X1)
                      | ~ r2_hidden(X3,X2) ) )
                | k4_orders_2(X0,X1) != X2 ) )
          | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k4_orders_2(X0,X1) = X2
            <=> ! [X3] :
                  ( r2_hidden(X3,X2)
                <=> m2_orders_2(X3,X0,X1) ) )
          | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k4_orders_2(X0,X1) = X2
            <=> ! [X3] :
                  ( r2_hidden(X3,X2)
                <=> m2_orders_2(X3,X0,X1) ) )
          | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
         => ! [X2] :
              ( k4_orders_2(X0,X1) = X2
            <=> ! [X3] :
                  ( r2_hidden(X3,X2)
                <=> m2_orders_2(X3,X0,X1) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d17_orders_2)).

fof(f106,plain,(
    ! [X0] :
      ( ~ m2_orders_2(X0,sK0,sK1)
      | r2_hidden(k1_funct_1(sK1,u1_struct_0(sK0)),X0) ) ),
    inference(resolution,[],[f105,f39])).

fof(f105,plain,(
    ! [X0,X1] :
      ( ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(sK0)))
      | ~ m2_orders_2(X0,sK0,X1)
      | r2_hidden(k1_funct_1(X1,u1_struct_0(sK0)),X0) ) ),
    inference(subsumption_resolution,[],[f104,f34])).

fof(f104,plain,(
    ! [X0,X1] :
      ( ~ m2_orders_2(X0,sK0,X1)
      | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(sK0)))
      | r2_hidden(k1_funct_1(X1,u1_struct_0(sK0)),X0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f103,f35])).

fof(f103,plain,(
    ! [X0,X1] :
      ( ~ m2_orders_2(X0,sK0,X1)
      | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(sK0)))
      | r2_hidden(k1_funct_1(X1,u1_struct_0(sK0)),X0)
      | ~ v3_orders_2(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f102,f36])).

fof(f102,plain,(
    ! [X0,X1] :
      ( ~ m2_orders_2(X0,sK0,X1)
      | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(sK0)))
      | r2_hidden(k1_funct_1(X1,u1_struct_0(sK0)),X0)
      | ~ v4_orders_2(sK0)
      | ~ v3_orders_2(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f101,f37])).

fof(f101,plain,(
    ! [X0,X1] :
      ( ~ m2_orders_2(X0,sK0,X1)
      | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(sK0)))
      | r2_hidden(k1_funct_1(X1,u1_struct_0(sK0)),X0)
      | ~ v5_orders_2(sK0)
      | ~ v4_orders_2(sK0)
      | ~ v3_orders_2(sK0)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f42,f38])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_orders_2(X0)
      | ~ m2_orders_2(X2,X0,X1)
      | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
      | r2_hidden(k1_funct_1(X1,u1_struct_0(X0)),X2)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r2_hidden(k1_funct_1(X1,u1_struct_0(X0)),X2)
              | ~ m2_orders_2(X2,X0,X1) )
          | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r2_hidden(k1_funct_1(X1,u1_struct_0(X0)),X2)
              | ~ m2_orders_2(X2,X0,X1) )
          | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) )
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
          ( m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m2_orders_2(X2,X0,X1)
             => r2_hidden(k1_funct_1(X1,u1_struct_0(X0)),X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_orders_2)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.10  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.12  % Command    : run_vampire %s %d
% 0.12/0.31  % Computer   : n013.cluster.edu
% 0.12/0.31  % Model      : x86_64 x86_64
% 0.12/0.31  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.31  % Memory     : 8042.1875MB
% 0.12/0.31  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.31  % CPULimit   : 60
% 0.12/0.31  % WCLimit    : 600
% 0.12/0.31  % DateTime   : Tue Dec  1 20:21:39 EST 2020
% 0.12/0.31  % CPUTime    : 
% 0.17/0.46  % (28002)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 0.17/0.46  % (27994)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 0.17/0.46  % (27994)Refutation not found, incomplete strategy% (27994)------------------------------
% 0.17/0.46  % (27994)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.17/0.46  % (27994)Termination reason: Refutation not found, incomplete strategy
% 0.17/0.46  
% 0.17/0.46  % (27994)Memory used [KB]: 6140
% 0.17/0.46  % (27994)Time elapsed: 0.069 s
% 0.17/0.46  % (27994)------------------------------
% 0.17/0.46  % (27994)------------------------------
% 0.17/0.46  % (28002)Refutation found. Thanks to Tanya!
% 0.17/0.46  % SZS status Theorem for theBenchmark
% 0.17/0.46  % SZS output start Proof for theBenchmark
% 0.17/0.46  fof(f116,plain,(
% 0.17/0.46    $false),
% 0.17/0.46    inference(subsumption_resolution,[],[f115,f34])).
% 0.17/0.46  fof(f34,plain,(
% 0.17/0.46    ~v2_struct_0(sK0)),
% 0.17/0.46    inference(cnf_transformation,[],[f23])).
% 0.17/0.46  fof(f23,plain,(
% 0.17/0.46    (k1_xboole_0 = k3_tarski(k4_orders_2(sK0,sK1)) & m1_orders_1(sK1,k1_orders_1(u1_struct_0(sK0)))) & l1_orders_2(sK0) & v5_orders_2(sK0) & v4_orders_2(sK0) & v3_orders_2(sK0) & ~v2_struct_0(sK0)),
% 0.17/0.46    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f12,f22,f21])).
% 0.17/0.46  fof(f21,plain,(
% 0.17/0.46    ? [X0] : (? [X1] : (k1_xboole_0 = k3_tarski(k4_orders_2(X0,X1)) & m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => (? [X1] : (k1_xboole_0 = k3_tarski(k4_orders_2(sK0,X1)) & m1_orders_1(X1,k1_orders_1(u1_struct_0(sK0)))) & l1_orders_2(sK0) & v5_orders_2(sK0) & v4_orders_2(sK0) & v3_orders_2(sK0) & ~v2_struct_0(sK0))),
% 0.17/0.46    introduced(choice_axiom,[])).
% 0.17/0.46  fof(f22,plain,(
% 0.17/0.46    ? [X1] : (k1_xboole_0 = k3_tarski(k4_orders_2(sK0,X1)) & m1_orders_1(X1,k1_orders_1(u1_struct_0(sK0)))) => (k1_xboole_0 = k3_tarski(k4_orders_2(sK0,sK1)) & m1_orders_1(sK1,k1_orders_1(u1_struct_0(sK0))))),
% 0.17/0.46    introduced(choice_axiom,[])).
% 0.17/0.46  fof(f12,plain,(
% 0.17/0.46    ? [X0] : (? [X1] : (k1_xboole_0 = k3_tarski(k4_orders_2(X0,X1)) & m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0))),
% 0.17/0.46    inference(flattening,[],[f11])).
% 0.17/0.46  fof(f11,plain,(
% 0.17/0.46    ? [X0] : (? [X1] : (k1_xboole_0 = k3_tarski(k4_orders_2(X0,X1)) & m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) & (l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)))),
% 0.17/0.46    inference(ennf_transformation,[],[f10])).
% 0.17/0.46  fof(f10,negated_conjecture,(
% 0.17/0.46    ~! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) => k1_xboole_0 != k3_tarski(k4_orders_2(X0,X1))))),
% 0.17/0.46    inference(negated_conjecture,[],[f9])).
% 0.17/0.46  fof(f9,conjecture,(
% 0.17/0.46    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) => k1_xboole_0 != k3_tarski(k4_orders_2(X0,X1))))),
% 0.17/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t87_orders_2)).
% 0.17/0.46  fof(f115,plain,(
% 0.17/0.46    v2_struct_0(sK0)),
% 0.17/0.46    inference(subsumption_resolution,[],[f114,f35])).
% 0.17/0.46  fof(f35,plain,(
% 0.17/0.46    v3_orders_2(sK0)),
% 0.17/0.46    inference(cnf_transformation,[],[f23])).
% 0.17/0.46  fof(f114,plain,(
% 0.17/0.46    ~v3_orders_2(sK0) | v2_struct_0(sK0)),
% 0.17/0.46    inference(subsumption_resolution,[],[f113,f36])).
% 0.17/0.46  fof(f36,plain,(
% 0.17/0.46    v4_orders_2(sK0)),
% 0.17/0.46    inference(cnf_transformation,[],[f23])).
% 0.17/0.46  fof(f113,plain,(
% 0.17/0.46    ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0)),
% 0.17/0.46    inference(subsumption_resolution,[],[f112,f37])).
% 0.17/0.46  fof(f37,plain,(
% 0.17/0.46    v5_orders_2(sK0)),
% 0.17/0.46    inference(cnf_transformation,[],[f23])).
% 0.17/0.46  fof(f112,plain,(
% 0.17/0.46    ~v5_orders_2(sK0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0)),
% 0.17/0.46    inference(subsumption_resolution,[],[f111,f38])).
% 0.17/0.46  fof(f38,plain,(
% 0.17/0.46    l1_orders_2(sK0)),
% 0.17/0.46    inference(cnf_transformation,[],[f23])).
% 0.17/0.46  fof(f111,plain,(
% 0.17/0.46    ~l1_orders_2(sK0) | ~v5_orders_2(sK0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0)),
% 0.17/0.46    inference(subsumption_resolution,[],[f109,f39])).
% 0.17/0.46  fof(f39,plain,(
% 0.17/0.46    m1_orders_1(sK1,k1_orders_1(u1_struct_0(sK0)))),
% 0.17/0.46    inference(cnf_transformation,[],[f23])).
% 0.17/0.46  fof(f109,plain,(
% 0.17/0.46    ~m1_orders_1(sK1,k1_orders_1(u1_struct_0(sK0))) | ~l1_orders_2(sK0) | ~v5_orders_2(sK0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0)),
% 0.17/0.46    inference(resolution,[],[f108,f50])).
% 0.17/0.46  fof(f50,plain,(
% 0.17/0.46    ( ! [X0,X1] : (~v1_xboole_0(k4_orders_2(X0,X1)) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 0.17/0.46    inference(cnf_transformation,[],[f19])).
% 0.17/0.46  fof(f19,plain,(
% 0.17/0.46    ! [X0,X1] : (~v1_xboole_0(k4_orders_2(X0,X1)) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 0.17/0.46    inference(flattening,[],[f18])).
% 0.17/0.47  fof(f18,plain,(
% 0.17/0.47    ! [X0,X1] : (~v1_xboole_0(k4_orders_2(X0,X1)) | (~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 0.17/0.47    inference(ennf_transformation,[],[f7])).
% 0.17/0.47  fof(f7,axiom,(
% 0.17/0.47    ! [X0,X1] : ((m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ~v1_xboole_0(k4_orders_2(X0,X1)))),
% 0.17/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc9_orders_2)).
% 0.17/0.47  fof(f108,plain,(
% 0.17/0.47    v1_xboole_0(k4_orders_2(sK0,sK1))),
% 0.17/0.47    inference(subsumption_resolution,[],[f107,f61])).
% 0.17/0.47  fof(f61,plain,(
% 0.17/0.47    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0)) )),
% 0.17/0.47    inference(resolution,[],[f60,f47])).
% 0.17/0.47  fof(f47,plain,(
% 0.17/0.47    ( ! [X2,X0] : (~v1_xboole_0(X0) | ~r2_hidden(X2,X0)) )),
% 0.17/0.47    inference(cnf_transformation,[],[f31])).
% 0.17/0.47  fof(f31,plain,(
% 0.17/0.47    ! [X0] : ((v1_xboole_0(X0) | r2_hidden(sK3(X0),X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 0.17/0.47    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f29,f30])).
% 0.17/0.47  fof(f30,plain,(
% 0.17/0.47    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK3(X0),X0))),
% 0.17/0.47    introduced(choice_axiom,[])).
% 0.17/0.47  fof(f29,plain,(
% 0.17/0.47    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 0.17/0.47    inference(rectify,[],[f28])).
% 0.17/0.47  fof(f28,plain,(
% 0.17/0.47    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0)))),
% 0.17/0.47    inference(nnf_transformation,[],[f1])).
% 0.17/0.47  fof(f1,axiom,(
% 0.17/0.47    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 0.17/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).
% 0.17/0.47  fof(f60,plain,(
% 0.17/0.47    v1_xboole_0(k1_xboole_0)),
% 0.17/0.47    inference(resolution,[],[f59,f41])).
% 0.17/0.47  fof(f41,plain,(
% 0.17/0.47    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 0.17/0.47    inference(cnf_transformation,[],[f3])).
% 0.17/0.47  fof(f3,axiom,(
% 0.17/0.47    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 0.17/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).
% 0.17/0.47  fof(f59,plain,(
% 0.17/0.47    ( ! [X0] : (~r1_tarski(X0,sK3(X0)) | v1_xboole_0(X0)) )),
% 0.17/0.47    inference(resolution,[],[f54,f48])).
% 0.17/0.47  fof(f48,plain,(
% 0.17/0.47    ( ! [X0] : (r2_hidden(sK3(X0),X0) | v1_xboole_0(X0)) )),
% 0.17/0.47    inference(cnf_transformation,[],[f31])).
% 0.17/0.47  fof(f54,plain,(
% 0.17/0.47    ( ! [X0,X1] : (~r2_hidden(X0,X1) | ~r1_tarski(X1,X0)) )),
% 0.17/0.47    inference(cnf_transformation,[],[f20])).
% 0.17/0.47  fof(f20,plain,(
% 0.17/0.47    ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1))),
% 0.17/0.47    inference(ennf_transformation,[],[f5])).
% 0.17/0.47  fof(f5,axiom,(
% 0.17/0.47    ! [X0,X1] : ~(r1_tarski(X1,X0) & r2_hidden(X0,X1))),
% 0.17/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).
% 0.17/0.47  fof(f107,plain,(
% 0.17/0.47    r2_hidden(k1_funct_1(sK1,u1_struct_0(sK0)),k1_xboole_0) | v1_xboole_0(k4_orders_2(sK0,sK1))),
% 0.17/0.47    inference(resolution,[],[f106,f99])).
% 0.17/0.47  fof(f99,plain,(
% 0.17/0.47    m2_orders_2(k1_xboole_0,sK0,sK1) | v1_xboole_0(k4_orders_2(sK0,sK1))),
% 0.17/0.47    inference(forward_demodulation,[],[f97,f83])).
% 0.17/0.47  fof(f83,plain,(
% 0.17/0.47    k1_xboole_0 = sK3(k4_orders_2(sK0,sK1))),
% 0.17/0.47    inference(subsumption_resolution,[],[f82,f34])).
% 0.17/0.47  fof(f82,plain,(
% 0.17/0.47    v2_struct_0(sK0) | k1_xboole_0 = sK3(k4_orders_2(sK0,sK1))),
% 0.17/0.47    inference(subsumption_resolution,[],[f81,f35])).
% 0.17/0.47  fof(f81,plain,(
% 0.17/0.47    ~v3_orders_2(sK0) | v2_struct_0(sK0) | k1_xboole_0 = sK3(k4_orders_2(sK0,sK1))),
% 0.17/0.47    inference(subsumption_resolution,[],[f80,f36])).
% 0.17/0.47  fof(f80,plain,(
% 0.17/0.47    ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0) | k1_xboole_0 = sK3(k4_orders_2(sK0,sK1))),
% 0.17/0.47    inference(subsumption_resolution,[],[f79,f37])).
% 0.17/0.47  fof(f79,plain,(
% 0.17/0.47    ~v5_orders_2(sK0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0) | k1_xboole_0 = sK3(k4_orders_2(sK0,sK1))),
% 0.17/0.47    inference(subsumption_resolution,[],[f78,f38])).
% 0.17/0.47  fof(f78,plain,(
% 0.17/0.47    ~l1_orders_2(sK0) | ~v5_orders_2(sK0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0) | k1_xboole_0 = sK3(k4_orders_2(sK0,sK1))),
% 0.17/0.47    inference(subsumption_resolution,[],[f77,f39])).
% 0.17/0.47  fof(f77,plain,(
% 0.17/0.47    ~m1_orders_1(sK1,k1_orders_1(u1_struct_0(sK0))) | ~l1_orders_2(sK0) | ~v5_orders_2(sK0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0) | k1_xboole_0 = sK3(k4_orders_2(sK0,sK1))),
% 0.17/0.47    inference(resolution,[],[f50,f70])).
% 0.17/0.47  fof(f70,plain,(
% 0.17/0.47    v1_xboole_0(k4_orders_2(sK0,sK1)) | k1_xboole_0 = sK3(k4_orders_2(sK0,sK1))),
% 0.17/0.47    inference(resolution,[],[f64,f65])).
% 0.17/0.47  fof(f65,plain,(
% 0.17/0.47    ( ! [X0] : (~r1_tarski(X0,k1_xboole_0) | k1_xboole_0 = X0) )),
% 0.17/0.47    inference(resolution,[],[f53,f41])).
% 0.17/0.47  fof(f53,plain,(
% 0.17/0.47    ( ! [X0,X1] : (~r1_tarski(X0,X1) | ~r1_tarski(X1,X0) | X0 = X1) )),
% 0.17/0.47    inference(cnf_transformation,[],[f33])).
% 0.17/0.47  fof(f33,plain,(
% 0.17/0.47    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.17/0.47    inference(flattening,[],[f32])).
% 0.17/0.47  fof(f32,plain,(
% 0.17/0.47    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.17/0.47    inference(nnf_transformation,[],[f2])).
% 0.17/0.47  fof(f2,axiom,(
% 0.17/0.47    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.17/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.17/0.47  fof(f64,plain,(
% 0.17/0.47    r1_tarski(sK3(k4_orders_2(sK0,sK1)),k1_xboole_0) | v1_xboole_0(k4_orders_2(sK0,sK1))),
% 0.17/0.47    inference(resolution,[],[f63,f48])).
% 0.17/0.47  fof(f63,plain,(
% 0.17/0.47    ( ! [X0] : (~r2_hidden(X0,k4_orders_2(sK0,sK1)) | r1_tarski(X0,k1_xboole_0)) )),
% 0.17/0.47    inference(superposition,[],[f49,f40])).
% 0.17/0.47  fof(f40,plain,(
% 0.17/0.47    k1_xboole_0 = k3_tarski(k4_orders_2(sK0,sK1))),
% 0.17/0.47    inference(cnf_transformation,[],[f23])).
% 0.17/0.47  fof(f49,plain,(
% 0.17/0.47    ( ! [X0,X1] : (r1_tarski(X0,k3_tarski(X1)) | ~r2_hidden(X0,X1)) )),
% 0.17/0.47    inference(cnf_transformation,[],[f17])).
% 0.17/0.47  fof(f17,plain,(
% 0.17/0.47    ! [X0,X1] : (r1_tarski(X0,k3_tarski(X1)) | ~r2_hidden(X0,X1))),
% 0.17/0.47    inference(ennf_transformation,[],[f4])).
% 0.17/0.47  fof(f4,axiom,(
% 0.17/0.47    ! [X0,X1] : (r2_hidden(X0,X1) => r1_tarski(X0,k3_tarski(X1)))),
% 0.17/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l49_zfmisc_1)).
% 0.17/0.47  fof(f97,plain,(
% 0.17/0.47    m2_orders_2(sK3(k4_orders_2(sK0,sK1)),sK0,sK1) | v1_xboole_0(k4_orders_2(sK0,sK1))),
% 0.17/0.47    inference(resolution,[],[f96,f48])).
% 0.17/0.47  fof(f96,plain,(
% 0.17/0.47    ( ! [X0] : (~r2_hidden(X0,k4_orders_2(sK0,sK1)) | m2_orders_2(X0,sK0,sK1)) )),
% 0.17/0.47    inference(resolution,[],[f95,f39])).
% 0.17/0.47  fof(f95,plain,(
% 0.17/0.47    ( ! [X0,X1] : (~m1_orders_1(X1,k1_orders_1(u1_struct_0(sK0))) | ~r2_hidden(X0,k4_orders_2(sK0,X1)) | m2_orders_2(X0,sK0,X1)) )),
% 0.17/0.47    inference(subsumption_resolution,[],[f94,f34])).
% 0.17/0.47  fof(f94,plain,(
% 0.17/0.47    ( ! [X0,X1] : (~r2_hidden(X0,k4_orders_2(sK0,X1)) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(sK0))) | m2_orders_2(X0,sK0,X1) | v2_struct_0(sK0)) )),
% 0.17/0.47    inference(subsumption_resolution,[],[f93,f35])).
% 0.17/0.47  fof(f93,plain,(
% 0.17/0.47    ( ! [X0,X1] : (~r2_hidden(X0,k4_orders_2(sK0,X1)) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(sK0))) | m2_orders_2(X0,sK0,X1) | ~v3_orders_2(sK0) | v2_struct_0(sK0)) )),
% 0.17/0.47    inference(subsumption_resolution,[],[f92,f36])).
% 0.17/0.47  fof(f92,plain,(
% 0.17/0.47    ( ! [X0,X1] : (~r2_hidden(X0,k4_orders_2(sK0,X1)) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(sK0))) | m2_orders_2(X0,sK0,X1) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0)) )),
% 0.17/0.47    inference(subsumption_resolution,[],[f91,f37])).
% 0.17/0.47  fof(f91,plain,(
% 0.17/0.47    ( ! [X0,X1] : (~r2_hidden(X0,k4_orders_2(sK0,X1)) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(sK0))) | m2_orders_2(X0,sK0,X1) | ~v5_orders_2(sK0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0)) )),
% 0.17/0.47    inference(resolution,[],[f56,f38])).
% 0.17/0.47  fof(f56,plain,(
% 0.17/0.47    ( ! [X4,X0,X1] : (~l1_orders_2(X0) | ~r2_hidden(X4,k4_orders_2(X0,X1)) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) | m2_orders_2(X4,X0,X1) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 0.17/0.47    inference(equality_resolution,[],[f43])).
% 0.17/0.47  fof(f43,plain,(
% 0.17/0.47    ( ! [X4,X2,X0,X1] : (m2_orders_2(X4,X0,X1) | ~r2_hidden(X4,X2) | k4_orders_2(X0,X1) != X2 | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 0.17/0.47    inference(cnf_transformation,[],[f27])).
% 0.17/0.47  fof(f27,plain,(
% 0.17/0.47    ! [X0] : (! [X1] : (! [X2] : ((k4_orders_2(X0,X1) = X2 | ((~m2_orders_2(sK2(X0,X1,X2),X0,X1) | ~r2_hidden(sK2(X0,X1,X2),X2)) & (m2_orders_2(sK2(X0,X1,X2),X0,X1) | r2_hidden(sK2(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~m2_orders_2(X4,X0,X1)) & (m2_orders_2(X4,X0,X1) | ~r2_hidden(X4,X2))) | k4_orders_2(X0,X1) != X2)) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 0.17/0.47    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f25,f26])).
% 0.17/0.47  fof(f26,plain,(
% 0.17/0.47    ! [X2,X1,X0] : (? [X3] : ((~m2_orders_2(X3,X0,X1) | ~r2_hidden(X3,X2)) & (m2_orders_2(X3,X0,X1) | r2_hidden(X3,X2))) => ((~m2_orders_2(sK2(X0,X1,X2),X0,X1) | ~r2_hidden(sK2(X0,X1,X2),X2)) & (m2_orders_2(sK2(X0,X1,X2),X0,X1) | r2_hidden(sK2(X0,X1,X2),X2))))),
% 0.17/0.47    introduced(choice_axiom,[])).
% 0.17/0.47  fof(f25,plain,(
% 0.17/0.47    ! [X0] : (! [X1] : (! [X2] : ((k4_orders_2(X0,X1) = X2 | ? [X3] : ((~m2_orders_2(X3,X0,X1) | ~r2_hidden(X3,X2)) & (m2_orders_2(X3,X0,X1) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~m2_orders_2(X4,X0,X1)) & (m2_orders_2(X4,X0,X1) | ~r2_hidden(X4,X2))) | k4_orders_2(X0,X1) != X2)) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 0.17/0.47    inference(rectify,[],[f24])).
% 0.17/0.47  fof(f24,plain,(
% 0.17/0.47    ! [X0] : (! [X1] : (! [X2] : ((k4_orders_2(X0,X1) = X2 | ? [X3] : ((~m2_orders_2(X3,X0,X1) | ~r2_hidden(X3,X2)) & (m2_orders_2(X3,X0,X1) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | ~m2_orders_2(X3,X0,X1)) & (m2_orders_2(X3,X0,X1) | ~r2_hidden(X3,X2))) | k4_orders_2(X0,X1) != X2)) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 0.17/0.47    inference(nnf_transformation,[],[f16])).
% 0.17/0.47  fof(f16,plain,(
% 0.17/0.47    ! [X0] : (! [X1] : (! [X2] : (k4_orders_2(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> m2_orders_2(X3,X0,X1))) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 0.17/0.47    inference(flattening,[],[f15])).
% 0.17/0.47  fof(f15,plain,(
% 0.17/0.47    ! [X0] : (! [X1] : (! [X2] : (k4_orders_2(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> m2_orders_2(X3,X0,X1))) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) | (~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 0.17/0.47    inference(ennf_transformation,[],[f6])).
% 0.17/0.47  fof(f6,axiom,(
% 0.17/0.47    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) => ! [X2] : (k4_orders_2(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> m2_orders_2(X3,X0,X1)))))),
% 0.17/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d17_orders_2)).
% 0.17/0.47  fof(f106,plain,(
% 0.17/0.47    ( ! [X0] : (~m2_orders_2(X0,sK0,sK1) | r2_hidden(k1_funct_1(sK1,u1_struct_0(sK0)),X0)) )),
% 0.17/0.47    inference(resolution,[],[f105,f39])).
% 0.17/0.47  fof(f105,plain,(
% 0.17/0.47    ( ! [X0,X1] : (~m1_orders_1(X1,k1_orders_1(u1_struct_0(sK0))) | ~m2_orders_2(X0,sK0,X1) | r2_hidden(k1_funct_1(X1,u1_struct_0(sK0)),X0)) )),
% 0.17/0.47    inference(subsumption_resolution,[],[f104,f34])).
% 0.17/0.47  fof(f104,plain,(
% 0.17/0.47    ( ! [X0,X1] : (~m2_orders_2(X0,sK0,X1) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(sK0))) | r2_hidden(k1_funct_1(X1,u1_struct_0(sK0)),X0) | v2_struct_0(sK0)) )),
% 0.17/0.47    inference(subsumption_resolution,[],[f103,f35])).
% 0.17/0.47  fof(f103,plain,(
% 0.17/0.47    ( ! [X0,X1] : (~m2_orders_2(X0,sK0,X1) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(sK0))) | r2_hidden(k1_funct_1(X1,u1_struct_0(sK0)),X0) | ~v3_orders_2(sK0) | v2_struct_0(sK0)) )),
% 0.17/0.47    inference(subsumption_resolution,[],[f102,f36])).
% 0.17/0.47  fof(f102,plain,(
% 0.17/0.47    ( ! [X0,X1] : (~m2_orders_2(X0,sK0,X1) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(sK0))) | r2_hidden(k1_funct_1(X1,u1_struct_0(sK0)),X0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0)) )),
% 0.17/0.47    inference(subsumption_resolution,[],[f101,f37])).
% 0.17/0.47  fof(f101,plain,(
% 0.17/0.47    ( ! [X0,X1] : (~m2_orders_2(X0,sK0,X1) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(sK0))) | r2_hidden(k1_funct_1(X1,u1_struct_0(sK0)),X0) | ~v5_orders_2(sK0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0)) )),
% 0.17/0.47    inference(resolution,[],[f42,f38])).
% 0.17/0.47  fof(f42,plain,(
% 0.17/0.47    ( ! [X2,X0,X1] : (~l1_orders_2(X0) | ~m2_orders_2(X2,X0,X1) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) | r2_hidden(k1_funct_1(X1,u1_struct_0(X0)),X2) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 0.17/0.47    inference(cnf_transformation,[],[f14])).
% 0.17/0.47  fof(f14,plain,(
% 0.17/0.47    ! [X0] : (! [X1] : (! [X2] : (r2_hidden(k1_funct_1(X1,u1_struct_0(X0)),X2) | ~m2_orders_2(X2,X0,X1)) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 0.17/0.47    inference(flattening,[],[f13])).
% 0.17/0.47  fof(f13,plain,(
% 0.17/0.47    ! [X0] : (! [X1] : (! [X2] : (r2_hidden(k1_funct_1(X1,u1_struct_0(X0)),X2) | ~m2_orders_2(X2,X0,X1)) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) | (~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 0.17/0.47    inference(ennf_transformation,[],[f8])).
% 0.17/0.47  fof(f8,axiom,(
% 0.17/0.47    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) => ! [X2] : (m2_orders_2(X2,X0,X1) => r2_hidden(k1_funct_1(X1,u1_struct_0(X0)),X2))))),
% 0.17/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_orders_2)).
% 0.17/0.47  % SZS output end Proof for theBenchmark
% 0.17/0.47  % (28002)------------------------------
% 0.17/0.47  % (28002)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.17/0.47  % (28002)Termination reason: Refutation
% 0.17/0.47  
% 0.17/0.47  % (28002)Memory used [KB]: 6140
% 0.17/0.47  % (28002)Time elapsed: 0.078 s
% 0.17/0.47  % (28002)------------------------------
% 0.17/0.47  % (28002)------------------------------
% 0.17/0.47  % (27980)Success in time 0.141 s
%------------------------------------------------------------------------------
