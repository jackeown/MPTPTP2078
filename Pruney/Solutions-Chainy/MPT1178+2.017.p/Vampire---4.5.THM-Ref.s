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
% DateTime   : Thu Dec  3 13:10:27 EST 2020

% Result     : Theorem 1.34s
% Output     : Refutation 1.43s
% Verified   : 
% Statistics : Number of formulae       :   93 ( 295 expanded)
%              Number of leaves         :   17 (  92 expanded)
%              Depth                    :   22
%              Number of atoms          :  390 (1741 expanded)
%              Number of equality atoms :   48 ( 264 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f374,plain,(
    $false ),
    inference(subsumption_resolution,[],[f373,f43])).

fof(f43,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,
    ( k1_xboole_0 = k3_tarski(k4_orders_2(sK0,sK1))
    & m1_orders_1(sK1,k1_orders_1(u1_struct_0(sK0)))
    & l1_orders_2(sK0)
    & v5_orders_2(sK0)
    & v4_orders_2(sK0)
    & v3_orders_2(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f19,f30,f29])).

fof(f29,plain,
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

fof(f30,plain,
    ( ? [X1] :
        ( k1_xboole_0 = k3_tarski(k4_orders_2(sK0,X1))
        & m1_orders_1(X1,k1_orders_1(u1_struct_0(sK0))) )
   => ( k1_xboole_0 = k3_tarski(k4_orders_2(sK0,sK1))
      & m1_orders_1(sK1,k1_orders_1(u1_struct_0(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,(
    ? [X0] :
      ( ? [X1] :
          ( k1_xboole_0 = k3_tarski(k4_orders_2(X0,X1))
          & m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) )
      & l1_orders_2(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ? [X0] :
      ( ? [X1] :
          ( k1_xboole_0 = k3_tarski(k4_orders_2(X0,X1))
          & m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) )
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
            ( m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
           => k1_xboole_0 != k3_tarski(k4_orders_2(X0,X1)) ) ) ),
    inference(negated_conjecture,[],[f15])).

fof(f15,conjecture,(
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

fof(f373,plain,(
    v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f372,f44])).

fof(f44,plain,(
    v3_orders_2(sK0) ),
    inference(cnf_transformation,[],[f31])).

% (28976)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
fof(f372,plain,
    ( ~ v3_orders_2(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f371,f45])).

fof(f45,plain,(
    v4_orders_2(sK0) ),
    inference(cnf_transformation,[],[f31])).

fof(f371,plain,
    ( ~ v4_orders_2(sK0)
    | ~ v3_orders_2(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f370,f46])).

fof(f46,plain,(
    v5_orders_2(sK0) ),
    inference(cnf_transformation,[],[f31])).

fof(f370,plain,
    ( ~ v5_orders_2(sK0)
    | ~ v4_orders_2(sK0)
    | ~ v3_orders_2(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f369,f47])).

fof(f47,plain,(
    l1_orders_2(sK0) ),
    inference(cnf_transformation,[],[f31])).

fof(f369,plain,
    ( ~ l1_orders_2(sK0)
    | ~ v5_orders_2(sK0)
    | ~ v4_orders_2(sK0)
    | ~ v3_orders_2(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f368,f164])).

fof(f164,plain,(
    m2_orders_2(k1_xboole_0,sK0,sK1) ),
    inference(backward_demodulation,[],[f136,f161])).

fof(f161,plain,(
    k1_xboole_0 = sK3(k4_orders_2(sK0,sK1)) ),
    inference(resolution,[],[f155,f90])).

fof(f90,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,k1_xboole_0)
      | k1_xboole_0 = X0 ) ),
    inference(resolution,[],[f66,f50])).

fof(f50,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f66,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f38])).

fof(f38,plain,(
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

fof(f155,plain,(
    r1_tarski(sK3(k4_orders_2(sK0,sK1)),k1_xboole_0) ),
    inference(subsumption_resolution,[],[f152,f105])).

fof(f105,plain,(
    ~ v1_xboole_0(k4_orders_2(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f104,f43])).

fof(f104,plain,
    ( ~ v1_xboole_0(k4_orders_2(sK0,sK1))
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f103,f44])).

fof(f103,plain,
    ( ~ v1_xboole_0(k4_orders_2(sK0,sK1))
    | ~ v3_orders_2(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f102,f45])).

fof(f102,plain,
    ( ~ v1_xboole_0(k4_orders_2(sK0,sK1))
    | ~ v4_orders_2(sK0)
    | ~ v3_orders_2(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f101,f46])).

fof(f101,plain,
    ( ~ v1_xboole_0(k4_orders_2(sK0,sK1))
    | ~ v5_orders_2(sK0)
    | ~ v4_orders_2(sK0)
    | ~ v3_orders_2(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f100,f47])).

fof(f100,plain,
    ( ~ v1_xboole_0(k4_orders_2(sK0,sK1))
    | ~ l1_orders_2(sK0)
    | ~ v5_orders_2(sK0)
    | ~ v4_orders_2(sK0)
    | ~ v3_orders_2(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f63,f48])).

fof(f48,plain,(
    m1_orders_1(sK1,k1_orders_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f31])).

fof(f63,plain,(
    ! [X0,X1] :
      ( ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
      | ~ v1_xboole_0(k4_orders_2(X0,X1))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(k4_orders_2(X0,X1))
      | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(k4_orders_2(X0,X1))
      | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( ( m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
        & l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(k4_orders_2(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc9_orders_2)).

fof(f152,plain,
    ( r1_tarski(sK3(k4_orders_2(sK0,sK1)),k1_xboole_0)
    | v1_xboole_0(k4_orders_2(sK0,sK1)) ),
    inference(resolution,[],[f151,f58])).

fof(f58,plain,(
    ! [X0] :
      ( r2_hidden(sK3(X0),X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0] :
      ( v1_xboole_0(X0)
      | r2_hidden(sK3(X0),X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f24,f36])).

fof(f36,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK3(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,(
    ! [X0] :
      ( v1_xboole_0(X0)
      | ? [X1] : r2_hidden(X1,X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] : ~ r2_hidden(X1,X0)
     => v1_xboole_0(X0) ) ),
    inference(unused_predicate_definition_removal,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

fof(f151,plain,(
    ! [X2] :
      ( ~ r2_hidden(X2,k4_orders_2(sK0,sK1))
      | r1_tarski(X2,k1_xboole_0) ) ),
    inference(forward_demodulation,[],[f148,f51])).

fof(f51,plain,(
    ! [X0] : k3_tarski(k1_tarski(X0)) = X0 ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] : k3_tarski(k1_tarski(X0)) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_zfmisc_1)).

fof(f148,plain,(
    ! [X2] :
      ( ~ r2_hidden(X2,k4_orders_2(sK0,sK1))
      | r1_tarski(k3_tarski(k1_tarski(X2)),k1_xboole_0) ) ),
    inference(resolution,[],[f82,f85])).

fof(f85,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,k4_orders_2(sK0,sK1))
      | r1_tarski(k3_tarski(X0),k1_xboole_0) ) ),
    inference(superposition,[],[f62,f49])).

fof(f49,plain,(
    k1_xboole_0 = k3_tarski(k4_orders_2(sK0,sK1)) ),
    inference(cnf_transformation,[],[f31])).

fof(f62,plain,(
    ! [X0,X1] :
      ( r1_tarski(k3_tarski(X0),k3_tarski(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( r1_tarski(k3_tarski(X0),k3_tarski(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => r1_tarski(k3_tarski(X0),k3_tarski(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t95_zfmisc_1)).

fof(f82,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(resolution,[],[f61,f67])).

fof(f67,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f61,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_subset_1)).

fof(f136,plain,(
    m2_orders_2(sK3(k4_orders_2(sK0,sK1)),sK0,sK1) ),
    inference(subsumption_resolution,[],[f133,f105])).

fof(f133,plain,
    ( m2_orders_2(sK3(k4_orders_2(sK0,sK1)),sK0,sK1)
    | v1_xboole_0(k4_orders_2(sK0,sK1)) ),
    inference(resolution,[],[f122,f58])).

fof(f122,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k4_orders_2(sK0,sK1))
      | m2_orders_2(X0,sK0,sK1) ) ),
    inference(subsumption_resolution,[],[f121,f43])).

fof(f121,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k4_orders_2(sK0,sK1))
      | m2_orders_2(X0,sK0,sK1)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f120,f44])).

fof(f120,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k4_orders_2(sK0,sK1))
      | m2_orders_2(X0,sK0,sK1)
      | ~ v3_orders_2(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f119,f45])).

fof(f119,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k4_orders_2(sK0,sK1))
      | m2_orders_2(X0,sK0,sK1)
      | ~ v4_orders_2(sK0)
      | ~ v3_orders_2(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f118,f46])).

fof(f118,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k4_orders_2(sK0,sK1))
      | m2_orders_2(X0,sK0,sK1)
      | ~ v5_orders_2(sK0)
      | ~ v4_orders_2(sK0)
      | ~ v3_orders_2(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f117,f47])).

fof(f117,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k4_orders_2(sK0,sK1))
      | m2_orders_2(X0,sK0,sK1)
      | ~ l1_orders_2(sK0)
      | ~ v5_orders_2(sK0)
      | ~ v4_orders_2(sK0)
      | ~ v3_orders_2(sK0)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f73,f48])).

fof(f73,plain,(
    ! [X4,X0,X1] :
      ( ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
      | ~ r2_hidden(X4,k4_orders_2(X0,X1))
      | m2_orders_2(X4,X0,X1)
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f54])).

fof(f54,plain,(
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
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f33,f34])).

fof(f34,plain,(
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

fof(f33,plain,(
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
    inference(rectify,[],[f32])).

fof(f32,plain,(
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
    inference(nnf_transformation,[],[f23])).

fof(f23,plain,(
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
    inference(flattening,[],[f22])).

fof(f22,plain,(
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
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
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

fof(f368,plain,
    ( ~ m2_orders_2(k1_xboole_0,sK0,sK1)
    | ~ l1_orders_2(sK0)
    | ~ v5_orders_2(sK0)
    | ~ v4_orders_2(sK0)
    | ~ v3_orders_2(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f124,f48])).

fof(f124,plain,(
    ! [X4,X3] :
      ( ~ m1_orders_1(X4,k1_orders_1(u1_struct_0(X3)))
      | ~ m2_orders_2(k1_xboole_0,X3,X4)
      | ~ l1_orders_2(X3)
      | ~ v5_orders_2(X3)
      | ~ v4_orders_2(X3)
      | ~ v3_orders_2(X3)
      | v2_struct_0(X3) ) ),
    inference(resolution,[],[f53,f78])).

fof(f78,plain,(
    ! [X0] : ~ r2_hidden(X0,k1_xboole_0) ),
    inference(superposition,[],[f59,f76])).

fof(f76,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f71])).

fof(f71,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f59,plain,(
    ! [X0,X1] : ~ r2_hidden(X0,k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : ~ r2_hidden(X0,k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t152_zfmisc_1)).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k1_funct_1(X1,u1_struct_0(X0)),X2)
      | ~ m2_orders_2(X2,X0,X1)
      | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
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
    inference(flattening,[],[f20])).

fof(f20,plain,(
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
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
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
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n002.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 12:55:22 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.20/0.49  % (28972)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.20/0.50  % (28980)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.20/0.52  % (28974)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.20/0.53  % (28977)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 1.34/0.53  % (28979)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 1.34/0.53  % (28975)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 1.34/0.53  % (28988)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 1.34/0.53  % (28973)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 1.34/0.53  % (28981)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 1.34/0.54  % (28995)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 1.34/0.54  % (28981)Refutation found. Thanks to Tanya!
% 1.34/0.54  % SZS status Theorem for theBenchmark
% 1.34/0.54  % (28973)Refutation not found, incomplete strategy% (28973)------------------------------
% 1.34/0.54  % (28973)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.34/0.54  % (28973)Termination reason: Refutation not found, incomplete strategy
% 1.34/0.54  
% 1.34/0.54  % (28973)Memory used [KB]: 1663
% 1.34/0.54  % (28973)Time elapsed: 0.135 s
% 1.34/0.54  % (28973)------------------------------
% 1.34/0.54  % (28973)------------------------------
% 1.34/0.54  % (28986)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 1.34/0.54  % (28999)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 1.34/0.54  % SZS output start Proof for theBenchmark
% 1.34/0.54  fof(f374,plain,(
% 1.34/0.54    $false),
% 1.34/0.54    inference(subsumption_resolution,[],[f373,f43])).
% 1.34/0.54  fof(f43,plain,(
% 1.34/0.54    ~v2_struct_0(sK0)),
% 1.34/0.54    inference(cnf_transformation,[],[f31])).
% 1.34/0.54  fof(f31,plain,(
% 1.34/0.54    (k1_xboole_0 = k3_tarski(k4_orders_2(sK0,sK1)) & m1_orders_1(sK1,k1_orders_1(u1_struct_0(sK0)))) & l1_orders_2(sK0) & v5_orders_2(sK0) & v4_orders_2(sK0) & v3_orders_2(sK0) & ~v2_struct_0(sK0)),
% 1.34/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f19,f30,f29])).
% 1.34/0.54  fof(f29,plain,(
% 1.34/0.54    ? [X0] : (? [X1] : (k1_xboole_0 = k3_tarski(k4_orders_2(X0,X1)) & m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => (? [X1] : (k1_xboole_0 = k3_tarski(k4_orders_2(sK0,X1)) & m1_orders_1(X1,k1_orders_1(u1_struct_0(sK0)))) & l1_orders_2(sK0) & v5_orders_2(sK0) & v4_orders_2(sK0) & v3_orders_2(sK0) & ~v2_struct_0(sK0))),
% 1.34/0.54    introduced(choice_axiom,[])).
% 1.34/0.54  fof(f30,plain,(
% 1.34/0.54    ? [X1] : (k1_xboole_0 = k3_tarski(k4_orders_2(sK0,X1)) & m1_orders_1(X1,k1_orders_1(u1_struct_0(sK0)))) => (k1_xboole_0 = k3_tarski(k4_orders_2(sK0,sK1)) & m1_orders_1(sK1,k1_orders_1(u1_struct_0(sK0))))),
% 1.34/0.54    introduced(choice_axiom,[])).
% 1.34/0.54  fof(f19,plain,(
% 1.34/0.54    ? [X0] : (? [X1] : (k1_xboole_0 = k3_tarski(k4_orders_2(X0,X1)) & m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0))),
% 1.34/0.54    inference(flattening,[],[f18])).
% 1.34/0.54  fof(f18,plain,(
% 1.34/0.54    ? [X0] : (? [X1] : (k1_xboole_0 = k3_tarski(k4_orders_2(X0,X1)) & m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) & (l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)))),
% 1.34/0.54    inference(ennf_transformation,[],[f16])).
% 1.34/0.54  fof(f16,negated_conjecture,(
% 1.34/0.54    ~! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) => k1_xboole_0 != k3_tarski(k4_orders_2(X0,X1))))),
% 1.34/0.54    inference(negated_conjecture,[],[f15])).
% 1.34/0.54  fof(f15,conjecture,(
% 1.34/0.54    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) => k1_xboole_0 != k3_tarski(k4_orders_2(X0,X1))))),
% 1.34/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t87_orders_2)).
% 1.34/0.54  fof(f373,plain,(
% 1.34/0.54    v2_struct_0(sK0)),
% 1.34/0.54    inference(subsumption_resolution,[],[f372,f44])).
% 1.34/0.54  fof(f44,plain,(
% 1.34/0.54    v3_orders_2(sK0)),
% 1.34/0.54    inference(cnf_transformation,[],[f31])).
% 1.34/0.54  % (28976)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 1.34/0.54  fof(f372,plain,(
% 1.34/0.54    ~v3_orders_2(sK0) | v2_struct_0(sK0)),
% 1.34/0.54    inference(subsumption_resolution,[],[f371,f45])).
% 1.34/0.54  fof(f45,plain,(
% 1.34/0.54    v4_orders_2(sK0)),
% 1.34/0.54    inference(cnf_transformation,[],[f31])).
% 1.34/0.54  fof(f371,plain,(
% 1.34/0.54    ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0)),
% 1.34/0.54    inference(subsumption_resolution,[],[f370,f46])).
% 1.34/0.54  fof(f46,plain,(
% 1.34/0.54    v5_orders_2(sK0)),
% 1.34/0.54    inference(cnf_transformation,[],[f31])).
% 1.34/0.54  fof(f370,plain,(
% 1.34/0.54    ~v5_orders_2(sK0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0)),
% 1.34/0.54    inference(subsumption_resolution,[],[f369,f47])).
% 1.34/0.54  fof(f47,plain,(
% 1.34/0.54    l1_orders_2(sK0)),
% 1.34/0.54    inference(cnf_transformation,[],[f31])).
% 1.34/0.54  fof(f369,plain,(
% 1.34/0.54    ~l1_orders_2(sK0) | ~v5_orders_2(sK0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0)),
% 1.34/0.54    inference(subsumption_resolution,[],[f368,f164])).
% 1.34/0.54  fof(f164,plain,(
% 1.34/0.54    m2_orders_2(k1_xboole_0,sK0,sK1)),
% 1.34/0.54    inference(backward_demodulation,[],[f136,f161])).
% 1.34/0.54  fof(f161,plain,(
% 1.34/0.54    k1_xboole_0 = sK3(k4_orders_2(sK0,sK1))),
% 1.34/0.54    inference(resolution,[],[f155,f90])).
% 1.34/0.54  fof(f90,plain,(
% 1.34/0.54    ( ! [X0] : (~r1_tarski(X0,k1_xboole_0) | k1_xboole_0 = X0) )),
% 1.34/0.54    inference(resolution,[],[f66,f50])).
% 1.34/0.54  fof(f50,plain,(
% 1.34/0.54    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 1.34/0.54    inference(cnf_transformation,[],[f3])).
% 1.34/0.54  fof(f3,axiom,(
% 1.34/0.54    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 1.34/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).
% 1.34/0.54  fof(f66,plain,(
% 1.34/0.54    ( ! [X0,X1] : (~r1_tarski(X1,X0) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 1.34/0.54    inference(cnf_transformation,[],[f39])).
% 1.34/0.54  fof(f39,plain,(
% 1.34/0.54    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.34/0.54    inference(flattening,[],[f38])).
% 1.34/0.54  fof(f38,plain,(
% 1.34/0.54    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.34/0.54    inference(nnf_transformation,[],[f2])).
% 1.34/0.54  fof(f2,axiom,(
% 1.34/0.54    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.34/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 1.34/0.54  fof(f155,plain,(
% 1.34/0.54    r1_tarski(sK3(k4_orders_2(sK0,sK1)),k1_xboole_0)),
% 1.34/0.54    inference(subsumption_resolution,[],[f152,f105])).
% 1.34/0.54  fof(f105,plain,(
% 1.34/0.54    ~v1_xboole_0(k4_orders_2(sK0,sK1))),
% 1.34/0.54    inference(subsumption_resolution,[],[f104,f43])).
% 1.34/0.54  fof(f104,plain,(
% 1.34/0.54    ~v1_xboole_0(k4_orders_2(sK0,sK1)) | v2_struct_0(sK0)),
% 1.34/0.54    inference(subsumption_resolution,[],[f103,f44])).
% 1.34/0.54  fof(f103,plain,(
% 1.34/0.54    ~v1_xboole_0(k4_orders_2(sK0,sK1)) | ~v3_orders_2(sK0) | v2_struct_0(sK0)),
% 1.34/0.54    inference(subsumption_resolution,[],[f102,f45])).
% 1.34/0.54  fof(f102,plain,(
% 1.34/0.54    ~v1_xboole_0(k4_orders_2(sK0,sK1)) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0)),
% 1.34/0.54    inference(subsumption_resolution,[],[f101,f46])).
% 1.34/0.54  fof(f101,plain,(
% 1.34/0.54    ~v1_xboole_0(k4_orders_2(sK0,sK1)) | ~v5_orders_2(sK0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0)),
% 1.34/0.54    inference(subsumption_resolution,[],[f100,f47])).
% 1.34/0.54  fof(f100,plain,(
% 1.34/0.54    ~v1_xboole_0(k4_orders_2(sK0,sK1)) | ~l1_orders_2(sK0) | ~v5_orders_2(sK0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0)),
% 1.34/0.54    inference(resolution,[],[f63,f48])).
% 1.34/0.54  fof(f48,plain,(
% 1.34/0.54    m1_orders_1(sK1,k1_orders_1(u1_struct_0(sK0)))),
% 1.34/0.54    inference(cnf_transformation,[],[f31])).
% 1.34/0.54  fof(f63,plain,(
% 1.34/0.54    ( ! [X0,X1] : (~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) | ~v1_xboole_0(k4_orders_2(X0,X1)) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 1.34/0.54    inference(cnf_transformation,[],[f28])).
% 1.34/0.54  fof(f28,plain,(
% 1.34/0.54    ! [X0,X1] : (~v1_xboole_0(k4_orders_2(X0,X1)) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 1.34/0.54    inference(flattening,[],[f27])).
% 1.34/0.54  fof(f27,plain,(
% 1.34/0.54    ! [X0,X1] : (~v1_xboole_0(k4_orders_2(X0,X1)) | (~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 1.34/0.54    inference(ennf_transformation,[],[f13])).
% 1.34/0.54  fof(f13,axiom,(
% 1.34/0.54    ! [X0,X1] : ((m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ~v1_xboole_0(k4_orders_2(X0,X1)))),
% 1.34/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc9_orders_2)).
% 1.34/0.54  fof(f152,plain,(
% 1.34/0.54    r1_tarski(sK3(k4_orders_2(sK0,sK1)),k1_xboole_0) | v1_xboole_0(k4_orders_2(sK0,sK1))),
% 1.34/0.54    inference(resolution,[],[f151,f58])).
% 1.34/0.54  fof(f58,plain,(
% 1.34/0.54    ( ! [X0] : (r2_hidden(sK3(X0),X0) | v1_xboole_0(X0)) )),
% 1.34/0.54    inference(cnf_transformation,[],[f37])).
% 1.34/0.54  fof(f37,plain,(
% 1.34/0.54    ! [X0] : (v1_xboole_0(X0) | r2_hidden(sK3(X0),X0))),
% 1.34/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f24,f36])).
% 1.34/0.54  fof(f36,plain,(
% 1.34/0.54    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK3(X0),X0))),
% 1.34/0.54    introduced(choice_axiom,[])).
% 1.34/0.54  fof(f24,plain,(
% 1.34/0.54    ! [X0] : (v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0))),
% 1.34/0.54    inference(ennf_transformation,[],[f17])).
% 1.34/0.54  fof(f17,plain,(
% 1.34/0.54    ! [X0] : (! [X1] : ~r2_hidden(X1,X0) => v1_xboole_0(X0))),
% 1.34/0.54    inference(unused_predicate_definition_removal,[],[f1])).
% 1.34/0.54  fof(f1,axiom,(
% 1.34/0.54    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 1.34/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).
% 1.34/0.54  fof(f151,plain,(
% 1.34/0.54    ( ! [X2] : (~r2_hidden(X2,k4_orders_2(sK0,sK1)) | r1_tarski(X2,k1_xboole_0)) )),
% 1.34/0.54    inference(forward_demodulation,[],[f148,f51])).
% 1.34/0.54  fof(f51,plain,(
% 1.34/0.54    ( ! [X0] : (k3_tarski(k1_tarski(X0)) = X0) )),
% 1.34/0.54    inference(cnf_transformation,[],[f8])).
% 1.34/0.54  fof(f8,axiom,(
% 1.34/0.54    ! [X0] : k3_tarski(k1_tarski(X0)) = X0),
% 1.34/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_zfmisc_1)).
% 1.34/0.54  fof(f148,plain,(
% 1.34/0.54    ( ! [X2] : (~r2_hidden(X2,k4_orders_2(sK0,sK1)) | r1_tarski(k3_tarski(k1_tarski(X2)),k1_xboole_0)) )),
% 1.34/0.54    inference(resolution,[],[f82,f85])).
% 1.34/0.54  fof(f85,plain,(
% 1.34/0.54    ( ! [X0] : (~r1_tarski(X0,k4_orders_2(sK0,sK1)) | r1_tarski(k3_tarski(X0),k1_xboole_0)) )),
% 1.34/0.54    inference(superposition,[],[f62,f49])).
% 1.34/0.54  fof(f49,plain,(
% 1.34/0.54    k1_xboole_0 = k3_tarski(k4_orders_2(sK0,sK1))),
% 1.34/0.54    inference(cnf_transformation,[],[f31])).
% 1.34/0.54  fof(f62,plain,(
% 1.34/0.54    ( ! [X0,X1] : (r1_tarski(k3_tarski(X0),k3_tarski(X1)) | ~r1_tarski(X0,X1)) )),
% 1.34/0.54    inference(cnf_transformation,[],[f26])).
% 1.34/0.54  fof(f26,plain,(
% 1.34/0.54    ! [X0,X1] : (r1_tarski(k3_tarski(X0),k3_tarski(X1)) | ~r1_tarski(X0,X1))),
% 1.34/0.54    inference(ennf_transformation,[],[f9])).
% 1.34/0.54  fof(f9,axiom,(
% 1.34/0.54    ! [X0,X1] : (r1_tarski(X0,X1) => r1_tarski(k3_tarski(X0),k3_tarski(X1)))),
% 1.34/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t95_zfmisc_1)).
% 1.34/0.54  fof(f82,plain,(
% 1.34/0.54    ( ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) )),
% 1.34/0.54    inference(resolution,[],[f61,f67])).
% 1.34/0.54  fof(f67,plain,(
% 1.34/0.54    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 1.34/0.54    inference(cnf_transformation,[],[f40])).
% 1.34/0.54  fof(f40,plain,(
% 1.34/0.54    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 1.34/0.54    inference(nnf_transformation,[],[f11])).
% 1.34/0.54  fof(f11,axiom,(
% 1.34/0.54    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 1.34/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).
% 1.34/0.54  fof(f61,plain,(
% 1.34/0.54    ( ! [X0,X1] : (m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1)) | ~r2_hidden(X0,X1)) )),
% 1.34/0.54    inference(cnf_transformation,[],[f25])).
% 1.43/0.54  fof(f25,plain,(
% 1.43/0.54    ! [X0,X1] : (m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1)) | ~r2_hidden(X0,X1))),
% 1.43/0.54    inference(ennf_transformation,[],[f10])).
% 1.43/0.54  fof(f10,axiom,(
% 1.43/0.54    ! [X0,X1] : (r2_hidden(X0,X1) => m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1)))),
% 1.43/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_subset_1)).
% 1.43/0.54  fof(f136,plain,(
% 1.43/0.54    m2_orders_2(sK3(k4_orders_2(sK0,sK1)),sK0,sK1)),
% 1.43/0.54    inference(subsumption_resolution,[],[f133,f105])).
% 1.43/0.54  fof(f133,plain,(
% 1.43/0.54    m2_orders_2(sK3(k4_orders_2(sK0,sK1)),sK0,sK1) | v1_xboole_0(k4_orders_2(sK0,sK1))),
% 1.43/0.54    inference(resolution,[],[f122,f58])).
% 1.43/0.54  fof(f122,plain,(
% 1.43/0.54    ( ! [X0] : (~r2_hidden(X0,k4_orders_2(sK0,sK1)) | m2_orders_2(X0,sK0,sK1)) )),
% 1.43/0.54    inference(subsumption_resolution,[],[f121,f43])).
% 1.43/0.54  fof(f121,plain,(
% 1.43/0.54    ( ! [X0] : (~r2_hidden(X0,k4_orders_2(sK0,sK1)) | m2_orders_2(X0,sK0,sK1) | v2_struct_0(sK0)) )),
% 1.43/0.54    inference(subsumption_resolution,[],[f120,f44])).
% 1.43/0.54  fof(f120,plain,(
% 1.43/0.54    ( ! [X0] : (~r2_hidden(X0,k4_orders_2(sK0,sK1)) | m2_orders_2(X0,sK0,sK1) | ~v3_orders_2(sK0) | v2_struct_0(sK0)) )),
% 1.43/0.54    inference(subsumption_resolution,[],[f119,f45])).
% 1.43/0.54  fof(f119,plain,(
% 1.43/0.54    ( ! [X0] : (~r2_hidden(X0,k4_orders_2(sK0,sK1)) | m2_orders_2(X0,sK0,sK1) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0)) )),
% 1.43/0.54    inference(subsumption_resolution,[],[f118,f46])).
% 1.43/0.54  fof(f118,plain,(
% 1.43/0.54    ( ! [X0] : (~r2_hidden(X0,k4_orders_2(sK0,sK1)) | m2_orders_2(X0,sK0,sK1) | ~v5_orders_2(sK0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0)) )),
% 1.43/0.54    inference(subsumption_resolution,[],[f117,f47])).
% 1.43/0.54  fof(f117,plain,(
% 1.43/0.54    ( ! [X0] : (~r2_hidden(X0,k4_orders_2(sK0,sK1)) | m2_orders_2(X0,sK0,sK1) | ~l1_orders_2(sK0) | ~v5_orders_2(sK0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0)) )),
% 1.43/0.54    inference(resolution,[],[f73,f48])).
% 1.43/0.54  fof(f73,plain,(
% 1.43/0.54    ( ! [X4,X0,X1] : (~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) | ~r2_hidden(X4,k4_orders_2(X0,X1)) | m2_orders_2(X4,X0,X1) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 1.43/0.54    inference(equality_resolution,[],[f54])).
% 1.43/0.54  fof(f54,plain,(
% 1.43/0.54    ( ! [X4,X2,X0,X1] : (m2_orders_2(X4,X0,X1) | ~r2_hidden(X4,X2) | k4_orders_2(X0,X1) != X2 | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 1.43/0.54    inference(cnf_transformation,[],[f35])).
% 1.43/0.54  fof(f35,plain,(
% 1.43/0.54    ! [X0] : (! [X1] : (! [X2] : ((k4_orders_2(X0,X1) = X2 | ((~m2_orders_2(sK2(X0,X1,X2),X0,X1) | ~r2_hidden(sK2(X0,X1,X2),X2)) & (m2_orders_2(sK2(X0,X1,X2),X0,X1) | r2_hidden(sK2(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~m2_orders_2(X4,X0,X1)) & (m2_orders_2(X4,X0,X1) | ~r2_hidden(X4,X2))) | k4_orders_2(X0,X1) != X2)) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 1.43/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f33,f34])).
% 1.43/0.54  fof(f34,plain,(
% 1.43/0.54    ! [X2,X1,X0] : (? [X3] : ((~m2_orders_2(X3,X0,X1) | ~r2_hidden(X3,X2)) & (m2_orders_2(X3,X0,X1) | r2_hidden(X3,X2))) => ((~m2_orders_2(sK2(X0,X1,X2),X0,X1) | ~r2_hidden(sK2(X0,X1,X2),X2)) & (m2_orders_2(sK2(X0,X1,X2),X0,X1) | r2_hidden(sK2(X0,X1,X2),X2))))),
% 1.43/0.54    introduced(choice_axiom,[])).
% 1.43/0.54  fof(f33,plain,(
% 1.43/0.54    ! [X0] : (! [X1] : (! [X2] : ((k4_orders_2(X0,X1) = X2 | ? [X3] : ((~m2_orders_2(X3,X0,X1) | ~r2_hidden(X3,X2)) & (m2_orders_2(X3,X0,X1) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~m2_orders_2(X4,X0,X1)) & (m2_orders_2(X4,X0,X1) | ~r2_hidden(X4,X2))) | k4_orders_2(X0,X1) != X2)) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 1.43/0.54    inference(rectify,[],[f32])).
% 1.43/0.54  fof(f32,plain,(
% 1.43/0.54    ! [X0] : (! [X1] : (! [X2] : ((k4_orders_2(X0,X1) = X2 | ? [X3] : ((~m2_orders_2(X3,X0,X1) | ~r2_hidden(X3,X2)) & (m2_orders_2(X3,X0,X1) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | ~m2_orders_2(X3,X0,X1)) & (m2_orders_2(X3,X0,X1) | ~r2_hidden(X3,X2))) | k4_orders_2(X0,X1) != X2)) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 1.43/0.54    inference(nnf_transformation,[],[f23])).
% 1.43/0.54  fof(f23,plain,(
% 1.43/0.54    ! [X0] : (! [X1] : (! [X2] : (k4_orders_2(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> m2_orders_2(X3,X0,X1))) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 1.43/0.54    inference(flattening,[],[f22])).
% 1.43/0.54  fof(f22,plain,(
% 1.43/0.54    ! [X0] : (! [X1] : (! [X2] : (k4_orders_2(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> m2_orders_2(X3,X0,X1))) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) | (~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 1.43/0.54    inference(ennf_transformation,[],[f12])).
% 1.43/0.54  fof(f12,axiom,(
% 1.43/0.54    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) => ! [X2] : (k4_orders_2(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> m2_orders_2(X3,X0,X1)))))),
% 1.43/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d17_orders_2)).
% 1.43/0.54  fof(f368,plain,(
% 1.43/0.54    ~m2_orders_2(k1_xboole_0,sK0,sK1) | ~l1_orders_2(sK0) | ~v5_orders_2(sK0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0)),
% 1.43/0.54    inference(resolution,[],[f124,f48])).
% 1.43/0.54  fof(f124,plain,(
% 1.43/0.54    ( ! [X4,X3] : (~m1_orders_1(X4,k1_orders_1(u1_struct_0(X3))) | ~m2_orders_2(k1_xboole_0,X3,X4) | ~l1_orders_2(X3) | ~v5_orders_2(X3) | ~v4_orders_2(X3) | ~v3_orders_2(X3) | v2_struct_0(X3)) )),
% 1.43/0.54    inference(resolution,[],[f53,f78])).
% 1.43/0.54  fof(f78,plain,(
% 1.43/0.54    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0)) )),
% 1.43/0.54    inference(superposition,[],[f59,f76])).
% 1.43/0.54  fof(f76,plain,(
% 1.43/0.54    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 1.43/0.54    inference(equality_resolution,[],[f71])).
% 1.43/0.54  fof(f71,plain,(
% 1.43/0.54    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X1) )),
% 1.43/0.54    inference(cnf_transformation,[],[f42])).
% 1.43/0.54  fof(f42,plain,(
% 1.43/0.54    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 1.43/0.54    inference(flattening,[],[f41])).
% 1.43/0.54  fof(f41,plain,(
% 1.43/0.54    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 1.43/0.54    inference(nnf_transformation,[],[f6])).
% 1.43/0.54  fof(f6,axiom,(
% 1.43/0.54    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 1.43/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 1.43/0.54  fof(f59,plain,(
% 1.43/0.54    ( ! [X0,X1] : (~r2_hidden(X0,k2_zfmisc_1(X0,X1))) )),
% 1.43/0.54    inference(cnf_transformation,[],[f7])).
% 1.43/0.54  fof(f7,axiom,(
% 1.43/0.54    ! [X0,X1] : ~r2_hidden(X0,k2_zfmisc_1(X0,X1))),
% 1.43/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t152_zfmisc_1)).
% 1.43/0.54  fof(f53,plain,(
% 1.43/0.54    ( ! [X2,X0,X1] : (r2_hidden(k1_funct_1(X1,u1_struct_0(X0)),X2) | ~m2_orders_2(X2,X0,X1) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 1.43/0.54    inference(cnf_transformation,[],[f21])).
% 1.43/0.54  fof(f21,plain,(
% 1.43/0.54    ! [X0] : (! [X1] : (! [X2] : (r2_hidden(k1_funct_1(X1,u1_struct_0(X0)),X2) | ~m2_orders_2(X2,X0,X1)) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 1.43/0.54    inference(flattening,[],[f20])).
% 1.43/0.54  fof(f20,plain,(
% 1.43/0.54    ! [X0] : (! [X1] : (! [X2] : (r2_hidden(k1_funct_1(X1,u1_struct_0(X0)),X2) | ~m2_orders_2(X2,X0,X1)) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) | (~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 1.43/0.54    inference(ennf_transformation,[],[f14])).
% 1.43/0.54  fof(f14,axiom,(
% 1.43/0.54    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) => ! [X2] : (m2_orders_2(X2,X0,X1) => r2_hidden(k1_funct_1(X1,u1_struct_0(X0)),X2))))),
% 1.43/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_orders_2)).
% 1.43/0.54  % SZS output end Proof for theBenchmark
% 1.43/0.54  % (28981)------------------------------
% 1.43/0.54  % (28981)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.43/0.54  % (28981)Termination reason: Refutation
% 1.43/0.54  
% 1.43/0.54  % (28981)Memory used [KB]: 1918
% 1.43/0.54  % (28981)Time elapsed: 0.131 s
% 1.43/0.54  % (28981)------------------------------
% 1.43/0.54  % (28981)------------------------------
% 1.43/0.55  % (28971)Success in time 0.187 s
%------------------------------------------------------------------------------
