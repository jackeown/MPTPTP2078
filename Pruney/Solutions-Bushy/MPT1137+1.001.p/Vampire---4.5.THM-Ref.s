%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1137+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n032.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:49:20 EST 2020

% Result     : Theorem 0.12s
% Output     : Refutation 0.12s
% Verified   : 
% Statistics : Number of formulae       :  119 ( 562 expanded)
%              Number of leaves         :   16 ( 191 expanded)
%              Depth                    :   33
%              Number of atoms          :  466 (3498 expanded)
%              Number of equality atoms :   37 ( 476 expanded)
%              Maximal formula depth    :   12 (   6 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f195,plain,(
    $false ),
    inference(subsumption_resolution,[],[f194,f139])).

fof(f139,plain,(
    r2_hidden(sK3,u1_struct_0(sK2)) ),
    inference(subsumption_resolution,[],[f138,f44])).

fof(f44,plain,(
    m1_subset_1(sK4,u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,
    ( sK3 != sK4
    & r1_orders_2(sK2,sK4,sK3)
    & r1_orders_2(sK2,sK3,sK4)
    & m1_subset_1(sK4,u1_struct_0(sK2))
    & m1_subset_1(sK3,u1_struct_0(sK2))
    & l1_orders_2(sK2)
    & v5_orders_2(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f13,f30,f29,f28])).

fof(f28,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( X1 != X2
                & r1_orders_2(X0,X2,X1)
                & r1_orders_2(X0,X1,X2)
                & m1_subset_1(X2,u1_struct_0(X0)) )
            & m1_subset_1(X1,u1_struct_0(X0)) )
        & l1_orders_2(X0)
        & v5_orders_2(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( X1 != X2
              & r1_orders_2(sK2,X2,X1)
              & r1_orders_2(sK2,X1,X2)
              & m1_subset_1(X2,u1_struct_0(sK2)) )
          & m1_subset_1(X1,u1_struct_0(sK2)) )
      & l1_orders_2(sK2)
      & v5_orders_2(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( X1 != X2
            & r1_orders_2(sK2,X2,X1)
            & r1_orders_2(sK2,X1,X2)
            & m1_subset_1(X2,u1_struct_0(sK2)) )
        & m1_subset_1(X1,u1_struct_0(sK2)) )
   => ( ? [X2] :
          ( sK3 != X2
          & r1_orders_2(sK2,X2,sK3)
          & r1_orders_2(sK2,sK3,X2)
          & m1_subset_1(X2,u1_struct_0(sK2)) )
      & m1_subset_1(sK3,u1_struct_0(sK2)) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,
    ( ? [X2] :
        ( sK3 != X2
        & r1_orders_2(sK2,X2,sK3)
        & r1_orders_2(sK2,sK3,X2)
        & m1_subset_1(X2,u1_struct_0(sK2)) )
   => ( sK3 != sK4
      & r1_orders_2(sK2,sK4,sK3)
      & r1_orders_2(sK2,sK3,sK4)
      & m1_subset_1(sK4,u1_struct_0(sK2)) ) ),
    introduced(choice_axiom,[])).

fof(f13,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( X1 != X2
              & r1_orders_2(X0,X2,X1)
              & r1_orders_2(X0,X1,X2)
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_orders_2(X0)
      & v5_orders_2(X0) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( X1 != X2
              & r1_orders_2(X0,X2,X1)
              & r1_orders_2(X0,X1,X2)
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_orders_2(X0)
      & v5_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_orders_2(X0)
          & v5_orders_2(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => ( ( r1_orders_2(X0,X2,X1)
                    & r1_orders_2(X0,X1,X2) )
                 => X1 = X2 ) ) ) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f10,conjecture,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( ( r1_orders_2(X0,X2,X1)
                  & r1_orders_2(X0,X1,X2) )
               => X1 = X2 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t25_orders_2)).

fof(f138,plain,
    ( r2_hidden(sK3,u1_struct_0(sK2))
    | ~ m1_subset_1(sK4,u1_struct_0(sK2)) ),
    inference(resolution,[],[f136,f45])).

fof(f45,plain,(
    r1_orders_2(sK2,sK3,sK4) ),
    inference(cnf_transformation,[],[f31])).

fof(f136,plain,(
    ! [X0] :
      ( ~ r1_orders_2(sK2,sK3,X0)
      | r2_hidden(sK3,u1_struct_0(sK2))
      | ~ m1_subset_1(X0,u1_struct_0(sK2)) ) ),
    inference(resolution,[],[f121,f43])).

fof(f43,plain,(
    m1_subset_1(sK3,u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f31])).

fof(f121,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,u1_struct_0(sK2))
      | ~ m1_subset_1(X0,u1_struct_0(sK2))
      | r2_hidden(sK3,u1_struct_0(sK2))
      | ~ r1_orders_2(sK2,X1,X0) ) ),
    inference(resolution,[],[f120,f88])).

fof(f88,plain,(
    ! [X0,X1] :
      ( r2_hidden(k4_tarski(X0,X1),u1_orders_2(sK2))
      | ~ m1_subset_1(X1,u1_struct_0(sK2))
      | ~ m1_subset_1(X0,u1_struct_0(sK2))
      | ~ r1_orders_2(sK2,X0,X1) ) ),
    inference(resolution,[],[f60,f42])).

fof(f42,plain,(
    l1_orders_2(sK2) ),
    inference(cnf_transformation,[],[f31])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_orders_2(X0)
      | ~ r1_orders_2(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0)) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( r1_orders_2(X0,X1,X2)
                  | ~ r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0)) )
                & ( r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0))
                  | ~ r1_orders_2(X0,X1,X2) ) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(nnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r1_orders_2(X0,X1,X2)
              <=> r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( r1_orders_2(X0,X1,X2)
              <=> r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d9_orders_2)).

fof(f120,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,u1_orders_2(sK2))
      | r2_hidden(sK3,u1_struct_0(sK2)) ) ),
    inference(resolution,[],[f119,f71])).

fof(f71,plain,(
    m1_subset_1(u1_orders_2(sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK2)))) ),
    inference(resolution,[],[f57,f42])).

fof(f57,plain,(
    ! [X0] :
      ( ~ l1_orders_2(X0)
      | m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)))) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_u1_orders_2)).

fof(f119,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK2))))
      | r2_hidden(sK3,u1_struct_0(sK2))
      | ~ r2_hidden(X1,X0) ) ),
    inference(resolution,[],[f118,f65])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).

fof(f118,plain,
    ( v1_xboole_0(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK2)))
    | r2_hidden(sK3,u1_struct_0(sK2)) ),
    inference(subsumption_resolution,[],[f117,f43])).

fof(f117,plain,
    ( ~ m1_subset_1(sK3,u1_struct_0(sK2))
    | r2_hidden(sK3,u1_struct_0(sK2))
    | v1_xboole_0(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK2))) ),
    inference(resolution,[],[f93,f46])).

fof(f46,plain,(
    r1_orders_2(sK2,sK4,sK3) ),
    inference(cnf_transformation,[],[f31])).

fof(f93,plain,(
    ! [X1] :
      ( ~ r1_orders_2(sK2,sK4,X1)
      | ~ m1_subset_1(X1,u1_struct_0(sK2))
      | r2_hidden(X1,u1_struct_0(sK2))
      | v1_xboole_0(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK2))) ) ),
    inference(resolution,[],[f89,f44])).

fof(f89,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,u1_struct_0(sK2))
      | ~ m1_subset_1(X0,u1_struct_0(sK2))
      | ~ r1_orders_2(sK2,X1,X0)
      | r2_hidden(X0,u1_struct_0(sK2))
      | v1_xboole_0(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK2))) ) ),
    inference(resolution,[],[f88,f81])).

fof(f81,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(k4_tarski(X1,X0),u1_orders_2(sK2))
      | r2_hidden(X0,u1_struct_0(sK2))
      | v1_xboole_0(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK2))) ) ),
    inference(resolution,[],[f70,f73])).

fof(f73,plain,(
    ! [X0] :
      ( m1_subset_1(X0,k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK2)))
      | ~ r2_hidden(X0,u1_orders_2(sK2)) ) ),
    inference(resolution,[],[f71,f64])).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | m1_subset_1(X0,X2)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).

fof(f70,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(k4_tarski(X3,X0),k2_zfmisc_1(X2,X1))
      | v1_xboole_0(k2_zfmisc_1(X2,X1))
      | r2_hidden(X0,X1) ) ),
    inference(resolution,[],[f67,f62])).

fof(f62,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

fof(f67,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
      | r2_hidden(X1,X3) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
        | ~ r2_hidden(X1,X3)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X3)
          & r2_hidden(X0,X2) )
        | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ) ),
    inference(flattening,[],[f39])).

fof(f39,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
        | ~ r2_hidden(X1,X3)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X3)
          & r2_hidden(X0,X2) )
        | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ) ),
    inference(nnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
    <=> ( r2_hidden(X1,X3)
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t106_zfmisc_1)).

fof(f194,plain,(
    ~ r2_hidden(sK3,u1_struct_0(sK2)) ),
    inference(resolution,[],[f192,f116])).

fof(f116,plain,(
    r2_hidden(sK4,u1_struct_0(sK2)) ),
    inference(subsumption_resolution,[],[f115,f44])).

fof(f115,plain,
    ( r2_hidden(sK4,u1_struct_0(sK2))
    | ~ m1_subset_1(sK4,u1_struct_0(sK2)) ),
    inference(resolution,[],[f113,f45])).

fof(f113,plain,(
    ! [X0] :
      ( ~ r1_orders_2(sK2,sK3,X0)
      | r2_hidden(sK4,u1_struct_0(sK2))
      | ~ m1_subset_1(X0,u1_struct_0(sK2)) ) ),
    inference(resolution,[],[f99,f43])).

fof(f99,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,u1_struct_0(sK2))
      | ~ m1_subset_1(X0,u1_struct_0(sK2))
      | r2_hidden(sK4,u1_struct_0(sK2))
      | ~ r1_orders_2(sK2,X1,X0) ) ),
    inference(resolution,[],[f98,f88])).

fof(f98,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,u1_orders_2(sK2))
      | r2_hidden(sK4,u1_struct_0(sK2)) ) ),
    inference(resolution,[],[f97,f71])).

fof(f97,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK2))))
      | r2_hidden(sK4,u1_struct_0(sK2))
      | ~ r2_hidden(X1,X0) ) ),
    inference(resolution,[],[f95,f65])).

fof(f95,plain,
    ( v1_xboole_0(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK2)))
    | r2_hidden(sK4,u1_struct_0(sK2)) ),
    inference(subsumption_resolution,[],[f94,f44])).

fof(f94,plain,
    ( ~ m1_subset_1(sK4,u1_struct_0(sK2))
    | r2_hidden(sK4,u1_struct_0(sK2))
    | v1_xboole_0(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK2))) ),
    inference(resolution,[],[f92,f45])).

fof(f92,plain,(
    ! [X0] :
      ( ~ r1_orders_2(sK2,sK3,X0)
      | ~ m1_subset_1(X0,u1_struct_0(sK2))
      | r2_hidden(X0,u1_struct_0(sK2))
      | v1_xboole_0(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK2))) ) ),
    inference(resolution,[],[f89,f43])).

fof(f192,plain,(
    ! [X0] :
      ( ~ r2_hidden(sK4,X0)
      | ~ r2_hidden(sK3,X0) ) ),
    inference(subsumption_resolution,[],[f191,f46])).

fof(f191,plain,(
    ! [X0] :
      ( ~ r2_hidden(sK4,X0)
      | ~ r2_hidden(sK3,X0)
      | ~ r1_orders_2(sK2,sK4,sK3) ) ),
    inference(subsumption_resolution,[],[f190,f44])).

fof(f190,plain,(
    ! [X0] :
      ( ~ r2_hidden(sK4,X0)
      | ~ r2_hidden(sK3,X0)
      | ~ m1_subset_1(sK4,u1_struct_0(sK2))
      | ~ r1_orders_2(sK2,sK4,sK3) ) ),
    inference(subsumption_resolution,[],[f188,f43])).

fof(f188,plain,(
    ! [X0] :
      ( ~ r2_hidden(sK4,X0)
      | ~ r2_hidden(sK3,X0)
      | ~ m1_subset_1(sK3,u1_struct_0(sK2))
      | ~ m1_subset_1(sK4,u1_struct_0(sK2))
      | ~ r1_orders_2(sK2,sK4,sK3) ) ),
    inference(resolution,[],[f187,f88])).

fof(f187,plain,(
    ! [X0] :
      ( ~ r2_hidden(k4_tarski(sK4,sK3),u1_orders_2(sK2))
      | ~ r2_hidden(sK4,X0)
      | ~ r2_hidden(sK3,X0) ) ),
    inference(subsumption_resolution,[],[f186,f44])).

fof(f186,plain,(
    ! [X0] :
      ( ~ r2_hidden(sK4,X0)
      | ~ m1_subset_1(sK4,u1_struct_0(sK2))
      | ~ r2_hidden(k4_tarski(sK4,sK3),u1_orders_2(sK2))
      | ~ r2_hidden(sK3,X0) ) ),
    inference(subsumption_resolution,[],[f185,f47])).

fof(f47,plain,(
    sK3 != sK4 ),
    inference(cnf_transformation,[],[f31])).

fof(f185,plain,(
    ! [X0] :
      ( ~ r2_hidden(sK4,X0)
      | sK3 = sK4
      | ~ m1_subset_1(sK4,u1_struct_0(sK2))
      | ~ r2_hidden(k4_tarski(sK4,sK3),u1_orders_2(sK2))
      | ~ r2_hidden(sK3,X0) ) ),
    inference(resolution,[],[f183,f45])).

fof(f183,plain,(
    ! [X0,X1] :
      ( ~ r1_orders_2(sK2,sK3,X1)
      | ~ r2_hidden(X1,X0)
      | sK3 = X1
      | ~ m1_subset_1(X1,u1_struct_0(sK2))
      | ~ r2_hidden(k4_tarski(X1,sK3),u1_orders_2(sK2))
      | ~ r2_hidden(sK3,X0) ) ),
    inference(resolution,[],[f175,f43])).

fof(f175,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,u1_struct_0(sK2))
      | ~ r2_hidden(X1,X2)
      | ~ r2_hidden(X0,X2)
      | X0 = X1
      | ~ m1_subset_1(X0,u1_struct_0(sK2))
      | ~ r2_hidden(k4_tarski(X0,X1),u1_orders_2(sK2))
      | ~ r1_orders_2(sK2,X1,X0) ) ),
    inference(resolution,[],[f174,f88])).

fof(f174,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),u1_orders_2(sK2))
      | ~ r2_hidden(k4_tarski(X1,X0),u1_orders_2(sK2))
      | ~ r2_hidden(X0,X2)
      | ~ r2_hidden(X1,X2)
      | X0 = X1 ) ),
    inference(resolution,[],[f173,f50])).

fof(f50,plain,(
    ! [X4,X0,X5,X1] :
      ( ~ sP0(X0,X1)
      | ~ r2_hidden(k4_tarski(X5,X4),X0)
      | ~ r2_hidden(k4_tarski(X4,X5),X0)
      | ~ r2_hidden(X5,X1)
      | ~ r2_hidden(X4,X1)
      | X4 = X5 ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( sP0(X0,X1)
        | ( sK5(X0,X1) != sK6(X0,X1)
          & r2_hidden(k4_tarski(sK6(X0,X1),sK5(X0,X1)),X0)
          & r2_hidden(k4_tarski(sK5(X0,X1),sK6(X0,X1)),X0)
          & r2_hidden(sK6(X0,X1),X1)
          & r2_hidden(sK5(X0,X1),X1) ) )
      & ( ! [X4,X5] :
            ( X4 = X5
            | ~ r2_hidden(k4_tarski(X5,X4),X0)
            | ~ r2_hidden(k4_tarski(X4,X5),X0)
            | ~ r2_hidden(X5,X1)
            | ~ r2_hidden(X4,X1) )
        | ~ sP0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6])],[f34,f35])).

fof(f35,plain,(
    ! [X1,X0] :
      ( ? [X2,X3] :
          ( X2 != X3
          & r2_hidden(k4_tarski(X3,X2),X0)
          & r2_hidden(k4_tarski(X2,X3),X0)
          & r2_hidden(X3,X1)
          & r2_hidden(X2,X1) )
     => ( sK5(X0,X1) != sK6(X0,X1)
        & r2_hidden(k4_tarski(sK6(X0,X1),sK5(X0,X1)),X0)
        & r2_hidden(k4_tarski(sK5(X0,X1),sK6(X0,X1)),X0)
        & r2_hidden(sK6(X0,X1),X1)
        & r2_hidden(sK5(X0,X1),X1) ) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( sP0(X0,X1)
        | ? [X2,X3] :
            ( X2 != X3
            & r2_hidden(k4_tarski(X3,X2),X0)
            & r2_hidden(k4_tarski(X2,X3),X0)
            & r2_hidden(X3,X1)
            & r2_hidden(X2,X1) ) )
      & ( ! [X4,X5] :
            ( X4 = X5
            | ~ r2_hidden(k4_tarski(X5,X4),X0)
            | ~ r2_hidden(k4_tarski(X4,X5),X0)
            | ~ r2_hidden(X5,X1)
            | ~ r2_hidden(X4,X1) )
        | ~ sP0(X0,X1) ) ) ),
    inference(rectify,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( sP0(X0,X1)
        | ? [X2,X3] :
            ( X2 != X3
            & r2_hidden(k4_tarski(X3,X2),X0)
            & r2_hidden(k4_tarski(X2,X3),X0)
            & r2_hidden(X3,X1)
            & r2_hidden(X2,X1) ) )
      & ( ! [X2,X3] :
            ( X2 = X3
            | ~ r2_hidden(k4_tarski(X3,X2),X0)
            | ~ r2_hidden(k4_tarski(X2,X3),X0)
            | ~ r2_hidden(X3,X1)
            | ~ r2_hidden(X2,X1) )
        | ~ sP0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( sP0(X0,X1)
    <=> ! [X2,X3] :
          ( X2 = X3
          | ~ r2_hidden(k4_tarski(X3,X2),X0)
          | ~ r2_hidden(k4_tarski(X2,X3),X0)
          | ~ r2_hidden(X3,X1)
          | ~ r2_hidden(X2,X1) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f173,plain,(
    ! [X0] : sP0(u1_orders_2(sK2),X0) ),
    inference(condensation,[],[f163])).

fof(f163,plain,(
    ! [X4,X3] :
      ( sP0(u1_orders_2(sK2),X3)
      | sP0(u1_orders_2(sK2),X4) ) ),
    inference(resolution,[],[f161,f53])).

fof(f53,plain,(
    ! [X0,X1] :
      ( r2_hidden(k4_tarski(sK5(X0,X1),sK6(X0,X1)),X0)
      | sP0(X0,X1) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f161,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,u1_orders_2(sK2))
      | sP0(u1_orders_2(sK2),X0) ) ),
    inference(resolution,[],[f160,f71])).

fof(f160,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK2))))
      | sP0(u1_orders_2(sK2),X0)
      | ~ r2_hidden(X2,X1) ) ),
    inference(resolution,[],[f156,f65])).

fof(f156,plain,(
    ! [X0] :
      ( sP0(u1_orders_2(sK2),X0)
      | v1_xboole_0(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK2))) ) ),
    inference(subsumption_resolution,[],[f155,f83])).

fof(f83,plain,(
    ! [X2] :
      ( r2_hidden(sK5(u1_orders_2(sK2),X2),u1_struct_0(sK2))
      | v1_xboole_0(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK2)))
      | sP0(u1_orders_2(sK2),X2) ) ),
    inference(resolution,[],[f80,f53])).

fof(f80,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),u1_orders_2(sK2))
      | r2_hidden(X0,u1_struct_0(sK2))
      | v1_xboole_0(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK2))) ) ),
    inference(resolution,[],[f69,f73])).

fof(f69,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(k4_tarski(X0,X3),k2_zfmisc_1(X1,X2))
      | v1_xboole_0(k2_zfmisc_1(X1,X2))
      | r2_hidden(X0,X1) ) ),
    inference(resolution,[],[f66,f62])).

fof(f66,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
      | r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f155,plain,(
    ! [X0] :
      ( ~ r2_hidden(sK5(u1_orders_2(sK2),X0),u1_struct_0(sK2))
      | sP0(u1_orders_2(sK2),X0)
      | v1_xboole_0(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK2))) ) ),
    inference(duplicate_literal_removal,[],[f151])).

fof(f151,plain,(
    ! [X0] :
      ( ~ r2_hidden(sK5(u1_orders_2(sK2),X0),u1_struct_0(sK2))
      | sP0(u1_orders_2(sK2),X0)
      | v1_xboole_0(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK2)))
      | sP0(u1_orders_2(sK2),X0) ) ),
    inference(resolution,[],[f150,f84])).

fof(f84,plain,(
    ! [X3] :
      ( r2_hidden(sK6(u1_orders_2(sK2),X3),u1_struct_0(sK2))
      | v1_xboole_0(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK2)))
      | sP0(u1_orders_2(sK2),X3) ) ),
    inference(resolution,[],[f80,f54])).

fof(f54,plain,(
    ! [X0,X1] :
      ( r2_hidden(k4_tarski(sK6(X0,X1),sK5(X0,X1)),X0)
      | sP0(X0,X1) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f150,plain,(
    ! [X2] :
      ( ~ r2_hidden(sK6(u1_orders_2(sK2),X2),u1_struct_0(sK2))
      | ~ r2_hidden(sK5(u1_orders_2(sK2),X2),u1_struct_0(sK2))
      | sP0(u1_orders_2(sK2),X2) ) ),
    inference(subsumption_resolution,[],[f149,f54])).

fof(f149,plain,(
    ! [X2] :
      ( ~ r2_hidden(sK6(u1_orders_2(sK2),X2),u1_struct_0(sK2))
      | ~ r2_hidden(k4_tarski(sK6(u1_orders_2(sK2),X2),sK5(u1_orders_2(sK2),X2)),u1_orders_2(sK2))
      | ~ r2_hidden(sK5(u1_orders_2(sK2),X2),u1_struct_0(sK2))
      | sP0(u1_orders_2(sK2),X2) ) ),
    inference(subsumption_resolution,[],[f146,f55])).

fof(f55,plain,(
    ! [X0,X1] :
      ( sK5(X0,X1) != sK6(X0,X1)
      | sP0(X0,X1) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f146,plain,(
    ! [X2] :
      ( sK5(u1_orders_2(sK2),X2) = sK6(u1_orders_2(sK2),X2)
      | ~ r2_hidden(sK6(u1_orders_2(sK2),X2),u1_struct_0(sK2))
      | ~ r2_hidden(k4_tarski(sK6(u1_orders_2(sK2),X2),sK5(u1_orders_2(sK2),X2)),u1_orders_2(sK2))
      | ~ r2_hidden(sK5(u1_orders_2(sK2),X2),u1_struct_0(sK2))
      | sP0(u1_orders_2(sK2),X2) ) ),
    inference(resolution,[],[f144,f53])).

fof(f144,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),u1_orders_2(sK2))
      | X0 = X1
      | ~ r2_hidden(X1,u1_struct_0(sK2))
      | ~ r2_hidden(k4_tarski(X1,X0),u1_orders_2(sK2))
      | ~ r2_hidden(X0,u1_struct_0(sK2)) ) ),
    inference(subsumption_resolution,[],[f143,f42])).

fof(f143,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,u1_struct_0(sK2))
      | X0 = X1
      | ~ r2_hidden(X1,u1_struct_0(sK2))
      | ~ r2_hidden(k4_tarski(X1,X0),u1_orders_2(sK2))
      | ~ r2_hidden(k4_tarski(X0,X1),u1_orders_2(sK2))
      | ~ l1_orders_2(sK2) ) ),
    inference(subsumption_resolution,[],[f142,f41])).

fof(f41,plain,(
    v5_orders_2(sK2) ),
    inference(cnf_transformation,[],[f31])).

fof(f142,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,u1_struct_0(sK2))
      | X0 = X1
      | ~ r2_hidden(X1,u1_struct_0(sK2))
      | ~ r2_hidden(k4_tarski(X1,X0),u1_orders_2(sK2))
      | ~ r2_hidden(k4_tarski(X0,X1),u1_orders_2(sK2))
      | ~ v5_orders_2(sK2)
      | ~ l1_orders_2(sK2) ) ),
    inference(resolution,[],[f135,f58])).

fof(f58,plain,(
    ! [X0] :
      ( r4_relat_2(u1_orders_2(X0),u1_struct_0(X0))
      | ~ v5_orders_2(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0] :
      ( ( ( v5_orders_2(X0)
          | ~ r4_relat_2(u1_orders_2(X0),u1_struct_0(X0)) )
        & ( r4_relat_2(u1_orders_2(X0),u1_struct_0(X0))
          | ~ v5_orders_2(X0) ) )
      | ~ l1_orders_2(X0) ) ),
    inference(nnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ( v5_orders_2(X0)
      <=> r4_relat_2(u1_orders_2(X0),u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ( v5_orders_2(X0)
      <=> r4_relat_2(u1_orders_2(X0),u1_struct_0(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d6_orders_2)).

fof(f135,plain,(
    ! [X2,X0,X1] :
      ( ~ r4_relat_2(u1_orders_2(sK2),X1)
      | ~ r2_hidden(X2,X1)
      | X0 = X2
      | ~ r2_hidden(X0,X1)
      | ~ r2_hidden(k4_tarski(X0,X2),u1_orders_2(sK2))
      | ~ r2_hidden(k4_tarski(X2,X0),u1_orders_2(sK2)) ) ),
    inference(resolution,[],[f96,f72])).

fof(f72,plain,(
    v1_relat_1(u1_orders_2(sK2)) ),
    inference(resolution,[],[f71,f63])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f96,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_relat_1(X2)
      | ~ r2_hidden(X1,X3)
      | ~ r2_hidden(X0,X3)
      | X0 = X1
      | ~ r4_relat_2(X2,X3)
      | ~ r2_hidden(k4_tarski(X1,X0),X2)
      | ~ r2_hidden(k4_tarski(X0,X1),X2) ) ),
    inference(resolution,[],[f91,f56])).

fof(f56,plain,(
    ! [X0] :
      ( sP1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( sP1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(definition_folding,[],[f15,f26,f25])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r4_relat_2(X0,X1)
        <=> sP0(X0,X1) )
      | ~ sP1(X0) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r4_relat_2(X0,X1)
        <=> ! [X2,X3] :
              ( X2 = X3
              | ~ r2_hidden(k4_tarski(X3,X2),X0)
              | ~ r2_hidden(k4_tarski(X2,X3),X0)
              | ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X2,X1) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r4_relat_2(X0,X1)
        <=> ! [X2,X3] :
              ( X2 = X3
              | ~ r2_hidden(k4_tarski(X3,X2),X0)
              | ~ r2_hidden(k4_tarski(X2,X3),X0)
              | ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X2,X1) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( r4_relat_2(X0,X1)
        <=> ! [X2,X3] :
              ( ( r2_hidden(k4_tarski(X3,X2),X0)
                & r2_hidden(k4_tarski(X2,X3),X0)
                & r2_hidden(X3,X1)
                & r2_hidden(X2,X1) )
             => X2 = X3 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_relat_2)).

fof(f91,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ sP1(X2)
      | ~ r2_hidden(k4_tarski(X1,X0),X2)
      | ~ r2_hidden(X0,X3)
      | ~ r2_hidden(X1,X3)
      | X0 = X1
      | ~ r4_relat_2(X2,X3)
      | ~ r2_hidden(k4_tarski(X0,X1),X2) ) ),
    inference(resolution,[],[f50,f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( sP0(X0,X1)
      | ~ r4_relat_2(X0,X1)
      | ~ sP1(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r4_relat_2(X0,X1)
            | ~ sP0(X0,X1) )
          & ( sP0(X0,X1)
            | ~ r4_relat_2(X0,X1) ) )
      | ~ sP1(X0) ) ),
    inference(nnf_transformation,[],[f26])).

%------------------------------------------------------------------------------
