%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : waybel_0__t21_waybel_0.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:39:45 EDT 2019

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   82 ( 319 expanded)
%              Number of leaves         :   13 ( 110 expanded)
%              Depth                    :   18
%              Number of atoms          :  319 (1859 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   13 (   6 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f4786,plain,(
    $false ),
    inference(subsumption_resolution,[],[f4785,f1856])).

fof(f1856,plain,(
    r1_orders_2(sK0,sK3(k5_waybel_0(sK0,sK1),k5_waybel_0(sK0,sK2)),sK1) ),
    inference(resolution,[],[f276,f803])).

fof(f803,plain,(
    ! [X3] :
      ( ~ m1_subset_1(X3,k5_waybel_0(sK0,sK1))
      | r1_orders_2(sK0,X3,sK1) ) ),
    inference(subsumption_resolution,[],[f802,f428])).

fof(f428,plain,(
    ! [X1] :
      ( ~ m1_subset_1(X1,k5_waybel_0(sK0,sK1))
      | m1_subset_1(X1,u1_struct_0(sK0)) ) ),
    inference(subsumption_resolution,[],[f424,f275])).

fof(f275,plain,(
    ~ v1_xboole_0(k5_waybel_0(sK0,sK1)) ),
    inference(resolution,[],[f174,f81])).

fof(f81,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f28])).

fof(f28,axiom,(
    ! [X0,X1] :
      ~ ( v1_xboole_0(X1)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/waybel_0__t21_waybel_0.p',t7_boole)).

fof(f174,plain,(
    r2_hidden(sK3(k5_waybel_0(sK0,sK1),k5_waybel_0(sK0,sK2)),k5_waybel_0(sK0,sK1)) ),
    inference(resolution,[],[f67,f71])).

fof(f71,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK3(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f55,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK3(X0,X1),X1)
          & r2_hidden(sK3(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f53,f54])).

fof(f54,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK3(X0,X1),X1)
        & r2_hidden(sK3(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f53,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/waybel_0__t21_waybel_0.p',d3_tarski)).

fof(f67,plain,(
    ~ r1_tarski(k5_waybel_0(sK0,sK1),k5_waybel_0(sK0,sK2)) ),
    inference(cnf_transformation,[],[f50])).

fof(f50,plain,
    ( ~ r1_tarski(k5_waybel_0(sK0,sK1),k5_waybel_0(sK0,sK2))
    & r1_orders_2(sK0,sK1,sK2)
    & m1_subset_1(sK2,u1_struct_0(sK0))
    & m1_subset_1(sK1,u1_struct_0(sK0))
    & l1_orders_2(sK0)
    & v4_orders_2(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f31,f49,f48,f47])).

fof(f47,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ~ r1_tarski(k5_waybel_0(X0,X1),k5_waybel_0(X0,X2))
                & r1_orders_2(X0,X1,X2)
                & m1_subset_1(X2,u1_struct_0(X0)) )
            & m1_subset_1(X1,u1_struct_0(X0)) )
        & l1_orders_2(X0)
        & v4_orders_2(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ~ r1_tarski(k5_waybel_0(sK0,X1),k5_waybel_0(sK0,X2))
              & r1_orders_2(sK0,X1,X2)
              & m1_subset_1(X2,u1_struct_0(sK0)) )
          & m1_subset_1(X1,u1_struct_0(sK0)) )
      & l1_orders_2(sK0)
      & v4_orders_2(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f48,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ r1_tarski(k5_waybel_0(X0,X1),k5_waybel_0(X0,X2))
              & r1_orders_2(X0,X1,X2)
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
     => ( ? [X2] :
            ( ~ r1_tarski(k5_waybel_0(X0,sK1),k5_waybel_0(X0,X2))
            & r1_orders_2(X0,sK1,X2)
            & m1_subset_1(X2,u1_struct_0(X0)) )
        & m1_subset_1(sK1,u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f49,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ~ r1_tarski(k5_waybel_0(X0,X1),k5_waybel_0(X0,X2))
          & r1_orders_2(X0,X1,X2)
          & m1_subset_1(X2,u1_struct_0(X0)) )
     => ( ~ r1_tarski(k5_waybel_0(X0,X1),k5_waybel_0(X0,sK2))
        & r1_orders_2(X0,X1,sK2)
        & m1_subset_1(sK2,u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ r1_tarski(k5_waybel_0(X0,X1),k5_waybel_0(X0,X2))
              & r1_orders_2(X0,X1,X2)
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_orders_2(X0)
      & v4_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ r1_tarski(k5_waybel_0(X0,X1),k5_waybel_0(X0,X2))
              & r1_orders_2(X0,X1,X2)
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_orders_2(X0)
      & v4_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_orders_2(X0)
          & v4_orders_2(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => ( r1_orders_2(X0,X1,X2)
                 => r1_tarski(k5_waybel_0(X0,X1),k5_waybel_0(X0,X2)) ) ) ) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v4_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( r1_orders_2(X0,X1,X2)
               => r1_tarski(k5_waybel_0(X0,X1),k5_waybel_0(X0,X2)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/waybel_0__t21_waybel_0.p',t21_waybel_0)).

fof(f424,plain,(
    ! [X1] :
      ( m1_subset_1(X1,u1_struct_0(sK0))
      | v1_xboole_0(k5_waybel_0(sK0,sK1))
      | ~ m1_subset_1(X1,k5_waybel_0(sK0,sK1)) ) ),
    inference(resolution,[],[f179,f82])).

fof(f82,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f23,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/waybel_0__t21_waybel_0.p',t2_subset)).

fof(f179,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k5_waybel_0(sK0,sK1))
      | m1_subset_1(X0,u1_struct_0(sK0)) ) ),
    inference(resolution,[],[f107,f80])).

fof(f80,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f40])).

fof(f40,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f25])).

fof(f25,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/waybel_0__t21_waybel_0.p',t4_subset)).

fof(f107,plain,(
    m1_subset_1(k5_waybel_0(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(subsumption_resolution,[],[f106,f61])).

fof(f61,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f50])).

fof(f106,plain,
    ( m1_subset_1(k5_waybel_0(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f97,f63])).

fof(f63,plain,(
    l1_orders_2(sK0) ),
    inference(cnf_transformation,[],[f50])).

fof(f97,plain,
    ( m1_subset_1(k5_waybel_0(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_orders_2(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f64,f73])).

fof(f73,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k5_waybel_0(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k5_waybel_0(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k5_waybel_0(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,u1_struct_0(X0))
        & l1_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => m1_subset_1(k5_waybel_0(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox/benchmark/waybel_0__t21_waybel_0.p',dt_k5_waybel_0)).

fof(f64,plain,(
    m1_subset_1(sK1,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f50])).

fof(f802,plain,(
    ! [X3] :
      ( ~ m1_subset_1(X3,k5_waybel_0(sK0,sK1))
      | r1_orders_2(sK0,X3,sK1)
      | ~ m1_subset_1(X3,u1_struct_0(sK0)) ) ),
    inference(subsumption_resolution,[],[f801,f61])).

fof(f801,plain,(
    ! [X3] :
      ( ~ m1_subset_1(X3,k5_waybel_0(sK0,sK1))
      | r1_orders_2(sK0,X3,sK1)
      | ~ m1_subset_1(X3,u1_struct_0(sK0))
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f800,f63])).

fof(f800,plain,(
    ! [X3] :
      ( ~ m1_subset_1(X3,k5_waybel_0(sK0,sK1))
      | r1_orders_2(sK0,X3,sK1)
      | ~ m1_subset_1(X3,u1_struct_0(sK0))
      | ~ l1_orders_2(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f780,f64])).

fof(f780,plain,(
    ! [X3] :
      ( ~ m1_subset_1(X3,k5_waybel_0(sK0,sK1))
      | r1_orders_2(sK0,X3,sK1)
      | ~ m1_subset_1(X3,u1_struct_0(sK0))
      | ~ m1_subset_1(sK1,u1_struct_0(sK0))
      | ~ l1_orders_2(sK0)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f282,f74])).

fof(f74,plain,(
    ! [X2,X0,X1] :
      ( r1_orders_2(X0,X2,X1)
      | ~ r2_hidden(X2,k5_waybel_0(X0,X1))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f56])).

fof(f56,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( r2_hidden(X2,k5_waybel_0(X0,X1))
                  | ~ r1_orders_2(X0,X2,X1) )
                & ( r1_orders_2(X0,X2,X1)
                  | ~ r2_hidden(X2,k5_waybel_0(X0,X1)) ) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r2_hidden(X2,k5_waybel_0(X0,X1))
              <=> r1_orders_2(X0,X2,X1) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f35])).

fof(f35,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r2_hidden(X2,k5_waybel_0(X0,X1))
              <=> r1_orders_2(X0,X2,X1) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( r2_hidden(X2,k5_waybel_0(X0,X1))
              <=> r1_orders_2(X0,X2,X1) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/waybel_0__t21_waybel_0.p',t17_waybel_0)).

fof(f282,plain,(
    ! [X0] :
      ( r2_hidden(X0,k5_waybel_0(sK0,sK1))
      | ~ m1_subset_1(X0,k5_waybel_0(sK0,sK1)) ) ),
    inference(resolution,[],[f275,f82])).

fof(f276,plain,(
    m1_subset_1(sK3(k5_waybel_0(sK0,sK1),k5_waybel_0(sK0,sK2)),k5_waybel_0(sK0,sK1)) ),
    inference(resolution,[],[f174,f83])).

fof(f83,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/waybel_0__t21_waybel_0.p',t1_subset)).

fof(f4785,plain,(
    ~ r1_orders_2(sK0,sK3(k5_waybel_0(sK0,sK1),k5_waybel_0(sK0,sK2)),sK1) ),
    inference(subsumption_resolution,[],[f4732,f426])).

fof(f426,plain,(
    m1_subset_1(sK3(k5_waybel_0(sK0,sK1),k5_waybel_0(sK0,sK2)),u1_struct_0(sK0)) ),
    inference(resolution,[],[f179,f174])).

fof(f4732,plain,
    ( ~ m1_subset_1(sK3(k5_waybel_0(sK0,sK1),k5_waybel_0(sK0,sK2)),u1_struct_0(sK0))
    | ~ r1_orders_2(sK0,sK3(k5_waybel_0(sK0,sK1),k5_waybel_0(sK0,sK2)),sK1) ),
    inference(resolution,[],[f457,f175])).

fof(f175,plain,(
    ~ r2_hidden(sK3(k5_waybel_0(sK0,sK1),k5_waybel_0(sK0,sK2)),k5_waybel_0(sK0,sK2)) ),
    inference(resolution,[],[f67,f72])).

fof(f72,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r2_hidden(sK3(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f457,plain,(
    ! [X4] :
      ( r2_hidden(X4,k5_waybel_0(sK0,sK2))
      | ~ m1_subset_1(X4,u1_struct_0(sK0))
      | ~ r1_orders_2(sK0,X4,sK1) ) ),
    inference(subsumption_resolution,[],[f456,f61])).

fof(f456,plain,(
    ! [X4] :
      ( ~ r1_orders_2(sK0,X4,sK1)
      | ~ m1_subset_1(X4,u1_struct_0(sK0))
      | r2_hidden(X4,k5_waybel_0(sK0,sK2))
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f455,f63])).

fof(f455,plain,(
    ! [X4] :
      ( ~ r1_orders_2(sK0,X4,sK1)
      | ~ m1_subset_1(X4,u1_struct_0(sK0))
      | r2_hidden(X4,k5_waybel_0(sK0,sK2))
      | ~ l1_orders_2(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f445,f65])).

fof(f65,plain,(
    m1_subset_1(sK2,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f50])).

fof(f445,plain,(
    ! [X4] :
      ( ~ r1_orders_2(sK0,X4,sK1)
      | ~ m1_subset_1(X4,u1_struct_0(sK0))
      | r2_hidden(X4,k5_waybel_0(sK0,sK2))
      | ~ m1_subset_1(sK2,u1_struct_0(sK0))
      | ~ l1_orders_2(sK0)
      | v2_struct_0(sK0) ) ),
    inference(duplicate_literal_removal,[],[f444])).

fof(f444,plain,(
    ! [X4] :
      ( ~ r1_orders_2(sK0,X4,sK1)
      | ~ m1_subset_1(X4,u1_struct_0(sK0))
      | r2_hidden(X4,k5_waybel_0(sK0,sK2))
      | ~ m1_subset_1(X4,u1_struct_0(sK0))
      | ~ m1_subset_1(sK2,u1_struct_0(sK0))
      | ~ l1_orders_2(sK0)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f157,f75])).

fof(f75,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X2,k5_waybel_0(X0,X1))
      | ~ r1_orders_2(X0,X2,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f56])).

fof(f157,plain,(
    ! [X1] :
      ( r1_orders_2(sK0,X1,sK2)
      | ~ r1_orders_2(sK0,X1,sK1)
      | ~ m1_subset_1(X1,u1_struct_0(sK0)) ) ),
    inference(subsumption_resolution,[],[f156,f62])).

fof(f62,plain,(
    v4_orders_2(sK0) ),
    inference(cnf_transformation,[],[f50])).

fof(f156,plain,(
    ! [X1] :
      ( r1_orders_2(sK0,X1,sK2)
      | ~ r1_orders_2(sK0,X1,sK1)
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ v4_orders_2(sK0) ) ),
    inference(subsumption_resolution,[],[f155,f63])).

fof(f155,plain,(
    ! [X1] :
      ( r1_orders_2(sK0,X1,sK2)
      | ~ r1_orders_2(sK0,X1,sK1)
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ l1_orders_2(sK0)
      | ~ v4_orders_2(sK0) ) ),
    inference(subsumption_resolution,[],[f154,f64])).

fof(f154,plain,(
    ! [X1] :
      ( r1_orders_2(sK0,X1,sK2)
      | ~ r1_orders_2(sK0,X1,sK1)
      | ~ m1_subset_1(sK1,u1_struct_0(sK0))
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ l1_orders_2(sK0)
      | ~ v4_orders_2(sK0) ) ),
    inference(subsumption_resolution,[],[f148,f65])).

fof(f148,plain,(
    ! [X1] :
      ( r1_orders_2(sK0,X1,sK2)
      | ~ r1_orders_2(sK0,X1,sK1)
      | ~ m1_subset_1(sK2,u1_struct_0(sK0))
      | ~ m1_subset_1(sK1,u1_struct_0(sK0))
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ l1_orders_2(sK0)
      | ~ v4_orders_2(sK0) ) ),
    inference(resolution,[],[f66,f78])).

fof(f78,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_orders_2(X0,X1,X3)
      | ~ r1_orders_2(X0,X2,X3)
      | ~ r1_orders_2(X0,X1,X2)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v4_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( r1_orders_2(X0,X1,X3)
                  | ~ r1_orders_2(X0,X2,X3)
                  | ~ r1_orders_2(X0,X1,X2)
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v4_orders_2(X0) ) ),
    inference(flattening,[],[f37])).

fof(f37,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( r1_orders_2(X0,X1,X3)
                  | ~ r1_orders_2(X0,X2,X3)
                  | ~ r1_orders_2(X0,X1,X2)
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v4_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v4_orders_2(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ! [X3] :
                  ( m1_subset_1(X3,u1_struct_0(X0))
                 => ( ( r1_orders_2(X0,X2,X3)
                      & r1_orders_2(X0,X1,X2) )
                   => r1_orders_2(X0,X1,X3) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/waybel_0__t21_waybel_0.p',t26_orders_2)).

fof(f66,plain,(
    r1_orders_2(sK0,sK1,sK2) ),
    inference(cnf_transformation,[],[f50])).
%------------------------------------------------------------------------------
