%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : yellow_0__t36_yellow_0.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:41:41 EDT 2019

% Result     : Theorem 163.98s
% Output     : Refutation 163.98s
% Verified   : 
% Statistics : Number of formulae       :  212 (6414 expanded)
%              Number of leaves         :   15 (1956 expanded)
%              Depth                    :   48
%              Number of atoms          : 1145 (43874 expanded)
%              Number of equality atoms :   82 (5699 expanded)
%              Maximal formula depth    :   17 (   7 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f126197,plain,(
    $false ),
    inference(subsumption_resolution,[],[f126196,f24165])).

fof(f24165,plain,(
    m1_subset_1(sK3(sK0,k1_yellow_0(sK0,sK1),k1_yellow_0(sK0,sK2),k1_yellow_0(sK0,k2_xboole_0(sK1,sK2))),u1_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f24164,f173])).

fof(f173,plain,(
    ! [X26] : m1_subset_1(k1_yellow_0(sK0,X26),u1_struct_0(sK0)) ),
    inference(resolution,[],[f73,f93])).

fof(f93,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( l1_orders_2(X0)
     => m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/yellow_0__t36_yellow_0.p',dt_k1_yellow_0)).

fof(f73,plain,(
    l1_orders_2(sK0) ),
    inference(cnf_transformation,[],[f61])).

fof(f61,plain,
    ( k1_yellow_0(sK0,k2_xboole_0(sK1,sK2)) != k10_lattice3(sK0,k1_yellow_0(sK0,sK1),k1_yellow_0(sK0,sK2))
    & r1_yellow_0(sK0,k2_xboole_0(sK1,sK2))
    & r1_yellow_0(sK0,sK2)
    & r1_yellow_0(sK0,sK1)
    & l1_orders_2(sK0)
    & v5_orders_2(sK0)
    & v4_orders_2(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f39,f60,f59])).

fof(f59,plain,
    ( ? [X0] :
        ( ? [X1,X2] :
            ( k1_yellow_0(X0,k2_xboole_0(X1,X2)) != k10_lattice3(X0,k1_yellow_0(X0,X1),k1_yellow_0(X0,X2))
            & r1_yellow_0(X0,k2_xboole_0(X1,X2))
            & r1_yellow_0(X0,X2)
            & r1_yellow_0(X0,X1) )
        & l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0) )
   => ( ? [X2,X1] :
          ( k1_yellow_0(sK0,k2_xboole_0(X1,X2)) != k10_lattice3(sK0,k1_yellow_0(sK0,X1),k1_yellow_0(sK0,X2))
          & r1_yellow_0(sK0,k2_xboole_0(X1,X2))
          & r1_yellow_0(sK0,X2)
          & r1_yellow_0(sK0,X1) )
      & l1_orders_2(sK0)
      & v5_orders_2(sK0)
      & v4_orders_2(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f60,plain,(
    ! [X0] :
      ( ? [X1,X2] :
          ( k1_yellow_0(X0,k2_xboole_0(X1,X2)) != k10_lattice3(X0,k1_yellow_0(X0,X1),k1_yellow_0(X0,X2))
          & r1_yellow_0(X0,k2_xboole_0(X1,X2))
          & r1_yellow_0(X0,X2)
          & r1_yellow_0(X0,X1) )
     => ( k1_yellow_0(X0,k2_xboole_0(sK1,sK2)) != k10_lattice3(X0,k1_yellow_0(X0,sK1),k1_yellow_0(X0,sK2))
        & r1_yellow_0(X0,k2_xboole_0(sK1,sK2))
        & r1_yellow_0(X0,sK2)
        & r1_yellow_0(X0,sK1) ) ) ),
    introduced(choice_axiom,[])).

fof(f39,plain,(
    ? [X0] :
      ( ? [X1,X2] :
          ( k1_yellow_0(X0,k2_xboole_0(X1,X2)) != k10_lattice3(X0,k1_yellow_0(X0,X1),k1_yellow_0(X0,X2))
          & r1_yellow_0(X0,k2_xboole_0(X1,X2))
          & r1_yellow_0(X0,X2)
          & r1_yellow_0(X0,X1) )
      & l1_orders_2(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0) ) ),
    inference(flattening,[],[f38])).

fof(f38,plain,(
    ? [X0] :
      ( ? [X1,X2] :
          ( k1_yellow_0(X0,k2_xboole_0(X1,X2)) != k10_lattice3(X0,k1_yellow_0(X0,X1),k1_yellow_0(X0,X2))
          & r1_yellow_0(X0,k2_xboole_0(X1,X2))
          & r1_yellow_0(X0,X2)
          & r1_yellow_0(X0,X1) )
      & l1_orders_2(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_orders_2(X0)
          & v5_orders_2(X0)
          & v4_orders_2(X0) )
       => ! [X1,X2] :
            ( ( r1_yellow_0(X0,k2_xboole_0(X1,X2))
              & r1_yellow_0(X0,X2)
              & r1_yellow_0(X0,X1) )
           => k1_yellow_0(X0,k2_xboole_0(X1,X2)) = k10_lattice3(X0,k1_yellow_0(X0,X1),k1_yellow_0(X0,X2)) ) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0) )
     => ! [X1,X2] :
          ( ( r1_yellow_0(X0,k2_xboole_0(X1,X2))
            & r1_yellow_0(X0,X2)
            & r1_yellow_0(X0,X1) )
         => k1_yellow_0(X0,k2_xboole_0(X1,X2)) = k10_lattice3(X0,k1_yellow_0(X0,X1),k1_yellow_0(X0,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/yellow_0__t36_yellow_0.p',t36_yellow_0)).

fof(f24164,plain,
    ( m1_subset_1(sK3(sK0,k1_yellow_0(sK0,sK1),k1_yellow_0(sK0,sK2),k1_yellow_0(sK0,k2_xboole_0(sK1,sK2))),u1_struct_0(sK0))
    | ~ m1_subset_1(k1_yellow_0(sK0,k2_xboole_0(sK1,sK2)),u1_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f24157,f2086])).

fof(f2086,plain,(
    r1_orders_2(sK0,k1_yellow_0(sK0,sK1),k1_yellow_0(sK0,k2_xboole_0(sK1,sK2))) ),
    inference(subsumption_resolution,[],[f2070,f173])).

fof(f2070,plain,
    ( r1_orders_2(sK0,k1_yellow_0(sK0,sK1),k1_yellow_0(sK0,k2_xboole_0(sK1,sK2)))
    | ~ m1_subset_1(k1_yellow_0(sK0,k2_xboole_0(sK1,sK2)),u1_struct_0(sK0)) ),
    inference(resolution,[],[f2048,f201])).

fof(f201,plain,(
    ! [X2] :
      ( ~ r2_lattice3(sK0,sK1,X2)
      | r1_orders_2(sK0,k1_yellow_0(sK0,sK1),X2)
      | ~ m1_subset_1(X2,u1_struct_0(sK0)) ) ),
    inference(subsumption_resolution,[],[f200,f72])).

fof(f72,plain,(
    v5_orders_2(sK0) ),
    inference(cnf_transformation,[],[f61])).

fof(f200,plain,(
    ! [X2] :
      ( r1_orders_2(sK0,k1_yellow_0(sK0,sK1),X2)
      | ~ r2_lattice3(sK0,sK1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(sK0))
      | ~ v5_orders_2(sK0) ) ),
    inference(subsumption_resolution,[],[f199,f73])).

fof(f199,plain,(
    ! [X2] :
      ( r1_orders_2(sK0,k1_yellow_0(sK0,sK1),X2)
      | ~ r2_lattice3(sK0,sK1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(sK0))
      | ~ l1_orders_2(sK0)
      | ~ v5_orders_2(sK0) ) ),
    inference(subsumption_resolution,[],[f193,f173])).

fof(f193,plain,(
    ! [X2] :
      ( r1_orders_2(sK0,k1_yellow_0(sK0,sK1),X2)
      | ~ r2_lattice3(sK0,sK1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(sK0))
      | ~ m1_subset_1(k1_yellow_0(sK0,sK1),u1_struct_0(sK0))
      | ~ l1_orders_2(sK0)
      | ~ v5_orders_2(sK0) ) ),
    inference(resolution,[],[f74,f120])).

fof(f120,plain,(
    ! [X4,X2,X0] :
      ( r1_orders_2(X0,k1_yellow_0(X0,X2),X4)
      | ~ r2_lattice3(X0,X2,X4)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ r1_yellow_0(X0,X2)
      | ~ m1_subset_1(k1_yellow_0(X0,X2),u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(equality_resolution,[],[f95])).

fof(f95,plain,(
    ! [X4,X2,X0,X1] :
      ( r1_orders_2(X0,X1,X4)
      | ~ r2_lattice3(X0,X2,X4)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ r1_yellow_0(X0,X2)
      | k1_yellow_0(X0,X2) != X1
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f65])).

fof(f65,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( r1_yellow_0(X0,X2)
                  & k1_yellow_0(X0,X2) = X1 )
                | ( ~ r1_orders_2(X0,X1,sK4(X0,X1,X2))
                  & r2_lattice3(X0,X2,sK4(X0,X1,X2))
                  & m1_subset_1(sK4(X0,X1,X2),u1_struct_0(X0)) )
                | ~ r2_lattice3(X0,X2,X1) )
              & ( ( ! [X4] :
                      ( r1_orders_2(X0,X1,X4)
                      | ~ r2_lattice3(X0,X2,X4)
                      | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                  & r2_lattice3(X0,X2,X1) )
                | ~ r1_yellow_0(X0,X2)
                | k1_yellow_0(X0,X2) != X1 ) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f47,f64])).

fof(f64,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r1_orders_2(X0,X1,X3)
          & r2_lattice3(X0,X2,X3)
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ~ r1_orders_2(X0,X1,sK4(X0,X1,X2))
        & r2_lattice3(X0,X2,sK4(X0,X1,X2))
        & m1_subset_1(sK4(X0,X1,X2),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f47,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( r1_yellow_0(X0,X2)
                  & k1_yellow_0(X0,X2) = X1 )
                | ? [X3] :
                    ( ~ r1_orders_2(X0,X1,X3)
                    & r2_lattice3(X0,X2,X3)
                    & m1_subset_1(X3,u1_struct_0(X0)) )
                | ~ r2_lattice3(X0,X2,X1) )
              & ( ( ! [X4] :
                      ( r1_orders_2(X0,X1,X4)
                      | ~ r2_lattice3(X0,X2,X4)
                      | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                  & r2_lattice3(X0,X2,X1) )
                | ~ r1_yellow_0(X0,X2)
                | k1_yellow_0(X0,X2) != X1 ) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(flattening,[],[f46])).

fof(f46,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( r1_yellow_0(X0,X2)
                  & k1_yellow_0(X0,X2) = X1 )
                | ? [X3] :
                    ( ~ r1_orders_2(X0,X1,X3)
                    & r2_lattice3(X0,X2,X3)
                    & m1_subset_1(X3,u1_struct_0(X0)) )
                | ~ r2_lattice3(X0,X2,X1) )
              & ( ( ! [X4] :
                      ( r1_orders_2(X0,X1,X4)
                      | ~ r2_lattice3(X0,X2,X4)
                      | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                  & r2_lattice3(X0,X2,X1) )
                | ~ r1_yellow_0(X0,X2)
                | k1_yellow_0(X0,X2) != X1 ) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( ( ( ! [X3] :
                      ( m1_subset_1(X3,u1_struct_0(X0))
                     => ( r2_lattice3(X0,X2,X3)
                       => r1_orders_2(X0,X1,X3) ) )
                  & r2_lattice3(X0,X2,X1) )
               => ( r1_yellow_0(X0,X2)
                  & k1_yellow_0(X0,X2) = X1 ) )
              & ( ( r1_yellow_0(X0,X2)
                  & k1_yellow_0(X0,X2) = X1 )
               => ( ! [X4] :
                      ( m1_subset_1(X4,u1_struct_0(X0))
                     => ( r2_lattice3(X0,X2,X4)
                       => r1_orders_2(X0,X1,X4) ) )
                  & r2_lattice3(X0,X2,X1) ) ) ) ) ) ),
    inference(rectify,[],[f25])).

fof(f25,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( ( ( ! [X3] :
                      ( m1_subset_1(X3,u1_struct_0(X0))
                     => ( r2_lattice3(X0,X2,X3)
                       => r1_orders_2(X0,X1,X3) ) )
                  & r2_lattice3(X0,X2,X1) )
               => ( r1_yellow_0(X0,X2)
                  & k1_yellow_0(X0,X2) = X1 ) )
              & ( ( r1_yellow_0(X0,X2)
                  & k1_yellow_0(X0,X2) = X1 )
               => ( ! [X3] :
                      ( m1_subset_1(X3,u1_struct_0(X0))
                     => ( r2_lattice3(X0,X2,X3)
                       => r1_orders_2(X0,X1,X3) ) )
                  & r2_lattice3(X0,X2,X1) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/yellow_0__t36_yellow_0.p',t30_yellow_0)).

fof(f74,plain,(
    r1_yellow_0(sK0,sK1) ),
    inference(cnf_transformation,[],[f61])).

fof(f2048,plain,(
    r2_lattice3(sK0,sK1,k1_yellow_0(sK0,k2_xboole_0(sK1,sK2))) ),
    inference(resolution,[],[f2046,f76])).

fof(f76,plain,(
    r1_yellow_0(sK0,k2_xboole_0(sK1,sK2)) ),
    inference(cnf_transformation,[],[f61])).

fof(f2046,plain,(
    ! [X0] :
      ( ~ r1_yellow_0(sK0,k2_xboole_0(sK1,X0))
      | r2_lattice3(sK0,sK1,k1_yellow_0(sK0,k2_xboole_0(sK1,X0))) ) ),
    inference(resolution,[],[f2021,f103])).

fof(f103,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/yellow_0__t36_yellow_0.p',t7_xboole_1)).

fof(f2021,plain,(
    ! [X1] :
      ( ~ r1_tarski(sK1,X1)
      | ~ r1_yellow_0(sK0,X1)
      | r2_lattice3(sK0,sK1,k1_yellow_0(sK0,X1)) ) ),
    inference(subsumption_resolution,[],[f2020,f73])).

fof(f2020,plain,(
    ! [X1] :
      ( r2_lattice3(sK0,sK1,k1_yellow_0(sK0,X1))
      | ~ r1_yellow_0(sK0,X1)
      | ~ r1_tarski(sK1,X1)
      | ~ l1_orders_2(sK0) ) ),
    inference(subsumption_resolution,[],[f2019,f74])).

fof(f2019,plain,(
    ! [X1] :
      ( r2_lattice3(sK0,sK1,k1_yellow_0(sK0,X1))
      | ~ r1_yellow_0(sK0,X1)
      | ~ r1_yellow_0(sK0,sK1)
      | ~ r1_tarski(sK1,X1)
      | ~ l1_orders_2(sK0) ) ),
    inference(subsumption_resolution,[],[f2006,f173])).

fof(f2006,plain,(
    ! [X1] :
      ( r2_lattice3(sK0,sK1,k1_yellow_0(sK0,X1))
      | ~ m1_subset_1(k1_yellow_0(sK0,X1),u1_struct_0(sK0))
      | ~ r1_yellow_0(sK0,X1)
      | ~ r1_yellow_0(sK0,sK1)
      | ~ r1_tarski(sK1,X1)
      | ~ l1_orders_2(sK0) ) ),
    inference(resolution,[],[f442,f102])).

fof(f102,plain,(
    ! [X2,X0,X1] :
      ( r1_orders_2(X0,k1_yellow_0(X0,X1),k1_yellow_0(X0,X2))
      | ~ r1_yellow_0(X0,X2)
      | ~ r1_yellow_0(X0,X1)
      | ~ r1_tarski(X1,X2)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f49,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( r1_orders_2(X0,k1_yellow_0(X0,X1),k1_yellow_0(X0,X2))
          | ~ r1_yellow_0(X0,X2)
          | ~ r1_yellow_0(X0,X1)
          | ~ r1_tarski(X1,X2) )
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f48])).

fof(f48,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( r1_orders_2(X0,k1_yellow_0(X0,X1),k1_yellow_0(X0,X2))
          | ~ r1_yellow_0(X0,X2)
          | ~ r1_yellow_0(X0,X1)
          | ~ r1_tarski(X1,X2) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f26])).

fof(f26,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1,X2] :
          ( ( r1_yellow_0(X0,X2)
            & r1_yellow_0(X0,X1)
            & r1_tarski(X1,X2) )
         => r1_orders_2(X0,k1_yellow_0(X0,X1),k1_yellow_0(X0,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/yellow_0__t36_yellow_0.p',t34_yellow_0)).

fof(f442,plain,(
    ! [X0] :
      ( ~ r1_orders_2(sK0,k1_yellow_0(sK0,sK1),X0)
      | r2_lattice3(sK0,sK1,X0)
      | ~ m1_subset_1(X0,u1_struct_0(sK0)) ) ),
    inference(subsumption_resolution,[],[f441,f71])).

fof(f71,plain,(
    v4_orders_2(sK0) ),
    inference(cnf_transformation,[],[f61])).

fof(f441,plain,(
    ! [X0] :
      ( r2_lattice3(sK0,sK1,X0)
      | ~ r1_orders_2(sK0,k1_yellow_0(sK0,sK1),X0)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ v4_orders_2(sK0) ) ),
    inference(subsumption_resolution,[],[f440,f73])).

fof(f440,plain,(
    ! [X0] :
      ( r2_lattice3(sK0,sK1,X0)
      | ~ r1_orders_2(sK0,k1_yellow_0(sK0,sK1),X0)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ l1_orders_2(sK0)
      | ~ v4_orders_2(sK0) ) ),
    inference(subsumption_resolution,[],[f432,f173])).

fof(f432,plain,(
    ! [X0] :
      ( r2_lattice3(sK0,sK1,X0)
      | ~ r1_orders_2(sK0,k1_yellow_0(sK0,sK1),X0)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ m1_subset_1(k1_yellow_0(sK0,sK1),u1_struct_0(sK0))
      | ~ l1_orders_2(sK0)
      | ~ v4_orders_2(sK0) ) ),
    inference(resolution,[],[f198,f106])).

fof(f106,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_lattice3(X0,X3,X2)
      | ~ r2_lattice3(X0,X3,X1)
      | ~ r1_orders_2(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v4_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f51,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( r2_lattice3(X0,X3,X2)
                    | ~ r2_lattice3(X0,X3,X1) )
                  & ( r1_lattice3(X0,X3,X1)
                    | ~ r1_lattice3(X0,X3,X2) ) )
              | ~ r1_orders_2(X0,X1,X2)
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v4_orders_2(X0) ) ),
    inference(flattening,[],[f50])).

fof(f50,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( r2_lattice3(X0,X3,X2)
                    | ~ r2_lattice3(X0,X3,X1) )
                  & ( r1_lattice3(X0,X3,X1)
                    | ~ r1_lattice3(X0,X3,X2) ) )
              | ~ r1_orders_2(X0,X1,X2)
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v4_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f29])).

fof(f29,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v4_orders_2(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( r1_orders_2(X0,X1,X2)
               => ! [X3] :
                    ( ( r2_lattice3(X0,X3,X1)
                     => r2_lattice3(X0,X3,X2) )
                    & ( r1_lattice3(X0,X3,X2)
                     => r1_lattice3(X0,X3,X1) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/yellow_0__t36_yellow_0.p',t4_yellow_0)).

fof(f198,plain,(
    r2_lattice3(sK0,sK1,k1_yellow_0(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f197,f72])).

fof(f197,plain,
    ( r2_lattice3(sK0,sK1,k1_yellow_0(sK0,sK1))
    | ~ v5_orders_2(sK0) ),
    inference(subsumption_resolution,[],[f196,f73])).

fof(f196,plain,
    ( r2_lattice3(sK0,sK1,k1_yellow_0(sK0,sK1))
    | ~ l1_orders_2(sK0)
    | ~ v5_orders_2(sK0) ),
    inference(subsumption_resolution,[],[f192,f173])).

fof(f192,plain,
    ( r2_lattice3(sK0,sK1,k1_yellow_0(sK0,sK1))
    | ~ m1_subset_1(k1_yellow_0(sK0,sK1),u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | ~ v5_orders_2(sK0) ),
    inference(resolution,[],[f74,f121])).

fof(f121,plain,(
    ! [X2,X0] :
      ( r2_lattice3(X0,X2,k1_yellow_0(X0,X2))
      | ~ r1_yellow_0(X0,X2)
      | ~ m1_subset_1(k1_yellow_0(X0,X2),u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(equality_resolution,[],[f94])).

fof(f94,plain,(
    ! [X2,X0,X1] :
      ( r2_lattice3(X0,X2,X1)
      | ~ r1_yellow_0(X0,X2)
      | k1_yellow_0(X0,X2) != X1
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f65])).

fof(f24157,plain,
    ( m1_subset_1(sK3(sK0,k1_yellow_0(sK0,sK1),k1_yellow_0(sK0,sK2),k1_yellow_0(sK0,k2_xboole_0(sK1,sK2))),u1_struct_0(sK0))
    | ~ r1_orders_2(sK0,k1_yellow_0(sK0,sK1),k1_yellow_0(sK0,k2_xboole_0(sK1,sK2)))
    | ~ m1_subset_1(k1_yellow_0(sK0,k2_xboole_0(sK1,sK2)),u1_struct_0(sK0)) ),
    inference(trivial_inequality_removal,[],[f24117])).

fof(f24117,plain,
    ( m1_subset_1(sK3(sK0,k1_yellow_0(sK0,sK1),k1_yellow_0(sK0,sK2),k1_yellow_0(sK0,k2_xboole_0(sK1,sK2))),u1_struct_0(sK0))
    | k1_yellow_0(sK0,k2_xboole_0(sK1,sK2)) != k1_yellow_0(sK0,k2_xboole_0(sK1,sK2))
    | ~ r1_orders_2(sK0,k1_yellow_0(sK0,sK1),k1_yellow_0(sK0,k2_xboole_0(sK1,sK2)))
    | ~ m1_subset_1(k1_yellow_0(sK0,k2_xboole_0(sK1,sK2)),u1_struct_0(sK0)) ),
    inference(resolution,[],[f22878,f251])).

fof(f251,plain,(
    ! [X0] :
      ( ~ r1_orders_2(sK0,k1_yellow_0(sK0,sK2),X0)
      | m1_subset_1(sK3(sK0,k1_yellow_0(sK0,sK1),k1_yellow_0(sK0,sK2),X0),u1_struct_0(sK0))
      | k1_yellow_0(sK0,k2_xboole_0(sK1,sK2)) != X0
      | ~ r1_orders_2(sK0,k1_yellow_0(sK0,sK1),X0)
      | ~ m1_subset_1(X0,u1_struct_0(sK0)) ) ),
    inference(subsumption_resolution,[],[f250,f72])).

fof(f250,plain,(
    ! [X0] :
      ( k1_yellow_0(sK0,k2_xboole_0(sK1,sK2)) != X0
      | m1_subset_1(sK3(sK0,k1_yellow_0(sK0,sK1),k1_yellow_0(sK0,sK2),X0),u1_struct_0(sK0))
      | ~ r1_orders_2(sK0,k1_yellow_0(sK0,sK2),X0)
      | ~ r1_orders_2(sK0,k1_yellow_0(sK0,sK1),X0)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ v5_orders_2(sK0) ) ),
    inference(subsumption_resolution,[],[f249,f73])).

fof(f249,plain,(
    ! [X0] :
      ( k1_yellow_0(sK0,k2_xboole_0(sK1,sK2)) != X0
      | m1_subset_1(sK3(sK0,k1_yellow_0(sK0,sK1),k1_yellow_0(sK0,sK2),X0),u1_struct_0(sK0))
      | ~ r1_orders_2(sK0,k1_yellow_0(sK0,sK2),X0)
      | ~ r1_orders_2(sK0,k1_yellow_0(sK0,sK1),X0)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ l1_orders_2(sK0)
      | ~ v5_orders_2(sK0) ) ),
    inference(subsumption_resolution,[],[f248,f173])).

fof(f248,plain,(
    ! [X0] :
      ( k1_yellow_0(sK0,k2_xboole_0(sK1,sK2)) != X0
      | m1_subset_1(sK3(sK0,k1_yellow_0(sK0,sK1),k1_yellow_0(sK0,sK2),X0),u1_struct_0(sK0))
      | ~ r1_orders_2(sK0,k1_yellow_0(sK0,sK2),X0)
      | ~ r1_orders_2(sK0,k1_yellow_0(sK0,sK1),X0)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ m1_subset_1(k1_yellow_0(sK0,sK1),u1_struct_0(sK0))
      | ~ l1_orders_2(sK0)
      | ~ v5_orders_2(sK0) ) ),
    inference(subsumption_resolution,[],[f232,f173])).

fof(f232,plain,(
    ! [X0] :
      ( k1_yellow_0(sK0,k2_xboole_0(sK1,sK2)) != X0
      | m1_subset_1(sK3(sK0,k1_yellow_0(sK0,sK1),k1_yellow_0(sK0,sK2),X0),u1_struct_0(sK0))
      | ~ r1_orders_2(sK0,k1_yellow_0(sK0,sK2),X0)
      | ~ r1_orders_2(sK0,k1_yellow_0(sK0,sK1),X0)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ m1_subset_1(k1_yellow_0(sK0,sK2),u1_struct_0(sK0))
      | ~ m1_subset_1(k1_yellow_0(sK0,sK1),u1_struct_0(sK0))
      | ~ l1_orders_2(sK0)
      | ~ v5_orders_2(sK0) ) ),
    inference(superposition,[],[f77,f85])).

fof(f85,plain,(
    ! [X2,X0,X3,X1] :
      ( k10_lattice3(X0,X1,X2) = X3
      | m1_subset_1(sK3(X0,X1,X2,X3),u1_struct_0(X0))
      | ~ r1_orders_2(X0,X2,X3)
      | ~ r1_orders_2(X0,X1,X3)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f63])).

fof(f63,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ( ( r1_yellow_0(X0,k2_tarski(X1,X2))
                        & k10_lattice3(X0,X1,X2) = X3 )
                      | ( ~ r1_orders_2(X0,X3,sK3(X0,X1,X2,X3))
                        & r1_orders_2(X0,X2,sK3(X0,X1,X2,X3))
                        & r1_orders_2(X0,X1,sK3(X0,X1,X2,X3))
                        & m1_subset_1(sK3(X0,X1,X2,X3),u1_struct_0(X0)) )
                      | ~ r1_orders_2(X0,X2,X3)
                      | ~ r1_orders_2(X0,X1,X3) )
                    & ( ( ! [X5] :
                            ( r1_orders_2(X0,X3,X5)
                            | ~ r1_orders_2(X0,X2,X5)
                            | ~ r1_orders_2(X0,X1,X5)
                            | ~ m1_subset_1(X5,u1_struct_0(X0)) )
                        & r1_orders_2(X0,X2,X3)
                        & r1_orders_2(X0,X1,X3) )
                      | ~ r1_yellow_0(X0,k2_tarski(X1,X2))
                      | k10_lattice3(X0,X1,X2) != X3 ) )
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f44,f62])).

fof(f62,plain,(
    ! [X3,X2,X1,X0] :
      ( ? [X4] :
          ( ~ r1_orders_2(X0,X3,X4)
          & r1_orders_2(X0,X2,X4)
          & r1_orders_2(X0,X1,X4)
          & m1_subset_1(X4,u1_struct_0(X0)) )
     => ( ~ r1_orders_2(X0,X3,sK3(X0,X1,X2,X3))
        & r1_orders_2(X0,X2,sK3(X0,X1,X2,X3))
        & r1_orders_2(X0,X1,sK3(X0,X1,X2,X3))
        & m1_subset_1(sK3(X0,X1,X2,X3),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f44,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ( ( r1_yellow_0(X0,k2_tarski(X1,X2))
                        & k10_lattice3(X0,X1,X2) = X3 )
                      | ? [X4] :
                          ( ~ r1_orders_2(X0,X3,X4)
                          & r1_orders_2(X0,X2,X4)
                          & r1_orders_2(X0,X1,X4)
                          & m1_subset_1(X4,u1_struct_0(X0)) )
                      | ~ r1_orders_2(X0,X2,X3)
                      | ~ r1_orders_2(X0,X1,X3) )
                    & ( ( ! [X5] :
                            ( r1_orders_2(X0,X3,X5)
                            | ~ r1_orders_2(X0,X2,X5)
                            | ~ r1_orders_2(X0,X1,X5)
                            | ~ m1_subset_1(X5,u1_struct_0(X0)) )
                        & r1_orders_2(X0,X2,X3)
                        & r1_orders_2(X0,X1,X3) )
                      | ~ r1_yellow_0(X0,k2_tarski(X1,X2))
                      | k10_lattice3(X0,X1,X2) != X3 ) )
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(flattening,[],[f43])).

fof(f43,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ( ( r1_yellow_0(X0,k2_tarski(X1,X2))
                        & k10_lattice3(X0,X1,X2) = X3 )
                      | ? [X4] :
                          ( ~ r1_orders_2(X0,X3,X4)
                          & r1_orders_2(X0,X2,X4)
                          & r1_orders_2(X0,X1,X4)
                          & m1_subset_1(X4,u1_struct_0(X0)) )
                      | ~ r1_orders_2(X0,X2,X3)
                      | ~ r1_orders_2(X0,X1,X3) )
                    & ( ( ! [X5] :
                            ( r1_orders_2(X0,X3,X5)
                            | ~ r1_orders_2(X0,X2,X5)
                            | ~ r1_orders_2(X0,X1,X5)
                            | ~ m1_subset_1(X5,u1_struct_0(X0)) )
                        & r1_orders_2(X0,X2,X3)
                        & r1_orders_2(X0,X1,X3) )
                      | ~ r1_yellow_0(X0,k2_tarski(X1,X2))
                      | k10_lattice3(X0,X1,X2) != X3 ) )
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ! [X3] :
                  ( m1_subset_1(X3,u1_struct_0(X0))
                 => ( ( ( ! [X4] :
                            ( m1_subset_1(X4,u1_struct_0(X0))
                           => ( ( r1_orders_2(X0,X2,X4)
                                & r1_orders_2(X0,X1,X4) )
                             => r1_orders_2(X0,X3,X4) ) )
                        & r1_orders_2(X0,X2,X3)
                        & r1_orders_2(X0,X1,X3) )
                     => ( r1_yellow_0(X0,k2_tarski(X1,X2))
                        & k10_lattice3(X0,X1,X2) = X3 ) )
                    & ( ( r1_yellow_0(X0,k2_tarski(X1,X2))
                        & k10_lattice3(X0,X1,X2) = X3 )
                     => ( ! [X5] :
                            ( m1_subset_1(X5,u1_struct_0(X0))
                           => ( ( r1_orders_2(X0,X2,X5)
                                & r1_orders_2(X0,X1,X5) )
                             => r1_orders_2(X0,X3,X5) ) )
                        & r1_orders_2(X0,X2,X3)
                        & r1_orders_2(X0,X1,X3) ) ) ) ) ) ) ) ),
    inference(rectify,[],[f21])).

fof(f21,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ! [X3] :
                  ( m1_subset_1(X3,u1_struct_0(X0))
                 => ( ( ( ! [X4] :
                            ( m1_subset_1(X4,u1_struct_0(X0))
                           => ( ( r1_orders_2(X0,X2,X4)
                                & r1_orders_2(X0,X1,X4) )
                             => r1_orders_2(X0,X3,X4) ) )
                        & r1_orders_2(X0,X2,X3)
                        & r1_orders_2(X0,X1,X3) )
                     => ( r1_yellow_0(X0,k2_tarski(X1,X2))
                        & k10_lattice3(X0,X1,X2) = X3 ) )
                    & ( ( r1_yellow_0(X0,k2_tarski(X1,X2))
                        & k10_lattice3(X0,X1,X2) = X3 )
                     => ( ! [X4] :
                            ( m1_subset_1(X4,u1_struct_0(X0))
                           => ( ( r1_orders_2(X0,X2,X4)
                                & r1_orders_2(X0,X1,X4) )
                             => r1_orders_2(X0,X3,X4) ) )
                        & r1_orders_2(X0,X2,X3)
                        & r1_orders_2(X0,X1,X3) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/yellow_0__t36_yellow_0.p',t18_yellow_0)).

fof(f77,plain,(
    k1_yellow_0(sK0,k2_xboole_0(sK1,sK2)) != k10_lattice3(sK0,k1_yellow_0(sK0,sK1),k1_yellow_0(sK0,sK2)) ),
    inference(cnf_transformation,[],[f61])).

fof(f22878,plain,(
    r1_orders_2(sK0,k1_yellow_0(sK0,sK2),k1_yellow_0(sK0,k2_xboole_0(sK1,sK2))) ),
    inference(subsumption_resolution,[],[f22877,f72])).

fof(f22877,plain,
    ( r1_orders_2(sK0,k1_yellow_0(sK0,sK2),k1_yellow_0(sK0,k2_xboole_0(sK1,sK2)))
    | ~ v5_orders_2(sK0) ),
    inference(subsumption_resolution,[],[f22876,f73])).

fof(f22876,plain,
    ( r1_orders_2(sK0,k1_yellow_0(sK0,sK2),k1_yellow_0(sK0,k2_xboole_0(sK1,sK2)))
    | ~ l1_orders_2(sK0)
    | ~ v5_orders_2(sK0) ),
    inference(subsumption_resolution,[],[f22875,f173])).

fof(f22875,plain,
    ( r1_orders_2(sK0,k1_yellow_0(sK0,sK2),k1_yellow_0(sK0,k2_xboole_0(sK1,sK2)))
    | ~ m1_subset_1(k1_yellow_0(sK0,sK2),u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | ~ v5_orders_2(sK0) ),
    inference(subsumption_resolution,[],[f22874,f75])).

fof(f75,plain,(
    r1_yellow_0(sK0,sK2) ),
    inference(cnf_transformation,[],[f61])).

fof(f22874,plain,
    ( r1_orders_2(sK0,k1_yellow_0(sK0,sK2),k1_yellow_0(sK0,k2_xboole_0(sK1,sK2)))
    | ~ r1_yellow_0(sK0,sK2)
    | ~ m1_subset_1(k1_yellow_0(sK0,sK2),u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | ~ v5_orders_2(sK0) ),
    inference(subsumption_resolution,[],[f22768,f173])).

fof(f22768,plain,
    ( r1_orders_2(sK0,k1_yellow_0(sK0,sK2),k1_yellow_0(sK0,k2_xboole_0(sK1,sK2)))
    | ~ m1_subset_1(k1_yellow_0(sK0,k2_xboole_0(sK1,sK2)),u1_struct_0(sK0))
    | ~ r1_yellow_0(sK0,sK2)
    | ~ m1_subset_1(k1_yellow_0(sK0,sK2),u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | ~ v5_orders_2(sK0) ),
    inference(resolution,[],[f11723,f120])).

fof(f11723,plain,(
    r2_lattice3(sK0,sK2,k1_yellow_0(sK0,k2_xboole_0(sK1,sK2))) ),
    inference(forward_demodulation,[],[f11722,f79])).

fof(f79,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/yellow_0__t36_yellow_0.p',commutativity_k2_xboole_0)).

fof(f11722,plain,(
    r2_lattice3(sK0,sK2,k1_yellow_0(sK0,k2_xboole_0(sK2,sK1))) ),
    inference(subsumption_resolution,[],[f11701,f75])).

fof(f11701,plain,
    ( ~ r1_yellow_0(sK0,sK2)
    | r2_lattice3(sK0,sK2,k1_yellow_0(sK0,k2_xboole_0(sK2,sK1))) ),
    inference(resolution,[],[f11599,f76])).

fof(f11599,plain,(
    ! [X0,X1] :
      ( ~ r1_yellow_0(sK0,k2_xboole_0(X1,X0))
      | ~ r1_yellow_0(sK0,X0)
      | r2_lattice3(sK0,X0,k1_yellow_0(sK0,k2_xboole_0(X0,X1))) ) ),
    inference(superposition,[],[f10582,f79])).

fof(f10582,plain,(
    ! [X0,X1] :
      ( ~ r1_yellow_0(sK0,k2_xboole_0(X0,X1))
      | ~ r1_yellow_0(sK0,X0)
      | r2_lattice3(sK0,X0,k1_yellow_0(sK0,k2_xboole_0(X0,X1))) ) ),
    inference(resolution,[],[f10557,f103])).

fof(f10557,plain,(
    ! [X2,X3] :
      ( ~ r1_tarski(X2,X3)
      | ~ r1_yellow_0(sK0,X2)
      | ~ r1_yellow_0(sK0,X3)
      | r2_lattice3(sK0,X2,k1_yellow_0(sK0,X3)) ) ),
    inference(subsumption_resolution,[],[f10556,f73])).

fof(f10556,plain,(
    ! [X2,X3] :
      ( r2_lattice3(sK0,X2,k1_yellow_0(sK0,X3))
      | ~ r1_yellow_0(sK0,X2)
      | ~ r1_yellow_0(sK0,X3)
      | ~ r1_tarski(X2,X3)
      | ~ l1_orders_2(sK0) ) ),
    inference(subsumption_resolution,[],[f10554,f173])).

fof(f10554,plain,(
    ! [X2,X3] :
      ( r2_lattice3(sK0,X2,k1_yellow_0(sK0,X3))
      | ~ m1_subset_1(k1_yellow_0(sK0,X3),u1_struct_0(sK0))
      | ~ r1_yellow_0(sK0,X2)
      | ~ r1_yellow_0(sK0,X3)
      | ~ r1_tarski(X2,X3)
      | ~ l1_orders_2(sK0) ) ),
    inference(duplicate_literal_removal,[],[f10527])).

fof(f10527,plain,(
    ! [X2,X3] :
      ( r2_lattice3(sK0,X2,k1_yellow_0(sK0,X3))
      | ~ m1_subset_1(k1_yellow_0(sK0,X3),u1_struct_0(sK0))
      | ~ r1_yellow_0(sK0,X2)
      | ~ r1_yellow_0(sK0,X3)
      | ~ r1_yellow_0(sK0,X2)
      | ~ r1_tarski(X2,X3)
      | ~ l1_orders_2(sK0) ) ),
    inference(resolution,[],[f3334,f102])).

fof(f3334,plain,(
    ! [X15,X16] :
      ( ~ r1_orders_2(sK0,k1_yellow_0(sK0,X15),X16)
      | r2_lattice3(sK0,X15,X16)
      | ~ m1_subset_1(X16,u1_struct_0(sK0))
      | ~ r1_yellow_0(sK0,X15) ) ),
    inference(subsumption_resolution,[],[f3333,f72])).

fof(f3333,plain,(
    ! [X15,X16] :
      ( r2_lattice3(sK0,X15,X16)
      | ~ r1_orders_2(sK0,k1_yellow_0(sK0,X15),X16)
      | ~ m1_subset_1(X16,u1_struct_0(sK0))
      | ~ r1_yellow_0(sK0,X15)
      | ~ v5_orders_2(sK0) ) ),
    inference(subsumption_resolution,[],[f3332,f73])).

fof(f3332,plain,(
    ! [X15,X16] :
      ( r2_lattice3(sK0,X15,X16)
      | ~ r1_orders_2(sK0,k1_yellow_0(sK0,X15),X16)
      | ~ m1_subset_1(X16,u1_struct_0(sK0))
      | ~ r1_yellow_0(sK0,X15)
      | ~ l1_orders_2(sK0)
      | ~ v5_orders_2(sK0) ) ),
    inference(subsumption_resolution,[],[f3323,f173])).

fof(f3323,plain,(
    ! [X15,X16] :
      ( r2_lattice3(sK0,X15,X16)
      | ~ r1_orders_2(sK0,k1_yellow_0(sK0,X15),X16)
      | ~ m1_subset_1(X16,u1_struct_0(sK0))
      | ~ m1_subset_1(k1_yellow_0(sK0,X15),u1_struct_0(sK0))
      | ~ r1_yellow_0(sK0,X15)
      | ~ l1_orders_2(sK0)
      | ~ v5_orders_2(sK0) ) ),
    inference(duplicate_literal_removal,[],[f3318])).

fof(f3318,plain,(
    ! [X15,X16] :
      ( r2_lattice3(sK0,X15,X16)
      | ~ r1_orders_2(sK0,k1_yellow_0(sK0,X15),X16)
      | ~ m1_subset_1(X16,u1_struct_0(sK0))
      | ~ m1_subset_1(k1_yellow_0(sK0,X15),u1_struct_0(sK0))
      | ~ r1_yellow_0(sK0,X15)
      | ~ m1_subset_1(k1_yellow_0(sK0,X15),u1_struct_0(sK0))
      | ~ l1_orders_2(sK0)
      | ~ v5_orders_2(sK0) ) ),
    inference(resolution,[],[f125,f121])).

fof(f125,plain,(
    ! [X4,X5,X3] :
      ( ~ r2_lattice3(sK0,X3,X5)
      | r2_lattice3(sK0,X3,X4)
      | ~ r1_orders_2(sK0,X5,X4)
      | ~ m1_subset_1(X4,u1_struct_0(sK0))
      | ~ m1_subset_1(X5,u1_struct_0(sK0)) ) ),
    inference(subsumption_resolution,[],[f123,f73])).

fof(f123,plain,(
    ! [X4,X5,X3] :
      ( r2_lattice3(sK0,X3,X4)
      | ~ r2_lattice3(sK0,X3,X5)
      | ~ r1_orders_2(sK0,X5,X4)
      | ~ m1_subset_1(X4,u1_struct_0(sK0))
      | ~ m1_subset_1(X5,u1_struct_0(sK0))
      | ~ l1_orders_2(sK0) ) ),
    inference(resolution,[],[f71,f106])).

fof(f126196,plain,(
    ~ m1_subset_1(sK3(sK0,k1_yellow_0(sK0,sK1),k1_yellow_0(sK0,sK2),k1_yellow_0(sK0,k2_xboole_0(sK1,sK2))),u1_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f126033,f125800])).

fof(f125800,plain,(
    ~ r2_lattice3(sK0,sK1,sK3(sK0,k1_yellow_0(sK0,sK1),k1_yellow_0(sK0,sK2),k1_yellow_0(sK0,k2_xboole_0(sK1,sK2)))) ),
    inference(subsumption_resolution,[],[f125799,f95564])).

fof(f95564,plain,(
    ~ r1_orders_2(sK0,k1_yellow_0(sK0,k2_xboole_0(sK1,sK2)),sK3(sK0,k1_yellow_0(sK0,sK1),k1_yellow_0(sK0,sK2),k1_yellow_0(sK0,k2_xboole_0(sK1,sK2)))) ),
    inference(subsumption_resolution,[],[f95563,f24184])).

fof(f24184,plain,(
    r1_yellow_0(sK0,k2_tarski(k1_yellow_0(sK0,sK2),k1_yellow_0(sK0,k2_xboole_0(sK1,sK2)))) ),
    inference(forward_demodulation,[],[f24183,f112])).

fof(f112,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/yellow_0__t36_yellow_0.p',commutativity_k2_tarski)).

fof(f24183,plain,(
    r1_yellow_0(sK0,k2_tarski(k1_yellow_0(sK0,k2_xboole_0(sK1,sK2)),k1_yellow_0(sK0,sK2))) ),
    inference(subsumption_resolution,[],[f24182,f173])).

fof(f24182,plain,
    ( r1_yellow_0(sK0,k2_tarski(k1_yellow_0(sK0,k2_xboole_0(sK1,sK2)),k1_yellow_0(sK0,sK2)))
    | ~ m1_subset_1(k1_yellow_0(sK0,sK2),u1_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f24181,f173])).

fof(f24181,plain,
    ( r1_yellow_0(sK0,k2_tarski(k1_yellow_0(sK0,k2_xboole_0(sK1,sK2)),k1_yellow_0(sK0,sK2)))
    | ~ m1_subset_1(k1_yellow_0(sK0,k2_xboole_0(sK1,sK2)),u1_struct_0(sK0))
    | ~ m1_subset_1(k1_yellow_0(sK0,sK2),u1_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f24129,f512])).

fof(f512,plain,(
    r1_orders_2(sK0,k1_yellow_0(sK0,k2_xboole_0(sK1,sK2)),k1_yellow_0(sK0,k2_xboole_0(sK1,sK2))) ),
    inference(subsumption_resolution,[],[f511,f72])).

fof(f511,plain,
    ( r1_orders_2(sK0,k1_yellow_0(sK0,k2_xboole_0(sK1,sK2)),k1_yellow_0(sK0,k2_xboole_0(sK1,sK2)))
    | ~ v5_orders_2(sK0) ),
    inference(subsumption_resolution,[],[f510,f73])).

fof(f510,plain,
    ( r1_orders_2(sK0,k1_yellow_0(sK0,k2_xboole_0(sK1,sK2)),k1_yellow_0(sK0,k2_xboole_0(sK1,sK2)))
    | ~ l1_orders_2(sK0)
    | ~ v5_orders_2(sK0) ),
    inference(subsumption_resolution,[],[f509,f76])).

fof(f509,plain,
    ( r1_orders_2(sK0,k1_yellow_0(sK0,k2_xboole_0(sK1,sK2)),k1_yellow_0(sK0,k2_xboole_0(sK1,sK2)))
    | ~ r1_yellow_0(sK0,k2_xboole_0(sK1,sK2))
    | ~ l1_orders_2(sK0)
    | ~ v5_orders_2(sK0) ),
    inference(subsumption_resolution,[],[f501,f173])).

fof(f501,plain,
    ( r1_orders_2(sK0,k1_yellow_0(sK0,k2_xboole_0(sK1,sK2)),k1_yellow_0(sK0,k2_xboole_0(sK1,sK2)))
    | ~ m1_subset_1(k1_yellow_0(sK0,k2_xboole_0(sK1,sK2)),u1_struct_0(sK0))
    | ~ r1_yellow_0(sK0,k2_xboole_0(sK1,sK2))
    | ~ l1_orders_2(sK0)
    | ~ v5_orders_2(sK0) ),
    inference(duplicate_literal_removal,[],[f497])).

fof(f497,plain,
    ( r1_orders_2(sK0,k1_yellow_0(sK0,k2_xboole_0(sK1,sK2)),k1_yellow_0(sK0,k2_xboole_0(sK1,sK2)))
    | ~ m1_subset_1(k1_yellow_0(sK0,k2_xboole_0(sK1,sK2)),u1_struct_0(sK0))
    | ~ r1_yellow_0(sK0,k2_xboole_0(sK1,sK2))
    | ~ m1_subset_1(k1_yellow_0(sK0,k2_xboole_0(sK1,sK2)),u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | ~ v5_orders_2(sK0) ),
    inference(resolution,[],[f222,f120])).

fof(f222,plain,(
    r2_lattice3(sK0,k2_xboole_0(sK1,sK2),k1_yellow_0(sK0,k2_xboole_0(sK1,sK2))) ),
    inference(subsumption_resolution,[],[f221,f72])).

fof(f221,plain,
    ( r2_lattice3(sK0,k2_xboole_0(sK1,sK2),k1_yellow_0(sK0,k2_xboole_0(sK1,sK2)))
    | ~ v5_orders_2(sK0) ),
    inference(subsumption_resolution,[],[f220,f73])).

fof(f220,plain,
    ( r2_lattice3(sK0,k2_xboole_0(sK1,sK2),k1_yellow_0(sK0,k2_xboole_0(sK1,sK2)))
    | ~ l1_orders_2(sK0)
    | ~ v5_orders_2(sK0) ),
    inference(subsumption_resolution,[],[f216,f173])).

fof(f216,plain,
    ( r2_lattice3(sK0,k2_xboole_0(sK1,sK2),k1_yellow_0(sK0,k2_xboole_0(sK1,sK2)))
    | ~ m1_subset_1(k1_yellow_0(sK0,k2_xboole_0(sK1,sK2)),u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | ~ v5_orders_2(sK0) ),
    inference(resolution,[],[f76,f121])).

fof(f24129,plain,
    ( r1_yellow_0(sK0,k2_tarski(k1_yellow_0(sK0,k2_xboole_0(sK1,sK2)),k1_yellow_0(sK0,sK2)))
    | ~ r1_orders_2(sK0,k1_yellow_0(sK0,k2_xboole_0(sK1,sK2)),k1_yellow_0(sK0,k2_xboole_0(sK1,sK2)))
    | ~ m1_subset_1(k1_yellow_0(sK0,k2_xboole_0(sK1,sK2)),u1_struct_0(sK0))
    | ~ m1_subset_1(k1_yellow_0(sK0,sK2),u1_struct_0(sK0)) ),
    inference(resolution,[],[f22878,f7049])).

fof(f7049,plain,(
    ! [X6,X7] :
      ( ~ r1_orders_2(sK0,X7,X6)
      | r1_yellow_0(sK0,k2_tarski(X6,X7))
      | ~ r1_orders_2(sK0,X6,X6)
      | ~ m1_subset_1(X6,u1_struct_0(sK0))
      | ~ m1_subset_1(X7,u1_struct_0(sK0)) ) ),
    inference(subsumption_resolution,[],[f7048,f72])).

fof(f7048,plain,(
    ! [X6,X7] :
      ( r1_yellow_0(sK0,k2_tarski(X6,X7))
      | ~ r1_orders_2(sK0,X7,X6)
      | ~ r1_orders_2(sK0,X6,X6)
      | ~ m1_subset_1(X6,u1_struct_0(sK0))
      | ~ m1_subset_1(X7,u1_struct_0(sK0))
      | ~ v5_orders_2(sK0) ) ),
    inference(subsumption_resolution,[],[f7038,f73])).

fof(f7038,plain,(
    ! [X6,X7] :
      ( r1_yellow_0(sK0,k2_tarski(X6,X7))
      | ~ r1_orders_2(sK0,X7,X6)
      | ~ r1_orders_2(sK0,X6,X6)
      | ~ m1_subset_1(X6,u1_struct_0(sK0))
      | ~ m1_subset_1(X7,u1_struct_0(sK0))
      | ~ l1_orders_2(sK0)
      | ~ v5_orders_2(sK0) ) ),
    inference(duplicate_literal_removal,[],[f7033])).

fof(f7033,plain,(
    ! [X6,X7] :
      ( r1_yellow_0(sK0,k2_tarski(X6,X7))
      | ~ r1_orders_2(sK0,X7,X6)
      | ~ r1_orders_2(sK0,X6,X6)
      | ~ m1_subset_1(X6,u1_struct_0(sK0))
      | ~ m1_subset_1(X7,u1_struct_0(sK0))
      | ~ m1_subset_1(X6,u1_struct_0(sK0))
      | r1_yellow_0(sK0,k2_tarski(X6,X7))
      | ~ r1_orders_2(sK0,X7,X6)
      | ~ r1_orders_2(sK0,X6,X6)
      | ~ m1_subset_1(X6,u1_struct_0(sK0))
      | ~ m1_subset_1(X7,u1_struct_0(sK0))
      | ~ m1_subset_1(X6,u1_struct_0(sK0))
      | ~ l1_orders_2(sK0)
      | ~ v5_orders_2(sK0) ) ),
    inference(resolution,[],[f152,f90])).

fof(f90,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_yellow_0(X0,k2_tarski(X1,X2))
      | r1_orders_2(X0,X1,sK3(X0,X1,X2,X3))
      | ~ r1_orders_2(X0,X2,X3)
      | ~ r1_orders_2(X0,X1,X3)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f63])).

fof(f152,plain,(
    ! [X23,X21,X22] :
      ( ~ r1_orders_2(sK0,X23,sK3(sK0,X21,X22,X23))
      | r1_yellow_0(sK0,k2_tarski(X21,X22))
      | ~ r1_orders_2(sK0,X22,X23)
      | ~ r1_orders_2(sK0,X21,X23)
      | ~ m1_subset_1(X23,u1_struct_0(sK0))
      | ~ m1_subset_1(X22,u1_struct_0(sK0))
      | ~ m1_subset_1(X21,u1_struct_0(sK0)) ) ),
    inference(subsumption_resolution,[],[f133,f73])).

fof(f133,plain,(
    ! [X23,X21,X22] :
      ( r1_yellow_0(sK0,k2_tarski(X21,X22))
      | ~ r1_orders_2(sK0,X23,sK3(sK0,X21,X22,X23))
      | ~ r1_orders_2(sK0,X22,X23)
      | ~ r1_orders_2(sK0,X21,X23)
      | ~ m1_subset_1(X23,u1_struct_0(sK0))
      | ~ m1_subset_1(X22,u1_struct_0(sK0))
      | ~ m1_subset_1(X21,u1_struct_0(sK0))
      | ~ l1_orders_2(sK0) ) ),
    inference(resolution,[],[f72,f92])).

fof(f92,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_yellow_0(X0,k2_tarski(X1,X2))
      | ~ r1_orders_2(X0,X3,sK3(X0,X1,X2,X3))
      | ~ r1_orders_2(X0,X2,X3)
      | ~ r1_orders_2(X0,X1,X3)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f63])).

fof(f95563,plain,
    ( ~ r1_yellow_0(sK0,k2_tarski(k1_yellow_0(sK0,sK2),k1_yellow_0(sK0,k2_xboole_0(sK1,sK2))))
    | ~ r1_orders_2(sK0,k1_yellow_0(sK0,k2_xboole_0(sK1,sK2)),sK3(sK0,k1_yellow_0(sK0,sK1),k1_yellow_0(sK0,sK2),k1_yellow_0(sK0,k2_xboole_0(sK1,sK2)))) ),
    inference(forward_demodulation,[],[f95562,f112])).

fof(f95562,plain,
    ( ~ r1_orders_2(sK0,k1_yellow_0(sK0,k2_xboole_0(sK1,sK2)),sK3(sK0,k1_yellow_0(sK0,sK1),k1_yellow_0(sK0,sK2),k1_yellow_0(sK0,k2_xboole_0(sK1,sK2))))
    | ~ r1_yellow_0(sK0,k2_tarski(k1_yellow_0(sK0,k2_xboole_0(sK1,sK2)),k1_yellow_0(sK0,sK2))) ),
    inference(subsumption_resolution,[],[f95561,f24165])).

fof(f95561,plain,
    ( ~ m1_subset_1(sK3(sK0,k1_yellow_0(sK0,sK1),k1_yellow_0(sK0,sK2),k1_yellow_0(sK0,k2_xboole_0(sK1,sK2))),u1_struct_0(sK0))
    | ~ r1_orders_2(sK0,k1_yellow_0(sK0,k2_xboole_0(sK1,sK2)),sK3(sK0,k1_yellow_0(sK0,sK1),k1_yellow_0(sK0,sK2),k1_yellow_0(sK0,k2_xboole_0(sK1,sK2))))
    | ~ r1_yellow_0(sK0,k2_tarski(k1_yellow_0(sK0,k2_xboole_0(sK1,sK2)),k1_yellow_0(sK0,sK2))) ),
    inference(forward_demodulation,[],[f95560,f24187])).

fof(f24187,plain,(
    k1_yellow_0(sK0,k2_xboole_0(sK1,sK2)) = k10_lattice3(sK0,k1_yellow_0(sK0,k2_xboole_0(sK1,sK2)),k1_yellow_0(sK0,sK2)) ),
    inference(subsumption_resolution,[],[f24186,f173])).

fof(f24186,plain,
    ( k1_yellow_0(sK0,k2_xboole_0(sK1,sK2)) = k10_lattice3(sK0,k1_yellow_0(sK0,k2_xboole_0(sK1,sK2)),k1_yellow_0(sK0,sK2))
    | ~ m1_subset_1(k1_yellow_0(sK0,sK2),u1_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f24185,f173])).

fof(f24185,plain,
    ( k1_yellow_0(sK0,k2_xboole_0(sK1,sK2)) = k10_lattice3(sK0,k1_yellow_0(sK0,k2_xboole_0(sK1,sK2)),k1_yellow_0(sK0,sK2))
    | ~ m1_subset_1(k1_yellow_0(sK0,k2_xboole_0(sK1,sK2)),u1_struct_0(sK0))
    | ~ m1_subset_1(k1_yellow_0(sK0,sK2),u1_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f24130,f512])).

fof(f24130,plain,
    ( k1_yellow_0(sK0,k2_xboole_0(sK1,sK2)) = k10_lattice3(sK0,k1_yellow_0(sK0,k2_xboole_0(sK1,sK2)),k1_yellow_0(sK0,sK2))
    | ~ r1_orders_2(sK0,k1_yellow_0(sK0,k2_xboole_0(sK1,sK2)),k1_yellow_0(sK0,k2_xboole_0(sK1,sK2)))
    | ~ m1_subset_1(k1_yellow_0(sK0,k2_xboole_0(sK1,sK2)),u1_struct_0(sK0))
    | ~ m1_subset_1(k1_yellow_0(sK0,sK2),u1_struct_0(sK0)) ),
    inference(resolution,[],[f22878,f7502])).

fof(f7502,plain,(
    ! [X4,X5] :
      ( ~ r1_orders_2(sK0,X5,X4)
      | k10_lattice3(sK0,X4,X5) = X4
      | ~ r1_orders_2(sK0,X4,X4)
      | ~ m1_subset_1(X4,u1_struct_0(sK0))
      | ~ m1_subset_1(X5,u1_struct_0(sK0)) ) ),
    inference(subsumption_resolution,[],[f7501,f72])).

fof(f7501,plain,(
    ! [X4,X5] :
      ( k10_lattice3(sK0,X4,X5) = X4
      | ~ r1_orders_2(sK0,X5,X4)
      | ~ r1_orders_2(sK0,X4,X4)
      | ~ m1_subset_1(X4,u1_struct_0(sK0))
      | ~ m1_subset_1(X5,u1_struct_0(sK0))
      | ~ v5_orders_2(sK0) ) ),
    inference(subsumption_resolution,[],[f7496,f73])).

fof(f7496,plain,(
    ! [X4,X5] :
      ( k10_lattice3(sK0,X4,X5) = X4
      | ~ r1_orders_2(sK0,X5,X4)
      | ~ r1_orders_2(sK0,X4,X4)
      | ~ m1_subset_1(X4,u1_struct_0(sK0))
      | ~ m1_subset_1(X5,u1_struct_0(sK0))
      | ~ l1_orders_2(sK0)
      | ~ v5_orders_2(sK0) ) ),
    inference(duplicate_literal_removal,[],[f7489])).

fof(f7489,plain,(
    ! [X4,X5] :
      ( k10_lattice3(sK0,X4,X5) = X4
      | ~ r1_orders_2(sK0,X5,X4)
      | ~ r1_orders_2(sK0,X4,X4)
      | ~ m1_subset_1(X4,u1_struct_0(sK0))
      | ~ m1_subset_1(X5,u1_struct_0(sK0))
      | ~ m1_subset_1(X4,u1_struct_0(sK0))
      | k10_lattice3(sK0,X4,X5) = X4
      | ~ r1_orders_2(sK0,X5,X4)
      | ~ r1_orders_2(sK0,X4,X4)
      | ~ m1_subset_1(X4,u1_struct_0(sK0))
      | ~ m1_subset_1(X5,u1_struct_0(sK0))
      | ~ m1_subset_1(X4,u1_struct_0(sK0))
      | ~ l1_orders_2(sK0)
      | ~ v5_orders_2(sK0) ) ),
    inference(resolution,[],[f148,f86])).

fof(f86,plain,(
    ! [X2,X0,X3,X1] :
      ( k10_lattice3(X0,X1,X2) = X3
      | r1_orders_2(X0,X1,sK3(X0,X1,X2,X3))
      | ~ r1_orders_2(X0,X2,X3)
      | ~ r1_orders_2(X0,X1,X3)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f63])).

fof(f148,plain,(
    ! [X10,X11,X9] :
      ( ~ r1_orders_2(sK0,X11,sK3(sK0,X9,X10,X11))
      | k10_lattice3(sK0,X9,X10) = X11
      | ~ r1_orders_2(sK0,X10,X11)
      | ~ r1_orders_2(sK0,X9,X11)
      | ~ m1_subset_1(X11,u1_struct_0(sK0))
      | ~ m1_subset_1(X10,u1_struct_0(sK0))
      | ~ m1_subset_1(X9,u1_struct_0(sK0)) ) ),
    inference(subsumption_resolution,[],[f129,f73])).

fof(f129,plain,(
    ! [X10,X11,X9] :
      ( k10_lattice3(sK0,X9,X10) = X11
      | ~ r1_orders_2(sK0,X11,sK3(sK0,X9,X10,X11))
      | ~ r1_orders_2(sK0,X10,X11)
      | ~ r1_orders_2(sK0,X9,X11)
      | ~ m1_subset_1(X11,u1_struct_0(sK0))
      | ~ m1_subset_1(X10,u1_struct_0(sK0))
      | ~ m1_subset_1(X9,u1_struct_0(sK0))
      | ~ l1_orders_2(sK0) ) ),
    inference(resolution,[],[f72,f88])).

fof(f88,plain,(
    ! [X2,X0,X3,X1] :
      ( k10_lattice3(X0,X1,X2) = X3
      | ~ r1_orders_2(X0,X3,sK3(X0,X1,X2,X3))
      | ~ r1_orders_2(X0,X2,X3)
      | ~ r1_orders_2(X0,X1,X3)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f63])).

fof(f95560,plain,
    ( ~ r1_orders_2(sK0,k1_yellow_0(sK0,k2_xboole_0(sK1,sK2)),sK3(sK0,k1_yellow_0(sK0,sK1),k1_yellow_0(sK0,sK2),k1_yellow_0(sK0,k2_xboole_0(sK1,sK2))))
    | ~ m1_subset_1(sK3(sK0,k1_yellow_0(sK0,sK1),k1_yellow_0(sK0,sK2),k10_lattice3(sK0,k1_yellow_0(sK0,k2_xboole_0(sK1,sK2)),k1_yellow_0(sK0,sK2))),u1_struct_0(sK0))
    | ~ r1_yellow_0(sK0,k2_tarski(k1_yellow_0(sK0,k2_xboole_0(sK1,sK2)),k1_yellow_0(sK0,sK2))) ),
    inference(forward_demodulation,[],[f95559,f24187])).

fof(f95559,plain,
    ( ~ r1_orders_2(sK0,k1_yellow_0(sK0,k2_xboole_0(sK1,sK2)),sK3(sK0,k1_yellow_0(sK0,sK1),k1_yellow_0(sK0,sK2),k10_lattice3(sK0,k1_yellow_0(sK0,k2_xboole_0(sK1,sK2)),k1_yellow_0(sK0,sK2))))
    | ~ m1_subset_1(sK3(sK0,k1_yellow_0(sK0,sK1),k1_yellow_0(sK0,sK2),k10_lattice3(sK0,k1_yellow_0(sK0,k2_xboole_0(sK1,sK2)),k1_yellow_0(sK0,sK2))),u1_struct_0(sK0))
    | ~ r1_yellow_0(sK0,k2_tarski(k1_yellow_0(sK0,k2_xboole_0(sK1,sK2)),k1_yellow_0(sK0,sK2))) ),
    inference(subsumption_resolution,[],[f95558,f2086])).

fof(f95558,plain,
    ( ~ r1_orders_2(sK0,k1_yellow_0(sK0,sK1),k1_yellow_0(sK0,k2_xboole_0(sK1,sK2)))
    | ~ r1_orders_2(sK0,k1_yellow_0(sK0,k2_xboole_0(sK1,sK2)),sK3(sK0,k1_yellow_0(sK0,sK1),k1_yellow_0(sK0,sK2),k10_lattice3(sK0,k1_yellow_0(sK0,k2_xboole_0(sK1,sK2)),k1_yellow_0(sK0,sK2))))
    | ~ m1_subset_1(sK3(sK0,k1_yellow_0(sK0,sK1),k1_yellow_0(sK0,sK2),k10_lattice3(sK0,k1_yellow_0(sK0,k2_xboole_0(sK1,sK2)),k1_yellow_0(sK0,sK2))),u1_struct_0(sK0))
    | ~ r1_yellow_0(sK0,k2_tarski(k1_yellow_0(sK0,k2_xboole_0(sK1,sK2)),k1_yellow_0(sK0,sK2))) ),
    inference(forward_demodulation,[],[f95557,f24187])).

fof(f95557,plain,
    ( ~ r1_orders_2(sK0,k1_yellow_0(sK0,sK1),k10_lattice3(sK0,k1_yellow_0(sK0,k2_xboole_0(sK1,sK2)),k1_yellow_0(sK0,sK2)))
    | ~ r1_orders_2(sK0,k1_yellow_0(sK0,k2_xboole_0(sK1,sK2)),sK3(sK0,k1_yellow_0(sK0,sK1),k1_yellow_0(sK0,sK2),k10_lattice3(sK0,k1_yellow_0(sK0,k2_xboole_0(sK1,sK2)),k1_yellow_0(sK0,sK2))))
    | ~ m1_subset_1(sK3(sK0,k1_yellow_0(sK0,sK1),k1_yellow_0(sK0,sK2),k10_lattice3(sK0,k1_yellow_0(sK0,k2_xboole_0(sK1,sK2)),k1_yellow_0(sK0,sK2))),u1_struct_0(sK0))
    | ~ r1_yellow_0(sK0,k2_tarski(k1_yellow_0(sK0,k2_xboole_0(sK1,sK2)),k1_yellow_0(sK0,sK2))) ),
    inference(subsumption_resolution,[],[f95556,f22878])).

fof(f95556,plain,
    ( ~ r1_orders_2(sK0,k1_yellow_0(sK0,sK2),k1_yellow_0(sK0,k2_xboole_0(sK1,sK2)))
    | ~ r1_orders_2(sK0,k1_yellow_0(sK0,sK1),k10_lattice3(sK0,k1_yellow_0(sK0,k2_xboole_0(sK1,sK2)),k1_yellow_0(sK0,sK2)))
    | ~ r1_orders_2(sK0,k1_yellow_0(sK0,k2_xboole_0(sK1,sK2)),sK3(sK0,k1_yellow_0(sK0,sK1),k1_yellow_0(sK0,sK2),k10_lattice3(sK0,k1_yellow_0(sK0,k2_xboole_0(sK1,sK2)),k1_yellow_0(sK0,sK2))))
    | ~ m1_subset_1(sK3(sK0,k1_yellow_0(sK0,sK1),k1_yellow_0(sK0,sK2),k10_lattice3(sK0,k1_yellow_0(sK0,k2_xboole_0(sK1,sK2)),k1_yellow_0(sK0,sK2))),u1_struct_0(sK0))
    | ~ r1_yellow_0(sK0,k2_tarski(k1_yellow_0(sK0,k2_xboole_0(sK1,sK2)),k1_yellow_0(sK0,sK2))) ),
    inference(forward_demodulation,[],[f95555,f24187])).

fof(f95555,plain,
    ( ~ r1_orders_2(sK0,k1_yellow_0(sK0,sK2),k10_lattice3(sK0,k1_yellow_0(sK0,k2_xboole_0(sK1,sK2)),k1_yellow_0(sK0,sK2)))
    | ~ r1_orders_2(sK0,k1_yellow_0(sK0,sK1),k10_lattice3(sK0,k1_yellow_0(sK0,k2_xboole_0(sK1,sK2)),k1_yellow_0(sK0,sK2)))
    | ~ r1_orders_2(sK0,k1_yellow_0(sK0,k2_xboole_0(sK1,sK2)),sK3(sK0,k1_yellow_0(sK0,sK1),k1_yellow_0(sK0,sK2),k10_lattice3(sK0,k1_yellow_0(sK0,k2_xboole_0(sK1,sK2)),k1_yellow_0(sK0,sK2))))
    | ~ m1_subset_1(sK3(sK0,k1_yellow_0(sK0,sK1),k1_yellow_0(sK0,sK2),k10_lattice3(sK0,k1_yellow_0(sK0,k2_xboole_0(sK1,sK2)),k1_yellow_0(sK0,sK2))),u1_struct_0(sK0))
    | ~ r1_yellow_0(sK0,k2_tarski(k1_yellow_0(sK0,k2_xboole_0(sK1,sK2)),k1_yellow_0(sK0,sK2))) ),
    inference(subsumption_resolution,[],[f95554,f173])).

fof(f95554,plain,
    ( ~ r1_orders_2(sK0,k1_yellow_0(sK0,sK2),k10_lattice3(sK0,k1_yellow_0(sK0,k2_xboole_0(sK1,sK2)),k1_yellow_0(sK0,sK2)))
    | ~ r1_orders_2(sK0,k1_yellow_0(sK0,sK1),k10_lattice3(sK0,k1_yellow_0(sK0,k2_xboole_0(sK1,sK2)),k1_yellow_0(sK0,sK2)))
    | ~ r1_orders_2(sK0,k1_yellow_0(sK0,k2_xboole_0(sK1,sK2)),sK3(sK0,k1_yellow_0(sK0,sK1),k1_yellow_0(sK0,sK2),k10_lattice3(sK0,k1_yellow_0(sK0,k2_xboole_0(sK1,sK2)),k1_yellow_0(sK0,sK2))))
    | ~ m1_subset_1(sK3(sK0,k1_yellow_0(sK0,sK1),k1_yellow_0(sK0,sK2),k10_lattice3(sK0,k1_yellow_0(sK0,k2_xboole_0(sK1,sK2)),k1_yellow_0(sK0,sK2))),u1_struct_0(sK0))
    | ~ r1_yellow_0(sK0,k2_tarski(k1_yellow_0(sK0,k2_xboole_0(sK1,sK2)),k1_yellow_0(sK0,sK2)))
    | ~ m1_subset_1(k1_yellow_0(sK0,k2_xboole_0(sK1,sK2)),u1_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f95553,f173])).

fof(f95553,plain,
    ( ~ r1_orders_2(sK0,k1_yellow_0(sK0,sK2),k10_lattice3(sK0,k1_yellow_0(sK0,k2_xboole_0(sK1,sK2)),k1_yellow_0(sK0,sK2)))
    | ~ r1_orders_2(sK0,k1_yellow_0(sK0,sK1),k10_lattice3(sK0,k1_yellow_0(sK0,k2_xboole_0(sK1,sK2)),k1_yellow_0(sK0,sK2)))
    | ~ r1_orders_2(sK0,k1_yellow_0(sK0,k2_xboole_0(sK1,sK2)),sK3(sK0,k1_yellow_0(sK0,sK1),k1_yellow_0(sK0,sK2),k10_lattice3(sK0,k1_yellow_0(sK0,k2_xboole_0(sK1,sK2)),k1_yellow_0(sK0,sK2))))
    | ~ m1_subset_1(sK3(sK0,k1_yellow_0(sK0,sK1),k1_yellow_0(sK0,sK2),k10_lattice3(sK0,k1_yellow_0(sK0,k2_xboole_0(sK1,sK2)),k1_yellow_0(sK0,sK2))),u1_struct_0(sK0))
    | ~ r1_yellow_0(sK0,k2_tarski(k1_yellow_0(sK0,k2_xboole_0(sK1,sK2)),k1_yellow_0(sK0,sK2)))
    | ~ m1_subset_1(k1_yellow_0(sK0,sK2),u1_struct_0(sK0))
    | ~ m1_subset_1(k1_yellow_0(sK0,k2_xboole_0(sK1,sK2)),u1_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f95552,f24187])).

fof(f95552,plain,
    ( ~ r1_orders_2(sK0,k1_yellow_0(sK0,sK2),k10_lattice3(sK0,k1_yellow_0(sK0,k2_xboole_0(sK1,sK2)),k1_yellow_0(sK0,sK2)))
    | ~ r1_orders_2(sK0,k1_yellow_0(sK0,sK1),k10_lattice3(sK0,k1_yellow_0(sK0,k2_xboole_0(sK1,sK2)),k1_yellow_0(sK0,sK2)))
    | k1_yellow_0(sK0,k2_xboole_0(sK1,sK2)) != k10_lattice3(sK0,k1_yellow_0(sK0,k2_xboole_0(sK1,sK2)),k1_yellow_0(sK0,sK2))
    | ~ r1_orders_2(sK0,k1_yellow_0(sK0,k2_xboole_0(sK1,sK2)),sK3(sK0,k1_yellow_0(sK0,sK1),k1_yellow_0(sK0,sK2),k10_lattice3(sK0,k1_yellow_0(sK0,k2_xboole_0(sK1,sK2)),k1_yellow_0(sK0,sK2))))
    | ~ m1_subset_1(sK3(sK0,k1_yellow_0(sK0,sK1),k1_yellow_0(sK0,sK2),k10_lattice3(sK0,k1_yellow_0(sK0,k2_xboole_0(sK1,sK2)),k1_yellow_0(sK0,sK2))),u1_struct_0(sK0))
    | ~ r1_yellow_0(sK0,k2_tarski(k1_yellow_0(sK0,k2_xboole_0(sK1,sK2)),k1_yellow_0(sK0,sK2)))
    | ~ m1_subset_1(k1_yellow_0(sK0,sK2),u1_struct_0(sK0))
    | ~ m1_subset_1(k1_yellow_0(sK0,k2_xboole_0(sK1,sK2)),u1_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f95513,f24161])).

fof(f24161,plain,(
    r1_orders_2(sK0,k1_yellow_0(sK0,sK2),sK3(sK0,k1_yellow_0(sK0,sK1),k1_yellow_0(sK0,sK2),k1_yellow_0(sK0,k2_xboole_0(sK1,sK2)))) ),
    inference(subsumption_resolution,[],[f24160,f173])).

fof(f24160,plain,
    ( r1_orders_2(sK0,k1_yellow_0(sK0,sK2),sK3(sK0,k1_yellow_0(sK0,sK1),k1_yellow_0(sK0,sK2),k1_yellow_0(sK0,k2_xboole_0(sK1,sK2))))
    | ~ m1_subset_1(k1_yellow_0(sK0,k2_xboole_0(sK1,sK2)),u1_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f24159,f2086])).

fof(f24159,plain,
    ( r1_orders_2(sK0,k1_yellow_0(sK0,sK2),sK3(sK0,k1_yellow_0(sK0,sK1),k1_yellow_0(sK0,sK2),k1_yellow_0(sK0,k2_xboole_0(sK1,sK2))))
    | ~ r1_orders_2(sK0,k1_yellow_0(sK0,sK1),k1_yellow_0(sK0,k2_xboole_0(sK1,sK2)))
    | ~ m1_subset_1(k1_yellow_0(sK0,k2_xboole_0(sK1,sK2)),u1_struct_0(sK0)) ),
    inference(trivial_inequality_removal,[],[f24115])).

fof(f24115,plain,
    ( r1_orders_2(sK0,k1_yellow_0(sK0,sK2),sK3(sK0,k1_yellow_0(sK0,sK1),k1_yellow_0(sK0,sK2),k1_yellow_0(sK0,k2_xboole_0(sK1,sK2))))
    | k1_yellow_0(sK0,k2_xboole_0(sK1,sK2)) != k1_yellow_0(sK0,k2_xboole_0(sK1,sK2))
    | ~ r1_orders_2(sK0,k1_yellow_0(sK0,sK1),k1_yellow_0(sK0,k2_xboole_0(sK1,sK2)))
    | ~ m1_subset_1(k1_yellow_0(sK0,k2_xboole_0(sK1,sK2)),u1_struct_0(sK0)) ),
    inference(resolution,[],[f22878,f259])).

fof(f259,plain,(
    ! [X2] :
      ( ~ r1_orders_2(sK0,k1_yellow_0(sK0,sK2),X2)
      | r1_orders_2(sK0,k1_yellow_0(sK0,sK2),sK3(sK0,k1_yellow_0(sK0,sK1),k1_yellow_0(sK0,sK2),X2))
      | k1_yellow_0(sK0,k2_xboole_0(sK1,sK2)) != X2
      | ~ r1_orders_2(sK0,k1_yellow_0(sK0,sK1),X2)
      | ~ m1_subset_1(X2,u1_struct_0(sK0)) ) ),
    inference(subsumption_resolution,[],[f258,f72])).

fof(f258,plain,(
    ! [X2] :
      ( k1_yellow_0(sK0,k2_xboole_0(sK1,sK2)) != X2
      | r1_orders_2(sK0,k1_yellow_0(sK0,sK2),sK3(sK0,k1_yellow_0(sK0,sK1),k1_yellow_0(sK0,sK2),X2))
      | ~ r1_orders_2(sK0,k1_yellow_0(sK0,sK2),X2)
      | ~ r1_orders_2(sK0,k1_yellow_0(sK0,sK1),X2)
      | ~ m1_subset_1(X2,u1_struct_0(sK0))
      | ~ v5_orders_2(sK0) ) ),
    inference(subsumption_resolution,[],[f257,f73])).

fof(f257,plain,(
    ! [X2] :
      ( k1_yellow_0(sK0,k2_xboole_0(sK1,sK2)) != X2
      | r1_orders_2(sK0,k1_yellow_0(sK0,sK2),sK3(sK0,k1_yellow_0(sK0,sK1),k1_yellow_0(sK0,sK2),X2))
      | ~ r1_orders_2(sK0,k1_yellow_0(sK0,sK2),X2)
      | ~ r1_orders_2(sK0,k1_yellow_0(sK0,sK1),X2)
      | ~ m1_subset_1(X2,u1_struct_0(sK0))
      | ~ l1_orders_2(sK0)
      | ~ v5_orders_2(sK0) ) ),
    inference(subsumption_resolution,[],[f256,f173])).

fof(f256,plain,(
    ! [X2] :
      ( k1_yellow_0(sK0,k2_xboole_0(sK1,sK2)) != X2
      | r1_orders_2(sK0,k1_yellow_0(sK0,sK2),sK3(sK0,k1_yellow_0(sK0,sK1),k1_yellow_0(sK0,sK2),X2))
      | ~ r1_orders_2(sK0,k1_yellow_0(sK0,sK2),X2)
      | ~ r1_orders_2(sK0,k1_yellow_0(sK0,sK1),X2)
      | ~ m1_subset_1(X2,u1_struct_0(sK0))
      | ~ m1_subset_1(k1_yellow_0(sK0,sK1),u1_struct_0(sK0))
      | ~ l1_orders_2(sK0)
      | ~ v5_orders_2(sK0) ) ),
    inference(subsumption_resolution,[],[f234,f173])).

fof(f234,plain,(
    ! [X2] :
      ( k1_yellow_0(sK0,k2_xboole_0(sK1,sK2)) != X2
      | r1_orders_2(sK0,k1_yellow_0(sK0,sK2),sK3(sK0,k1_yellow_0(sK0,sK1),k1_yellow_0(sK0,sK2),X2))
      | ~ r1_orders_2(sK0,k1_yellow_0(sK0,sK2),X2)
      | ~ r1_orders_2(sK0,k1_yellow_0(sK0,sK1),X2)
      | ~ m1_subset_1(X2,u1_struct_0(sK0))
      | ~ m1_subset_1(k1_yellow_0(sK0,sK2),u1_struct_0(sK0))
      | ~ m1_subset_1(k1_yellow_0(sK0,sK1),u1_struct_0(sK0))
      | ~ l1_orders_2(sK0)
      | ~ v5_orders_2(sK0) ) ),
    inference(superposition,[],[f77,f87])).

fof(f87,plain,(
    ! [X2,X0,X3,X1] :
      ( k10_lattice3(X0,X1,X2) = X3
      | r1_orders_2(X0,X2,sK3(X0,X1,X2,X3))
      | ~ r1_orders_2(X0,X2,X3)
      | ~ r1_orders_2(X0,X1,X3)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f63])).

fof(f95513,plain,
    ( ~ r1_orders_2(sK0,k1_yellow_0(sK0,sK2),sK3(sK0,k1_yellow_0(sK0,sK1),k1_yellow_0(sK0,sK2),k1_yellow_0(sK0,k2_xboole_0(sK1,sK2))))
    | ~ r1_orders_2(sK0,k1_yellow_0(sK0,sK2),k10_lattice3(sK0,k1_yellow_0(sK0,k2_xboole_0(sK1,sK2)),k1_yellow_0(sK0,sK2)))
    | ~ r1_orders_2(sK0,k1_yellow_0(sK0,sK1),k10_lattice3(sK0,k1_yellow_0(sK0,k2_xboole_0(sK1,sK2)),k1_yellow_0(sK0,sK2)))
    | k1_yellow_0(sK0,k2_xboole_0(sK1,sK2)) != k10_lattice3(sK0,k1_yellow_0(sK0,k2_xboole_0(sK1,sK2)),k1_yellow_0(sK0,sK2))
    | ~ r1_orders_2(sK0,k1_yellow_0(sK0,k2_xboole_0(sK1,sK2)),sK3(sK0,k1_yellow_0(sK0,sK1),k1_yellow_0(sK0,sK2),k10_lattice3(sK0,k1_yellow_0(sK0,k2_xboole_0(sK1,sK2)),k1_yellow_0(sK0,sK2))))
    | ~ m1_subset_1(sK3(sK0,k1_yellow_0(sK0,sK1),k1_yellow_0(sK0,sK2),k10_lattice3(sK0,k1_yellow_0(sK0,k2_xboole_0(sK1,sK2)),k1_yellow_0(sK0,sK2))),u1_struct_0(sK0))
    | ~ r1_yellow_0(sK0,k2_tarski(k1_yellow_0(sK0,k2_xboole_0(sK1,sK2)),k1_yellow_0(sK0,sK2)))
    | ~ m1_subset_1(k1_yellow_0(sK0,sK2),u1_struct_0(sK0))
    | ~ m1_subset_1(k1_yellow_0(sK0,k2_xboole_0(sK1,sK2)),u1_struct_0(sK0)) ),
    inference(superposition,[],[f7927,f24187])).

fof(f7927,plain,(
    ! [X2,X1] :
      ( ~ r1_orders_2(sK0,X2,sK3(sK0,k1_yellow_0(sK0,sK1),k1_yellow_0(sK0,sK2),k10_lattice3(sK0,X1,X2)))
      | ~ r1_orders_2(sK0,k1_yellow_0(sK0,sK2),k10_lattice3(sK0,X1,X2))
      | ~ r1_orders_2(sK0,k1_yellow_0(sK0,sK1),k10_lattice3(sK0,X1,X2))
      | k1_yellow_0(sK0,k2_xboole_0(sK1,sK2)) != k10_lattice3(sK0,X1,X2)
      | ~ r1_orders_2(sK0,X1,sK3(sK0,k1_yellow_0(sK0,sK1),k1_yellow_0(sK0,sK2),k10_lattice3(sK0,X1,X2)))
      | ~ m1_subset_1(sK3(sK0,k1_yellow_0(sK0,sK1),k1_yellow_0(sK0,sK2),k10_lattice3(sK0,X1,X2)),u1_struct_0(sK0))
      | ~ r1_yellow_0(sK0,k2_tarski(X1,X2))
      | ~ m1_subset_1(X2,u1_struct_0(sK0))
      | ~ m1_subset_1(X1,u1_struct_0(sK0)) ) ),
    inference(subsumption_resolution,[],[f7926,f164])).

fof(f164,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,u1_struct_0(sK0))
      | m1_subset_1(k10_lattice3(sK0,X0,X1),u1_struct_0(sK0))
      | ~ m1_subset_1(X0,u1_struct_0(sK0)) ) ),
    inference(resolution,[],[f73,f81])).

fof(f81,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k10_lattice3(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k10_lattice3(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f41])).

fof(f41,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k10_lattice3(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l1_orders_2(X0) )
     => m1_subset_1(k10_lattice3(X0,X1,X2),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/yellow_0__t36_yellow_0.p',dt_k10_lattice3)).

fof(f7926,plain,(
    ! [X2,X1] :
      ( k1_yellow_0(sK0,k2_xboole_0(sK1,sK2)) != k10_lattice3(sK0,X1,X2)
      | ~ r1_orders_2(sK0,k1_yellow_0(sK0,sK2),k10_lattice3(sK0,X1,X2))
      | ~ r1_orders_2(sK0,k1_yellow_0(sK0,sK1),k10_lattice3(sK0,X1,X2))
      | ~ m1_subset_1(k10_lattice3(sK0,X1,X2),u1_struct_0(sK0))
      | ~ r1_orders_2(sK0,X2,sK3(sK0,k1_yellow_0(sK0,sK1),k1_yellow_0(sK0,sK2),k10_lattice3(sK0,X1,X2)))
      | ~ r1_orders_2(sK0,X1,sK3(sK0,k1_yellow_0(sK0,sK1),k1_yellow_0(sK0,sK2),k10_lattice3(sK0,X1,X2)))
      | ~ m1_subset_1(sK3(sK0,k1_yellow_0(sK0,sK1),k1_yellow_0(sK0,sK2),k10_lattice3(sK0,X1,X2)),u1_struct_0(sK0))
      | ~ r1_yellow_0(sK0,k2_tarski(X1,X2))
      | ~ m1_subset_1(X2,u1_struct_0(sK0))
      | ~ m1_subset_1(X1,u1_struct_0(sK0)) ) ),
    inference(subsumption_resolution,[],[f7925,f72])).

fof(f7925,plain,(
    ! [X2,X1] :
      ( k1_yellow_0(sK0,k2_xboole_0(sK1,sK2)) != k10_lattice3(sK0,X1,X2)
      | ~ r1_orders_2(sK0,k1_yellow_0(sK0,sK2),k10_lattice3(sK0,X1,X2))
      | ~ r1_orders_2(sK0,k1_yellow_0(sK0,sK1),k10_lattice3(sK0,X1,X2))
      | ~ m1_subset_1(k10_lattice3(sK0,X1,X2),u1_struct_0(sK0))
      | ~ r1_orders_2(sK0,X2,sK3(sK0,k1_yellow_0(sK0,sK1),k1_yellow_0(sK0,sK2),k10_lattice3(sK0,X1,X2)))
      | ~ r1_orders_2(sK0,X1,sK3(sK0,k1_yellow_0(sK0,sK1),k1_yellow_0(sK0,sK2),k10_lattice3(sK0,X1,X2)))
      | ~ m1_subset_1(sK3(sK0,k1_yellow_0(sK0,sK1),k1_yellow_0(sK0,sK2),k10_lattice3(sK0,X1,X2)),u1_struct_0(sK0))
      | ~ r1_yellow_0(sK0,k2_tarski(X1,X2))
      | ~ m1_subset_1(X2,u1_struct_0(sK0))
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ v5_orders_2(sK0) ) ),
    inference(subsumption_resolution,[],[f7911,f73])).

fof(f7911,plain,(
    ! [X2,X1] :
      ( k1_yellow_0(sK0,k2_xboole_0(sK1,sK2)) != k10_lattice3(sK0,X1,X2)
      | ~ r1_orders_2(sK0,k1_yellow_0(sK0,sK2),k10_lattice3(sK0,X1,X2))
      | ~ r1_orders_2(sK0,k1_yellow_0(sK0,sK1),k10_lattice3(sK0,X1,X2))
      | ~ m1_subset_1(k10_lattice3(sK0,X1,X2),u1_struct_0(sK0))
      | ~ r1_orders_2(sK0,X2,sK3(sK0,k1_yellow_0(sK0,sK1),k1_yellow_0(sK0,sK2),k10_lattice3(sK0,X1,X2)))
      | ~ r1_orders_2(sK0,X1,sK3(sK0,k1_yellow_0(sK0,sK1),k1_yellow_0(sK0,sK2),k10_lattice3(sK0,X1,X2)))
      | ~ m1_subset_1(sK3(sK0,k1_yellow_0(sK0,sK1),k1_yellow_0(sK0,sK2),k10_lattice3(sK0,X1,X2)),u1_struct_0(sK0))
      | ~ r1_yellow_0(sK0,k2_tarski(X1,X2))
      | ~ m1_subset_1(X2,u1_struct_0(sK0))
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ l1_orders_2(sK0)
      | ~ v5_orders_2(sK0) ) ),
    inference(duplicate_literal_removal,[],[f7903])).

fof(f7903,plain,(
    ! [X2,X1] :
      ( k1_yellow_0(sK0,k2_xboole_0(sK1,sK2)) != k10_lattice3(sK0,X1,X2)
      | ~ r1_orders_2(sK0,k1_yellow_0(sK0,sK2),k10_lattice3(sK0,X1,X2))
      | ~ r1_orders_2(sK0,k1_yellow_0(sK0,sK1),k10_lattice3(sK0,X1,X2))
      | ~ m1_subset_1(k10_lattice3(sK0,X1,X2),u1_struct_0(sK0))
      | ~ r1_orders_2(sK0,X2,sK3(sK0,k1_yellow_0(sK0,sK1),k1_yellow_0(sK0,sK2),k10_lattice3(sK0,X1,X2)))
      | ~ r1_orders_2(sK0,X1,sK3(sK0,k1_yellow_0(sK0,sK1),k1_yellow_0(sK0,sK2),k10_lattice3(sK0,X1,X2)))
      | ~ m1_subset_1(sK3(sK0,k1_yellow_0(sK0,sK1),k1_yellow_0(sK0,sK2),k10_lattice3(sK0,X1,X2)),u1_struct_0(sK0))
      | ~ r1_yellow_0(sK0,k2_tarski(X1,X2))
      | ~ m1_subset_1(k10_lattice3(sK0,X1,X2),u1_struct_0(sK0))
      | ~ m1_subset_1(X2,u1_struct_0(sK0))
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ l1_orders_2(sK0)
      | ~ v5_orders_2(sK0) ) ),
    inference(resolution,[],[f263,f117])).

fof(f117,plain,(
    ! [X2,X0,X5,X1] :
      ( r1_orders_2(X0,k10_lattice3(X0,X1,X2),X5)
      | ~ r1_orders_2(X0,X2,X5)
      | ~ r1_orders_2(X0,X1,X5)
      | ~ m1_subset_1(X5,u1_struct_0(X0))
      | ~ r1_yellow_0(X0,k2_tarski(X1,X2))
      | ~ m1_subset_1(k10_lattice3(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(equality_resolution,[],[f84])).

fof(f84,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r1_orders_2(X0,X3,X5)
      | ~ r1_orders_2(X0,X2,X5)
      | ~ r1_orders_2(X0,X1,X5)
      | ~ m1_subset_1(X5,u1_struct_0(X0))
      | ~ r1_yellow_0(X0,k2_tarski(X1,X2))
      | k10_lattice3(X0,X1,X2) != X3
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f63])).

fof(f263,plain,(
    ! [X3] :
      ( ~ r1_orders_2(sK0,X3,sK3(sK0,k1_yellow_0(sK0,sK1),k1_yellow_0(sK0,sK2),X3))
      | k1_yellow_0(sK0,k2_xboole_0(sK1,sK2)) != X3
      | ~ r1_orders_2(sK0,k1_yellow_0(sK0,sK2),X3)
      | ~ r1_orders_2(sK0,k1_yellow_0(sK0,sK1),X3)
      | ~ m1_subset_1(X3,u1_struct_0(sK0)) ) ),
    inference(subsumption_resolution,[],[f262,f72])).

fof(f262,plain,(
    ! [X3] :
      ( k1_yellow_0(sK0,k2_xboole_0(sK1,sK2)) != X3
      | ~ r1_orders_2(sK0,X3,sK3(sK0,k1_yellow_0(sK0,sK1),k1_yellow_0(sK0,sK2),X3))
      | ~ r1_orders_2(sK0,k1_yellow_0(sK0,sK2),X3)
      | ~ r1_orders_2(sK0,k1_yellow_0(sK0,sK1),X3)
      | ~ m1_subset_1(X3,u1_struct_0(sK0))
      | ~ v5_orders_2(sK0) ) ),
    inference(subsumption_resolution,[],[f261,f73])).

fof(f261,plain,(
    ! [X3] :
      ( k1_yellow_0(sK0,k2_xboole_0(sK1,sK2)) != X3
      | ~ r1_orders_2(sK0,X3,sK3(sK0,k1_yellow_0(sK0,sK1),k1_yellow_0(sK0,sK2),X3))
      | ~ r1_orders_2(sK0,k1_yellow_0(sK0,sK2),X3)
      | ~ r1_orders_2(sK0,k1_yellow_0(sK0,sK1),X3)
      | ~ m1_subset_1(X3,u1_struct_0(sK0))
      | ~ l1_orders_2(sK0)
      | ~ v5_orders_2(sK0) ) ),
    inference(subsumption_resolution,[],[f260,f173])).

fof(f260,plain,(
    ! [X3] :
      ( k1_yellow_0(sK0,k2_xboole_0(sK1,sK2)) != X3
      | ~ r1_orders_2(sK0,X3,sK3(sK0,k1_yellow_0(sK0,sK1),k1_yellow_0(sK0,sK2),X3))
      | ~ r1_orders_2(sK0,k1_yellow_0(sK0,sK2),X3)
      | ~ r1_orders_2(sK0,k1_yellow_0(sK0,sK1),X3)
      | ~ m1_subset_1(X3,u1_struct_0(sK0))
      | ~ m1_subset_1(k1_yellow_0(sK0,sK1),u1_struct_0(sK0))
      | ~ l1_orders_2(sK0)
      | ~ v5_orders_2(sK0) ) ),
    inference(subsumption_resolution,[],[f235,f173])).

fof(f235,plain,(
    ! [X3] :
      ( k1_yellow_0(sK0,k2_xboole_0(sK1,sK2)) != X3
      | ~ r1_orders_2(sK0,X3,sK3(sK0,k1_yellow_0(sK0,sK1),k1_yellow_0(sK0,sK2),X3))
      | ~ r1_orders_2(sK0,k1_yellow_0(sK0,sK2),X3)
      | ~ r1_orders_2(sK0,k1_yellow_0(sK0,sK1),X3)
      | ~ m1_subset_1(X3,u1_struct_0(sK0))
      | ~ m1_subset_1(k1_yellow_0(sK0,sK2),u1_struct_0(sK0))
      | ~ m1_subset_1(k1_yellow_0(sK0,sK1),u1_struct_0(sK0))
      | ~ l1_orders_2(sK0)
      | ~ v5_orders_2(sK0) ) ),
    inference(superposition,[],[f77,f88])).

fof(f125799,plain,
    ( r1_orders_2(sK0,k1_yellow_0(sK0,k2_xboole_0(sK1,sK2)),sK3(sK0,k1_yellow_0(sK0,sK1),k1_yellow_0(sK0,sK2),k1_yellow_0(sK0,k2_xboole_0(sK1,sK2))))
    | ~ r2_lattice3(sK0,sK1,sK3(sK0,k1_yellow_0(sK0,sK1),k1_yellow_0(sK0,sK2),k1_yellow_0(sK0,k2_xboole_0(sK1,sK2)))) ),
    inference(subsumption_resolution,[],[f125729,f24165])).

fof(f125729,plain,
    ( ~ m1_subset_1(sK3(sK0,k1_yellow_0(sK0,sK1),k1_yellow_0(sK0,sK2),k1_yellow_0(sK0,k2_xboole_0(sK1,sK2))),u1_struct_0(sK0))
    | r1_orders_2(sK0,k1_yellow_0(sK0,k2_xboole_0(sK1,sK2)),sK3(sK0,k1_yellow_0(sK0,sK1),k1_yellow_0(sK0,sK2),k1_yellow_0(sK0,k2_xboole_0(sK1,sK2))))
    | ~ r2_lattice3(sK0,sK1,sK3(sK0,k1_yellow_0(sK0,sK1),k1_yellow_0(sK0,sK2),k1_yellow_0(sK0,k2_xboole_0(sK1,sK2)))) ),
    inference(resolution,[],[f125517,f2923])).

fof(f2923,plain,(
    ! [X0] :
      ( ~ r2_lattice3(sK0,sK2,X0)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | r1_orders_2(sK0,k1_yellow_0(sK0,k2_xboole_0(sK1,sK2)),X0)
      | ~ r2_lattice3(sK0,sK1,X0) ) ),
    inference(subsumption_resolution,[],[f2920,f73])).

fof(f2920,plain,(
    ! [X0] :
      ( r1_orders_2(sK0,k1_yellow_0(sK0,k2_xboole_0(sK1,sK2)),X0)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ r2_lattice3(sK0,sK2,X0)
      | ~ r2_lattice3(sK0,sK1,X0)
      | ~ l1_orders_2(sK0) ) ),
    inference(duplicate_literal_removal,[],[f2913])).

fof(f2913,plain,(
    ! [X0] :
      ( r1_orders_2(sK0,k1_yellow_0(sK0,k2_xboole_0(sK1,sK2)),X0)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ r2_lattice3(sK0,sK2,X0)
      | ~ r2_lattice3(sK0,sK1,X0)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ l1_orders_2(sK0) ) ),
    inference(resolution,[],[f225,f114])).

fof(f114,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_lattice3(X0,k2_xboole_0(X1,X2),X3)
      | ~ r2_lattice3(X0,X2,X3)
      | ~ r2_lattice3(X0,X1,X3)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f58])).

fof(f58,plain,(
    ! [X0] :
      ( ! [X1,X2,X3] :
          ( ( ( r2_lattice3(X0,k2_xboole_0(X1,X2),X3)
              | ~ r2_lattice3(X0,X2,X3)
              | ~ r2_lattice3(X0,X1,X3) )
            & ( r1_lattice3(X0,k2_xboole_0(X1,X2),X3)
              | ~ r1_lattice3(X0,X2,X3)
              | ~ r1_lattice3(X0,X1,X3) ) )
          | ~ m1_subset_1(X3,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f57])).

fof(f57,plain,(
    ! [X0] :
      ( ! [X1,X2,X3] :
          ( ( ( r2_lattice3(X0,k2_xboole_0(X1,X2),X3)
              | ~ r2_lattice3(X0,X2,X3)
              | ~ r2_lattice3(X0,X1,X3) )
            & ( r1_lattice3(X0,k2_xboole_0(X1,X2),X3)
              | ~ r1_lattice3(X0,X2,X3)
              | ~ r1_lattice3(X0,X1,X3) ) )
          | ~ m1_subset_1(X3,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1,X2,X3] :
          ( m1_subset_1(X3,u1_struct_0(X0))
         => ( ( ( r2_lattice3(X0,X2,X3)
                & r2_lattice3(X0,X1,X3) )
             => r2_lattice3(X0,k2_xboole_0(X1,X2),X3) )
            & ( ( r1_lattice3(X0,X2,X3)
                & r1_lattice3(X0,X1,X3) )
             => r1_lattice3(X0,k2_xboole_0(X1,X2),X3) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/yellow_0__t36_yellow_0.p',t10_yellow_0)).

fof(f225,plain,(
    ! [X2] :
      ( ~ r2_lattice3(sK0,k2_xboole_0(sK1,sK2),X2)
      | r1_orders_2(sK0,k1_yellow_0(sK0,k2_xboole_0(sK1,sK2)),X2)
      | ~ m1_subset_1(X2,u1_struct_0(sK0)) ) ),
    inference(subsumption_resolution,[],[f224,f72])).

fof(f224,plain,(
    ! [X2] :
      ( r1_orders_2(sK0,k1_yellow_0(sK0,k2_xboole_0(sK1,sK2)),X2)
      | ~ r2_lattice3(sK0,k2_xboole_0(sK1,sK2),X2)
      | ~ m1_subset_1(X2,u1_struct_0(sK0))
      | ~ v5_orders_2(sK0) ) ),
    inference(subsumption_resolution,[],[f223,f73])).

fof(f223,plain,(
    ! [X2] :
      ( r1_orders_2(sK0,k1_yellow_0(sK0,k2_xboole_0(sK1,sK2)),X2)
      | ~ r2_lattice3(sK0,k2_xboole_0(sK1,sK2),X2)
      | ~ m1_subset_1(X2,u1_struct_0(sK0))
      | ~ l1_orders_2(sK0)
      | ~ v5_orders_2(sK0) ) ),
    inference(subsumption_resolution,[],[f217,f173])).

fof(f217,plain,(
    ! [X2] :
      ( r1_orders_2(sK0,k1_yellow_0(sK0,k2_xboole_0(sK1,sK2)),X2)
      | ~ r2_lattice3(sK0,k2_xboole_0(sK1,sK2),X2)
      | ~ m1_subset_1(X2,u1_struct_0(sK0))
      | ~ m1_subset_1(k1_yellow_0(sK0,k2_xboole_0(sK1,sK2)),u1_struct_0(sK0))
      | ~ l1_orders_2(sK0)
      | ~ v5_orders_2(sK0) ) ),
    inference(resolution,[],[f76,f120])).

fof(f125517,plain,(
    r2_lattice3(sK0,sK2,sK3(sK0,k1_yellow_0(sK0,sK1),k1_yellow_0(sK0,sK2),k1_yellow_0(sK0,k2_xboole_0(sK1,sK2)))) ),
    inference(subsumption_resolution,[],[f125321,f24165])).

fof(f125321,plain,
    ( r2_lattice3(sK0,sK2,sK3(sK0,k1_yellow_0(sK0,sK1),k1_yellow_0(sK0,sK2),k1_yellow_0(sK0,k2_xboole_0(sK1,sK2))))
    | ~ m1_subset_1(sK3(sK0,k1_yellow_0(sK0,sK1),k1_yellow_0(sK0,sK2),k1_yellow_0(sK0,k2_xboole_0(sK1,sK2))),u1_struct_0(sK0)) ),
    inference(resolution,[],[f24161,f467])).

fof(f467,plain,(
    ! [X0] :
      ( ~ r1_orders_2(sK0,k1_yellow_0(sK0,sK2),X0)
      | r2_lattice3(sK0,sK2,X0)
      | ~ m1_subset_1(X0,u1_struct_0(sK0)) ) ),
    inference(subsumption_resolution,[],[f466,f71])).

fof(f466,plain,(
    ! [X0] :
      ( r2_lattice3(sK0,sK2,X0)
      | ~ r1_orders_2(sK0,k1_yellow_0(sK0,sK2),X0)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ v4_orders_2(sK0) ) ),
    inference(subsumption_resolution,[],[f465,f73])).

fof(f465,plain,(
    ! [X0] :
      ( r2_lattice3(sK0,sK2,X0)
      | ~ r1_orders_2(sK0,k1_yellow_0(sK0,sK2),X0)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ l1_orders_2(sK0)
      | ~ v4_orders_2(sK0) ) ),
    inference(subsumption_resolution,[],[f457,f173])).

fof(f457,plain,(
    ! [X0] :
      ( r2_lattice3(sK0,sK2,X0)
      | ~ r1_orders_2(sK0,k1_yellow_0(sK0,sK2),X0)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ m1_subset_1(k1_yellow_0(sK0,sK2),u1_struct_0(sK0))
      | ~ l1_orders_2(sK0)
      | ~ v4_orders_2(sK0) ) ),
    inference(resolution,[],[f210,f106])).

fof(f210,plain,(
    r2_lattice3(sK0,sK2,k1_yellow_0(sK0,sK2)) ),
    inference(subsumption_resolution,[],[f209,f72])).

fof(f209,plain,
    ( r2_lattice3(sK0,sK2,k1_yellow_0(sK0,sK2))
    | ~ v5_orders_2(sK0) ),
    inference(subsumption_resolution,[],[f208,f73])).

fof(f208,plain,
    ( r2_lattice3(sK0,sK2,k1_yellow_0(sK0,sK2))
    | ~ l1_orders_2(sK0)
    | ~ v5_orders_2(sK0) ),
    inference(subsumption_resolution,[],[f204,f173])).

fof(f204,plain,
    ( r2_lattice3(sK0,sK2,k1_yellow_0(sK0,sK2))
    | ~ m1_subset_1(k1_yellow_0(sK0,sK2),u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | ~ v5_orders_2(sK0) ),
    inference(resolution,[],[f75,f121])).

fof(f126033,plain,
    ( r2_lattice3(sK0,sK1,sK3(sK0,k1_yellow_0(sK0,sK1),k1_yellow_0(sK0,sK2),k1_yellow_0(sK0,k2_xboole_0(sK1,sK2))))
    | ~ m1_subset_1(sK3(sK0,k1_yellow_0(sK0,sK1),k1_yellow_0(sK0,sK2),k1_yellow_0(sK0,k2_xboole_0(sK1,sK2))),u1_struct_0(sK0)) ),
    inference(resolution,[],[f24163,f442])).

fof(f24163,plain,(
    r1_orders_2(sK0,k1_yellow_0(sK0,sK1),sK3(sK0,k1_yellow_0(sK0,sK1),k1_yellow_0(sK0,sK2),k1_yellow_0(sK0,k2_xboole_0(sK1,sK2)))) ),
    inference(subsumption_resolution,[],[f24162,f173])).

fof(f24162,plain,
    ( r1_orders_2(sK0,k1_yellow_0(sK0,sK1),sK3(sK0,k1_yellow_0(sK0,sK1),k1_yellow_0(sK0,sK2),k1_yellow_0(sK0,k2_xboole_0(sK1,sK2))))
    | ~ m1_subset_1(k1_yellow_0(sK0,k2_xboole_0(sK1,sK2)),u1_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f24158,f2086])).

fof(f24158,plain,
    ( r1_orders_2(sK0,k1_yellow_0(sK0,sK1),sK3(sK0,k1_yellow_0(sK0,sK1),k1_yellow_0(sK0,sK2),k1_yellow_0(sK0,k2_xboole_0(sK1,sK2))))
    | ~ r1_orders_2(sK0,k1_yellow_0(sK0,sK1),k1_yellow_0(sK0,k2_xboole_0(sK1,sK2)))
    | ~ m1_subset_1(k1_yellow_0(sK0,k2_xboole_0(sK1,sK2)),u1_struct_0(sK0)) ),
    inference(trivial_inequality_removal,[],[f24116])).

fof(f24116,plain,
    ( r1_orders_2(sK0,k1_yellow_0(sK0,sK1),sK3(sK0,k1_yellow_0(sK0,sK1),k1_yellow_0(sK0,sK2),k1_yellow_0(sK0,k2_xboole_0(sK1,sK2))))
    | k1_yellow_0(sK0,k2_xboole_0(sK1,sK2)) != k1_yellow_0(sK0,k2_xboole_0(sK1,sK2))
    | ~ r1_orders_2(sK0,k1_yellow_0(sK0,sK1),k1_yellow_0(sK0,k2_xboole_0(sK1,sK2)))
    | ~ m1_subset_1(k1_yellow_0(sK0,k2_xboole_0(sK1,sK2)),u1_struct_0(sK0)) ),
    inference(resolution,[],[f22878,f255])).

fof(f255,plain,(
    ! [X1] :
      ( ~ r1_orders_2(sK0,k1_yellow_0(sK0,sK2),X1)
      | r1_orders_2(sK0,k1_yellow_0(sK0,sK1),sK3(sK0,k1_yellow_0(sK0,sK1),k1_yellow_0(sK0,sK2),X1))
      | k1_yellow_0(sK0,k2_xboole_0(sK1,sK2)) != X1
      | ~ r1_orders_2(sK0,k1_yellow_0(sK0,sK1),X1)
      | ~ m1_subset_1(X1,u1_struct_0(sK0)) ) ),
    inference(subsumption_resolution,[],[f254,f72])).

fof(f254,plain,(
    ! [X1] :
      ( k1_yellow_0(sK0,k2_xboole_0(sK1,sK2)) != X1
      | r1_orders_2(sK0,k1_yellow_0(sK0,sK1),sK3(sK0,k1_yellow_0(sK0,sK1),k1_yellow_0(sK0,sK2),X1))
      | ~ r1_orders_2(sK0,k1_yellow_0(sK0,sK2),X1)
      | ~ r1_orders_2(sK0,k1_yellow_0(sK0,sK1),X1)
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ v5_orders_2(sK0) ) ),
    inference(subsumption_resolution,[],[f253,f73])).

fof(f253,plain,(
    ! [X1] :
      ( k1_yellow_0(sK0,k2_xboole_0(sK1,sK2)) != X1
      | r1_orders_2(sK0,k1_yellow_0(sK0,sK1),sK3(sK0,k1_yellow_0(sK0,sK1),k1_yellow_0(sK0,sK2),X1))
      | ~ r1_orders_2(sK0,k1_yellow_0(sK0,sK2),X1)
      | ~ r1_orders_2(sK0,k1_yellow_0(sK0,sK1),X1)
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ l1_orders_2(sK0)
      | ~ v5_orders_2(sK0) ) ),
    inference(subsumption_resolution,[],[f252,f173])).

fof(f252,plain,(
    ! [X1] :
      ( k1_yellow_0(sK0,k2_xboole_0(sK1,sK2)) != X1
      | r1_orders_2(sK0,k1_yellow_0(sK0,sK1),sK3(sK0,k1_yellow_0(sK0,sK1),k1_yellow_0(sK0,sK2),X1))
      | ~ r1_orders_2(sK0,k1_yellow_0(sK0,sK2),X1)
      | ~ r1_orders_2(sK0,k1_yellow_0(sK0,sK1),X1)
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ m1_subset_1(k1_yellow_0(sK0,sK1),u1_struct_0(sK0))
      | ~ l1_orders_2(sK0)
      | ~ v5_orders_2(sK0) ) ),
    inference(subsumption_resolution,[],[f233,f173])).

fof(f233,plain,(
    ! [X1] :
      ( k1_yellow_0(sK0,k2_xboole_0(sK1,sK2)) != X1
      | r1_orders_2(sK0,k1_yellow_0(sK0,sK1),sK3(sK0,k1_yellow_0(sK0,sK1),k1_yellow_0(sK0,sK2),X1))
      | ~ r1_orders_2(sK0,k1_yellow_0(sK0,sK2),X1)
      | ~ r1_orders_2(sK0,k1_yellow_0(sK0,sK1),X1)
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ m1_subset_1(k1_yellow_0(sK0,sK2),u1_struct_0(sK0))
      | ~ m1_subset_1(k1_yellow_0(sK0,sK1),u1_struct_0(sK0))
      | ~ l1_orders_2(sK0)
      | ~ v5_orders_2(sK0) ) ),
    inference(superposition,[],[f77,f86])).
%------------------------------------------------------------------------------
