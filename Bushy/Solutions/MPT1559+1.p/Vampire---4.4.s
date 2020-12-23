%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : yellow_0__t37_yellow_0.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:41:41 EDT 2019

% Result     : Theorem 162.73s
% Output     : Refutation 162.73s
% Verified   : 
% Statistics : Number of formulae       :  230 (5210 expanded)
%              Number of leaves         :   15 (1592 expanded)
%              Depth                    :   42
%              Number of atoms          : 1272 (35835 expanded)
%              Number of equality atoms :  100 (4710 expanded)
%              Maximal formula depth    :   17 (   7 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f139323,plain,(
    $false ),
    inference(subsumption_resolution,[],[f139322,f42654])).

fof(f42654,plain,(
    m1_subset_1(sK3(sK0,k2_yellow_0(sK0,sK1),k2_yellow_0(sK0,sK2),k2_yellow_0(sK0,k2_xboole_0(sK1,sK2))),u1_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f42653,f12105])).

fof(f12105,plain,(
    r1_lattice3(sK0,sK2,k2_yellow_0(sK0,k2_xboole_0(sK1,sK2))) ),
    inference(forward_demodulation,[],[f12104,f79])).

fof(f79,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/yellow_0__t37_yellow_0.p',commutativity_k2_xboole_0)).

fof(f12104,plain,(
    r1_lattice3(sK0,sK2,k2_yellow_0(sK0,k2_xboole_0(sK2,sK1))) ),
    inference(subsumption_resolution,[],[f12083,f75])).

fof(f75,plain,(
    r2_yellow_0(sK0,sK2) ),
    inference(cnf_transformation,[],[f61])).

fof(f61,plain,
    ( k2_yellow_0(sK0,k2_xboole_0(sK1,sK2)) != k11_lattice3(sK0,k2_yellow_0(sK0,sK1),k2_yellow_0(sK0,sK2))
    & r2_yellow_0(sK0,k2_xboole_0(sK1,sK2))
    & r2_yellow_0(sK0,sK2)
    & r2_yellow_0(sK0,sK1)
    & l1_orders_2(sK0)
    & v5_orders_2(sK0)
    & v4_orders_2(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f39,f60,f59])).

fof(f59,plain,
    ( ? [X0] :
        ( ? [X1,X2] :
            ( k2_yellow_0(X0,k2_xboole_0(X1,X2)) != k11_lattice3(X0,k2_yellow_0(X0,X1),k2_yellow_0(X0,X2))
            & r2_yellow_0(X0,k2_xboole_0(X1,X2))
            & r2_yellow_0(X0,X2)
            & r2_yellow_0(X0,X1) )
        & l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0) )
   => ( ? [X2,X1] :
          ( k2_yellow_0(sK0,k2_xboole_0(X1,X2)) != k11_lattice3(sK0,k2_yellow_0(sK0,X1),k2_yellow_0(sK0,X2))
          & r2_yellow_0(sK0,k2_xboole_0(X1,X2))
          & r2_yellow_0(sK0,X2)
          & r2_yellow_0(sK0,X1) )
      & l1_orders_2(sK0)
      & v5_orders_2(sK0)
      & v4_orders_2(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f60,plain,(
    ! [X0] :
      ( ? [X1,X2] :
          ( k2_yellow_0(X0,k2_xboole_0(X1,X2)) != k11_lattice3(X0,k2_yellow_0(X0,X1),k2_yellow_0(X0,X2))
          & r2_yellow_0(X0,k2_xboole_0(X1,X2))
          & r2_yellow_0(X0,X2)
          & r2_yellow_0(X0,X1) )
     => ( k2_yellow_0(X0,k2_xboole_0(sK1,sK2)) != k11_lattice3(X0,k2_yellow_0(X0,sK1),k2_yellow_0(X0,sK2))
        & r2_yellow_0(X0,k2_xboole_0(sK1,sK2))
        & r2_yellow_0(X0,sK2)
        & r2_yellow_0(X0,sK1) ) ) ),
    introduced(choice_axiom,[])).

fof(f39,plain,(
    ? [X0] :
      ( ? [X1,X2] :
          ( k2_yellow_0(X0,k2_xboole_0(X1,X2)) != k11_lattice3(X0,k2_yellow_0(X0,X1),k2_yellow_0(X0,X2))
          & r2_yellow_0(X0,k2_xboole_0(X1,X2))
          & r2_yellow_0(X0,X2)
          & r2_yellow_0(X0,X1) )
      & l1_orders_2(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0) ) ),
    inference(flattening,[],[f38])).

fof(f38,plain,(
    ? [X0] :
      ( ? [X1,X2] :
          ( k2_yellow_0(X0,k2_xboole_0(X1,X2)) != k11_lattice3(X0,k2_yellow_0(X0,X1),k2_yellow_0(X0,X2))
          & r2_yellow_0(X0,k2_xboole_0(X1,X2))
          & r2_yellow_0(X0,X2)
          & r2_yellow_0(X0,X1) )
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
            ( ( r2_yellow_0(X0,k2_xboole_0(X1,X2))
              & r2_yellow_0(X0,X2)
              & r2_yellow_0(X0,X1) )
           => k2_yellow_0(X0,k2_xboole_0(X1,X2)) = k11_lattice3(X0,k2_yellow_0(X0,X1),k2_yellow_0(X0,X2)) ) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0) )
     => ! [X1,X2] :
          ( ( r2_yellow_0(X0,k2_xboole_0(X1,X2))
            & r2_yellow_0(X0,X2)
            & r2_yellow_0(X0,X1) )
         => k2_yellow_0(X0,k2_xboole_0(X1,X2)) = k11_lattice3(X0,k2_yellow_0(X0,X1),k2_yellow_0(X0,X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/yellow_0__t37_yellow_0.p',t37_yellow_0)).

fof(f12083,plain,
    ( ~ r2_yellow_0(sK0,sK2)
    | r1_lattice3(sK0,sK2,k2_yellow_0(sK0,k2_xboole_0(sK2,sK1))) ),
    inference(resolution,[],[f11987,f76])).

fof(f76,plain,(
    r2_yellow_0(sK0,k2_xboole_0(sK1,sK2)) ),
    inference(cnf_transformation,[],[f61])).

fof(f11987,plain,(
    ! [X0,X1] :
      ( ~ r2_yellow_0(sK0,k2_xboole_0(X1,X0))
      | ~ r2_yellow_0(sK0,X0)
      | r1_lattice3(sK0,X0,k2_yellow_0(sK0,k2_xboole_0(X0,X1))) ) ),
    inference(superposition,[],[f10062,f79])).

fof(f10062,plain,(
    ! [X0,X1] :
      ( ~ r2_yellow_0(sK0,k2_xboole_0(X0,X1))
      | ~ r2_yellow_0(sK0,X0)
      | r1_lattice3(sK0,X0,k2_yellow_0(sK0,k2_xboole_0(X0,X1))) ) ),
    inference(resolution,[],[f10037,f103])).

fof(f103,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/yellow_0__t37_yellow_0.p',t7_xboole_1)).

fof(f10037,plain,(
    ! [X2,X3] :
      ( ~ r1_tarski(X2,X3)
      | ~ r2_yellow_0(sK0,X2)
      | ~ r2_yellow_0(sK0,X3)
      | r1_lattice3(sK0,X2,k2_yellow_0(sK0,X3)) ) ),
    inference(subsumption_resolution,[],[f10036,f73])).

fof(f73,plain,(
    l1_orders_2(sK0) ),
    inference(cnf_transformation,[],[f61])).

fof(f10036,plain,(
    ! [X2,X3] :
      ( r1_lattice3(sK0,X2,k2_yellow_0(sK0,X3))
      | ~ r2_yellow_0(sK0,X2)
      | ~ r2_yellow_0(sK0,X3)
      | ~ r1_tarski(X2,X3)
      | ~ l1_orders_2(sK0) ) ),
    inference(subsumption_resolution,[],[f10034,f173])).

fof(f173,plain,(
    ! [X26] : m1_subset_1(k2_yellow_0(sK0,X26),u1_struct_0(sK0)) ),
    inference(resolution,[],[f73,f93])).

fof(f93,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_yellow_0(X0,X1),u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_yellow_0(X0,X1),u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( l1_orders_2(X0)
     => m1_subset_1(k2_yellow_0(X0,X1),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/yellow_0__t37_yellow_0.p',dt_k2_yellow_0)).

fof(f10034,plain,(
    ! [X2,X3] :
      ( r1_lattice3(sK0,X2,k2_yellow_0(sK0,X3))
      | ~ m1_subset_1(k2_yellow_0(sK0,X3),u1_struct_0(sK0))
      | ~ r2_yellow_0(sK0,X2)
      | ~ r2_yellow_0(sK0,X3)
      | ~ r1_tarski(X2,X3)
      | ~ l1_orders_2(sK0) ) ),
    inference(duplicate_literal_removal,[],[f10007])).

fof(f10007,plain,(
    ! [X2,X3] :
      ( r1_lattice3(sK0,X2,k2_yellow_0(sK0,X3))
      | ~ m1_subset_1(k2_yellow_0(sK0,X3),u1_struct_0(sK0))
      | ~ r2_yellow_0(sK0,X2)
      | ~ r2_yellow_0(sK0,X3)
      | ~ r2_yellow_0(sK0,X2)
      | ~ r1_tarski(X2,X3)
      | ~ l1_orders_2(sK0) ) ),
    inference(resolution,[],[f3108,f102])).

fof(f102,plain,(
    ! [X2,X0,X1] :
      ( r1_orders_2(X0,k2_yellow_0(X0,X2),k2_yellow_0(X0,X1))
      | ~ r2_yellow_0(X0,X2)
      | ~ r2_yellow_0(X0,X1)
      | ~ r1_tarski(X1,X2)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f49,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( r1_orders_2(X0,k2_yellow_0(X0,X2),k2_yellow_0(X0,X1))
          | ~ r2_yellow_0(X0,X2)
          | ~ r2_yellow_0(X0,X1)
          | ~ r1_tarski(X1,X2) )
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f48])).

fof(f48,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( r1_orders_2(X0,k2_yellow_0(X0,X2),k2_yellow_0(X0,X1))
          | ~ r2_yellow_0(X0,X2)
          | ~ r2_yellow_0(X0,X1)
          | ~ r1_tarski(X1,X2) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f26])).

fof(f26,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1,X2] :
          ( ( r2_yellow_0(X0,X2)
            & r2_yellow_0(X0,X1)
            & r1_tarski(X1,X2) )
         => r1_orders_2(X0,k2_yellow_0(X0,X2),k2_yellow_0(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/yellow_0__t37_yellow_0.p',t35_yellow_0)).

fof(f3108,plain,(
    ! [X15,X16] :
      ( ~ r1_orders_2(sK0,X16,k2_yellow_0(sK0,X15))
      | r1_lattice3(sK0,X15,X16)
      | ~ m1_subset_1(X16,u1_struct_0(sK0))
      | ~ r2_yellow_0(sK0,X15) ) ),
    inference(subsumption_resolution,[],[f3107,f72])).

fof(f72,plain,(
    v5_orders_2(sK0) ),
    inference(cnf_transformation,[],[f61])).

fof(f3107,plain,(
    ! [X15,X16] :
      ( r1_lattice3(sK0,X15,X16)
      | ~ r1_orders_2(sK0,X16,k2_yellow_0(sK0,X15))
      | ~ m1_subset_1(X16,u1_struct_0(sK0))
      | ~ r2_yellow_0(sK0,X15)
      | ~ v5_orders_2(sK0) ) ),
    inference(subsumption_resolution,[],[f3106,f73])).

fof(f3106,plain,(
    ! [X15,X16] :
      ( r1_lattice3(sK0,X15,X16)
      | ~ r1_orders_2(sK0,X16,k2_yellow_0(sK0,X15))
      | ~ m1_subset_1(X16,u1_struct_0(sK0))
      | ~ r2_yellow_0(sK0,X15)
      | ~ l1_orders_2(sK0)
      | ~ v5_orders_2(sK0) ) ),
    inference(subsumption_resolution,[],[f3097,f173])).

fof(f3097,plain,(
    ! [X15,X16] :
      ( r1_lattice3(sK0,X15,X16)
      | ~ r1_orders_2(sK0,X16,k2_yellow_0(sK0,X15))
      | ~ m1_subset_1(k2_yellow_0(sK0,X15),u1_struct_0(sK0))
      | ~ m1_subset_1(X16,u1_struct_0(sK0))
      | ~ r2_yellow_0(sK0,X15)
      | ~ l1_orders_2(sK0)
      | ~ v5_orders_2(sK0) ) ),
    inference(duplicate_literal_removal,[],[f3092])).

fof(f3092,plain,(
    ! [X15,X16] :
      ( r1_lattice3(sK0,X15,X16)
      | ~ r1_orders_2(sK0,X16,k2_yellow_0(sK0,X15))
      | ~ m1_subset_1(k2_yellow_0(sK0,X15),u1_struct_0(sK0))
      | ~ m1_subset_1(X16,u1_struct_0(sK0))
      | ~ r2_yellow_0(sK0,X15)
      | ~ m1_subset_1(k2_yellow_0(sK0,X15),u1_struct_0(sK0))
      | ~ l1_orders_2(sK0)
      | ~ v5_orders_2(sK0) ) ),
    inference(resolution,[],[f124,f121])).

fof(f121,plain,(
    ! [X2,X0] :
      ( r1_lattice3(X0,X2,k2_yellow_0(X0,X2))
      | ~ r2_yellow_0(X0,X2)
      | ~ m1_subset_1(k2_yellow_0(X0,X2),u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(equality_resolution,[],[f94])).

fof(f94,plain,(
    ! [X2,X0,X1] :
      ( r1_lattice3(X0,X2,X1)
      | ~ r2_yellow_0(X0,X2)
      | k2_yellow_0(X0,X2) != X1
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f65])).

fof(f65,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( r2_yellow_0(X0,X2)
                  & k2_yellow_0(X0,X2) = X1 )
                | ( ~ r1_orders_2(X0,sK4(X0,X1,X2),X1)
                  & r1_lattice3(X0,X2,sK4(X0,X1,X2))
                  & m1_subset_1(sK4(X0,X1,X2),u1_struct_0(X0)) )
                | ~ r1_lattice3(X0,X2,X1) )
              & ( ( ! [X4] :
                      ( r1_orders_2(X0,X4,X1)
                      | ~ r1_lattice3(X0,X2,X4)
                      | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                  & r1_lattice3(X0,X2,X1) )
                | ~ r2_yellow_0(X0,X2)
                | k2_yellow_0(X0,X2) != X1 ) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f47,f64])).

fof(f64,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r1_orders_2(X0,X3,X1)
          & r1_lattice3(X0,X2,X3)
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ~ r1_orders_2(X0,sK4(X0,X1,X2),X1)
        & r1_lattice3(X0,X2,sK4(X0,X1,X2))
        & m1_subset_1(sK4(X0,X1,X2),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f47,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( r2_yellow_0(X0,X2)
                  & k2_yellow_0(X0,X2) = X1 )
                | ? [X3] :
                    ( ~ r1_orders_2(X0,X3,X1)
                    & r1_lattice3(X0,X2,X3)
                    & m1_subset_1(X3,u1_struct_0(X0)) )
                | ~ r1_lattice3(X0,X2,X1) )
              & ( ( ! [X4] :
                      ( r1_orders_2(X0,X4,X1)
                      | ~ r1_lattice3(X0,X2,X4)
                      | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                  & r1_lattice3(X0,X2,X1) )
                | ~ r2_yellow_0(X0,X2)
                | k2_yellow_0(X0,X2) != X1 ) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(flattening,[],[f46])).

fof(f46,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( r2_yellow_0(X0,X2)
                  & k2_yellow_0(X0,X2) = X1 )
                | ? [X3] :
                    ( ~ r1_orders_2(X0,X3,X1)
                    & r1_lattice3(X0,X2,X3)
                    & m1_subset_1(X3,u1_struct_0(X0)) )
                | ~ r1_lattice3(X0,X2,X1) )
              & ( ( ! [X4] :
                      ( r1_orders_2(X0,X4,X1)
                      | ~ r1_lattice3(X0,X2,X4)
                      | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                  & r1_lattice3(X0,X2,X1) )
                | ~ r2_yellow_0(X0,X2)
                | k2_yellow_0(X0,X2) != X1 ) )
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
                     => ( r1_lattice3(X0,X2,X3)
                       => r1_orders_2(X0,X3,X1) ) )
                  & r1_lattice3(X0,X2,X1) )
               => ( r2_yellow_0(X0,X2)
                  & k2_yellow_0(X0,X2) = X1 ) )
              & ( ( r2_yellow_0(X0,X2)
                  & k2_yellow_0(X0,X2) = X1 )
               => ( ! [X4] :
                      ( m1_subset_1(X4,u1_struct_0(X0))
                     => ( r1_lattice3(X0,X2,X4)
                       => r1_orders_2(X0,X4,X1) ) )
                  & r1_lattice3(X0,X2,X1) ) ) ) ) ) ),
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
                     => ( r1_lattice3(X0,X2,X3)
                       => r1_orders_2(X0,X3,X1) ) )
                  & r1_lattice3(X0,X2,X1) )
               => ( r2_yellow_0(X0,X2)
                  & k2_yellow_0(X0,X2) = X1 ) )
              & ( ( r2_yellow_0(X0,X2)
                  & k2_yellow_0(X0,X2) = X1 )
               => ( ! [X3] :
                      ( m1_subset_1(X3,u1_struct_0(X0))
                     => ( r1_lattice3(X0,X2,X3)
                       => r1_orders_2(X0,X3,X1) ) )
                  & r1_lattice3(X0,X2,X1) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/yellow_0__t37_yellow_0.p',t31_yellow_0)).

fof(f124,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_lattice3(sK0,X0,X2)
      | r1_lattice3(sK0,X0,X1)
      | ~ r1_orders_2(sK0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(sK0))
      | ~ m1_subset_1(X1,u1_struct_0(sK0)) ) ),
    inference(subsumption_resolution,[],[f122,f73])).

fof(f122,plain,(
    ! [X2,X0,X1] :
      ( r1_lattice3(sK0,X0,X1)
      | ~ r1_lattice3(sK0,X0,X2)
      | ~ r1_orders_2(sK0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(sK0))
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ l1_orders_2(sK0) ) ),
    inference(resolution,[],[f71,f105])).

fof(f105,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_lattice3(X0,X3,X1)
      | ~ r1_lattice3(X0,X3,X2)
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
    file('/export/starexec/sandbox2/benchmark/yellow_0__t37_yellow_0.p',t4_yellow_0)).

fof(f71,plain,(
    v4_orders_2(sK0) ),
    inference(cnf_transformation,[],[f61])).

fof(f42653,plain,
    ( m1_subset_1(sK3(sK0,k2_yellow_0(sK0,sK1),k2_yellow_0(sK0,sK2),k2_yellow_0(sK0,k2_xboole_0(sK1,sK2))),u1_struct_0(sK0))
    | ~ r1_lattice3(sK0,sK2,k2_yellow_0(sK0,k2_xboole_0(sK1,sK2))) ),
    inference(subsumption_resolution,[],[f33831,f173])).

fof(f33831,plain,
    ( m1_subset_1(sK3(sK0,k2_yellow_0(sK0,sK1),k2_yellow_0(sK0,sK2),k2_yellow_0(sK0,k2_xboole_0(sK1,sK2))),u1_struct_0(sK0))
    | ~ m1_subset_1(k2_yellow_0(sK0,k2_xboole_0(sK1,sK2)),u1_struct_0(sK0))
    | ~ r1_lattice3(sK0,sK2,k2_yellow_0(sK0,k2_xboole_0(sK1,sK2))) ),
    inference(trivial_inequality_removal,[],[f33814])).

fof(f33814,plain,
    ( k2_yellow_0(sK0,k2_xboole_0(sK1,sK2)) != k2_yellow_0(sK0,k2_xboole_0(sK1,sK2))
    | m1_subset_1(sK3(sK0,k2_yellow_0(sK0,sK1),k2_yellow_0(sK0,sK2),k2_yellow_0(sK0,k2_xboole_0(sK1,sK2))),u1_struct_0(sK0))
    | ~ m1_subset_1(k2_yellow_0(sK0,k2_xboole_0(sK1,sK2)),u1_struct_0(sK0))
    | ~ r1_lattice3(sK0,sK2,k2_yellow_0(sK0,k2_xboole_0(sK1,sK2))) ),
    inference(resolution,[],[f7625,f2103])).

fof(f2103,plain,(
    r1_orders_2(sK0,k2_yellow_0(sK0,k2_xboole_0(sK1,sK2)),k2_yellow_0(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f2086,f173])).

fof(f2086,plain,
    ( r1_orders_2(sK0,k2_yellow_0(sK0,k2_xboole_0(sK1,sK2)),k2_yellow_0(sK0,sK1))
    | ~ m1_subset_1(k2_yellow_0(sK0,k2_xboole_0(sK1,sK2)),u1_struct_0(sK0)) ),
    inference(resolution,[],[f2048,f201])).

fof(f201,plain,(
    ! [X2] :
      ( ~ r1_lattice3(sK0,sK1,X2)
      | r1_orders_2(sK0,X2,k2_yellow_0(sK0,sK1))
      | ~ m1_subset_1(X2,u1_struct_0(sK0)) ) ),
    inference(subsumption_resolution,[],[f200,f72])).

fof(f200,plain,(
    ! [X2] :
      ( r1_orders_2(sK0,X2,k2_yellow_0(sK0,sK1))
      | ~ r1_lattice3(sK0,sK1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(sK0))
      | ~ v5_orders_2(sK0) ) ),
    inference(subsumption_resolution,[],[f199,f73])).

fof(f199,plain,(
    ! [X2] :
      ( r1_orders_2(sK0,X2,k2_yellow_0(sK0,sK1))
      | ~ r1_lattice3(sK0,sK1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(sK0))
      | ~ l1_orders_2(sK0)
      | ~ v5_orders_2(sK0) ) ),
    inference(subsumption_resolution,[],[f193,f173])).

fof(f193,plain,(
    ! [X2] :
      ( r1_orders_2(sK0,X2,k2_yellow_0(sK0,sK1))
      | ~ r1_lattice3(sK0,sK1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(sK0))
      | ~ m1_subset_1(k2_yellow_0(sK0,sK1),u1_struct_0(sK0))
      | ~ l1_orders_2(sK0)
      | ~ v5_orders_2(sK0) ) ),
    inference(resolution,[],[f74,f120])).

fof(f120,plain,(
    ! [X4,X2,X0] :
      ( r1_orders_2(X0,X4,k2_yellow_0(X0,X2))
      | ~ r1_lattice3(X0,X2,X4)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ r2_yellow_0(X0,X2)
      | ~ m1_subset_1(k2_yellow_0(X0,X2),u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(equality_resolution,[],[f95])).

fof(f95,plain,(
    ! [X4,X2,X0,X1] :
      ( r1_orders_2(X0,X4,X1)
      | ~ r1_lattice3(X0,X2,X4)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ r2_yellow_0(X0,X2)
      | k2_yellow_0(X0,X2) != X1
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f65])).

fof(f74,plain,(
    r2_yellow_0(sK0,sK1) ),
    inference(cnf_transformation,[],[f61])).

fof(f2048,plain,(
    r1_lattice3(sK0,sK1,k2_yellow_0(sK0,k2_xboole_0(sK1,sK2))) ),
    inference(resolution,[],[f2046,f76])).

fof(f2046,plain,(
    ! [X0] :
      ( ~ r2_yellow_0(sK0,k2_xboole_0(sK1,X0))
      | r1_lattice3(sK0,sK1,k2_yellow_0(sK0,k2_xboole_0(sK1,X0))) ) ),
    inference(resolution,[],[f2021,f103])).

fof(f2021,plain,(
    ! [X1] :
      ( ~ r1_tarski(sK1,X1)
      | ~ r2_yellow_0(sK0,X1)
      | r1_lattice3(sK0,sK1,k2_yellow_0(sK0,X1)) ) ),
    inference(subsumption_resolution,[],[f2020,f73])).

fof(f2020,plain,(
    ! [X1] :
      ( r1_lattice3(sK0,sK1,k2_yellow_0(sK0,X1))
      | ~ r2_yellow_0(sK0,X1)
      | ~ r1_tarski(sK1,X1)
      | ~ l1_orders_2(sK0) ) ),
    inference(subsumption_resolution,[],[f2019,f74])).

fof(f2019,plain,(
    ! [X1] :
      ( r1_lattice3(sK0,sK1,k2_yellow_0(sK0,X1))
      | ~ r2_yellow_0(sK0,X1)
      | ~ r2_yellow_0(sK0,sK1)
      | ~ r1_tarski(sK1,X1)
      | ~ l1_orders_2(sK0) ) ),
    inference(subsumption_resolution,[],[f2006,f173])).

fof(f2006,plain,(
    ! [X1] :
      ( r1_lattice3(sK0,sK1,k2_yellow_0(sK0,X1))
      | ~ m1_subset_1(k2_yellow_0(sK0,X1),u1_struct_0(sK0))
      | ~ r2_yellow_0(sK0,X1)
      | ~ r2_yellow_0(sK0,sK1)
      | ~ r1_tarski(sK1,X1)
      | ~ l1_orders_2(sK0) ) ),
    inference(resolution,[],[f442,f102])).

fof(f442,plain,(
    ! [X0] :
      ( ~ r1_orders_2(sK0,X0,k2_yellow_0(sK0,sK1))
      | r1_lattice3(sK0,sK1,X0)
      | ~ m1_subset_1(X0,u1_struct_0(sK0)) ) ),
    inference(subsumption_resolution,[],[f441,f71])).

fof(f441,plain,(
    ! [X0] :
      ( r1_lattice3(sK0,sK1,X0)
      | ~ r1_orders_2(sK0,X0,k2_yellow_0(sK0,sK1))
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ v4_orders_2(sK0) ) ),
    inference(subsumption_resolution,[],[f440,f73])).

fof(f440,plain,(
    ! [X0] :
      ( r1_lattice3(sK0,sK1,X0)
      | ~ r1_orders_2(sK0,X0,k2_yellow_0(sK0,sK1))
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ l1_orders_2(sK0)
      | ~ v4_orders_2(sK0) ) ),
    inference(subsumption_resolution,[],[f432,f173])).

fof(f432,plain,(
    ! [X0] :
      ( r1_lattice3(sK0,sK1,X0)
      | ~ r1_orders_2(sK0,X0,k2_yellow_0(sK0,sK1))
      | ~ m1_subset_1(k2_yellow_0(sK0,sK1),u1_struct_0(sK0))
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ l1_orders_2(sK0)
      | ~ v4_orders_2(sK0) ) ),
    inference(resolution,[],[f198,f105])).

fof(f198,plain,(
    r1_lattice3(sK0,sK1,k2_yellow_0(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f197,f72])).

fof(f197,plain,
    ( r1_lattice3(sK0,sK1,k2_yellow_0(sK0,sK1))
    | ~ v5_orders_2(sK0) ),
    inference(subsumption_resolution,[],[f196,f73])).

fof(f196,plain,
    ( r1_lattice3(sK0,sK1,k2_yellow_0(sK0,sK1))
    | ~ l1_orders_2(sK0)
    | ~ v5_orders_2(sK0) ),
    inference(subsumption_resolution,[],[f192,f173])).

fof(f192,plain,
    ( r1_lattice3(sK0,sK1,k2_yellow_0(sK0,sK1))
    | ~ m1_subset_1(k2_yellow_0(sK0,sK1),u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | ~ v5_orders_2(sK0) ),
    inference(resolution,[],[f74,f121])).

fof(f7625,plain,(
    ! [X0] :
      ( ~ r1_orders_2(sK0,X0,k2_yellow_0(sK0,sK1))
      | k2_yellow_0(sK0,k2_xboole_0(sK1,sK2)) != X0
      | m1_subset_1(sK3(sK0,k2_yellow_0(sK0,sK1),k2_yellow_0(sK0,sK2),X0),u1_struct_0(sK0))
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ r1_lattice3(sK0,sK2,X0) ) ),
    inference(subsumption_resolution,[],[f7624,f72])).

fof(f7624,plain,(
    ! [X0] :
      ( m1_subset_1(sK3(sK0,k2_yellow_0(sK0,sK1),k2_yellow_0(sK0,sK2),X0),u1_struct_0(sK0))
      | k2_yellow_0(sK0,k2_xboole_0(sK1,sK2)) != X0
      | ~ r1_orders_2(sK0,X0,k2_yellow_0(sK0,sK1))
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ r1_lattice3(sK0,sK2,X0)
      | ~ v5_orders_2(sK0) ) ),
    inference(subsumption_resolution,[],[f7623,f73])).

fof(f7623,plain,(
    ! [X0] :
      ( m1_subset_1(sK3(sK0,k2_yellow_0(sK0,sK1),k2_yellow_0(sK0,sK2),X0),u1_struct_0(sK0))
      | k2_yellow_0(sK0,k2_xboole_0(sK1,sK2)) != X0
      | ~ r1_orders_2(sK0,X0,k2_yellow_0(sK0,sK1))
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ r1_lattice3(sK0,sK2,X0)
      | ~ l1_orders_2(sK0)
      | ~ v5_orders_2(sK0) ) ),
    inference(subsumption_resolution,[],[f7622,f173])).

fof(f7622,plain,(
    ! [X0] :
      ( m1_subset_1(sK3(sK0,k2_yellow_0(sK0,sK1),k2_yellow_0(sK0,sK2),X0),u1_struct_0(sK0))
      | k2_yellow_0(sK0,k2_xboole_0(sK1,sK2)) != X0
      | ~ r1_orders_2(sK0,X0,k2_yellow_0(sK0,sK1))
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ r1_lattice3(sK0,sK2,X0)
      | ~ m1_subset_1(k2_yellow_0(sK0,sK2),u1_struct_0(sK0))
      | ~ l1_orders_2(sK0)
      | ~ v5_orders_2(sK0) ) ),
    inference(subsumption_resolution,[],[f7611,f75])).

fof(f7611,plain,(
    ! [X0] :
      ( m1_subset_1(sK3(sK0,k2_yellow_0(sK0,sK1),k2_yellow_0(sK0,sK2),X0),u1_struct_0(sK0))
      | k2_yellow_0(sK0,k2_xboole_0(sK1,sK2)) != X0
      | ~ r1_orders_2(sK0,X0,k2_yellow_0(sK0,sK1))
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ r1_lattice3(sK0,sK2,X0)
      | ~ r2_yellow_0(sK0,sK2)
      | ~ m1_subset_1(k2_yellow_0(sK0,sK2),u1_struct_0(sK0))
      | ~ l1_orders_2(sK0)
      | ~ v5_orders_2(sK0) ) ),
    inference(duplicate_literal_removal,[],[f7596])).

fof(f7596,plain,(
    ! [X0] :
      ( m1_subset_1(sK3(sK0,k2_yellow_0(sK0,sK1),k2_yellow_0(sK0,sK2),X0),u1_struct_0(sK0))
      | k2_yellow_0(sK0,k2_xboole_0(sK1,sK2)) != X0
      | ~ r1_orders_2(sK0,X0,k2_yellow_0(sK0,sK1))
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ r1_lattice3(sK0,sK2,X0)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ r2_yellow_0(sK0,sK2)
      | ~ m1_subset_1(k2_yellow_0(sK0,sK2),u1_struct_0(sK0))
      | ~ l1_orders_2(sK0)
      | ~ v5_orders_2(sK0) ) ),
    inference(resolution,[],[f251,f120])).

fof(f251,plain,(
    ! [X0] :
      ( ~ r1_orders_2(sK0,X0,k2_yellow_0(sK0,sK2))
      | m1_subset_1(sK3(sK0,k2_yellow_0(sK0,sK1),k2_yellow_0(sK0,sK2),X0),u1_struct_0(sK0))
      | k2_yellow_0(sK0,k2_xboole_0(sK1,sK2)) != X0
      | ~ r1_orders_2(sK0,X0,k2_yellow_0(sK0,sK1))
      | ~ m1_subset_1(X0,u1_struct_0(sK0)) ) ),
    inference(subsumption_resolution,[],[f250,f72])).

fof(f250,plain,(
    ! [X0] :
      ( k2_yellow_0(sK0,k2_xboole_0(sK1,sK2)) != X0
      | m1_subset_1(sK3(sK0,k2_yellow_0(sK0,sK1),k2_yellow_0(sK0,sK2),X0),u1_struct_0(sK0))
      | ~ r1_orders_2(sK0,X0,k2_yellow_0(sK0,sK2))
      | ~ r1_orders_2(sK0,X0,k2_yellow_0(sK0,sK1))
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ v5_orders_2(sK0) ) ),
    inference(subsumption_resolution,[],[f249,f73])).

fof(f249,plain,(
    ! [X0] :
      ( k2_yellow_0(sK0,k2_xboole_0(sK1,sK2)) != X0
      | m1_subset_1(sK3(sK0,k2_yellow_0(sK0,sK1),k2_yellow_0(sK0,sK2),X0),u1_struct_0(sK0))
      | ~ r1_orders_2(sK0,X0,k2_yellow_0(sK0,sK2))
      | ~ r1_orders_2(sK0,X0,k2_yellow_0(sK0,sK1))
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ l1_orders_2(sK0)
      | ~ v5_orders_2(sK0) ) ),
    inference(subsumption_resolution,[],[f248,f173])).

fof(f248,plain,(
    ! [X0] :
      ( k2_yellow_0(sK0,k2_xboole_0(sK1,sK2)) != X0
      | m1_subset_1(sK3(sK0,k2_yellow_0(sK0,sK1),k2_yellow_0(sK0,sK2),X0),u1_struct_0(sK0))
      | ~ r1_orders_2(sK0,X0,k2_yellow_0(sK0,sK2))
      | ~ r1_orders_2(sK0,X0,k2_yellow_0(sK0,sK1))
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ m1_subset_1(k2_yellow_0(sK0,sK1),u1_struct_0(sK0))
      | ~ l1_orders_2(sK0)
      | ~ v5_orders_2(sK0) ) ),
    inference(subsumption_resolution,[],[f232,f173])).

fof(f232,plain,(
    ! [X0] :
      ( k2_yellow_0(sK0,k2_xboole_0(sK1,sK2)) != X0
      | m1_subset_1(sK3(sK0,k2_yellow_0(sK0,sK1),k2_yellow_0(sK0,sK2),X0),u1_struct_0(sK0))
      | ~ r1_orders_2(sK0,X0,k2_yellow_0(sK0,sK2))
      | ~ r1_orders_2(sK0,X0,k2_yellow_0(sK0,sK1))
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ m1_subset_1(k2_yellow_0(sK0,sK2),u1_struct_0(sK0))
      | ~ m1_subset_1(k2_yellow_0(sK0,sK1),u1_struct_0(sK0))
      | ~ l1_orders_2(sK0)
      | ~ v5_orders_2(sK0) ) ),
    inference(superposition,[],[f77,f85])).

fof(f85,plain,(
    ! [X2,X0,X3,X1] :
      ( k11_lattice3(X0,X1,X2) = X3
      | m1_subset_1(sK3(X0,X1,X2,X3),u1_struct_0(X0))
      | ~ r1_orders_2(X0,X3,X2)
      | ~ r1_orders_2(X0,X3,X1)
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
                  ( ( ( ( r2_yellow_0(X0,k2_tarski(X1,X2))
                        & k11_lattice3(X0,X1,X2) = X3 )
                      | ( ~ r1_orders_2(X0,sK3(X0,X1,X2,X3),X3)
                        & r1_orders_2(X0,sK3(X0,X1,X2,X3),X2)
                        & r1_orders_2(X0,sK3(X0,X1,X2,X3),X1)
                        & m1_subset_1(sK3(X0,X1,X2,X3),u1_struct_0(X0)) )
                      | ~ r1_orders_2(X0,X3,X2)
                      | ~ r1_orders_2(X0,X3,X1) )
                    & ( ( ! [X5] :
                            ( r1_orders_2(X0,X5,X3)
                            | ~ r1_orders_2(X0,X5,X2)
                            | ~ r1_orders_2(X0,X5,X1)
                            | ~ m1_subset_1(X5,u1_struct_0(X0)) )
                        & r1_orders_2(X0,X3,X2)
                        & r1_orders_2(X0,X3,X1) )
                      | ~ r2_yellow_0(X0,k2_tarski(X1,X2))
                      | k11_lattice3(X0,X1,X2) != X3 ) )
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f44,f62])).

fof(f62,plain,(
    ! [X3,X2,X1,X0] :
      ( ? [X4] :
          ( ~ r1_orders_2(X0,X4,X3)
          & r1_orders_2(X0,X4,X2)
          & r1_orders_2(X0,X4,X1)
          & m1_subset_1(X4,u1_struct_0(X0)) )
     => ( ~ r1_orders_2(X0,sK3(X0,X1,X2,X3),X3)
        & r1_orders_2(X0,sK3(X0,X1,X2,X3),X2)
        & r1_orders_2(X0,sK3(X0,X1,X2,X3),X1)
        & m1_subset_1(sK3(X0,X1,X2,X3),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f44,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ( ( r2_yellow_0(X0,k2_tarski(X1,X2))
                        & k11_lattice3(X0,X1,X2) = X3 )
                      | ? [X4] :
                          ( ~ r1_orders_2(X0,X4,X3)
                          & r1_orders_2(X0,X4,X2)
                          & r1_orders_2(X0,X4,X1)
                          & m1_subset_1(X4,u1_struct_0(X0)) )
                      | ~ r1_orders_2(X0,X3,X2)
                      | ~ r1_orders_2(X0,X3,X1) )
                    & ( ( ! [X5] :
                            ( r1_orders_2(X0,X5,X3)
                            | ~ r1_orders_2(X0,X5,X2)
                            | ~ r1_orders_2(X0,X5,X1)
                            | ~ m1_subset_1(X5,u1_struct_0(X0)) )
                        & r1_orders_2(X0,X3,X2)
                        & r1_orders_2(X0,X3,X1) )
                      | ~ r2_yellow_0(X0,k2_tarski(X1,X2))
                      | k11_lattice3(X0,X1,X2) != X3 ) )
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
                  ( ( ( ( r2_yellow_0(X0,k2_tarski(X1,X2))
                        & k11_lattice3(X0,X1,X2) = X3 )
                      | ? [X4] :
                          ( ~ r1_orders_2(X0,X4,X3)
                          & r1_orders_2(X0,X4,X2)
                          & r1_orders_2(X0,X4,X1)
                          & m1_subset_1(X4,u1_struct_0(X0)) )
                      | ~ r1_orders_2(X0,X3,X2)
                      | ~ r1_orders_2(X0,X3,X1) )
                    & ( ( ! [X5] :
                            ( r1_orders_2(X0,X5,X3)
                            | ~ r1_orders_2(X0,X5,X2)
                            | ~ r1_orders_2(X0,X5,X1)
                            | ~ m1_subset_1(X5,u1_struct_0(X0)) )
                        & r1_orders_2(X0,X3,X2)
                        & r1_orders_2(X0,X3,X1) )
                      | ~ r2_yellow_0(X0,k2_tarski(X1,X2))
                      | k11_lattice3(X0,X1,X2) != X3 ) )
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
                           => ( ( r1_orders_2(X0,X4,X2)
                                & r1_orders_2(X0,X4,X1) )
                             => r1_orders_2(X0,X4,X3) ) )
                        & r1_orders_2(X0,X3,X2)
                        & r1_orders_2(X0,X3,X1) )
                     => ( r2_yellow_0(X0,k2_tarski(X1,X2))
                        & k11_lattice3(X0,X1,X2) = X3 ) )
                    & ( ( r2_yellow_0(X0,k2_tarski(X1,X2))
                        & k11_lattice3(X0,X1,X2) = X3 )
                     => ( ! [X5] :
                            ( m1_subset_1(X5,u1_struct_0(X0))
                           => ( ( r1_orders_2(X0,X5,X2)
                                & r1_orders_2(X0,X5,X1) )
                             => r1_orders_2(X0,X5,X3) ) )
                        & r1_orders_2(X0,X3,X2)
                        & r1_orders_2(X0,X3,X1) ) ) ) ) ) ) ) ),
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
                           => ( ( r1_orders_2(X0,X4,X2)
                                & r1_orders_2(X0,X4,X1) )
                             => r1_orders_2(X0,X4,X3) ) )
                        & r1_orders_2(X0,X3,X2)
                        & r1_orders_2(X0,X3,X1) )
                     => ( r2_yellow_0(X0,k2_tarski(X1,X2))
                        & k11_lattice3(X0,X1,X2) = X3 ) )
                    & ( ( r2_yellow_0(X0,k2_tarski(X1,X2))
                        & k11_lattice3(X0,X1,X2) = X3 )
                     => ( ! [X4] :
                            ( m1_subset_1(X4,u1_struct_0(X0))
                           => ( ( r1_orders_2(X0,X4,X2)
                                & r1_orders_2(X0,X4,X1) )
                             => r1_orders_2(X0,X4,X3) ) )
                        & r1_orders_2(X0,X3,X2)
                        & r1_orders_2(X0,X3,X1) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/yellow_0__t37_yellow_0.p',t19_yellow_0)).

fof(f77,plain,(
    k2_yellow_0(sK0,k2_xboole_0(sK1,sK2)) != k11_lattice3(sK0,k2_yellow_0(sK0,sK1),k2_yellow_0(sK0,sK2)) ),
    inference(cnf_transformation,[],[f61])).

fof(f139322,plain,(
    ~ m1_subset_1(sK3(sK0,k2_yellow_0(sK0,sK1),k2_yellow_0(sK0,sK2),k2_yellow_0(sK0,k2_xboole_0(sK1,sK2))),u1_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f139198,f139035])).

fof(f139035,plain,(
    ~ r1_lattice3(sK0,sK1,sK3(sK0,k2_yellow_0(sK0,sK1),k2_yellow_0(sK0,sK2),k2_yellow_0(sK0,k2_xboole_0(sK1,sK2)))) ),
    inference(subsumption_resolution,[],[f139034,f96723])).

fof(f96723,plain,(
    ~ r1_orders_2(sK0,sK3(sK0,k2_yellow_0(sK0,sK1),k2_yellow_0(sK0,sK2),k2_yellow_0(sK0,k2_xboole_0(sK1,sK2))),k2_yellow_0(sK0,k2_xboole_0(sK1,sK2))) ),
    inference(subsumption_resolution,[],[f96722,f43637])).

fof(f43637,plain,(
    r2_yellow_0(sK0,k2_tarski(k2_yellow_0(sK0,sK2),k2_yellow_0(sK0,k2_xboole_0(sK1,sK2)))) ),
    inference(forward_demodulation,[],[f43636,f112])).

fof(f112,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/yellow_0__t37_yellow_0.p',commutativity_k2_tarski)).

fof(f43636,plain,(
    r2_yellow_0(sK0,k2_tarski(k2_yellow_0(sK0,k2_xboole_0(sK1,sK2)),k2_yellow_0(sK0,sK2))) ),
    inference(subsumption_resolution,[],[f43635,f173])).

fof(f43635,plain,
    ( r2_yellow_0(sK0,k2_tarski(k2_yellow_0(sK0,k2_xboole_0(sK1,sK2)),k2_yellow_0(sK0,sK2)))
    | ~ m1_subset_1(k2_yellow_0(sK0,sK2),u1_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f43634,f173])).

fof(f43634,plain,
    ( r2_yellow_0(sK0,k2_tarski(k2_yellow_0(sK0,k2_xboole_0(sK1,sK2)),k2_yellow_0(sK0,sK2)))
    | ~ m1_subset_1(k2_yellow_0(sK0,k2_xboole_0(sK1,sK2)),u1_struct_0(sK0))
    | ~ m1_subset_1(k2_yellow_0(sK0,sK2),u1_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f43557,f512])).

fof(f512,plain,(
    r1_orders_2(sK0,k2_yellow_0(sK0,k2_xboole_0(sK1,sK2)),k2_yellow_0(sK0,k2_xboole_0(sK1,sK2))) ),
    inference(subsumption_resolution,[],[f511,f72])).

fof(f511,plain,
    ( r1_orders_2(sK0,k2_yellow_0(sK0,k2_xboole_0(sK1,sK2)),k2_yellow_0(sK0,k2_xboole_0(sK1,sK2)))
    | ~ v5_orders_2(sK0) ),
    inference(subsumption_resolution,[],[f510,f73])).

fof(f510,plain,
    ( r1_orders_2(sK0,k2_yellow_0(sK0,k2_xboole_0(sK1,sK2)),k2_yellow_0(sK0,k2_xboole_0(sK1,sK2)))
    | ~ l1_orders_2(sK0)
    | ~ v5_orders_2(sK0) ),
    inference(subsumption_resolution,[],[f509,f76])).

fof(f509,plain,
    ( r1_orders_2(sK0,k2_yellow_0(sK0,k2_xboole_0(sK1,sK2)),k2_yellow_0(sK0,k2_xboole_0(sK1,sK2)))
    | ~ r2_yellow_0(sK0,k2_xboole_0(sK1,sK2))
    | ~ l1_orders_2(sK0)
    | ~ v5_orders_2(sK0) ),
    inference(subsumption_resolution,[],[f501,f173])).

fof(f501,plain,
    ( r1_orders_2(sK0,k2_yellow_0(sK0,k2_xboole_0(sK1,sK2)),k2_yellow_0(sK0,k2_xboole_0(sK1,sK2)))
    | ~ m1_subset_1(k2_yellow_0(sK0,k2_xboole_0(sK1,sK2)),u1_struct_0(sK0))
    | ~ r2_yellow_0(sK0,k2_xboole_0(sK1,sK2))
    | ~ l1_orders_2(sK0)
    | ~ v5_orders_2(sK0) ),
    inference(duplicate_literal_removal,[],[f497])).

fof(f497,plain,
    ( r1_orders_2(sK0,k2_yellow_0(sK0,k2_xboole_0(sK1,sK2)),k2_yellow_0(sK0,k2_xboole_0(sK1,sK2)))
    | ~ m1_subset_1(k2_yellow_0(sK0,k2_xboole_0(sK1,sK2)),u1_struct_0(sK0))
    | ~ r2_yellow_0(sK0,k2_xboole_0(sK1,sK2))
    | ~ m1_subset_1(k2_yellow_0(sK0,k2_xboole_0(sK1,sK2)),u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | ~ v5_orders_2(sK0) ),
    inference(resolution,[],[f222,f120])).

fof(f222,plain,(
    r1_lattice3(sK0,k2_xboole_0(sK1,sK2),k2_yellow_0(sK0,k2_xboole_0(sK1,sK2))) ),
    inference(subsumption_resolution,[],[f221,f72])).

fof(f221,plain,
    ( r1_lattice3(sK0,k2_xboole_0(sK1,sK2),k2_yellow_0(sK0,k2_xboole_0(sK1,sK2)))
    | ~ v5_orders_2(sK0) ),
    inference(subsumption_resolution,[],[f220,f73])).

fof(f220,plain,
    ( r1_lattice3(sK0,k2_xboole_0(sK1,sK2),k2_yellow_0(sK0,k2_xboole_0(sK1,sK2)))
    | ~ l1_orders_2(sK0)
    | ~ v5_orders_2(sK0) ),
    inference(subsumption_resolution,[],[f216,f173])).

fof(f216,plain,
    ( r1_lattice3(sK0,k2_xboole_0(sK1,sK2),k2_yellow_0(sK0,k2_xboole_0(sK1,sK2)))
    | ~ m1_subset_1(k2_yellow_0(sK0,k2_xboole_0(sK1,sK2)),u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | ~ v5_orders_2(sK0) ),
    inference(resolution,[],[f76,f121])).

fof(f43557,plain,
    ( r2_yellow_0(sK0,k2_tarski(k2_yellow_0(sK0,k2_xboole_0(sK1,sK2)),k2_yellow_0(sK0,sK2)))
    | ~ r1_orders_2(sK0,k2_yellow_0(sK0,k2_xboole_0(sK1,sK2)),k2_yellow_0(sK0,k2_xboole_0(sK1,sK2)))
    | ~ m1_subset_1(k2_yellow_0(sK0,k2_xboole_0(sK1,sK2)),u1_struct_0(sK0))
    | ~ m1_subset_1(k2_yellow_0(sK0,sK2),u1_struct_0(sK0)) ),
    inference(resolution,[],[f39312,f7047])).

fof(f7047,plain,(
    ! [X6,X7] :
      ( ~ r1_orders_2(sK0,X6,X7)
      | r2_yellow_0(sK0,k2_tarski(X6,X7))
      | ~ r1_orders_2(sK0,X6,X6)
      | ~ m1_subset_1(X6,u1_struct_0(sK0))
      | ~ m1_subset_1(X7,u1_struct_0(sK0)) ) ),
    inference(subsumption_resolution,[],[f7046,f72])).

fof(f7046,plain,(
    ! [X6,X7] :
      ( r2_yellow_0(sK0,k2_tarski(X6,X7))
      | ~ r1_orders_2(sK0,X6,X7)
      | ~ r1_orders_2(sK0,X6,X6)
      | ~ m1_subset_1(X6,u1_struct_0(sK0))
      | ~ m1_subset_1(X7,u1_struct_0(sK0))
      | ~ v5_orders_2(sK0) ) ),
    inference(subsumption_resolution,[],[f7036,f73])).

fof(f7036,plain,(
    ! [X6,X7] :
      ( r2_yellow_0(sK0,k2_tarski(X6,X7))
      | ~ r1_orders_2(sK0,X6,X7)
      | ~ r1_orders_2(sK0,X6,X6)
      | ~ m1_subset_1(X6,u1_struct_0(sK0))
      | ~ m1_subset_1(X7,u1_struct_0(sK0))
      | ~ l1_orders_2(sK0)
      | ~ v5_orders_2(sK0) ) ),
    inference(duplicate_literal_removal,[],[f7031])).

fof(f7031,plain,(
    ! [X6,X7] :
      ( r2_yellow_0(sK0,k2_tarski(X6,X7))
      | ~ r1_orders_2(sK0,X6,X7)
      | ~ r1_orders_2(sK0,X6,X6)
      | ~ m1_subset_1(X6,u1_struct_0(sK0))
      | ~ m1_subset_1(X7,u1_struct_0(sK0))
      | ~ m1_subset_1(X6,u1_struct_0(sK0))
      | r2_yellow_0(sK0,k2_tarski(X6,X7))
      | ~ r1_orders_2(sK0,X6,X7)
      | ~ r1_orders_2(sK0,X6,X6)
      | ~ m1_subset_1(X6,u1_struct_0(sK0))
      | ~ m1_subset_1(X7,u1_struct_0(sK0))
      | ~ m1_subset_1(X6,u1_struct_0(sK0))
      | ~ l1_orders_2(sK0)
      | ~ v5_orders_2(sK0) ) ),
    inference(resolution,[],[f152,f90])).

fof(f90,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_yellow_0(X0,k2_tarski(X1,X2))
      | r1_orders_2(X0,sK3(X0,X1,X2,X3),X1)
      | ~ r1_orders_2(X0,X3,X2)
      | ~ r1_orders_2(X0,X3,X1)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f63])).

fof(f152,plain,(
    ! [X23,X21,X22] :
      ( ~ r1_orders_2(sK0,sK3(sK0,X21,X22,X23),X23)
      | r2_yellow_0(sK0,k2_tarski(X21,X22))
      | ~ r1_orders_2(sK0,X23,X22)
      | ~ r1_orders_2(sK0,X23,X21)
      | ~ m1_subset_1(X23,u1_struct_0(sK0))
      | ~ m1_subset_1(X22,u1_struct_0(sK0))
      | ~ m1_subset_1(X21,u1_struct_0(sK0)) ) ),
    inference(subsumption_resolution,[],[f133,f73])).

fof(f133,plain,(
    ! [X23,X21,X22] :
      ( r2_yellow_0(sK0,k2_tarski(X21,X22))
      | ~ r1_orders_2(sK0,sK3(sK0,X21,X22,X23),X23)
      | ~ r1_orders_2(sK0,X23,X22)
      | ~ r1_orders_2(sK0,X23,X21)
      | ~ m1_subset_1(X23,u1_struct_0(sK0))
      | ~ m1_subset_1(X22,u1_struct_0(sK0))
      | ~ m1_subset_1(X21,u1_struct_0(sK0))
      | ~ l1_orders_2(sK0) ) ),
    inference(resolution,[],[f72,f92])).

fof(f92,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_yellow_0(X0,k2_tarski(X1,X2))
      | ~ r1_orders_2(X0,sK3(X0,X1,X2,X3),X3)
      | ~ r1_orders_2(X0,X3,X2)
      | ~ r1_orders_2(X0,X3,X1)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f63])).

fof(f39312,plain,(
    r1_orders_2(sK0,k2_yellow_0(sK0,k2_xboole_0(sK1,sK2)),k2_yellow_0(sK0,sK2)) ),
    inference(forward_demodulation,[],[f39305,f79])).

fof(f39305,plain,(
    r1_orders_2(sK0,k2_yellow_0(sK0,k2_xboole_0(sK2,sK1)),k2_yellow_0(sK0,sK2)) ),
    inference(resolution,[],[f7091,f76])).

fof(f7091,plain,(
    ! [X1] :
      ( ~ r2_yellow_0(sK0,k2_xboole_0(X1,sK2))
      | r1_orders_2(sK0,k2_yellow_0(sK0,k2_xboole_0(sK2,X1)),k2_yellow_0(sK0,sK2)) ) ),
    inference(superposition,[],[f942,f79])).

fof(f942,plain,(
    ! [X0] :
      ( ~ r2_yellow_0(sK0,k2_xboole_0(sK2,X0))
      | r1_orders_2(sK0,k2_yellow_0(sK0,k2_xboole_0(sK2,X0)),k2_yellow_0(sK0,sK2)) ) ),
    inference(resolution,[],[f206,f103])).

fof(f206,plain,(
    ! [X0] :
      ( ~ r1_tarski(sK2,X0)
      | ~ r2_yellow_0(sK0,X0)
      | r1_orders_2(sK0,k2_yellow_0(sK0,X0),k2_yellow_0(sK0,sK2)) ) ),
    inference(subsumption_resolution,[],[f202,f73])).

fof(f202,plain,(
    ! [X0] :
      ( r1_orders_2(sK0,k2_yellow_0(sK0,X0),k2_yellow_0(sK0,sK2))
      | ~ r2_yellow_0(sK0,X0)
      | ~ r1_tarski(sK2,X0)
      | ~ l1_orders_2(sK0) ) ),
    inference(resolution,[],[f75,f102])).

fof(f96722,plain,
    ( ~ r2_yellow_0(sK0,k2_tarski(k2_yellow_0(sK0,sK2),k2_yellow_0(sK0,k2_xboole_0(sK1,sK2))))
    | ~ r1_orders_2(sK0,sK3(sK0,k2_yellow_0(sK0,sK1),k2_yellow_0(sK0,sK2),k2_yellow_0(sK0,k2_xboole_0(sK1,sK2))),k2_yellow_0(sK0,k2_xboole_0(sK1,sK2))) ),
    inference(forward_demodulation,[],[f96721,f112])).

fof(f96721,plain,
    ( ~ r1_orders_2(sK0,sK3(sK0,k2_yellow_0(sK0,sK1),k2_yellow_0(sK0,sK2),k2_yellow_0(sK0,k2_xboole_0(sK1,sK2))),k2_yellow_0(sK0,k2_xboole_0(sK1,sK2)))
    | ~ r2_yellow_0(sK0,k2_tarski(k2_yellow_0(sK0,k2_xboole_0(sK1,sK2)),k2_yellow_0(sK0,sK2))) ),
    inference(subsumption_resolution,[],[f96720,f42654])).

fof(f96720,plain,
    ( ~ m1_subset_1(sK3(sK0,k2_yellow_0(sK0,sK1),k2_yellow_0(sK0,sK2),k2_yellow_0(sK0,k2_xboole_0(sK1,sK2))),u1_struct_0(sK0))
    | ~ r1_orders_2(sK0,sK3(sK0,k2_yellow_0(sK0,sK1),k2_yellow_0(sK0,sK2),k2_yellow_0(sK0,k2_xboole_0(sK1,sK2))),k2_yellow_0(sK0,k2_xboole_0(sK1,sK2)))
    | ~ r2_yellow_0(sK0,k2_tarski(k2_yellow_0(sK0,k2_xboole_0(sK1,sK2)),k2_yellow_0(sK0,sK2))) ),
    inference(forward_demodulation,[],[f96719,f43640])).

fof(f43640,plain,(
    k2_yellow_0(sK0,k2_xboole_0(sK1,sK2)) = k11_lattice3(sK0,k2_yellow_0(sK0,k2_xboole_0(sK1,sK2)),k2_yellow_0(sK0,sK2)) ),
    inference(subsumption_resolution,[],[f43639,f173])).

fof(f43639,plain,
    ( k2_yellow_0(sK0,k2_xboole_0(sK1,sK2)) = k11_lattice3(sK0,k2_yellow_0(sK0,k2_xboole_0(sK1,sK2)),k2_yellow_0(sK0,sK2))
    | ~ m1_subset_1(k2_yellow_0(sK0,sK2),u1_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f43638,f173])).

fof(f43638,plain,
    ( k2_yellow_0(sK0,k2_xboole_0(sK1,sK2)) = k11_lattice3(sK0,k2_yellow_0(sK0,k2_xboole_0(sK1,sK2)),k2_yellow_0(sK0,sK2))
    | ~ m1_subset_1(k2_yellow_0(sK0,k2_xboole_0(sK1,sK2)),u1_struct_0(sK0))
    | ~ m1_subset_1(k2_yellow_0(sK0,sK2),u1_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f43558,f512])).

fof(f43558,plain,
    ( k2_yellow_0(sK0,k2_xboole_0(sK1,sK2)) = k11_lattice3(sK0,k2_yellow_0(sK0,k2_xboole_0(sK1,sK2)),k2_yellow_0(sK0,sK2))
    | ~ r1_orders_2(sK0,k2_yellow_0(sK0,k2_xboole_0(sK1,sK2)),k2_yellow_0(sK0,k2_xboole_0(sK1,sK2)))
    | ~ m1_subset_1(k2_yellow_0(sK0,k2_xboole_0(sK1,sK2)),u1_struct_0(sK0))
    | ~ m1_subset_1(k2_yellow_0(sK0,sK2),u1_struct_0(sK0)) ),
    inference(resolution,[],[f39312,f7509])).

fof(f7509,plain,(
    ! [X4,X5] :
      ( ~ r1_orders_2(sK0,X4,X5)
      | k11_lattice3(sK0,X4,X5) = X4
      | ~ r1_orders_2(sK0,X4,X4)
      | ~ m1_subset_1(X4,u1_struct_0(sK0))
      | ~ m1_subset_1(X5,u1_struct_0(sK0)) ) ),
    inference(subsumption_resolution,[],[f7508,f72])).

fof(f7508,plain,(
    ! [X4,X5] :
      ( k11_lattice3(sK0,X4,X5) = X4
      | ~ r1_orders_2(sK0,X4,X5)
      | ~ r1_orders_2(sK0,X4,X4)
      | ~ m1_subset_1(X4,u1_struct_0(sK0))
      | ~ m1_subset_1(X5,u1_struct_0(sK0))
      | ~ v5_orders_2(sK0) ) ),
    inference(subsumption_resolution,[],[f7503,f73])).

fof(f7503,plain,(
    ! [X4,X5] :
      ( k11_lattice3(sK0,X4,X5) = X4
      | ~ r1_orders_2(sK0,X4,X5)
      | ~ r1_orders_2(sK0,X4,X4)
      | ~ m1_subset_1(X4,u1_struct_0(sK0))
      | ~ m1_subset_1(X5,u1_struct_0(sK0))
      | ~ l1_orders_2(sK0)
      | ~ v5_orders_2(sK0) ) ),
    inference(duplicate_literal_removal,[],[f7496])).

fof(f7496,plain,(
    ! [X4,X5] :
      ( k11_lattice3(sK0,X4,X5) = X4
      | ~ r1_orders_2(sK0,X4,X5)
      | ~ r1_orders_2(sK0,X4,X4)
      | ~ m1_subset_1(X4,u1_struct_0(sK0))
      | ~ m1_subset_1(X5,u1_struct_0(sK0))
      | ~ m1_subset_1(X4,u1_struct_0(sK0))
      | k11_lattice3(sK0,X4,X5) = X4
      | ~ r1_orders_2(sK0,X4,X5)
      | ~ r1_orders_2(sK0,X4,X4)
      | ~ m1_subset_1(X4,u1_struct_0(sK0))
      | ~ m1_subset_1(X5,u1_struct_0(sK0))
      | ~ m1_subset_1(X4,u1_struct_0(sK0))
      | ~ l1_orders_2(sK0)
      | ~ v5_orders_2(sK0) ) ),
    inference(resolution,[],[f148,f86])).

fof(f86,plain,(
    ! [X2,X0,X3,X1] :
      ( k11_lattice3(X0,X1,X2) = X3
      | r1_orders_2(X0,sK3(X0,X1,X2,X3),X1)
      | ~ r1_orders_2(X0,X3,X2)
      | ~ r1_orders_2(X0,X3,X1)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f63])).

fof(f148,plain,(
    ! [X10,X11,X9] :
      ( ~ r1_orders_2(sK0,sK3(sK0,X9,X10,X11),X11)
      | k11_lattice3(sK0,X9,X10) = X11
      | ~ r1_orders_2(sK0,X11,X10)
      | ~ r1_orders_2(sK0,X11,X9)
      | ~ m1_subset_1(X11,u1_struct_0(sK0))
      | ~ m1_subset_1(X10,u1_struct_0(sK0))
      | ~ m1_subset_1(X9,u1_struct_0(sK0)) ) ),
    inference(subsumption_resolution,[],[f129,f73])).

fof(f129,plain,(
    ! [X10,X11,X9] :
      ( k11_lattice3(sK0,X9,X10) = X11
      | ~ r1_orders_2(sK0,sK3(sK0,X9,X10,X11),X11)
      | ~ r1_orders_2(sK0,X11,X10)
      | ~ r1_orders_2(sK0,X11,X9)
      | ~ m1_subset_1(X11,u1_struct_0(sK0))
      | ~ m1_subset_1(X10,u1_struct_0(sK0))
      | ~ m1_subset_1(X9,u1_struct_0(sK0))
      | ~ l1_orders_2(sK0) ) ),
    inference(resolution,[],[f72,f88])).

fof(f88,plain,(
    ! [X2,X0,X3,X1] :
      ( k11_lattice3(X0,X1,X2) = X3
      | ~ r1_orders_2(X0,sK3(X0,X1,X2,X3),X3)
      | ~ r1_orders_2(X0,X3,X2)
      | ~ r1_orders_2(X0,X3,X1)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f63])).

fof(f96719,plain,
    ( ~ r1_orders_2(sK0,sK3(sK0,k2_yellow_0(sK0,sK1),k2_yellow_0(sK0,sK2),k2_yellow_0(sK0,k2_xboole_0(sK1,sK2))),k2_yellow_0(sK0,k2_xboole_0(sK1,sK2)))
    | ~ m1_subset_1(sK3(sK0,k2_yellow_0(sK0,sK1),k2_yellow_0(sK0,sK2),k11_lattice3(sK0,k2_yellow_0(sK0,k2_xboole_0(sK1,sK2)),k2_yellow_0(sK0,sK2))),u1_struct_0(sK0))
    | ~ r2_yellow_0(sK0,k2_tarski(k2_yellow_0(sK0,k2_xboole_0(sK1,sK2)),k2_yellow_0(sK0,sK2))) ),
    inference(forward_demodulation,[],[f96718,f43640])).

fof(f96718,plain,
    ( ~ r1_orders_2(sK0,sK3(sK0,k2_yellow_0(sK0,sK1),k2_yellow_0(sK0,sK2),k11_lattice3(sK0,k2_yellow_0(sK0,k2_xboole_0(sK1,sK2)),k2_yellow_0(sK0,sK2))),k2_yellow_0(sK0,k2_xboole_0(sK1,sK2)))
    | ~ m1_subset_1(sK3(sK0,k2_yellow_0(sK0,sK1),k2_yellow_0(sK0,sK2),k11_lattice3(sK0,k2_yellow_0(sK0,k2_xboole_0(sK1,sK2)),k2_yellow_0(sK0,sK2))),u1_struct_0(sK0))
    | ~ r2_yellow_0(sK0,k2_tarski(k2_yellow_0(sK0,k2_xboole_0(sK1,sK2)),k2_yellow_0(sK0,sK2))) ),
    inference(subsumption_resolution,[],[f96717,f2103])).

fof(f96717,plain,
    ( ~ r1_orders_2(sK0,k2_yellow_0(sK0,k2_xboole_0(sK1,sK2)),k2_yellow_0(sK0,sK1))
    | ~ r1_orders_2(sK0,sK3(sK0,k2_yellow_0(sK0,sK1),k2_yellow_0(sK0,sK2),k11_lattice3(sK0,k2_yellow_0(sK0,k2_xboole_0(sK1,sK2)),k2_yellow_0(sK0,sK2))),k2_yellow_0(sK0,k2_xboole_0(sK1,sK2)))
    | ~ m1_subset_1(sK3(sK0,k2_yellow_0(sK0,sK1),k2_yellow_0(sK0,sK2),k11_lattice3(sK0,k2_yellow_0(sK0,k2_xboole_0(sK1,sK2)),k2_yellow_0(sK0,sK2))),u1_struct_0(sK0))
    | ~ r2_yellow_0(sK0,k2_tarski(k2_yellow_0(sK0,k2_xboole_0(sK1,sK2)),k2_yellow_0(sK0,sK2))) ),
    inference(forward_demodulation,[],[f96716,f43640])).

fof(f96716,plain,
    ( ~ r1_orders_2(sK0,k11_lattice3(sK0,k2_yellow_0(sK0,k2_xboole_0(sK1,sK2)),k2_yellow_0(sK0,sK2)),k2_yellow_0(sK0,sK1))
    | ~ r1_orders_2(sK0,sK3(sK0,k2_yellow_0(sK0,sK1),k2_yellow_0(sK0,sK2),k11_lattice3(sK0,k2_yellow_0(sK0,k2_xboole_0(sK1,sK2)),k2_yellow_0(sK0,sK2))),k2_yellow_0(sK0,k2_xboole_0(sK1,sK2)))
    | ~ m1_subset_1(sK3(sK0,k2_yellow_0(sK0,sK1),k2_yellow_0(sK0,sK2),k11_lattice3(sK0,k2_yellow_0(sK0,k2_xboole_0(sK1,sK2)),k2_yellow_0(sK0,sK2))),u1_struct_0(sK0))
    | ~ r2_yellow_0(sK0,k2_tarski(k2_yellow_0(sK0,k2_xboole_0(sK1,sK2)),k2_yellow_0(sK0,sK2))) ),
    inference(subsumption_resolution,[],[f96715,f39312])).

fof(f96715,plain,
    ( ~ r1_orders_2(sK0,k2_yellow_0(sK0,k2_xboole_0(sK1,sK2)),k2_yellow_0(sK0,sK2))
    | ~ r1_orders_2(sK0,k11_lattice3(sK0,k2_yellow_0(sK0,k2_xboole_0(sK1,sK2)),k2_yellow_0(sK0,sK2)),k2_yellow_0(sK0,sK1))
    | ~ r1_orders_2(sK0,sK3(sK0,k2_yellow_0(sK0,sK1),k2_yellow_0(sK0,sK2),k11_lattice3(sK0,k2_yellow_0(sK0,k2_xboole_0(sK1,sK2)),k2_yellow_0(sK0,sK2))),k2_yellow_0(sK0,k2_xboole_0(sK1,sK2)))
    | ~ m1_subset_1(sK3(sK0,k2_yellow_0(sK0,sK1),k2_yellow_0(sK0,sK2),k11_lattice3(sK0,k2_yellow_0(sK0,k2_xboole_0(sK1,sK2)),k2_yellow_0(sK0,sK2))),u1_struct_0(sK0))
    | ~ r2_yellow_0(sK0,k2_tarski(k2_yellow_0(sK0,k2_xboole_0(sK1,sK2)),k2_yellow_0(sK0,sK2))) ),
    inference(forward_demodulation,[],[f96714,f43640])).

fof(f96714,plain,
    ( ~ r1_orders_2(sK0,k11_lattice3(sK0,k2_yellow_0(sK0,k2_xboole_0(sK1,sK2)),k2_yellow_0(sK0,sK2)),k2_yellow_0(sK0,sK2))
    | ~ r1_orders_2(sK0,k11_lattice3(sK0,k2_yellow_0(sK0,k2_xboole_0(sK1,sK2)),k2_yellow_0(sK0,sK2)),k2_yellow_0(sK0,sK1))
    | ~ r1_orders_2(sK0,sK3(sK0,k2_yellow_0(sK0,sK1),k2_yellow_0(sK0,sK2),k11_lattice3(sK0,k2_yellow_0(sK0,k2_xboole_0(sK1,sK2)),k2_yellow_0(sK0,sK2))),k2_yellow_0(sK0,k2_xboole_0(sK1,sK2)))
    | ~ m1_subset_1(sK3(sK0,k2_yellow_0(sK0,sK1),k2_yellow_0(sK0,sK2),k11_lattice3(sK0,k2_yellow_0(sK0,k2_xboole_0(sK1,sK2)),k2_yellow_0(sK0,sK2))),u1_struct_0(sK0))
    | ~ r2_yellow_0(sK0,k2_tarski(k2_yellow_0(sK0,k2_xboole_0(sK1,sK2)),k2_yellow_0(sK0,sK2))) ),
    inference(subsumption_resolution,[],[f96713,f173])).

fof(f96713,plain,
    ( ~ r1_orders_2(sK0,k11_lattice3(sK0,k2_yellow_0(sK0,k2_xboole_0(sK1,sK2)),k2_yellow_0(sK0,sK2)),k2_yellow_0(sK0,sK2))
    | ~ r1_orders_2(sK0,k11_lattice3(sK0,k2_yellow_0(sK0,k2_xboole_0(sK1,sK2)),k2_yellow_0(sK0,sK2)),k2_yellow_0(sK0,sK1))
    | ~ r1_orders_2(sK0,sK3(sK0,k2_yellow_0(sK0,sK1),k2_yellow_0(sK0,sK2),k11_lattice3(sK0,k2_yellow_0(sK0,k2_xboole_0(sK1,sK2)),k2_yellow_0(sK0,sK2))),k2_yellow_0(sK0,k2_xboole_0(sK1,sK2)))
    | ~ m1_subset_1(sK3(sK0,k2_yellow_0(sK0,sK1),k2_yellow_0(sK0,sK2),k11_lattice3(sK0,k2_yellow_0(sK0,k2_xboole_0(sK1,sK2)),k2_yellow_0(sK0,sK2))),u1_struct_0(sK0))
    | ~ r2_yellow_0(sK0,k2_tarski(k2_yellow_0(sK0,k2_xboole_0(sK1,sK2)),k2_yellow_0(sK0,sK2)))
    | ~ m1_subset_1(k2_yellow_0(sK0,k2_xboole_0(sK1,sK2)),u1_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f96712,f173])).

fof(f96712,plain,
    ( ~ r1_orders_2(sK0,k11_lattice3(sK0,k2_yellow_0(sK0,k2_xboole_0(sK1,sK2)),k2_yellow_0(sK0,sK2)),k2_yellow_0(sK0,sK2))
    | ~ r1_orders_2(sK0,k11_lattice3(sK0,k2_yellow_0(sK0,k2_xboole_0(sK1,sK2)),k2_yellow_0(sK0,sK2)),k2_yellow_0(sK0,sK1))
    | ~ r1_orders_2(sK0,sK3(sK0,k2_yellow_0(sK0,sK1),k2_yellow_0(sK0,sK2),k11_lattice3(sK0,k2_yellow_0(sK0,k2_xboole_0(sK1,sK2)),k2_yellow_0(sK0,sK2))),k2_yellow_0(sK0,k2_xboole_0(sK1,sK2)))
    | ~ m1_subset_1(sK3(sK0,k2_yellow_0(sK0,sK1),k2_yellow_0(sK0,sK2),k11_lattice3(sK0,k2_yellow_0(sK0,k2_xboole_0(sK1,sK2)),k2_yellow_0(sK0,sK2))),u1_struct_0(sK0))
    | ~ r2_yellow_0(sK0,k2_tarski(k2_yellow_0(sK0,k2_xboole_0(sK1,sK2)),k2_yellow_0(sK0,sK2)))
    | ~ m1_subset_1(k2_yellow_0(sK0,sK2),u1_struct_0(sK0))
    | ~ m1_subset_1(k2_yellow_0(sK0,k2_xboole_0(sK1,sK2)),u1_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f96711,f43640])).

fof(f96711,plain,
    ( ~ r1_orders_2(sK0,k11_lattice3(sK0,k2_yellow_0(sK0,k2_xboole_0(sK1,sK2)),k2_yellow_0(sK0,sK2)),k2_yellow_0(sK0,sK2))
    | ~ r1_orders_2(sK0,k11_lattice3(sK0,k2_yellow_0(sK0,k2_xboole_0(sK1,sK2)),k2_yellow_0(sK0,sK2)),k2_yellow_0(sK0,sK1))
    | k2_yellow_0(sK0,k2_xboole_0(sK1,sK2)) != k11_lattice3(sK0,k2_yellow_0(sK0,k2_xboole_0(sK1,sK2)),k2_yellow_0(sK0,sK2))
    | ~ r1_orders_2(sK0,sK3(sK0,k2_yellow_0(sK0,sK1),k2_yellow_0(sK0,sK2),k11_lattice3(sK0,k2_yellow_0(sK0,k2_xboole_0(sK1,sK2)),k2_yellow_0(sK0,sK2))),k2_yellow_0(sK0,k2_xboole_0(sK1,sK2)))
    | ~ m1_subset_1(sK3(sK0,k2_yellow_0(sK0,sK1),k2_yellow_0(sK0,sK2),k11_lattice3(sK0,k2_yellow_0(sK0,k2_xboole_0(sK1,sK2)),k2_yellow_0(sK0,sK2))),u1_struct_0(sK0))
    | ~ r2_yellow_0(sK0,k2_tarski(k2_yellow_0(sK0,k2_xboole_0(sK1,sK2)),k2_yellow_0(sK0,sK2)))
    | ~ m1_subset_1(k2_yellow_0(sK0,sK2),u1_struct_0(sK0))
    | ~ m1_subset_1(k2_yellow_0(sK0,k2_xboole_0(sK1,sK2)),u1_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f96674,f42650])).

fof(f42650,plain,(
    r1_orders_2(sK0,sK3(sK0,k2_yellow_0(sK0,sK1),k2_yellow_0(sK0,sK2),k2_yellow_0(sK0,k2_xboole_0(sK1,sK2))),k2_yellow_0(sK0,sK2)) ),
    inference(subsumption_resolution,[],[f42649,f12105])).

fof(f42649,plain,
    ( r1_orders_2(sK0,sK3(sK0,k2_yellow_0(sK0,sK1),k2_yellow_0(sK0,sK2),k2_yellow_0(sK0,k2_xboole_0(sK1,sK2))),k2_yellow_0(sK0,sK2))
    | ~ r1_lattice3(sK0,sK2,k2_yellow_0(sK0,k2_xboole_0(sK1,sK2))) ),
    inference(subsumption_resolution,[],[f39448,f173])).

fof(f39448,plain,
    ( r1_orders_2(sK0,sK3(sK0,k2_yellow_0(sK0,sK1),k2_yellow_0(sK0,sK2),k2_yellow_0(sK0,k2_xboole_0(sK1,sK2))),k2_yellow_0(sK0,sK2))
    | ~ m1_subset_1(k2_yellow_0(sK0,k2_xboole_0(sK1,sK2)),u1_struct_0(sK0))
    | ~ r1_lattice3(sK0,sK2,k2_yellow_0(sK0,k2_xboole_0(sK1,sK2))) ),
    inference(trivial_inequality_removal,[],[f39428])).

fof(f39428,plain,
    ( k2_yellow_0(sK0,k2_xboole_0(sK1,sK2)) != k2_yellow_0(sK0,k2_xboole_0(sK1,sK2))
    | r1_orders_2(sK0,sK3(sK0,k2_yellow_0(sK0,sK1),k2_yellow_0(sK0,sK2),k2_yellow_0(sK0,k2_xboole_0(sK1,sK2))),k2_yellow_0(sK0,sK2))
    | ~ m1_subset_1(k2_yellow_0(sK0,k2_xboole_0(sK1,sK2)),u1_struct_0(sK0))
    | ~ r1_lattice3(sK0,sK2,k2_yellow_0(sK0,k2_xboole_0(sK1,sK2))) ),
    inference(resolution,[],[f8249,f2103])).

fof(f8249,plain,(
    ! [X0] :
      ( ~ r1_orders_2(sK0,X0,k2_yellow_0(sK0,sK1))
      | k2_yellow_0(sK0,k2_xboole_0(sK1,sK2)) != X0
      | r1_orders_2(sK0,sK3(sK0,k2_yellow_0(sK0,sK1),k2_yellow_0(sK0,sK2),X0),k2_yellow_0(sK0,sK2))
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ r1_lattice3(sK0,sK2,X0) ) ),
    inference(subsumption_resolution,[],[f8248,f72])).

fof(f8248,plain,(
    ! [X0] :
      ( r1_orders_2(sK0,sK3(sK0,k2_yellow_0(sK0,sK1),k2_yellow_0(sK0,sK2),X0),k2_yellow_0(sK0,sK2))
      | k2_yellow_0(sK0,k2_xboole_0(sK1,sK2)) != X0
      | ~ r1_orders_2(sK0,X0,k2_yellow_0(sK0,sK1))
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ r1_lattice3(sK0,sK2,X0)
      | ~ v5_orders_2(sK0) ) ),
    inference(subsumption_resolution,[],[f8247,f73])).

fof(f8247,plain,(
    ! [X0] :
      ( r1_orders_2(sK0,sK3(sK0,k2_yellow_0(sK0,sK1),k2_yellow_0(sK0,sK2),X0),k2_yellow_0(sK0,sK2))
      | k2_yellow_0(sK0,k2_xboole_0(sK1,sK2)) != X0
      | ~ r1_orders_2(sK0,X0,k2_yellow_0(sK0,sK1))
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ r1_lattice3(sK0,sK2,X0)
      | ~ l1_orders_2(sK0)
      | ~ v5_orders_2(sK0) ) ),
    inference(subsumption_resolution,[],[f8246,f173])).

fof(f8246,plain,(
    ! [X0] :
      ( r1_orders_2(sK0,sK3(sK0,k2_yellow_0(sK0,sK1),k2_yellow_0(sK0,sK2),X0),k2_yellow_0(sK0,sK2))
      | k2_yellow_0(sK0,k2_xboole_0(sK1,sK2)) != X0
      | ~ r1_orders_2(sK0,X0,k2_yellow_0(sK0,sK1))
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ r1_lattice3(sK0,sK2,X0)
      | ~ m1_subset_1(k2_yellow_0(sK0,sK2),u1_struct_0(sK0))
      | ~ l1_orders_2(sK0)
      | ~ v5_orders_2(sK0) ) ),
    inference(subsumption_resolution,[],[f8239,f75])).

fof(f8239,plain,(
    ! [X0] :
      ( r1_orders_2(sK0,sK3(sK0,k2_yellow_0(sK0,sK1),k2_yellow_0(sK0,sK2),X0),k2_yellow_0(sK0,sK2))
      | k2_yellow_0(sK0,k2_xboole_0(sK1,sK2)) != X0
      | ~ r1_orders_2(sK0,X0,k2_yellow_0(sK0,sK1))
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ r1_lattice3(sK0,sK2,X0)
      | ~ r2_yellow_0(sK0,sK2)
      | ~ m1_subset_1(k2_yellow_0(sK0,sK2),u1_struct_0(sK0))
      | ~ l1_orders_2(sK0)
      | ~ v5_orders_2(sK0) ) ),
    inference(duplicate_literal_removal,[],[f8224])).

fof(f8224,plain,(
    ! [X0] :
      ( r1_orders_2(sK0,sK3(sK0,k2_yellow_0(sK0,sK1),k2_yellow_0(sK0,sK2),X0),k2_yellow_0(sK0,sK2))
      | k2_yellow_0(sK0,k2_xboole_0(sK1,sK2)) != X0
      | ~ r1_orders_2(sK0,X0,k2_yellow_0(sK0,sK1))
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ r1_lattice3(sK0,sK2,X0)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ r2_yellow_0(sK0,sK2)
      | ~ m1_subset_1(k2_yellow_0(sK0,sK2),u1_struct_0(sK0))
      | ~ l1_orders_2(sK0)
      | ~ v5_orders_2(sK0) ) ),
    inference(resolution,[],[f259,f120])).

fof(f259,plain,(
    ! [X2] :
      ( ~ r1_orders_2(sK0,X2,k2_yellow_0(sK0,sK2))
      | r1_orders_2(sK0,sK3(sK0,k2_yellow_0(sK0,sK1),k2_yellow_0(sK0,sK2),X2),k2_yellow_0(sK0,sK2))
      | k2_yellow_0(sK0,k2_xboole_0(sK1,sK2)) != X2
      | ~ r1_orders_2(sK0,X2,k2_yellow_0(sK0,sK1))
      | ~ m1_subset_1(X2,u1_struct_0(sK0)) ) ),
    inference(subsumption_resolution,[],[f258,f72])).

fof(f258,plain,(
    ! [X2] :
      ( k2_yellow_0(sK0,k2_xboole_0(sK1,sK2)) != X2
      | r1_orders_2(sK0,sK3(sK0,k2_yellow_0(sK0,sK1),k2_yellow_0(sK0,sK2),X2),k2_yellow_0(sK0,sK2))
      | ~ r1_orders_2(sK0,X2,k2_yellow_0(sK0,sK2))
      | ~ r1_orders_2(sK0,X2,k2_yellow_0(sK0,sK1))
      | ~ m1_subset_1(X2,u1_struct_0(sK0))
      | ~ v5_orders_2(sK0) ) ),
    inference(subsumption_resolution,[],[f257,f73])).

fof(f257,plain,(
    ! [X2] :
      ( k2_yellow_0(sK0,k2_xboole_0(sK1,sK2)) != X2
      | r1_orders_2(sK0,sK3(sK0,k2_yellow_0(sK0,sK1),k2_yellow_0(sK0,sK2),X2),k2_yellow_0(sK0,sK2))
      | ~ r1_orders_2(sK0,X2,k2_yellow_0(sK0,sK2))
      | ~ r1_orders_2(sK0,X2,k2_yellow_0(sK0,sK1))
      | ~ m1_subset_1(X2,u1_struct_0(sK0))
      | ~ l1_orders_2(sK0)
      | ~ v5_orders_2(sK0) ) ),
    inference(subsumption_resolution,[],[f256,f173])).

fof(f256,plain,(
    ! [X2] :
      ( k2_yellow_0(sK0,k2_xboole_0(sK1,sK2)) != X2
      | r1_orders_2(sK0,sK3(sK0,k2_yellow_0(sK0,sK1),k2_yellow_0(sK0,sK2),X2),k2_yellow_0(sK0,sK2))
      | ~ r1_orders_2(sK0,X2,k2_yellow_0(sK0,sK2))
      | ~ r1_orders_2(sK0,X2,k2_yellow_0(sK0,sK1))
      | ~ m1_subset_1(X2,u1_struct_0(sK0))
      | ~ m1_subset_1(k2_yellow_0(sK0,sK1),u1_struct_0(sK0))
      | ~ l1_orders_2(sK0)
      | ~ v5_orders_2(sK0) ) ),
    inference(subsumption_resolution,[],[f234,f173])).

fof(f234,plain,(
    ! [X2] :
      ( k2_yellow_0(sK0,k2_xboole_0(sK1,sK2)) != X2
      | r1_orders_2(sK0,sK3(sK0,k2_yellow_0(sK0,sK1),k2_yellow_0(sK0,sK2),X2),k2_yellow_0(sK0,sK2))
      | ~ r1_orders_2(sK0,X2,k2_yellow_0(sK0,sK2))
      | ~ r1_orders_2(sK0,X2,k2_yellow_0(sK0,sK1))
      | ~ m1_subset_1(X2,u1_struct_0(sK0))
      | ~ m1_subset_1(k2_yellow_0(sK0,sK2),u1_struct_0(sK0))
      | ~ m1_subset_1(k2_yellow_0(sK0,sK1),u1_struct_0(sK0))
      | ~ l1_orders_2(sK0)
      | ~ v5_orders_2(sK0) ) ),
    inference(superposition,[],[f77,f87])).

fof(f87,plain,(
    ! [X2,X0,X3,X1] :
      ( k11_lattice3(X0,X1,X2) = X3
      | r1_orders_2(X0,sK3(X0,X1,X2,X3),X2)
      | ~ r1_orders_2(X0,X3,X2)
      | ~ r1_orders_2(X0,X3,X1)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f63])).

fof(f96674,plain,
    ( ~ r1_orders_2(sK0,sK3(sK0,k2_yellow_0(sK0,sK1),k2_yellow_0(sK0,sK2),k2_yellow_0(sK0,k2_xboole_0(sK1,sK2))),k2_yellow_0(sK0,sK2))
    | ~ r1_orders_2(sK0,k11_lattice3(sK0,k2_yellow_0(sK0,k2_xboole_0(sK1,sK2)),k2_yellow_0(sK0,sK2)),k2_yellow_0(sK0,sK2))
    | ~ r1_orders_2(sK0,k11_lattice3(sK0,k2_yellow_0(sK0,k2_xboole_0(sK1,sK2)),k2_yellow_0(sK0,sK2)),k2_yellow_0(sK0,sK1))
    | k2_yellow_0(sK0,k2_xboole_0(sK1,sK2)) != k11_lattice3(sK0,k2_yellow_0(sK0,k2_xboole_0(sK1,sK2)),k2_yellow_0(sK0,sK2))
    | ~ r1_orders_2(sK0,sK3(sK0,k2_yellow_0(sK0,sK1),k2_yellow_0(sK0,sK2),k11_lattice3(sK0,k2_yellow_0(sK0,k2_xboole_0(sK1,sK2)),k2_yellow_0(sK0,sK2))),k2_yellow_0(sK0,k2_xboole_0(sK1,sK2)))
    | ~ m1_subset_1(sK3(sK0,k2_yellow_0(sK0,sK1),k2_yellow_0(sK0,sK2),k11_lattice3(sK0,k2_yellow_0(sK0,k2_xboole_0(sK1,sK2)),k2_yellow_0(sK0,sK2))),u1_struct_0(sK0))
    | ~ r2_yellow_0(sK0,k2_tarski(k2_yellow_0(sK0,k2_xboole_0(sK1,sK2)),k2_yellow_0(sK0,sK2)))
    | ~ m1_subset_1(k2_yellow_0(sK0,sK2),u1_struct_0(sK0))
    | ~ m1_subset_1(k2_yellow_0(sK0,k2_xboole_0(sK1,sK2)),u1_struct_0(sK0)) ),
    inference(superposition,[],[f7930,f43640])).

fof(f7930,plain,(
    ! [X0,X1] :
      ( ~ r1_orders_2(sK0,sK3(sK0,k2_yellow_0(sK0,sK1),k2_yellow_0(sK0,sK2),k11_lattice3(sK0,X0,X1)),X1)
      | ~ r1_orders_2(sK0,k11_lattice3(sK0,X0,X1),k2_yellow_0(sK0,sK2))
      | ~ r1_orders_2(sK0,k11_lattice3(sK0,X0,X1),k2_yellow_0(sK0,sK1))
      | k2_yellow_0(sK0,k2_xboole_0(sK1,sK2)) != k11_lattice3(sK0,X0,X1)
      | ~ r1_orders_2(sK0,sK3(sK0,k2_yellow_0(sK0,sK1),k2_yellow_0(sK0,sK2),k11_lattice3(sK0,X0,X1)),X0)
      | ~ m1_subset_1(sK3(sK0,k2_yellow_0(sK0,sK1),k2_yellow_0(sK0,sK2),k11_lattice3(sK0,X0,X1)),u1_struct_0(sK0))
      | ~ r2_yellow_0(sK0,k2_tarski(X0,X1))
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ m1_subset_1(X0,u1_struct_0(sK0)) ) ),
    inference(subsumption_resolution,[],[f7929,f164])).

fof(f164,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,u1_struct_0(sK0))
      | m1_subset_1(k11_lattice3(sK0,X0,X1),u1_struct_0(sK0))
      | ~ m1_subset_1(X0,u1_struct_0(sK0)) ) ),
    inference(resolution,[],[f73,f81])).

fof(f81,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k11_lattice3(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k11_lattice3(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f41])).

fof(f41,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k11_lattice3(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l1_orders_2(X0) )
     => m1_subset_1(k11_lattice3(X0,X1,X2),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/yellow_0__t37_yellow_0.p',dt_k11_lattice3)).

fof(f7929,plain,(
    ! [X0,X1] :
      ( k2_yellow_0(sK0,k2_xboole_0(sK1,sK2)) != k11_lattice3(sK0,X0,X1)
      | ~ r1_orders_2(sK0,k11_lattice3(sK0,X0,X1),k2_yellow_0(sK0,sK2))
      | ~ r1_orders_2(sK0,k11_lattice3(sK0,X0,X1),k2_yellow_0(sK0,sK1))
      | ~ m1_subset_1(k11_lattice3(sK0,X0,X1),u1_struct_0(sK0))
      | ~ r1_orders_2(sK0,sK3(sK0,k2_yellow_0(sK0,sK1),k2_yellow_0(sK0,sK2),k11_lattice3(sK0,X0,X1)),X1)
      | ~ r1_orders_2(sK0,sK3(sK0,k2_yellow_0(sK0,sK1),k2_yellow_0(sK0,sK2),k11_lattice3(sK0,X0,X1)),X0)
      | ~ m1_subset_1(sK3(sK0,k2_yellow_0(sK0,sK1),k2_yellow_0(sK0,sK2),k11_lattice3(sK0,X0,X1)),u1_struct_0(sK0))
      | ~ r2_yellow_0(sK0,k2_tarski(X0,X1))
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ m1_subset_1(X0,u1_struct_0(sK0)) ) ),
    inference(subsumption_resolution,[],[f7928,f72])).

fof(f7928,plain,(
    ! [X0,X1] :
      ( k2_yellow_0(sK0,k2_xboole_0(sK1,sK2)) != k11_lattice3(sK0,X0,X1)
      | ~ r1_orders_2(sK0,k11_lattice3(sK0,X0,X1),k2_yellow_0(sK0,sK2))
      | ~ r1_orders_2(sK0,k11_lattice3(sK0,X0,X1),k2_yellow_0(sK0,sK1))
      | ~ m1_subset_1(k11_lattice3(sK0,X0,X1),u1_struct_0(sK0))
      | ~ r1_orders_2(sK0,sK3(sK0,k2_yellow_0(sK0,sK1),k2_yellow_0(sK0,sK2),k11_lattice3(sK0,X0,X1)),X1)
      | ~ r1_orders_2(sK0,sK3(sK0,k2_yellow_0(sK0,sK1),k2_yellow_0(sK0,sK2),k11_lattice3(sK0,X0,X1)),X0)
      | ~ m1_subset_1(sK3(sK0,k2_yellow_0(sK0,sK1),k2_yellow_0(sK0,sK2),k11_lattice3(sK0,X0,X1)),u1_struct_0(sK0))
      | ~ r2_yellow_0(sK0,k2_tarski(X0,X1))
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ v5_orders_2(sK0) ) ),
    inference(subsumption_resolution,[],[f7923,f73])).

fof(f7923,plain,(
    ! [X0,X1] :
      ( k2_yellow_0(sK0,k2_xboole_0(sK1,sK2)) != k11_lattice3(sK0,X0,X1)
      | ~ r1_orders_2(sK0,k11_lattice3(sK0,X0,X1),k2_yellow_0(sK0,sK2))
      | ~ r1_orders_2(sK0,k11_lattice3(sK0,X0,X1),k2_yellow_0(sK0,sK1))
      | ~ m1_subset_1(k11_lattice3(sK0,X0,X1),u1_struct_0(sK0))
      | ~ r1_orders_2(sK0,sK3(sK0,k2_yellow_0(sK0,sK1),k2_yellow_0(sK0,sK2),k11_lattice3(sK0,X0,X1)),X1)
      | ~ r1_orders_2(sK0,sK3(sK0,k2_yellow_0(sK0,sK1),k2_yellow_0(sK0,sK2),k11_lattice3(sK0,X0,X1)),X0)
      | ~ m1_subset_1(sK3(sK0,k2_yellow_0(sK0,sK1),k2_yellow_0(sK0,sK2),k11_lattice3(sK0,X0,X1)),u1_struct_0(sK0))
      | ~ r2_yellow_0(sK0,k2_tarski(X0,X1))
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ l1_orders_2(sK0)
      | ~ v5_orders_2(sK0) ) ),
    inference(duplicate_literal_removal,[],[f7913])).

fof(f7913,plain,(
    ! [X0,X1] :
      ( k2_yellow_0(sK0,k2_xboole_0(sK1,sK2)) != k11_lattice3(sK0,X0,X1)
      | ~ r1_orders_2(sK0,k11_lattice3(sK0,X0,X1),k2_yellow_0(sK0,sK2))
      | ~ r1_orders_2(sK0,k11_lattice3(sK0,X0,X1),k2_yellow_0(sK0,sK1))
      | ~ m1_subset_1(k11_lattice3(sK0,X0,X1),u1_struct_0(sK0))
      | ~ r1_orders_2(sK0,sK3(sK0,k2_yellow_0(sK0,sK1),k2_yellow_0(sK0,sK2),k11_lattice3(sK0,X0,X1)),X1)
      | ~ r1_orders_2(sK0,sK3(sK0,k2_yellow_0(sK0,sK1),k2_yellow_0(sK0,sK2),k11_lattice3(sK0,X0,X1)),X0)
      | ~ m1_subset_1(sK3(sK0,k2_yellow_0(sK0,sK1),k2_yellow_0(sK0,sK2),k11_lattice3(sK0,X0,X1)),u1_struct_0(sK0))
      | ~ r2_yellow_0(sK0,k2_tarski(X0,X1))
      | ~ m1_subset_1(k11_lattice3(sK0,X0,X1),u1_struct_0(sK0))
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ l1_orders_2(sK0)
      | ~ v5_orders_2(sK0) ) ),
    inference(resolution,[],[f263,f117])).

fof(f117,plain,(
    ! [X2,X0,X5,X1] :
      ( r1_orders_2(X0,X5,k11_lattice3(X0,X1,X2))
      | ~ r1_orders_2(X0,X5,X2)
      | ~ r1_orders_2(X0,X5,X1)
      | ~ m1_subset_1(X5,u1_struct_0(X0))
      | ~ r2_yellow_0(X0,k2_tarski(X1,X2))
      | ~ m1_subset_1(k11_lattice3(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(equality_resolution,[],[f84])).

fof(f84,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r1_orders_2(X0,X5,X3)
      | ~ r1_orders_2(X0,X5,X2)
      | ~ r1_orders_2(X0,X5,X1)
      | ~ m1_subset_1(X5,u1_struct_0(X0))
      | ~ r2_yellow_0(X0,k2_tarski(X1,X2))
      | k11_lattice3(X0,X1,X2) != X3
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f63])).

fof(f263,plain,(
    ! [X3] :
      ( ~ r1_orders_2(sK0,sK3(sK0,k2_yellow_0(sK0,sK1),k2_yellow_0(sK0,sK2),X3),X3)
      | k2_yellow_0(sK0,k2_xboole_0(sK1,sK2)) != X3
      | ~ r1_orders_2(sK0,X3,k2_yellow_0(sK0,sK2))
      | ~ r1_orders_2(sK0,X3,k2_yellow_0(sK0,sK1))
      | ~ m1_subset_1(X3,u1_struct_0(sK0)) ) ),
    inference(subsumption_resolution,[],[f262,f72])).

fof(f262,plain,(
    ! [X3] :
      ( k2_yellow_0(sK0,k2_xboole_0(sK1,sK2)) != X3
      | ~ r1_orders_2(sK0,sK3(sK0,k2_yellow_0(sK0,sK1),k2_yellow_0(sK0,sK2),X3),X3)
      | ~ r1_orders_2(sK0,X3,k2_yellow_0(sK0,sK2))
      | ~ r1_orders_2(sK0,X3,k2_yellow_0(sK0,sK1))
      | ~ m1_subset_1(X3,u1_struct_0(sK0))
      | ~ v5_orders_2(sK0) ) ),
    inference(subsumption_resolution,[],[f261,f73])).

fof(f261,plain,(
    ! [X3] :
      ( k2_yellow_0(sK0,k2_xboole_0(sK1,sK2)) != X3
      | ~ r1_orders_2(sK0,sK3(sK0,k2_yellow_0(sK0,sK1),k2_yellow_0(sK0,sK2),X3),X3)
      | ~ r1_orders_2(sK0,X3,k2_yellow_0(sK0,sK2))
      | ~ r1_orders_2(sK0,X3,k2_yellow_0(sK0,sK1))
      | ~ m1_subset_1(X3,u1_struct_0(sK0))
      | ~ l1_orders_2(sK0)
      | ~ v5_orders_2(sK0) ) ),
    inference(subsumption_resolution,[],[f260,f173])).

fof(f260,plain,(
    ! [X3] :
      ( k2_yellow_0(sK0,k2_xboole_0(sK1,sK2)) != X3
      | ~ r1_orders_2(sK0,sK3(sK0,k2_yellow_0(sK0,sK1),k2_yellow_0(sK0,sK2),X3),X3)
      | ~ r1_orders_2(sK0,X3,k2_yellow_0(sK0,sK2))
      | ~ r1_orders_2(sK0,X3,k2_yellow_0(sK0,sK1))
      | ~ m1_subset_1(X3,u1_struct_0(sK0))
      | ~ m1_subset_1(k2_yellow_0(sK0,sK1),u1_struct_0(sK0))
      | ~ l1_orders_2(sK0)
      | ~ v5_orders_2(sK0) ) ),
    inference(subsumption_resolution,[],[f235,f173])).

fof(f235,plain,(
    ! [X3] :
      ( k2_yellow_0(sK0,k2_xboole_0(sK1,sK2)) != X3
      | ~ r1_orders_2(sK0,sK3(sK0,k2_yellow_0(sK0,sK1),k2_yellow_0(sK0,sK2),X3),X3)
      | ~ r1_orders_2(sK0,X3,k2_yellow_0(sK0,sK2))
      | ~ r1_orders_2(sK0,X3,k2_yellow_0(sK0,sK1))
      | ~ m1_subset_1(X3,u1_struct_0(sK0))
      | ~ m1_subset_1(k2_yellow_0(sK0,sK2),u1_struct_0(sK0))
      | ~ m1_subset_1(k2_yellow_0(sK0,sK1),u1_struct_0(sK0))
      | ~ l1_orders_2(sK0)
      | ~ v5_orders_2(sK0) ) ),
    inference(superposition,[],[f77,f88])).

fof(f139034,plain,
    ( r1_orders_2(sK0,sK3(sK0,k2_yellow_0(sK0,sK1),k2_yellow_0(sK0,sK2),k2_yellow_0(sK0,k2_xboole_0(sK1,sK2))),k2_yellow_0(sK0,k2_xboole_0(sK1,sK2)))
    | ~ r1_lattice3(sK0,sK1,sK3(sK0,k2_yellow_0(sK0,sK1),k2_yellow_0(sK0,sK2),k2_yellow_0(sK0,k2_xboole_0(sK1,sK2)))) ),
    inference(subsumption_resolution,[],[f138954,f42654])).

fof(f138954,plain,
    ( ~ m1_subset_1(sK3(sK0,k2_yellow_0(sK0,sK1),k2_yellow_0(sK0,sK2),k2_yellow_0(sK0,k2_xboole_0(sK1,sK2))),u1_struct_0(sK0))
    | r1_orders_2(sK0,sK3(sK0,k2_yellow_0(sK0,sK1),k2_yellow_0(sK0,sK2),k2_yellow_0(sK0,k2_xboole_0(sK1,sK2))),k2_yellow_0(sK0,k2_xboole_0(sK1,sK2)))
    | ~ r1_lattice3(sK0,sK1,sK3(sK0,k2_yellow_0(sK0,sK1),k2_yellow_0(sK0,sK2),k2_yellow_0(sK0,k2_xboole_0(sK1,sK2)))) ),
    inference(resolution,[],[f138703,f2921])).

fof(f2921,plain,(
    ! [X0] :
      ( ~ r1_lattice3(sK0,sK2,X0)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | r1_orders_2(sK0,X0,k2_yellow_0(sK0,k2_xboole_0(sK1,sK2)))
      | ~ r1_lattice3(sK0,sK1,X0) ) ),
    inference(subsumption_resolution,[],[f2918,f73])).

fof(f2918,plain,(
    ! [X0] :
      ( r1_orders_2(sK0,X0,k2_yellow_0(sK0,k2_xboole_0(sK1,sK2)))
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ r1_lattice3(sK0,sK2,X0)
      | ~ r1_lattice3(sK0,sK1,X0)
      | ~ l1_orders_2(sK0) ) ),
    inference(duplicate_literal_removal,[],[f2911])).

fof(f2911,plain,(
    ! [X0] :
      ( r1_orders_2(sK0,X0,k2_yellow_0(sK0,k2_xboole_0(sK1,sK2)))
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ r1_lattice3(sK0,sK2,X0)
      | ~ r1_lattice3(sK0,sK1,X0)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ l1_orders_2(sK0) ) ),
    inference(resolution,[],[f225,f113])).

fof(f113,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_lattice3(X0,k2_xboole_0(X1,X2),X3)
      | ~ r1_lattice3(X0,X2,X3)
      | ~ r1_lattice3(X0,X1,X3)
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
    file('/export/starexec/sandbox2/benchmark/yellow_0__t37_yellow_0.p',t10_yellow_0)).

fof(f225,plain,(
    ! [X2] :
      ( ~ r1_lattice3(sK0,k2_xboole_0(sK1,sK2),X2)
      | r1_orders_2(sK0,X2,k2_yellow_0(sK0,k2_xboole_0(sK1,sK2)))
      | ~ m1_subset_1(X2,u1_struct_0(sK0)) ) ),
    inference(subsumption_resolution,[],[f224,f72])).

fof(f224,plain,(
    ! [X2] :
      ( r1_orders_2(sK0,X2,k2_yellow_0(sK0,k2_xboole_0(sK1,sK2)))
      | ~ r1_lattice3(sK0,k2_xboole_0(sK1,sK2),X2)
      | ~ m1_subset_1(X2,u1_struct_0(sK0))
      | ~ v5_orders_2(sK0) ) ),
    inference(subsumption_resolution,[],[f223,f73])).

fof(f223,plain,(
    ! [X2] :
      ( r1_orders_2(sK0,X2,k2_yellow_0(sK0,k2_xboole_0(sK1,sK2)))
      | ~ r1_lattice3(sK0,k2_xboole_0(sK1,sK2),X2)
      | ~ m1_subset_1(X2,u1_struct_0(sK0))
      | ~ l1_orders_2(sK0)
      | ~ v5_orders_2(sK0) ) ),
    inference(subsumption_resolution,[],[f217,f173])).

fof(f217,plain,(
    ! [X2] :
      ( r1_orders_2(sK0,X2,k2_yellow_0(sK0,k2_xboole_0(sK1,sK2)))
      | ~ r1_lattice3(sK0,k2_xboole_0(sK1,sK2),X2)
      | ~ m1_subset_1(X2,u1_struct_0(sK0))
      | ~ m1_subset_1(k2_yellow_0(sK0,k2_xboole_0(sK1,sK2)),u1_struct_0(sK0))
      | ~ l1_orders_2(sK0)
      | ~ v5_orders_2(sK0) ) ),
    inference(resolution,[],[f76,f120])).

fof(f138703,plain,(
    r1_lattice3(sK0,sK2,sK3(sK0,k2_yellow_0(sK0,sK1),k2_yellow_0(sK0,sK2),k2_yellow_0(sK0,k2_xboole_0(sK1,sK2)))) ),
    inference(subsumption_resolution,[],[f138529,f42654])).

fof(f138529,plain,
    ( r1_lattice3(sK0,sK2,sK3(sK0,k2_yellow_0(sK0,sK1),k2_yellow_0(sK0,sK2),k2_yellow_0(sK0,k2_xboole_0(sK1,sK2))))
    | ~ m1_subset_1(sK3(sK0,k2_yellow_0(sK0,sK1),k2_yellow_0(sK0,sK2),k2_yellow_0(sK0,k2_xboole_0(sK1,sK2))),u1_struct_0(sK0)) ),
    inference(resolution,[],[f42650,f467])).

fof(f467,plain,(
    ! [X0] :
      ( ~ r1_orders_2(sK0,X0,k2_yellow_0(sK0,sK2))
      | r1_lattice3(sK0,sK2,X0)
      | ~ m1_subset_1(X0,u1_struct_0(sK0)) ) ),
    inference(subsumption_resolution,[],[f466,f71])).

fof(f466,plain,(
    ! [X0] :
      ( r1_lattice3(sK0,sK2,X0)
      | ~ r1_orders_2(sK0,X0,k2_yellow_0(sK0,sK2))
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ v4_orders_2(sK0) ) ),
    inference(subsumption_resolution,[],[f465,f73])).

fof(f465,plain,(
    ! [X0] :
      ( r1_lattice3(sK0,sK2,X0)
      | ~ r1_orders_2(sK0,X0,k2_yellow_0(sK0,sK2))
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ l1_orders_2(sK0)
      | ~ v4_orders_2(sK0) ) ),
    inference(subsumption_resolution,[],[f457,f173])).

fof(f457,plain,(
    ! [X0] :
      ( r1_lattice3(sK0,sK2,X0)
      | ~ r1_orders_2(sK0,X0,k2_yellow_0(sK0,sK2))
      | ~ m1_subset_1(k2_yellow_0(sK0,sK2),u1_struct_0(sK0))
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ l1_orders_2(sK0)
      | ~ v4_orders_2(sK0) ) ),
    inference(resolution,[],[f210,f105])).

fof(f210,plain,(
    r1_lattice3(sK0,sK2,k2_yellow_0(sK0,sK2)) ),
    inference(subsumption_resolution,[],[f209,f72])).

fof(f209,plain,
    ( r1_lattice3(sK0,sK2,k2_yellow_0(sK0,sK2))
    | ~ v5_orders_2(sK0) ),
    inference(subsumption_resolution,[],[f208,f73])).

fof(f208,plain,
    ( r1_lattice3(sK0,sK2,k2_yellow_0(sK0,sK2))
    | ~ l1_orders_2(sK0)
    | ~ v5_orders_2(sK0) ),
    inference(subsumption_resolution,[],[f204,f173])).

fof(f204,plain,
    ( r1_lattice3(sK0,sK2,k2_yellow_0(sK0,sK2))
    | ~ m1_subset_1(k2_yellow_0(sK0,sK2),u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | ~ v5_orders_2(sK0) ),
    inference(resolution,[],[f75,f121])).

fof(f139198,plain,
    ( r1_lattice3(sK0,sK1,sK3(sK0,k2_yellow_0(sK0,sK1),k2_yellow_0(sK0,sK2),k2_yellow_0(sK0,k2_xboole_0(sK1,sK2))))
    | ~ m1_subset_1(sK3(sK0,k2_yellow_0(sK0,sK1),k2_yellow_0(sK0,sK2),k2_yellow_0(sK0,k2_xboole_0(sK1,sK2))),u1_struct_0(sK0)) ),
    inference(resolution,[],[f42652,f442])).

fof(f42652,plain,(
    r1_orders_2(sK0,sK3(sK0,k2_yellow_0(sK0,sK1),k2_yellow_0(sK0,sK2),k2_yellow_0(sK0,k2_xboole_0(sK1,sK2))),k2_yellow_0(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f42651,f12105])).

fof(f42651,plain,
    ( r1_orders_2(sK0,sK3(sK0,k2_yellow_0(sK0,sK1),k2_yellow_0(sK0,sK2),k2_yellow_0(sK0,k2_xboole_0(sK1,sK2))),k2_yellow_0(sK0,sK1))
    | ~ r1_lattice3(sK0,sK2,k2_yellow_0(sK0,k2_xboole_0(sK1,sK2))) ),
    inference(subsumption_resolution,[],[f39343,f173])).

fof(f39343,plain,
    ( r1_orders_2(sK0,sK3(sK0,k2_yellow_0(sK0,sK1),k2_yellow_0(sK0,sK2),k2_yellow_0(sK0,k2_xboole_0(sK1,sK2))),k2_yellow_0(sK0,sK1))
    | ~ m1_subset_1(k2_yellow_0(sK0,k2_xboole_0(sK1,sK2)),u1_struct_0(sK0))
    | ~ r1_lattice3(sK0,sK2,k2_yellow_0(sK0,k2_xboole_0(sK1,sK2))) ),
    inference(trivial_inequality_removal,[],[f39323])).

fof(f39323,plain,
    ( k2_yellow_0(sK0,k2_xboole_0(sK1,sK2)) != k2_yellow_0(sK0,k2_xboole_0(sK1,sK2))
    | r1_orders_2(sK0,sK3(sK0,k2_yellow_0(sK0,sK1),k2_yellow_0(sK0,sK2),k2_yellow_0(sK0,k2_xboole_0(sK1,sK2))),k2_yellow_0(sK0,sK1))
    | ~ m1_subset_1(k2_yellow_0(sK0,k2_xboole_0(sK1,sK2)),u1_struct_0(sK0))
    | ~ r1_lattice3(sK0,sK2,k2_yellow_0(sK0,k2_xboole_0(sK1,sK2))) ),
    inference(resolution,[],[f8063,f2103])).

fof(f8063,plain,(
    ! [X0] :
      ( ~ r1_orders_2(sK0,X0,k2_yellow_0(sK0,sK1))
      | k2_yellow_0(sK0,k2_xboole_0(sK1,sK2)) != X0
      | r1_orders_2(sK0,sK3(sK0,k2_yellow_0(sK0,sK1),k2_yellow_0(sK0,sK2),X0),k2_yellow_0(sK0,sK1))
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ r1_lattice3(sK0,sK2,X0) ) ),
    inference(subsumption_resolution,[],[f8062,f72])).

fof(f8062,plain,(
    ! [X0] :
      ( r1_orders_2(sK0,sK3(sK0,k2_yellow_0(sK0,sK1),k2_yellow_0(sK0,sK2),X0),k2_yellow_0(sK0,sK1))
      | k2_yellow_0(sK0,k2_xboole_0(sK1,sK2)) != X0
      | ~ r1_orders_2(sK0,X0,k2_yellow_0(sK0,sK1))
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ r1_lattice3(sK0,sK2,X0)
      | ~ v5_orders_2(sK0) ) ),
    inference(subsumption_resolution,[],[f8061,f73])).

fof(f8061,plain,(
    ! [X0] :
      ( r1_orders_2(sK0,sK3(sK0,k2_yellow_0(sK0,sK1),k2_yellow_0(sK0,sK2),X0),k2_yellow_0(sK0,sK1))
      | k2_yellow_0(sK0,k2_xboole_0(sK1,sK2)) != X0
      | ~ r1_orders_2(sK0,X0,k2_yellow_0(sK0,sK1))
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ r1_lattice3(sK0,sK2,X0)
      | ~ l1_orders_2(sK0)
      | ~ v5_orders_2(sK0) ) ),
    inference(subsumption_resolution,[],[f8060,f173])).

fof(f8060,plain,(
    ! [X0] :
      ( r1_orders_2(sK0,sK3(sK0,k2_yellow_0(sK0,sK1),k2_yellow_0(sK0,sK2),X0),k2_yellow_0(sK0,sK1))
      | k2_yellow_0(sK0,k2_xboole_0(sK1,sK2)) != X0
      | ~ r1_orders_2(sK0,X0,k2_yellow_0(sK0,sK1))
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ r1_lattice3(sK0,sK2,X0)
      | ~ m1_subset_1(k2_yellow_0(sK0,sK2),u1_struct_0(sK0))
      | ~ l1_orders_2(sK0)
      | ~ v5_orders_2(sK0) ) ),
    inference(subsumption_resolution,[],[f8049,f75])).

fof(f8049,plain,(
    ! [X0] :
      ( r1_orders_2(sK0,sK3(sK0,k2_yellow_0(sK0,sK1),k2_yellow_0(sK0,sK2),X0),k2_yellow_0(sK0,sK1))
      | k2_yellow_0(sK0,k2_xboole_0(sK1,sK2)) != X0
      | ~ r1_orders_2(sK0,X0,k2_yellow_0(sK0,sK1))
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ r1_lattice3(sK0,sK2,X0)
      | ~ r2_yellow_0(sK0,sK2)
      | ~ m1_subset_1(k2_yellow_0(sK0,sK2),u1_struct_0(sK0))
      | ~ l1_orders_2(sK0)
      | ~ v5_orders_2(sK0) ) ),
    inference(duplicate_literal_removal,[],[f8034])).

fof(f8034,plain,(
    ! [X0] :
      ( r1_orders_2(sK0,sK3(sK0,k2_yellow_0(sK0,sK1),k2_yellow_0(sK0,sK2),X0),k2_yellow_0(sK0,sK1))
      | k2_yellow_0(sK0,k2_xboole_0(sK1,sK2)) != X0
      | ~ r1_orders_2(sK0,X0,k2_yellow_0(sK0,sK1))
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ r1_lattice3(sK0,sK2,X0)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ r2_yellow_0(sK0,sK2)
      | ~ m1_subset_1(k2_yellow_0(sK0,sK2),u1_struct_0(sK0))
      | ~ l1_orders_2(sK0)
      | ~ v5_orders_2(sK0) ) ),
    inference(resolution,[],[f255,f120])).

fof(f255,plain,(
    ! [X1] :
      ( ~ r1_orders_2(sK0,X1,k2_yellow_0(sK0,sK2))
      | r1_orders_2(sK0,sK3(sK0,k2_yellow_0(sK0,sK1),k2_yellow_0(sK0,sK2),X1),k2_yellow_0(sK0,sK1))
      | k2_yellow_0(sK0,k2_xboole_0(sK1,sK2)) != X1
      | ~ r1_orders_2(sK0,X1,k2_yellow_0(sK0,sK1))
      | ~ m1_subset_1(X1,u1_struct_0(sK0)) ) ),
    inference(subsumption_resolution,[],[f254,f72])).

fof(f254,plain,(
    ! [X1] :
      ( k2_yellow_0(sK0,k2_xboole_0(sK1,sK2)) != X1
      | r1_orders_2(sK0,sK3(sK0,k2_yellow_0(sK0,sK1),k2_yellow_0(sK0,sK2),X1),k2_yellow_0(sK0,sK1))
      | ~ r1_orders_2(sK0,X1,k2_yellow_0(sK0,sK2))
      | ~ r1_orders_2(sK0,X1,k2_yellow_0(sK0,sK1))
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ v5_orders_2(sK0) ) ),
    inference(subsumption_resolution,[],[f253,f73])).

fof(f253,plain,(
    ! [X1] :
      ( k2_yellow_0(sK0,k2_xboole_0(sK1,sK2)) != X1
      | r1_orders_2(sK0,sK3(sK0,k2_yellow_0(sK0,sK1),k2_yellow_0(sK0,sK2),X1),k2_yellow_0(sK0,sK1))
      | ~ r1_orders_2(sK0,X1,k2_yellow_0(sK0,sK2))
      | ~ r1_orders_2(sK0,X1,k2_yellow_0(sK0,sK1))
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ l1_orders_2(sK0)
      | ~ v5_orders_2(sK0) ) ),
    inference(subsumption_resolution,[],[f252,f173])).

fof(f252,plain,(
    ! [X1] :
      ( k2_yellow_0(sK0,k2_xboole_0(sK1,sK2)) != X1
      | r1_orders_2(sK0,sK3(sK0,k2_yellow_0(sK0,sK1),k2_yellow_0(sK0,sK2),X1),k2_yellow_0(sK0,sK1))
      | ~ r1_orders_2(sK0,X1,k2_yellow_0(sK0,sK2))
      | ~ r1_orders_2(sK0,X1,k2_yellow_0(sK0,sK1))
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ m1_subset_1(k2_yellow_0(sK0,sK1),u1_struct_0(sK0))
      | ~ l1_orders_2(sK0)
      | ~ v5_orders_2(sK0) ) ),
    inference(subsumption_resolution,[],[f233,f173])).

fof(f233,plain,(
    ! [X1] :
      ( k2_yellow_0(sK0,k2_xboole_0(sK1,sK2)) != X1
      | r1_orders_2(sK0,sK3(sK0,k2_yellow_0(sK0,sK1),k2_yellow_0(sK0,sK2),X1),k2_yellow_0(sK0,sK1))
      | ~ r1_orders_2(sK0,X1,k2_yellow_0(sK0,sK2))
      | ~ r1_orders_2(sK0,X1,k2_yellow_0(sK0,sK1))
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ m1_subset_1(k2_yellow_0(sK0,sK2),u1_struct_0(sK0))
      | ~ m1_subset_1(k2_yellow_0(sK0,sK1),u1_struct_0(sK0))
      | ~ l1_orders_2(sK0)
      | ~ v5_orders_2(sK0) ) ),
    inference(superposition,[],[f77,f86])).
%------------------------------------------------------------------------------
