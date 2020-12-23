%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : lattice3__t15_lattice3.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:36:53 EDT 2019

% Result     : Theorem 1.05s
% Output     : Refutation 1.05s
% Verified   : 
% Statistics : Number of formulae       :   99 ( 343 expanded)
%              Number of leaves         :   12 (  82 expanded)
%              Depth                    :   35
%              Number of atoms          :  907 (3210 expanded)
%              Number of equality atoms :   59 ( 239 expanded)
%              Maximal formula depth    :   24 (  12 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f3633,plain,(
    $false ),
    inference(subsumption_resolution,[],[f3632,f68])).

fof(f68,plain,(
    m1_subset_1(sK3,u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,
    ( k11_lattice3(sK1,sK2,sK3) != k11_lattice3(sK1,sK3,sK2)
    & m1_subset_1(sK3,u1_struct_0(sK1))
    & m1_subset_1(sK2,u1_struct_0(sK1))
    & l1_orders_2(sK1)
    & v2_lattice3(sK1)
    & v5_orders_2(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f26,f46,f45,f44])).

fof(f44,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( k11_lattice3(X0,X1,X2) != k11_lattice3(X0,X2,X1)
                & m1_subset_1(X2,u1_struct_0(X0)) )
            & m1_subset_1(X1,u1_struct_0(X0)) )
        & l1_orders_2(X0)
        & v2_lattice3(X0)
        & v5_orders_2(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( k11_lattice3(sK1,X1,X2) != k11_lattice3(sK1,X2,X1)
              & m1_subset_1(X2,u1_struct_0(sK1)) )
          & m1_subset_1(X1,u1_struct_0(sK1)) )
      & l1_orders_2(sK1)
      & v2_lattice3(sK1)
      & v5_orders_2(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f45,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( k11_lattice3(X0,X1,X2) != k11_lattice3(X0,X2,X1)
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
     => ( ? [X2] :
            ( k11_lattice3(X0,X2,sK2) != k11_lattice3(X0,sK2,X2)
            & m1_subset_1(X2,u1_struct_0(X0)) )
        & m1_subset_1(sK2,u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( k11_lattice3(X0,X1,X2) != k11_lattice3(X0,X2,X1)
          & m1_subset_1(X2,u1_struct_0(X0)) )
     => ( k11_lattice3(X0,X1,sK3) != k11_lattice3(X0,sK3,X1)
        & m1_subset_1(sK3,u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( k11_lattice3(X0,X1,X2) != k11_lattice3(X0,X2,X1)
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_orders_2(X0)
      & v2_lattice3(X0)
      & v5_orders_2(X0) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( k11_lattice3(X0,X1,X2) != k11_lattice3(X0,X2,X1)
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_orders_2(X0)
      & v2_lattice3(X0)
      & v5_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_orders_2(X0)
          & v2_lattice3(X0)
          & v5_orders_2(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => k11_lattice3(X0,X1,X2) = k11_lattice3(X0,X2,X1) ) ) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v2_lattice3(X0)
        & v5_orders_2(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => k11_lattice3(X0,X1,X2) = k11_lattice3(X0,X2,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/lattice3__t15_lattice3.p',t15_lattice3)).

fof(f3632,plain,(
    ~ m1_subset_1(sK3,u1_struct_0(sK1)) ),
    inference(subsumption_resolution,[],[f3631,f64])).

fof(f64,plain,(
    v5_orders_2(sK1) ),
    inference(cnf_transformation,[],[f47])).

fof(f3631,plain,
    ( ~ v5_orders_2(sK1)
    | ~ m1_subset_1(sK3,u1_struct_0(sK1)) ),
    inference(subsumption_resolution,[],[f3630,f65])).

fof(f65,plain,(
    v2_lattice3(sK1) ),
    inference(cnf_transformation,[],[f47])).

fof(f3630,plain,
    ( ~ v2_lattice3(sK1)
    | ~ v5_orders_2(sK1)
    | ~ m1_subset_1(sK3,u1_struct_0(sK1)) ),
    inference(subsumption_resolution,[],[f3629,f66])).

fof(f66,plain,(
    l1_orders_2(sK1) ),
    inference(cnf_transformation,[],[f47])).

fof(f3629,plain,
    ( ~ l1_orders_2(sK1)
    | ~ v2_lattice3(sK1)
    | ~ v5_orders_2(sK1)
    | ~ m1_subset_1(sK3,u1_struct_0(sK1)) ),
    inference(subsumption_resolution,[],[f3620,f67])).

fof(f67,plain,(
    m1_subset_1(sK2,u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f47])).

fof(f3620,plain,
    ( ~ m1_subset_1(sK2,u1_struct_0(sK1))
    | ~ l1_orders_2(sK1)
    | ~ v2_lattice3(sK1)
    | ~ v5_orders_2(sK1)
    | ~ m1_subset_1(sK3,u1_struct_0(sK1)) ),
    inference(trivial_inequality_removal,[],[f3035])).

fof(f3035,plain,
    ( k11_lattice3(sK1,sK2,sK3) != k11_lattice3(sK1,sK2,sK3)
    | ~ m1_subset_1(sK2,u1_struct_0(sK1))
    | ~ l1_orders_2(sK1)
    | ~ v2_lattice3(sK1)
    | ~ v5_orders_2(sK1)
    | ~ m1_subset_1(sK3,u1_struct_0(sK1)) ),
    inference(superposition,[],[f69,f1566])).

fof(f1566,plain,(
    ! [X4,X5,X3] :
      ( k11_lattice3(X4,X3,X5) = k11_lattice3(X4,X5,X3)
      | ~ m1_subset_1(X5,u1_struct_0(X4))
      | ~ l1_orders_2(X4)
      | ~ v2_lattice3(X4)
      | ~ v5_orders_2(X4)
      | ~ m1_subset_1(X3,u1_struct_0(X4)) ) ),
    inference(subsumption_resolution,[],[f1565,f97])).

fof(f97,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k11_lattice3(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k11_lattice3(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f40])).

fof(f40,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k11_lattice3(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l1_orders_2(X0) )
     => m1_subset_1(k11_lattice3(X0,X1,X2),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/lattice3__t15_lattice3.p',dt_k11_lattice3)).

fof(f1565,plain,(
    ! [X4,X5,X3] :
      ( ~ m1_subset_1(X3,u1_struct_0(X4))
      | ~ m1_subset_1(X5,u1_struct_0(X4))
      | ~ l1_orders_2(X4)
      | ~ v2_lattice3(X4)
      | ~ v5_orders_2(X4)
      | k11_lattice3(X4,X3,X5) = k11_lattice3(X4,X5,X3)
      | ~ m1_subset_1(k11_lattice3(X4,X5,X3),u1_struct_0(X4)) ) ),
    inference(subsumption_resolution,[],[f1564,f134])).

fof(f134,plain,(
    ! [X2,X0,X1] :
      ( r1_orders_2(X0,k11_lattice3(X0,X1,X2),X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(duplicate_literal_removal,[],[f133])).

fof(f133,plain,(
    ! [X2,X0,X1] :
      ( r1_orders_2(X0,k11_lattice3(X0,X1,X2),X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(resolution,[],[f110,f97])).

fof(f110,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(k11_lattice3(X0,X1,X2),u1_struct_0(X0))
      | r1_orders_2(X0,k11_lattice3(X0,X1,X2),X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(subsumption_resolution,[],[f103,f72])).

fof(f72,plain,(
    ! [X0] :
      ( ~ v2_struct_0(X0)
      | ~ v2_lattice3(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ~ v2_struct_0(X0)
      | ~ v2_lattice3(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ~ v2_struct_0(X0)
      | ~ v2_lattice3(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ( v2_lattice3(X0)
       => ~ v2_struct_0(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/lattice3__t15_lattice3.p',cc2_lattice3)).

fof(f103,plain,(
    ! [X2,X0,X1] :
      ( r1_orders_2(X0,k11_lattice3(X0,X1,X2),X2)
      | ~ m1_subset_1(k11_lattice3(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f85])).

fof(f85,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_orders_2(X0,X3,X2)
      | k11_lattice3(X0,X1,X2) != X3
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f59])).

fof(f59,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ( k11_lattice3(X0,X1,X2) = X3
                      | ( ~ r1_orders_2(X0,sK6(X0,X1,X2,X3),X3)
                        & r1_orders_2(X0,sK6(X0,X1,X2,X3),X2)
                        & r1_orders_2(X0,sK6(X0,X1,X2,X3),X1)
                        & m1_subset_1(sK6(X0,X1,X2,X3),u1_struct_0(X0)) )
                      | ~ r1_orders_2(X0,X3,X2)
                      | ~ r1_orders_2(X0,X3,X1) )
                    & ( ( ! [X5] :
                            ( r1_orders_2(X0,X5,X3)
                            | ~ r1_orders_2(X0,X5,X2)
                            | ~ r1_orders_2(X0,X5,X1)
                            | ~ m1_subset_1(X5,u1_struct_0(X0)) )
                        & r1_orders_2(X0,X3,X2)
                        & r1_orders_2(X0,X3,X1) )
                      | k11_lattice3(X0,X1,X2) != X3 ) )
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f57,f58])).

fof(f58,plain,(
    ! [X3,X2,X1,X0] :
      ( ? [X4] :
          ( ~ r1_orders_2(X0,X4,X3)
          & r1_orders_2(X0,X4,X2)
          & r1_orders_2(X0,X4,X1)
          & m1_subset_1(X4,u1_struct_0(X0)) )
     => ( ~ r1_orders_2(X0,sK6(X0,X1,X2,X3),X3)
        & r1_orders_2(X0,sK6(X0,X1,X2,X3),X2)
        & r1_orders_2(X0,sK6(X0,X1,X2,X3),X1)
        & m1_subset_1(sK6(X0,X1,X2,X3),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f57,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ( k11_lattice3(X0,X1,X2) = X3
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
                      | k11_lattice3(X0,X1,X2) != X3 ) )
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(rectify,[],[f56])).

fof(f56,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ( k11_lattice3(X0,X1,X2) = X3
                      | ? [X4] :
                          ( ~ r1_orders_2(X0,X4,X3)
                          & r1_orders_2(X0,X4,X2)
                          & r1_orders_2(X0,X4,X1)
                          & m1_subset_1(X4,u1_struct_0(X0)) )
                      | ~ r1_orders_2(X0,X3,X2)
                      | ~ r1_orders_2(X0,X3,X1) )
                    & ( ( ! [X4] :
                            ( r1_orders_2(X0,X4,X3)
                            | ~ r1_orders_2(X0,X4,X2)
                            | ~ r1_orders_2(X0,X4,X1)
                            | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                        & r1_orders_2(X0,X3,X2)
                        & r1_orders_2(X0,X3,X1) )
                      | k11_lattice3(X0,X1,X2) != X3 ) )
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f55])).

fof(f55,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ( k11_lattice3(X0,X1,X2) = X3
                      | ? [X4] :
                          ( ~ r1_orders_2(X0,X4,X3)
                          & r1_orders_2(X0,X4,X2)
                          & r1_orders_2(X0,X4,X1)
                          & m1_subset_1(X4,u1_struct_0(X0)) )
                      | ~ r1_orders_2(X0,X3,X2)
                      | ~ r1_orders_2(X0,X3,X1) )
                    & ( ( ! [X4] :
                            ( r1_orders_2(X0,X4,X3)
                            | ~ r1_orders_2(X0,X4,X2)
                            | ~ r1_orders_2(X0,X4,X1)
                            | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                        & r1_orders_2(X0,X3,X2)
                        & r1_orders_2(X0,X3,X1) )
                      | k11_lattice3(X0,X1,X2) != X3 ) )
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( k11_lattice3(X0,X1,X2) = X3
                  <=> ( ! [X4] :
                          ( r1_orders_2(X0,X4,X3)
                          | ~ r1_orders_2(X0,X4,X2)
                          | ~ r1_orders_2(X0,X4,X1)
                          | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                      & r1_orders_2(X0,X3,X2)
                      & r1_orders_2(X0,X3,X1) ) )
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( k11_lattice3(X0,X1,X2) = X3
                  <=> ( ! [X4] :
                          ( r1_orders_2(X0,X4,X3)
                          | ~ r1_orders_2(X0,X4,X2)
                          | ~ r1_orders_2(X0,X4,X1)
                          | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                      & r1_orders_2(X0,X3,X2)
                      & r1_orders_2(X0,X3,X1) ) )
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v2_lattice3(X0)
        & v5_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ! [X3] :
                  ( m1_subset_1(X3,u1_struct_0(X0))
                 => ( k11_lattice3(X0,X1,X2) = X3
                  <=> ( ! [X4] :
                          ( m1_subset_1(X4,u1_struct_0(X0))
                         => ( ( r1_orders_2(X0,X4,X2)
                              & r1_orders_2(X0,X4,X1) )
                           => r1_orders_2(X0,X4,X3) ) )
                      & r1_orders_2(X0,X3,X2)
                      & r1_orders_2(X0,X3,X1) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/lattice3__t15_lattice3.p',l28_lattice3)).

fof(f1564,plain,(
    ! [X4,X5,X3] :
      ( ~ m1_subset_1(X3,u1_struct_0(X4))
      | ~ m1_subset_1(X5,u1_struct_0(X4))
      | ~ l1_orders_2(X4)
      | ~ v2_lattice3(X4)
      | ~ v5_orders_2(X4)
      | k11_lattice3(X4,X3,X5) = k11_lattice3(X4,X5,X3)
      | ~ r1_orders_2(X4,k11_lattice3(X4,X5,X3),X3)
      | ~ m1_subset_1(k11_lattice3(X4,X5,X3),u1_struct_0(X4)) ) ),
    inference(subsumption_resolution,[],[f1563,f136])).

fof(f136,plain,(
    ! [X2,X0,X1] :
      ( r1_orders_2(X0,k11_lattice3(X0,X1,X2),X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(duplicate_literal_removal,[],[f135])).

fof(f135,plain,(
    ! [X2,X0,X1] :
      ( r1_orders_2(X0,k11_lattice3(X0,X1,X2),X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(resolution,[],[f111,f97])).

fof(f111,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(k11_lattice3(X0,X1,X2),u1_struct_0(X0))
      | r1_orders_2(X0,k11_lattice3(X0,X1,X2),X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(subsumption_resolution,[],[f104,f72])).

fof(f104,plain,(
    ! [X2,X0,X1] :
      ( r1_orders_2(X0,k11_lattice3(X0,X1,X2),X1)
      | ~ m1_subset_1(k11_lattice3(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f84])).

fof(f84,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_orders_2(X0,X3,X1)
      | k11_lattice3(X0,X1,X2) != X3
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f59])).

fof(f1563,plain,(
    ! [X4,X5,X3] :
      ( ~ m1_subset_1(X3,u1_struct_0(X4))
      | ~ m1_subset_1(X5,u1_struct_0(X4))
      | ~ l1_orders_2(X4)
      | ~ v2_lattice3(X4)
      | ~ v5_orders_2(X4)
      | k11_lattice3(X4,X3,X5) = k11_lattice3(X4,X5,X3)
      | ~ r1_orders_2(X4,k11_lattice3(X4,X5,X3),X5)
      | ~ r1_orders_2(X4,k11_lattice3(X4,X5,X3),X3)
      | ~ m1_subset_1(k11_lattice3(X4,X5,X3),u1_struct_0(X4)) ) ),
    inference(subsumption_resolution,[],[f1559,f1217])).

fof(f1217,plain,(
    ! [X4,X5,X3] :
      ( ~ m1_subset_1(X5,u1_struct_0(X4))
      | ~ m1_subset_1(X3,u1_struct_0(X4))
      | ~ l1_orders_2(X4)
      | ~ v2_lattice3(X4)
      | ~ v5_orders_2(X4)
      | sP0(X4,X5,X3) ) ),
    inference(subsumption_resolution,[],[f1216,f97])).

fof(f1216,plain,(
    ! [X4,X5,X3] :
      ( ~ m1_subset_1(X3,u1_struct_0(X4))
      | ~ m1_subset_1(X5,u1_struct_0(X4))
      | ~ l1_orders_2(X4)
      | ~ v2_lattice3(X4)
      | ~ v5_orders_2(X4)
      | sP0(X4,X5,X3)
      | ~ m1_subset_1(k11_lattice3(X4,X5,X3),u1_struct_0(X4)) ) ),
    inference(subsumption_resolution,[],[f1215,f134])).

fof(f1215,plain,(
    ! [X4,X5,X3] :
      ( ~ m1_subset_1(X3,u1_struct_0(X4))
      | ~ m1_subset_1(X5,u1_struct_0(X4))
      | ~ l1_orders_2(X4)
      | ~ v2_lattice3(X4)
      | ~ v5_orders_2(X4)
      | sP0(X4,X5,X3)
      | ~ r1_orders_2(X4,k11_lattice3(X4,X5,X3),X3)
      | ~ m1_subset_1(k11_lattice3(X4,X5,X3),u1_struct_0(X4)) ) ),
    inference(subsumption_resolution,[],[f1211,f136])).

fof(f1211,plain,(
    ! [X4,X5,X3] :
      ( ~ m1_subset_1(X3,u1_struct_0(X4))
      | ~ m1_subset_1(X5,u1_struct_0(X4))
      | ~ l1_orders_2(X4)
      | ~ v2_lattice3(X4)
      | ~ v5_orders_2(X4)
      | sP0(X4,X5,X3)
      | ~ r1_orders_2(X4,k11_lattice3(X4,X5,X3),X5)
      | ~ r1_orders_2(X4,k11_lattice3(X4,X5,X3),X3)
      | ~ m1_subset_1(k11_lattice3(X4,X5,X3),u1_struct_0(X4)) ) ),
    inference(duplicate_literal_removal,[],[f1196])).

fof(f1196,plain,(
    ! [X4,X5,X3] :
      ( ~ m1_subset_1(X3,u1_struct_0(X4))
      | ~ m1_subset_1(X5,u1_struct_0(X4))
      | ~ l1_orders_2(X4)
      | ~ v2_lattice3(X4)
      | ~ v5_orders_2(X4)
      | sP0(X4,X5,X3)
      | ~ r1_orders_2(X4,k11_lattice3(X4,X5,X3),X5)
      | ~ m1_subset_1(X5,u1_struct_0(X4))
      | sP0(X4,X5,X3)
      | ~ r1_orders_2(X4,k11_lattice3(X4,X5,X3),X5)
      | ~ r1_orders_2(X4,k11_lattice3(X4,X5,X3),X3)
      | ~ m1_subset_1(k11_lattice3(X4,X5,X3),u1_struct_0(X4))
      | ~ m1_subset_1(X5,u1_struct_0(X4))
      | ~ m1_subset_1(X3,u1_struct_0(X4))
      | ~ v5_orders_2(X4)
      | ~ l1_orders_2(X4) ) ),
    inference(resolution,[],[f807,f82])).

fof(f82,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_orders_2(X0,sK5(X0,X1,X2,X3),X2)
      | sP0(X0,X2,X1)
      | ~ r1_orders_2(X0,X3,X2)
      | ~ r1_orders_2(X0,X3,X1)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ v5_orders_2(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f54,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( sP0(X0,X2,X1)
              | ! [X3] :
                  ( ( ~ r1_orders_2(X0,sK5(X0,X1,X2,X3),X3)
                    & r1_orders_2(X0,sK5(X0,X1,X2,X3),X2)
                    & r1_orders_2(X0,sK5(X0,X1,X2,X3),X1)
                    & m1_subset_1(sK5(X0,X1,X2,X3),u1_struct_0(X0)) )
                  | ~ r1_orders_2(X0,X3,X2)
                  | ~ r1_orders_2(X0,X3,X1)
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ v5_orders_2(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f43,f53])).

fof(f53,plain,(
    ! [X3,X2,X1,X0] :
      ( ? [X4] :
          ( ~ r1_orders_2(X0,X4,X3)
          & r1_orders_2(X0,X4,X2)
          & r1_orders_2(X0,X4,X1)
          & m1_subset_1(X4,u1_struct_0(X0)) )
     => ( ~ r1_orders_2(X0,sK5(X0,X1,X2,X3),X3)
        & r1_orders_2(X0,sK5(X0,X1,X2,X3),X2)
        & r1_orders_2(X0,sK5(X0,X1,X2,X3),X1)
        & m1_subset_1(sK5(X0,X1,X2,X3),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f43,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( sP0(X0,X2,X1)
              | ! [X3] :
                  ( ? [X4] :
                      ( ~ r1_orders_2(X0,X4,X3)
                      & r1_orders_2(X0,X4,X2)
                      & r1_orders_2(X0,X4,X1)
                      & m1_subset_1(X4,u1_struct_0(X0)) )
                  | ~ r1_orders_2(X0,X3,X2)
                  | ~ r1_orders_2(X0,X3,X1)
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ v5_orders_2(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(definition_folding,[],[f31,f42])).

fof(f42,plain,(
    ! [X0,X2,X1] :
      ( ! [X5] :
          ( ( k11_lattice3(X0,X1,X2) = X5
          <=> ( ! [X6] :
                  ( r1_orders_2(X0,X6,X5)
                  | ~ r1_orders_2(X0,X6,X2)
                  | ~ r1_orders_2(X0,X6,X1)
                  | ~ m1_subset_1(X6,u1_struct_0(X0)) )
              & r1_orders_2(X0,X5,X2)
              & r1_orders_2(X0,X5,X1) ) )
          | ~ m1_subset_1(X5,u1_struct_0(X0)) )
      | ~ sP0(X0,X2,X1) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X5] :
                  ( ( k11_lattice3(X0,X1,X2) = X5
                  <=> ( ! [X6] :
                          ( r1_orders_2(X0,X6,X5)
                          | ~ r1_orders_2(X0,X6,X2)
                          | ~ r1_orders_2(X0,X6,X1)
                          | ~ m1_subset_1(X6,u1_struct_0(X0)) )
                      & r1_orders_2(X0,X5,X2)
                      & r1_orders_2(X0,X5,X1) ) )
                  | ~ m1_subset_1(X5,u1_struct_0(X0)) )
              | ! [X3] :
                  ( ? [X4] :
                      ( ~ r1_orders_2(X0,X4,X3)
                      & r1_orders_2(X0,X4,X2)
                      & r1_orders_2(X0,X4,X1)
                      & m1_subset_1(X4,u1_struct_0(X0)) )
                  | ~ r1_orders_2(X0,X3,X2)
                  | ~ r1_orders_2(X0,X3,X1)
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ v5_orders_2(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X5] :
                  ( ( k11_lattice3(X0,X1,X2) = X5
                  <=> ( ! [X6] :
                          ( r1_orders_2(X0,X6,X5)
                          | ~ r1_orders_2(X0,X6,X2)
                          | ~ r1_orders_2(X0,X6,X1)
                          | ~ m1_subset_1(X6,u1_struct_0(X0)) )
                      & r1_orders_2(X0,X5,X2)
                      & r1_orders_2(X0,X5,X1) ) )
                  | ~ m1_subset_1(X5,u1_struct_0(X0)) )
              | ! [X3] :
                  ( ? [X4] :
                      ( ~ r1_orders_2(X0,X4,X3)
                      & r1_orders_2(X0,X4,X2)
                      & r1_orders_2(X0,X4,X1)
                      & m1_subset_1(X4,u1_struct_0(X0)) )
                  | ~ r1_orders_2(X0,X3,X2)
                  | ~ r1_orders_2(X0,X3,X1)
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ v5_orders_2(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ( v5_orders_2(X0)
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => ( ? [X3] :
                      ( ! [X4] :
                          ( m1_subset_1(X4,u1_struct_0(X0))
                         => ( ( r1_orders_2(X0,X4,X2)
                              & r1_orders_2(X0,X4,X1) )
                           => r1_orders_2(X0,X4,X3) ) )
                      & r1_orders_2(X0,X3,X2)
                      & r1_orders_2(X0,X3,X1)
                      & m1_subset_1(X3,u1_struct_0(X0)) )
                 => ! [X5] :
                      ( m1_subset_1(X5,u1_struct_0(X0))
                     => ( k11_lattice3(X0,X1,X2) = X5
                      <=> ( ! [X6] :
                              ( m1_subset_1(X6,u1_struct_0(X0))
                             => ( ( r1_orders_2(X0,X6,X2)
                                  & r1_orders_2(X0,X6,X1) )
                               => r1_orders_2(X0,X6,X5) ) )
                          & r1_orders_2(X0,X5,X2)
                          & r1_orders_2(X0,X5,X1) ) ) ) ) ) ) ) ) ),
    inference(rectify,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ( v5_orders_2(X0)
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => ( ? [X3] :
                      ( ! [X4] :
                          ( m1_subset_1(X4,u1_struct_0(X0))
                         => ( ( r1_orders_2(X0,X4,X2)
                              & r1_orders_2(X0,X4,X1) )
                           => r1_orders_2(X0,X4,X3) ) )
                      & r1_orders_2(X0,X3,X2)
                      & r1_orders_2(X0,X3,X1)
                      & m1_subset_1(X3,u1_struct_0(X0)) )
                 => ! [X3] :
                      ( m1_subset_1(X3,u1_struct_0(X0))
                     => ( k11_lattice3(X0,X1,X2) = X3
                      <=> ( ! [X4] :
                              ( m1_subset_1(X4,u1_struct_0(X0))
                             => ( ( r1_orders_2(X0,X4,X2)
                                  & r1_orders_2(X0,X4,X1) )
                               => r1_orders_2(X0,X4,X3) ) )
                          & r1_orders_2(X0,X3,X2)
                          & r1_orders_2(X0,X3,X1) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/lattice3__t15_lattice3.p',d14_lattice3)).

fof(f807,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r1_orders_2(X0,sK5(X0,X1,X2,k11_lattice3(X0,X3,X1)),X3)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0)
      | sP0(X0,X2,X1)
      | ~ r1_orders_2(X0,k11_lattice3(X0,X3,X1),X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0)) ) ),
    inference(subsumption_resolution,[],[f806,f97])).

fof(f806,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r1_orders_2(X0,sK5(X0,X1,X2,k11_lattice3(X0,X3,X1)),X3)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0)
      | sP0(X0,X2,X1)
      | ~ r1_orders_2(X0,k11_lattice3(X0,X3,X1),X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(k11_lattice3(X0,X3,X1),u1_struct_0(X0)) ) ),
    inference(subsumption_resolution,[],[f805,f134])).

fof(f805,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r1_orders_2(X0,sK5(X0,X1,X2,k11_lattice3(X0,X3,X1)),X3)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0)
      | sP0(X0,X2,X1)
      | ~ r1_orders_2(X0,k11_lattice3(X0,X3,X1),X2)
      | ~ r1_orders_2(X0,k11_lattice3(X0,X3,X1),X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(k11_lattice3(X0,X3,X1),u1_struct_0(X0)) ) ),
    inference(duplicate_literal_removal,[],[f788])).

fof(f788,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r1_orders_2(X0,sK5(X0,X1,X2,k11_lattice3(X0,X3,X1)),X3)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0)
      | sP0(X0,X2,X1)
      | ~ r1_orders_2(X0,k11_lattice3(X0,X3,X1),X2)
      | ~ r1_orders_2(X0,k11_lattice3(X0,X3,X1),X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | sP0(X0,X2,X1)
      | ~ r1_orders_2(X0,k11_lattice3(X0,X3,X1),X2)
      | ~ r1_orders_2(X0,k11_lattice3(X0,X3,X1),X1)
      | ~ m1_subset_1(k11_lattice3(X0,X3,X1),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ v5_orders_2(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(resolution,[],[f404,f81])).

fof(f81,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_orders_2(X0,sK5(X0,X1,X2,X3),X1)
      | sP0(X0,X2,X1)
      | ~ r1_orders_2(X0,X3,X2)
      | ~ r1_orders_2(X0,X3,X1)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ v5_orders_2(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f404,plain,(
    ! [X6,X8,X7,X5,X9] :
      ( ~ r1_orders_2(X5,sK5(X5,X6,X7,k11_lattice3(X5,X8,X9)),X9)
      | ~ r1_orders_2(X5,sK5(X5,X6,X7,k11_lattice3(X5,X8,X9)),X8)
      | ~ m1_subset_1(X9,u1_struct_0(X5))
      | ~ m1_subset_1(X8,u1_struct_0(X5))
      | ~ l1_orders_2(X5)
      | ~ v2_lattice3(X5)
      | ~ v5_orders_2(X5)
      | sP0(X5,X7,X6)
      | ~ r1_orders_2(X5,k11_lattice3(X5,X8,X9),X7)
      | ~ r1_orders_2(X5,k11_lattice3(X5,X8,X9),X6)
      | ~ m1_subset_1(X7,u1_struct_0(X5))
      | ~ m1_subset_1(X6,u1_struct_0(X5)) ) ),
    inference(subsumption_resolution,[],[f403,f97])).

fof(f403,plain,(
    ! [X6,X8,X7,X5,X9] :
      ( ~ r1_orders_2(X5,sK5(X5,X6,X7,k11_lattice3(X5,X8,X9)),X8)
      | ~ r1_orders_2(X5,sK5(X5,X6,X7,k11_lattice3(X5,X8,X9)),X9)
      | ~ m1_subset_1(X9,u1_struct_0(X5))
      | ~ m1_subset_1(X8,u1_struct_0(X5))
      | ~ l1_orders_2(X5)
      | ~ v2_lattice3(X5)
      | ~ v5_orders_2(X5)
      | sP0(X5,X7,X6)
      | ~ r1_orders_2(X5,k11_lattice3(X5,X8,X9),X7)
      | ~ r1_orders_2(X5,k11_lattice3(X5,X8,X9),X6)
      | ~ m1_subset_1(k11_lattice3(X5,X8,X9),u1_struct_0(X5))
      | ~ m1_subset_1(X7,u1_struct_0(X5))
      | ~ m1_subset_1(X6,u1_struct_0(X5)) ) ),
    inference(subsumption_resolution,[],[f400,f80])).

fof(f80,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(sK5(X0,X1,X2,X3),u1_struct_0(X0))
      | sP0(X0,X2,X1)
      | ~ r1_orders_2(X0,X3,X2)
      | ~ r1_orders_2(X0,X3,X1)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ v5_orders_2(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f400,plain,(
    ! [X6,X8,X7,X5,X9] :
      ( ~ r1_orders_2(X5,sK5(X5,X6,X7,k11_lattice3(X5,X8,X9)),X8)
      | ~ m1_subset_1(sK5(X5,X6,X7,k11_lattice3(X5,X8,X9)),u1_struct_0(X5))
      | ~ r1_orders_2(X5,sK5(X5,X6,X7,k11_lattice3(X5,X8,X9)),X9)
      | ~ m1_subset_1(X9,u1_struct_0(X5))
      | ~ m1_subset_1(X8,u1_struct_0(X5))
      | ~ l1_orders_2(X5)
      | ~ v2_lattice3(X5)
      | ~ v5_orders_2(X5)
      | sP0(X5,X7,X6)
      | ~ r1_orders_2(X5,k11_lattice3(X5,X8,X9),X7)
      | ~ r1_orders_2(X5,k11_lattice3(X5,X8,X9),X6)
      | ~ m1_subset_1(k11_lattice3(X5,X8,X9),u1_struct_0(X5))
      | ~ m1_subset_1(X7,u1_struct_0(X5))
      | ~ m1_subset_1(X6,u1_struct_0(X5)) ) ),
    inference(duplicate_literal_removal,[],[f385])).

fof(f385,plain,(
    ! [X6,X8,X7,X5,X9] :
      ( ~ r1_orders_2(X5,sK5(X5,X6,X7,k11_lattice3(X5,X8,X9)),X8)
      | ~ m1_subset_1(sK5(X5,X6,X7,k11_lattice3(X5,X8,X9)),u1_struct_0(X5))
      | ~ r1_orders_2(X5,sK5(X5,X6,X7,k11_lattice3(X5,X8,X9)),X9)
      | ~ m1_subset_1(X9,u1_struct_0(X5))
      | ~ m1_subset_1(X8,u1_struct_0(X5))
      | ~ l1_orders_2(X5)
      | ~ v2_lattice3(X5)
      | ~ v5_orders_2(X5)
      | sP0(X5,X7,X6)
      | ~ r1_orders_2(X5,k11_lattice3(X5,X8,X9),X7)
      | ~ r1_orders_2(X5,k11_lattice3(X5,X8,X9),X6)
      | ~ m1_subset_1(k11_lattice3(X5,X8,X9),u1_struct_0(X5))
      | ~ m1_subset_1(X7,u1_struct_0(X5))
      | ~ m1_subset_1(X6,u1_struct_0(X5))
      | ~ v5_orders_2(X5)
      | ~ l1_orders_2(X5) ) ),
    inference(resolution,[],[f198,f83])).

fof(f83,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r1_orders_2(X0,sK5(X0,X1,X2,X3),X3)
      | sP0(X0,X2,X1)
      | ~ r1_orders_2(X0,X3,X2)
      | ~ r1_orders_2(X0,X3,X1)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ v5_orders_2(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f198,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_orders_2(X0,X1,k11_lattice3(X0,X3,X2))
      | ~ r1_orders_2(X0,X1,X3)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ r1_orders_2(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(duplicate_literal_removal,[],[f195])).

fof(f195,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r1_orders_2(X0,X1,X2)
      | ~ r1_orders_2(X0,X1,X3)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | r1_orders_2(X0,X1,k11_lattice3(X0,X3,X2))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(resolution,[],[f109,f97])).

fof(f109,plain,(
    ! [X2,X0,X5,X1] :
      ( ~ m1_subset_1(k11_lattice3(X0,X1,X2),u1_struct_0(X0))
      | ~ r1_orders_2(X0,X5,X2)
      | ~ r1_orders_2(X0,X5,X1)
      | ~ m1_subset_1(X5,u1_struct_0(X0))
      | r1_orders_2(X0,X5,k11_lattice3(X0,X1,X2))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(subsumption_resolution,[],[f102,f72])).

fof(f102,plain,(
    ! [X2,X0,X5,X1] :
      ( r1_orders_2(X0,X5,k11_lattice3(X0,X1,X2))
      | ~ r1_orders_2(X0,X5,X2)
      | ~ r1_orders_2(X0,X5,X1)
      | ~ m1_subset_1(X5,u1_struct_0(X0))
      | ~ m1_subset_1(k11_lattice3(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f86])).

fof(f86,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r1_orders_2(X0,X5,X3)
      | ~ r1_orders_2(X0,X5,X2)
      | ~ r1_orders_2(X0,X5,X1)
      | ~ m1_subset_1(X5,u1_struct_0(X0))
      | k11_lattice3(X0,X1,X2) != X3
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f59])).

fof(f1559,plain,(
    ! [X4,X5,X3] :
      ( ~ m1_subset_1(X3,u1_struct_0(X4))
      | ~ m1_subset_1(X5,u1_struct_0(X4))
      | ~ l1_orders_2(X4)
      | ~ v2_lattice3(X4)
      | ~ v5_orders_2(X4)
      | k11_lattice3(X4,X3,X5) = k11_lattice3(X4,X5,X3)
      | ~ r1_orders_2(X4,k11_lattice3(X4,X5,X3),X5)
      | ~ sP0(X4,X5,X3)
      | ~ r1_orders_2(X4,k11_lattice3(X4,X5,X3),X3)
      | ~ m1_subset_1(k11_lattice3(X4,X5,X3),u1_struct_0(X4)) ) ),
    inference(duplicate_literal_removal,[],[f1544])).

fof(f1544,plain,(
    ! [X4,X5,X3] :
      ( ~ m1_subset_1(X3,u1_struct_0(X4))
      | ~ m1_subset_1(X5,u1_struct_0(X4))
      | ~ l1_orders_2(X4)
      | ~ v2_lattice3(X4)
      | ~ v5_orders_2(X4)
      | k11_lattice3(X4,X3,X5) = k11_lattice3(X4,X5,X3)
      | ~ r1_orders_2(X4,k11_lattice3(X4,X5,X3),X5)
      | ~ sP0(X4,X5,X3)
      | k11_lattice3(X4,X3,X5) = k11_lattice3(X4,X5,X3)
      | ~ r1_orders_2(X4,k11_lattice3(X4,X5,X3),X5)
      | ~ r1_orders_2(X4,k11_lattice3(X4,X5,X3),X3)
      | ~ m1_subset_1(k11_lattice3(X4,X5,X3),u1_struct_0(X4))
      | ~ sP0(X4,X5,X3) ) ),
    inference(resolution,[],[f867,f78])).

fof(f78,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_orders_2(X0,sK4(X0,X1,X2,X3),X1)
      | k11_lattice3(X0,X2,X1) = X3
      | ~ r1_orders_2(X0,X3,X1)
      | ~ r1_orders_2(X0,X3,X2)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f52,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( ( ( k11_lattice3(X0,X2,X1) = X3
              | ( ~ r1_orders_2(X0,sK4(X0,X1,X2,X3),X3)
                & r1_orders_2(X0,sK4(X0,X1,X2,X3),X1)
                & r1_orders_2(X0,sK4(X0,X1,X2,X3),X2)
                & m1_subset_1(sK4(X0,X1,X2,X3),u1_struct_0(X0)) )
              | ~ r1_orders_2(X0,X3,X1)
              | ~ r1_orders_2(X0,X3,X2) )
            & ( ( ! [X5] :
                    ( r1_orders_2(X0,X5,X3)
                    | ~ r1_orders_2(X0,X5,X1)
                    | ~ r1_orders_2(X0,X5,X2)
                    | ~ m1_subset_1(X5,u1_struct_0(X0)) )
                & r1_orders_2(X0,X3,X1)
                & r1_orders_2(X0,X3,X2) )
              | k11_lattice3(X0,X2,X1) != X3 ) )
          | ~ m1_subset_1(X3,u1_struct_0(X0)) )
      | ~ sP0(X0,X1,X2) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f50,f51])).

fof(f51,plain,(
    ! [X3,X2,X1,X0] :
      ( ? [X4] :
          ( ~ r1_orders_2(X0,X4,X3)
          & r1_orders_2(X0,X4,X1)
          & r1_orders_2(X0,X4,X2)
          & m1_subset_1(X4,u1_struct_0(X0)) )
     => ( ~ r1_orders_2(X0,sK4(X0,X1,X2,X3),X3)
        & r1_orders_2(X0,sK4(X0,X1,X2,X3),X1)
        & r1_orders_2(X0,sK4(X0,X1,X2,X3),X2)
        & m1_subset_1(sK4(X0,X1,X2,X3),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f50,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( ( ( k11_lattice3(X0,X2,X1) = X3
              | ? [X4] :
                  ( ~ r1_orders_2(X0,X4,X3)
                  & r1_orders_2(X0,X4,X1)
                  & r1_orders_2(X0,X4,X2)
                  & m1_subset_1(X4,u1_struct_0(X0)) )
              | ~ r1_orders_2(X0,X3,X1)
              | ~ r1_orders_2(X0,X3,X2) )
            & ( ( ! [X5] :
                    ( r1_orders_2(X0,X5,X3)
                    | ~ r1_orders_2(X0,X5,X1)
                    | ~ r1_orders_2(X0,X5,X2)
                    | ~ m1_subset_1(X5,u1_struct_0(X0)) )
                & r1_orders_2(X0,X3,X1)
                & r1_orders_2(X0,X3,X2) )
              | k11_lattice3(X0,X2,X1) != X3 ) )
          | ~ m1_subset_1(X3,u1_struct_0(X0)) )
      | ~ sP0(X0,X1,X2) ) ),
    inference(rectify,[],[f49])).

fof(f49,plain,(
    ! [X0,X2,X1] :
      ( ! [X5] :
          ( ( ( k11_lattice3(X0,X1,X2) = X5
              | ? [X6] :
                  ( ~ r1_orders_2(X0,X6,X5)
                  & r1_orders_2(X0,X6,X2)
                  & r1_orders_2(X0,X6,X1)
                  & m1_subset_1(X6,u1_struct_0(X0)) )
              | ~ r1_orders_2(X0,X5,X2)
              | ~ r1_orders_2(X0,X5,X1) )
            & ( ( ! [X6] :
                    ( r1_orders_2(X0,X6,X5)
                    | ~ r1_orders_2(X0,X6,X2)
                    | ~ r1_orders_2(X0,X6,X1)
                    | ~ m1_subset_1(X6,u1_struct_0(X0)) )
                & r1_orders_2(X0,X5,X2)
                & r1_orders_2(X0,X5,X1) )
              | k11_lattice3(X0,X1,X2) != X5 ) )
          | ~ m1_subset_1(X5,u1_struct_0(X0)) )
      | ~ sP0(X0,X2,X1) ) ),
    inference(flattening,[],[f48])).

fof(f48,plain,(
    ! [X0,X2,X1] :
      ( ! [X5] :
          ( ( ( k11_lattice3(X0,X1,X2) = X5
              | ? [X6] :
                  ( ~ r1_orders_2(X0,X6,X5)
                  & r1_orders_2(X0,X6,X2)
                  & r1_orders_2(X0,X6,X1)
                  & m1_subset_1(X6,u1_struct_0(X0)) )
              | ~ r1_orders_2(X0,X5,X2)
              | ~ r1_orders_2(X0,X5,X1) )
            & ( ( ! [X6] :
                    ( r1_orders_2(X0,X6,X5)
                    | ~ r1_orders_2(X0,X6,X2)
                    | ~ r1_orders_2(X0,X6,X1)
                    | ~ m1_subset_1(X6,u1_struct_0(X0)) )
                & r1_orders_2(X0,X5,X2)
                & r1_orders_2(X0,X5,X1) )
              | k11_lattice3(X0,X1,X2) != X5 ) )
          | ~ m1_subset_1(X5,u1_struct_0(X0)) )
      | ~ sP0(X0,X2,X1) ) ),
    inference(nnf_transformation,[],[f42])).

fof(f867,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r1_orders_2(X0,sK4(X0,X1,X2,k11_lattice3(X0,X3,X2)),X3)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0)
      | k11_lattice3(X0,X2,X1) = k11_lattice3(X0,X3,X2)
      | ~ r1_orders_2(X0,k11_lattice3(X0,X3,X2),X1)
      | ~ sP0(X0,X1,X2) ) ),
    inference(subsumption_resolution,[],[f866,f97])).

fof(f866,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r1_orders_2(X0,sK4(X0,X1,X2,k11_lattice3(X0,X3,X2)),X3)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0)
      | k11_lattice3(X0,X2,X1) = k11_lattice3(X0,X3,X2)
      | ~ r1_orders_2(X0,k11_lattice3(X0,X3,X2),X1)
      | ~ sP0(X0,X1,X2)
      | ~ m1_subset_1(k11_lattice3(X0,X3,X2),u1_struct_0(X0)) ) ),
    inference(subsumption_resolution,[],[f865,f134])).

fof(f865,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r1_orders_2(X0,sK4(X0,X1,X2,k11_lattice3(X0,X3,X2)),X3)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0)
      | k11_lattice3(X0,X2,X1) = k11_lattice3(X0,X3,X2)
      | ~ r1_orders_2(X0,k11_lattice3(X0,X3,X2),X1)
      | ~ r1_orders_2(X0,k11_lattice3(X0,X3,X2),X2)
      | ~ sP0(X0,X1,X2)
      | ~ m1_subset_1(k11_lattice3(X0,X3,X2),u1_struct_0(X0)) ) ),
    inference(duplicate_literal_removal,[],[f848])).

fof(f848,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r1_orders_2(X0,sK4(X0,X1,X2,k11_lattice3(X0,X3,X2)),X3)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0)
      | k11_lattice3(X0,X2,X1) = k11_lattice3(X0,X3,X2)
      | ~ r1_orders_2(X0,k11_lattice3(X0,X3,X2),X1)
      | ~ r1_orders_2(X0,k11_lattice3(X0,X3,X2),X2)
      | ~ sP0(X0,X1,X2)
      | k11_lattice3(X0,X2,X1) = k11_lattice3(X0,X3,X2)
      | ~ r1_orders_2(X0,k11_lattice3(X0,X3,X2),X1)
      | ~ r1_orders_2(X0,k11_lattice3(X0,X3,X2),X2)
      | ~ m1_subset_1(k11_lattice3(X0,X3,X2),u1_struct_0(X0))
      | ~ sP0(X0,X1,X2) ) ),
    inference(resolution,[],[f402,f77])).

fof(f77,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_orders_2(X0,sK4(X0,X1,X2,X3),X2)
      | k11_lattice3(X0,X2,X1) = X3
      | ~ r1_orders_2(X0,X3,X1)
      | ~ r1_orders_2(X0,X3,X2)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f402,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ r1_orders_2(X0,sK4(X0,X1,X2,k11_lattice3(X0,X3,X4)),X4)
      | ~ r1_orders_2(X0,sK4(X0,X1,X2,k11_lattice3(X0,X3,X4)),X3)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0)
      | k11_lattice3(X0,X2,X1) = k11_lattice3(X0,X3,X4)
      | ~ r1_orders_2(X0,k11_lattice3(X0,X3,X4),X1)
      | ~ r1_orders_2(X0,k11_lattice3(X0,X3,X4),X2)
      | ~ sP0(X0,X1,X2) ) ),
    inference(subsumption_resolution,[],[f401,f97])).

fof(f401,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ r1_orders_2(X0,sK4(X0,X1,X2,k11_lattice3(X0,X3,X4)),X3)
      | ~ r1_orders_2(X0,sK4(X0,X1,X2,k11_lattice3(X0,X3,X4)),X4)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0)
      | k11_lattice3(X0,X2,X1) = k11_lattice3(X0,X3,X4)
      | ~ r1_orders_2(X0,k11_lattice3(X0,X3,X4),X1)
      | ~ r1_orders_2(X0,k11_lattice3(X0,X3,X4),X2)
      | ~ m1_subset_1(k11_lattice3(X0,X3,X4),u1_struct_0(X0))
      | ~ sP0(X0,X1,X2) ) ),
    inference(subsumption_resolution,[],[f384,f76])).

fof(f76,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(sK4(X0,X1,X2,X3),u1_struct_0(X0))
      | k11_lattice3(X0,X2,X1) = X3
      | ~ r1_orders_2(X0,X3,X1)
      | ~ r1_orders_2(X0,X3,X2)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f384,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ r1_orders_2(X0,sK4(X0,X1,X2,k11_lattice3(X0,X3,X4)),X3)
      | ~ m1_subset_1(sK4(X0,X1,X2,k11_lattice3(X0,X3,X4)),u1_struct_0(X0))
      | ~ r1_orders_2(X0,sK4(X0,X1,X2,k11_lattice3(X0,X3,X4)),X4)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0)
      | k11_lattice3(X0,X2,X1) = k11_lattice3(X0,X3,X4)
      | ~ r1_orders_2(X0,k11_lattice3(X0,X3,X4),X1)
      | ~ r1_orders_2(X0,k11_lattice3(X0,X3,X4),X2)
      | ~ m1_subset_1(k11_lattice3(X0,X3,X4),u1_struct_0(X0))
      | ~ sP0(X0,X1,X2) ) ),
    inference(resolution,[],[f198,f79])).

fof(f79,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r1_orders_2(X0,sK4(X0,X1,X2,X3),X3)
      | k11_lattice3(X0,X2,X1) = X3
      | ~ r1_orders_2(X0,X3,X1)
      | ~ r1_orders_2(X0,X3,X2)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f69,plain,(
    k11_lattice3(sK1,sK2,sK3) != k11_lattice3(sK1,sK3,sK2) ),
    inference(cnf_transformation,[],[f47])).
%------------------------------------------------------------------------------
