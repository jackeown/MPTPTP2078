%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : yellow_0__t22_yellow_0.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n030.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:41:39 EDT 2019

% Result     : Theorem 1.80s
% Output     : Refutation 1.80s
% Verified   : 
% Statistics : Number of formulae       :  202 (1797 expanded)
%              Number of leaves         :   30 ( 691 expanded)
%              Depth                    :   44
%              Number of atoms          : 1533 (27484 expanded)
%              Number of equality atoms :   81 (1715 expanded)
%              Maximal formula depth    :   25 (   9 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f8340,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f137,f141,f145,f149,f156,f160,f164,f1923,f1946,f1954,f2517,f6815,f8169])).

fof(f8169,plain,
    ( spl14_1
    | ~ spl14_2
    | ~ spl14_4
    | ~ spl14_14 ),
    inference(avatar_contradiction_clause,[],[f8168])).

fof(f8168,plain,
    ( $false
    | ~ spl14_1
    | ~ spl14_2
    | ~ spl14_4
    | ~ spl14_14 ),
    inference(subsumption_resolution,[],[f8167,f76])).

fof(f76,plain,(
    v5_orders_2(sK1) ),
    inference(cnf_transformation,[],[f57])).

fof(f57,plain,
    ( ( ( ~ r1_orders_2(sK1,sK4,sK5)
        & r1_orders_2(sK1,sK3,sK5)
        & r1_orders_2(sK1,sK2,sK5)
        & m1_subset_1(sK5,u1_struct_0(sK1)) )
      | ~ r1_orders_2(sK1,sK3,sK4)
      | ~ r1_orders_2(sK1,sK2,sK4)
      | k13_lattice3(sK1,sK2,sK3) != sK4 )
    & ( ( ! [X5] :
            ( r1_orders_2(sK1,sK4,X5)
            | ~ r1_orders_2(sK1,sK3,X5)
            | ~ r1_orders_2(sK1,sK2,X5)
            | ~ m1_subset_1(X5,u1_struct_0(sK1)) )
        & r1_orders_2(sK1,sK3,sK4)
        & r1_orders_2(sK1,sK2,sK4) )
      | k13_lattice3(sK1,sK2,sK3) = sK4 )
    & m1_subset_1(sK4,u1_struct_0(sK1))
    & m1_subset_1(sK3,u1_struct_0(sK1))
    & m1_subset_1(sK2,u1_struct_0(sK1))
    & l1_orders_2(sK1)
    & v1_lattice3(sK1)
    & v5_orders_2(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4,sK5])],[f51,f56,f55,f54,f53,f52])).

fof(f52,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ? [X3] :
                    ( ( ? [X4] :
                          ( ~ r1_orders_2(X0,X3,X4)
                          & r1_orders_2(X0,X2,X4)
                          & r1_orders_2(X0,X1,X4)
                          & m1_subset_1(X4,u1_struct_0(X0)) )
                      | ~ r1_orders_2(X0,X2,X3)
                      | ~ r1_orders_2(X0,X1,X3)
                      | k13_lattice3(X0,X1,X2) != X3 )
                    & ( ( ! [X5] :
                            ( r1_orders_2(X0,X3,X5)
                            | ~ r1_orders_2(X0,X2,X5)
                            | ~ r1_orders_2(X0,X1,X5)
                            | ~ m1_subset_1(X5,u1_struct_0(X0)) )
                        & r1_orders_2(X0,X2,X3)
                        & r1_orders_2(X0,X1,X3) )
                      | k13_lattice3(X0,X1,X2) = X3 )
                    & m1_subset_1(X3,u1_struct_0(X0)) )
                & m1_subset_1(X2,u1_struct_0(X0)) )
            & m1_subset_1(X1,u1_struct_0(X0)) )
        & l1_orders_2(X0)
        & v1_lattice3(X0)
        & v5_orders_2(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( ? [X4] :
                        ( ~ r1_orders_2(sK1,X3,X4)
                        & r1_orders_2(sK1,X2,X4)
                        & r1_orders_2(sK1,X1,X4)
                        & m1_subset_1(X4,u1_struct_0(sK1)) )
                    | ~ r1_orders_2(sK1,X2,X3)
                    | ~ r1_orders_2(sK1,X1,X3)
                    | k13_lattice3(sK1,X1,X2) != X3 )
                  & ( ( ! [X5] :
                          ( r1_orders_2(sK1,X3,X5)
                          | ~ r1_orders_2(sK1,X2,X5)
                          | ~ r1_orders_2(sK1,X1,X5)
                          | ~ m1_subset_1(X5,u1_struct_0(sK1)) )
                      & r1_orders_2(sK1,X2,X3)
                      & r1_orders_2(sK1,X1,X3) )
                    | k13_lattice3(sK1,X1,X2) = X3 )
                  & m1_subset_1(X3,u1_struct_0(sK1)) )
              & m1_subset_1(X2,u1_struct_0(sK1)) )
          & m1_subset_1(X1,u1_struct_0(sK1)) )
      & l1_orders_2(sK1)
      & v1_lattice3(sK1)
      & v5_orders_2(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f53,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( ? [X4] :
                        ( ~ r1_orders_2(X0,X3,X4)
                        & r1_orders_2(X0,X2,X4)
                        & r1_orders_2(X0,X1,X4)
                        & m1_subset_1(X4,u1_struct_0(X0)) )
                    | ~ r1_orders_2(X0,X2,X3)
                    | ~ r1_orders_2(X0,X1,X3)
                    | k13_lattice3(X0,X1,X2) != X3 )
                  & ( ( ! [X5] :
                          ( r1_orders_2(X0,X3,X5)
                          | ~ r1_orders_2(X0,X2,X5)
                          | ~ r1_orders_2(X0,X1,X5)
                          | ~ m1_subset_1(X5,u1_struct_0(X0)) )
                      & r1_orders_2(X0,X2,X3)
                      & r1_orders_2(X0,X1,X3) )
                    | k13_lattice3(X0,X1,X2) = X3 )
                  & m1_subset_1(X3,u1_struct_0(X0)) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
     => ( ? [X2] :
            ( ? [X3] :
                ( ( ? [X4] :
                      ( ~ r1_orders_2(X0,X3,X4)
                      & r1_orders_2(X0,X2,X4)
                      & r1_orders_2(X0,sK2,X4)
                      & m1_subset_1(X4,u1_struct_0(X0)) )
                  | ~ r1_orders_2(X0,X2,X3)
                  | ~ r1_orders_2(X0,sK2,X3)
                  | k13_lattice3(X0,sK2,X2) != X3 )
                & ( ( ! [X5] :
                        ( r1_orders_2(X0,X3,X5)
                        | ~ r1_orders_2(X0,X2,X5)
                        | ~ r1_orders_2(X0,sK2,X5)
                        | ~ m1_subset_1(X5,u1_struct_0(X0)) )
                    & r1_orders_2(X0,X2,X3)
                    & r1_orders_2(X0,sK2,X3) )
                  | k13_lattice3(X0,sK2,X2) = X3 )
                & m1_subset_1(X3,u1_struct_0(X0)) )
            & m1_subset_1(X2,u1_struct_0(X0)) )
        & m1_subset_1(sK2,u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f54,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ? [X3] :
              ( ( ? [X4] :
                    ( ~ r1_orders_2(X0,X3,X4)
                    & r1_orders_2(X0,X2,X4)
                    & r1_orders_2(X0,X1,X4)
                    & m1_subset_1(X4,u1_struct_0(X0)) )
                | ~ r1_orders_2(X0,X2,X3)
                | ~ r1_orders_2(X0,X1,X3)
                | k13_lattice3(X0,X1,X2) != X3 )
              & ( ( ! [X5] :
                      ( r1_orders_2(X0,X3,X5)
                      | ~ r1_orders_2(X0,X2,X5)
                      | ~ r1_orders_2(X0,X1,X5)
                      | ~ m1_subset_1(X5,u1_struct_0(X0)) )
                  & r1_orders_2(X0,X2,X3)
                  & r1_orders_2(X0,X1,X3) )
                | k13_lattice3(X0,X1,X2) = X3 )
              & m1_subset_1(X3,u1_struct_0(X0)) )
          & m1_subset_1(X2,u1_struct_0(X0)) )
     => ( ? [X3] :
            ( ( ? [X4] :
                  ( ~ r1_orders_2(X0,X3,X4)
                  & r1_orders_2(X0,sK3,X4)
                  & r1_orders_2(X0,X1,X4)
                  & m1_subset_1(X4,u1_struct_0(X0)) )
              | ~ r1_orders_2(X0,sK3,X3)
              | ~ r1_orders_2(X0,X1,X3)
              | k13_lattice3(X0,X1,sK3) != X3 )
            & ( ( ! [X5] :
                    ( r1_orders_2(X0,X3,X5)
                    | ~ r1_orders_2(X0,sK3,X5)
                    | ~ r1_orders_2(X0,X1,X5)
                    | ~ m1_subset_1(X5,u1_struct_0(X0)) )
                & r1_orders_2(X0,sK3,X3)
                & r1_orders_2(X0,X1,X3) )
              | k13_lattice3(X0,X1,sK3) = X3 )
            & m1_subset_1(X3,u1_struct_0(X0)) )
        & m1_subset_1(sK3,u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( ? [X3] :
          ( ( ? [X4] :
                ( ~ r1_orders_2(X0,X3,X4)
                & r1_orders_2(X0,X2,X4)
                & r1_orders_2(X0,X1,X4)
                & m1_subset_1(X4,u1_struct_0(X0)) )
            | ~ r1_orders_2(X0,X2,X3)
            | ~ r1_orders_2(X0,X1,X3)
            | k13_lattice3(X0,X1,X2) != X3 )
          & ( ( ! [X5] :
                  ( r1_orders_2(X0,X3,X5)
                  | ~ r1_orders_2(X0,X2,X5)
                  | ~ r1_orders_2(X0,X1,X5)
                  | ~ m1_subset_1(X5,u1_struct_0(X0)) )
              & r1_orders_2(X0,X2,X3)
              & r1_orders_2(X0,X1,X3) )
            | k13_lattice3(X0,X1,X2) = X3 )
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ( ? [X4] :
              ( ~ r1_orders_2(X0,sK4,X4)
              & r1_orders_2(X0,X2,X4)
              & r1_orders_2(X0,X1,X4)
              & m1_subset_1(X4,u1_struct_0(X0)) )
          | ~ r1_orders_2(X0,X2,sK4)
          | ~ r1_orders_2(X0,X1,sK4)
          | k13_lattice3(X0,X1,X2) != sK4 )
        & ( ( ! [X5] :
                ( r1_orders_2(X0,sK4,X5)
                | ~ r1_orders_2(X0,X2,X5)
                | ~ r1_orders_2(X0,X1,X5)
                | ~ m1_subset_1(X5,u1_struct_0(X0)) )
            & r1_orders_2(X0,X2,sK4)
            & r1_orders_2(X0,X1,sK4) )
          | k13_lattice3(X0,X1,X2) = sK4 )
        & m1_subset_1(sK4,u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f56,plain,(
    ! [X2,X0,X3,X1] :
      ( ? [X4] :
          ( ~ r1_orders_2(X0,X3,X4)
          & r1_orders_2(X0,X2,X4)
          & r1_orders_2(X0,X1,X4)
          & m1_subset_1(X4,u1_struct_0(X0)) )
     => ( ~ r1_orders_2(X0,X3,sK5)
        & r1_orders_2(X0,X2,sK5)
        & r1_orders_2(X0,X1,sK5)
        & m1_subset_1(sK5,u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f51,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( ? [X4] :
                        ( ~ r1_orders_2(X0,X3,X4)
                        & r1_orders_2(X0,X2,X4)
                        & r1_orders_2(X0,X1,X4)
                        & m1_subset_1(X4,u1_struct_0(X0)) )
                    | ~ r1_orders_2(X0,X2,X3)
                    | ~ r1_orders_2(X0,X1,X3)
                    | k13_lattice3(X0,X1,X2) != X3 )
                  & ( ( ! [X5] :
                          ( r1_orders_2(X0,X3,X5)
                          | ~ r1_orders_2(X0,X2,X5)
                          | ~ r1_orders_2(X0,X1,X5)
                          | ~ m1_subset_1(X5,u1_struct_0(X0)) )
                      & r1_orders_2(X0,X2,X3)
                      & r1_orders_2(X0,X1,X3) )
                    | k13_lattice3(X0,X1,X2) = X3 )
                  & m1_subset_1(X3,u1_struct_0(X0)) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_orders_2(X0)
      & v1_lattice3(X0)
      & v5_orders_2(X0) ) ),
    inference(rectify,[],[f50])).

fof(f50,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( ? [X4] :
                        ( ~ r1_orders_2(X0,X3,X4)
                        & r1_orders_2(X0,X2,X4)
                        & r1_orders_2(X0,X1,X4)
                        & m1_subset_1(X4,u1_struct_0(X0)) )
                    | ~ r1_orders_2(X0,X2,X3)
                    | ~ r1_orders_2(X0,X1,X3)
                    | k13_lattice3(X0,X1,X2) != X3 )
                  & ( ( ! [X4] :
                          ( r1_orders_2(X0,X3,X4)
                          | ~ r1_orders_2(X0,X2,X4)
                          | ~ r1_orders_2(X0,X1,X4)
                          | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                      & r1_orders_2(X0,X2,X3)
                      & r1_orders_2(X0,X1,X3) )
                    | k13_lattice3(X0,X1,X2) = X3 )
                  & m1_subset_1(X3,u1_struct_0(X0)) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_orders_2(X0)
      & v1_lattice3(X0)
      & v5_orders_2(X0) ) ),
    inference(flattening,[],[f49])).

fof(f49,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( ? [X4] :
                        ( ~ r1_orders_2(X0,X3,X4)
                        & r1_orders_2(X0,X2,X4)
                        & r1_orders_2(X0,X1,X4)
                        & m1_subset_1(X4,u1_struct_0(X0)) )
                    | ~ r1_orders_2(X0,X2,X3)
                    | ~ r1_orders_2(X0,X1,X3)
                    | k13_lattice3(X0,X1,X2) != X3 )
                  & ( ( ! [X4] :
                          ( r1_orders_2(X0,X3,X4)
                          | ~ r1_orders_2(X0,X2,X4)
                          | ~ r1_orders_2(X0,X1,X4)
                          | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                      & r1_orders_2(X0,X2,X3)
                      & r1_orders_2(X0,X1,X3) )
                    | k13_lattice3(X0,X1,X2) = X3 )
                  & m1_subset_1(X3,u1_struct_0(X0)) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_orders_2(X0)
      & v1_lattice3(X0)
      & v5_orders_2(X0) ) ),
    inference(nnf_transformation,[],[f27])).

fof(f27,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( k13_lattice3(X0,X1,X2) = X3
                  <~> ( ! [X4] :
                          ( r1_orders_2(X0,X3,X4)
                          | ~ r1_orders_2(X0,X2,X4)
                          | ~ r1_orders_2(X0,X1,X4)
                          | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                      & r1_orders_2(X0,X2,X3)
                      & r1_orders_2(X0,X1,X3) ) )
                  & m1_subset_1(X3,u1_struct_0(X0)) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_orders_2(X0)
      & v1_lattice3(X0)
      & v5_orders_2(X0) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( k13_lattice3(X0,X1,X2) = X3
                  <~> ( ! [X4] :
                          ( r1_orders_2(X0,X3,X4)
                          | ~ r1_orders_2(X0,X2,X4)
                          | ~ r1_orders_2(X0,X1,X4)
                          | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                      & r1_orders_2(X0,X2,X3)
                      & r1_orders_2(X0,X1,X3) ) )
                  & m1_subset_1(X3,u1_struct_0(X0)) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_orders_2(X0)
      & v1_lattice3(X0)
      & v5_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_orders_2(X0)
          & v1_lattice3(X0)
          & v5_orders_2(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => ! [X3] :
                    ( m1_subset_1(X3,u1_struct_0(X0))
                   => ( k13_lattice3(X0,X1,X2) = X3
                    <=> ( ! [X4] :
                            ( m1_subset_1(X4,u1_struct_0(X0))
                           => ( ( r1_orders_2(X0,X2,X4)
                                & r1_orders_2(X0,X1,X4) )
                             => r1_orders_2(X0,X3,X4) ) )
                        & r1_orders_2(X0,X2,X3)
                        & r1_orders_2(X0,X1,X3) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v1_lattice3(X0)
        & v5_orders_2(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ! [X3] :
                  ( m1_subset_1(X3,u1_struct_0(X0))
                 => ( k13_lattice3(X0,X1,X2) = X3
                  <=> ( ! [X4] :
                          ( m1_subset_1(X4,u1_struct_0(X0))
                         => ( ( r1_orders_2(X0,X2,X4)
                              & r1_orders_2(X0,X1,X4) )
                           => r1_orders_2(X0,X3,X4) ) )
                      & r1_orders_2(X0,X2,X3)
                      & r1_orders_2(X0,X1,X3) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/yellow_0__t22_yellow_0.p',t22_yellow_0)).

fof(f8167,plain,
    ( ~ v5_orders_2(sK1)
    | ~ spl14_1
    | ~ spl14_2
    | ~ spl14_4
    | ~ spl14_14 ),
    inference(subsumption_resolution,[],[f8166,f77])).

fof(f77,plain,(
    v1_lattice3(sK1) ),
    inference(cnf_transformation,[],[f57])).

fof(f8166,plain,
    ( ~ v1_lattice3(sK1)
    | ~ v5_orders_2(sK1)
    | ~ spl14_1
    | ~ spl14_2
    | ~ spl14_4
    | ~ spl14_14 ),
    inference(subsumption_resolution,[],[f8165,f78])).

fof(f78,plain,(
    l1_orders_2(sK1) ),
    inference(cnf_transformation,[],[f57])).

fof(f8165,plain,
    ( ~ l1_orders_2(sK1)
    | ~ v1_lattice3(sK1)
    | ~ v5_orders_2(sK1)
    | ~ spl14_1
    | ~ spl14_2
    | ~ spl14_4
    | ~ spl14_14 ),
    inference(subsumption_resolution,[],[f8164,f79])).

fof(f79,plain,(
    m1_subset_1(sK2,u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f57])).

fof(f8164,plain,
    ( ~ m1_subset_1(sK2,u1_struct_0(sK1))
    | ~ l1_orders_2(sK1)
    | ~ v1_lattice3(sK1)
    | ~ v5_orders_2(sK1)
    | ~ spl14_1
    | ~ spl14_2
    | ~ spl14_4
    | ~ spl14_14 ),
    inference(subsumption_resolution,[],[f8163,f80])).

fof(f80,plain,(
    m1_subset_1(sK3,u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f57])).

fof(f8163,plain,
    ( ~ m1_subset_1(sK3,u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,u1_struct_0(sK1))
    | ~ l1_orders_2(sK1)
    | ~ v1_lattice3(sK1)
    | ~ v5_orders_2(sK1)
    | ~ spl14_1
    | ~ spl14_2
    | ~ spl14_4
    | ~ spl14_14 ),
    inference(subsumption_resolution,[],[f8053,f127])).

fof(f127,plain,
    ( k13_lattice3(sK1,sK2,sK3) != sK4
    | ~ spl14_1 ),
    inference(avatar_component_clause,[],[f126])).

fof(f126,plain,
    ( spl14_1
  <=> k13_lattice3(sK1,sK2,sK3) != sK4 ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_1])])).

fof(f8053,plain,
    ( k13_lattice3(sK1,sK2,sK3) = sK4
    | ~ m1_subset_1(sK3,u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,u1_struct_0(sK1))
    | ~ l1_orders_2(sK1)
    | ~ v1_lattice3(sK1)
    | ~ v5_orders_2(sK1)
    | ~ spl14_2
    | ~ spl14_4
    | ~ spl14_14 ),
    inference(superposition,[],[f118,f7769])).

fof(f7769,plain,
    ( k10_lattice3(sK1,sK2,sK3) = sK4
    | ~ spl14_2
    | ~ spl14_4
    | ~ spl14_14 ),
    inference(subsumption_resolution,[],[f7768,f2503])).

fof(f2503,plain,(
    sP0(sK1,sK3,sK2) ),
    inference(resolution,[],[f1884,f79])).

fof(f1884,plain,(
    ! [X1] :
      ( ~ m1_subset_1(X1,u1_struct_0(sK1))
      | sP0(sK1,sK3,X1) ) ),
    inference(subsumption_resolution,[],[f1883,f77])).

fof(f1883,plain,(
    ! [X1] :
      ( sP0(sK1,sK3,X1)
      | ~ m1_subset_1(X1,u1_struct_0(sK1))
      | ~ v1_lattice3(sK1) ) ),
    inference(subsumption_resolution,[],[f1882,f78])).

fof(f1882,plain,(
    ! [X1] :
      ( ~ l1_orders_2(sK1)
      | sP0(sK1,sK3,X1)
      | ~ m1_subset_1(X1,u1_struct_0(sK1))
      | ~ v1_lattice3(sK1) ) ),
    inference(subsumption_resolution,[],[f1861,f76])).

fof(f1861,plain,(
    ! [X1] :
      ( ~ v5_orders_2(sK1)
      | ~ l1_orders_2(sK1)
      | sP0(sK1,sK3,X1)
      | ~ m1_subset_1(X1,u1_struct_0(sK1))
      | ~ v1_lattice3(sK1) ) ),
    inference(resolution,[],[f1822,f80])).

fof(f1822,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ v5_orders_2(X1)
      | ~ l1_orders_2(X1)
      | sP0(X1,X2,X0)
      | ~ m1_subset_1(X0,u1_struct_0(X1))
      | ~ v1_lattice3(X1) ) ),
    inference(subsumption_resolution,[],[f1821,f101])).

fof(f101,plain,(
    ! [X6,X0,X5] :
      ( m1_subset_1(sK11(X0,X5,X6),u1_struct_0(X0))
      | ~ m1_subset_1(X6,u1_struct_0(X0))
      | ~ m1_subset_1(X5,u1_struct_0(X0))
      | ~ v1_lattice3(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f71])).

fof(f71,plain,(
    ! [X0] :
      ( ( ( v1_lattice3(X0)
          | ( ! [X3] :
                ( ( ~ r1_orders_2(X0,X3,sK10(X0,X3))
                  & r1_orders_2(X0,sK9(X0),sK10(X0,X3))
                  & r1_orders_2(X0,sK8(X0),sK10(X0,X3))
                  & m1_subset_1(sK10(X0,X3),u1_struct_0(X0)) )
                | ~ r1_orders_2(X0,sK9(X0),X3)
                | ~ r1_orders_2(X0,sK8(X0),X3)
                | ~ m1_subset_1(X3,u1_struct_0(X0)) )
            & m1_subset_1(sK9(X0),u1_struct_0(X0))
            & m1_subset_1(sK8(X0),u1_struct_0(X0)) ) )
        & ( ! [X5] :
              ( ! [X6] :
                  ( ( ! [X8] :
                        ( r1_orders_2(X0,sK11(X0,X5,X6),X8)
                        | ~ r1_orders_2(X0,X6,X8)
                        | ~ r1_orders_2(X0,X5,X8)
                        | ~ m1_subset_1(X8,u1_struct_0(X0)) )
                    & r1_orders_2(X0,X6,sK11(X0,X5,X6))
                    & r1_orders_2(X0,X5,sK11(X0,X5,X6))
                    & m1_subset_1(sK11(X0,X5,X6),u1_struct_0(X0)) )
                  | ~ m1_subset_1(X6,u1_struct_0(X0)) )
              | ~ m1_subset_1(X5,u1_struct_0(X0)) )
          | ~ v1_lattice3(X0) ) )
      | ~ l1_orders_2(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8,sK9,sK10,sK11])],[f66,f70,f69,f68,f67])).

fof(f67,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ! [X3] :
                  ( ? [X4] :
                      ( ~ r1_orders_2(X0,X3,X4)
                      & r1_orders_2(X0,X2,X4)
                      & r1_orders_2(X0,X1,X4)
                      & m1_subset_1(X4,u1_struct_0(X0)) )
                  | ~ r1_orders_2(X0,X2,X3)
                  | ~ r1_orders_2(X0,X1,X3)
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
     => ( ? [X2] :
            ( ! [X3] :
                ( ? [X4] :
                    ( ~ r1_orders_2(X0,X3,X4)
                    & r1_orders_2(X0,X2,X4)
                    & r1_orders_2(X0,sK8(X0),X4)
                    & m1_subset_1(X4,u1_struct_0(X0)) )
                | ~ r1_orders_2(X0,X2,X3)
                | ~ r1_orders_2(X0,sK8(X0),X3)
                | ~ m1_subset_1(X3,u1_struct_0(X0)) )
            & m1_subset_1(X2,u1_struct_0(X0)) )
        & m1_subset_1(sK8(X0),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f68,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ! [X3] :
              ( ? [X4] :
                  ( ~ r1_orders_2(X0,X3,X4)
                  & r1_orders_2(X0,X2,X4)
                  & r1_orders_2(X0,X1,X4)
                  & m1_subset_1(X4,u1_struct_0(X0)) )
              | ~ r1_orders_2(X0,X2,X3)
              | ~ r1_orders_2(X0,X1,X3)
              | ~ m1_subset_1(X3,u1_struct_0(X0)) )
          & m1_subset_1(X2,u1_struct_0(X0)) )
     => ( ! [X3] :
            ( ? [X4] :
                ( ~ r1_orders_2(X0,X3,X4)
                & r1_orders_2(X0,sK9(X0),X4)
                & r1_orders_2(X0,X1,X4)
                & m1_subset_1(X4,u1_struct_0(X0)) )
            | ~ r1_orders_2(X0,sK9(X0),X3)
            | ~ r1_orders_2(X0,X1,X3)
            | ~ m1_subset_1(X3,u1_struct_0(X0)) )
        & m1_subset_1(sK9(X0),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f69,plain,(
    ! [X2,X1,X3,X0] :
      ( ? [X4] :
          ( ~ r1_orders_2(X0,X3,X4)
          & r1_orders_2(X0,X2,X4)
          & r1_orders_2(X0,X1,X4)
          & m1_subset_1(X4,u1_struct_0(X0)) )
     => ( ~ r1_orders_2(X0,X3,sK10(X0,X3))
        & r1_orders_2(X0,X2,sK10(X0,X3))
        & r1_orders_2(X0,X1,sK10(X0,X3))
        & m1_subset_1(sK10(X0,X3),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f70,plain,(
    ! [X6,X5,X0] :
      ( ? [X7] :
          ( ! [X8] :
              ( r1_orders_2(X0,X7,X8)
              | ~ r1_orders_2(X0,X6,X8)
              | ~ r1_orders_2(X0,X5,X8)
              | ~ m1_subset_1(X8,u1_struct_0(X0)) )
          & r1_orders_2(X0,X6,X7)
          & r1_orders_2(X0,X5,X7)
          & m1_subset_1(X7,u1_struct_0(X0)) )
     => ( ! [X8] :
            ( r1_orders_2(X0,sK11(X0,X5,X6),X8)
            | ~ r1_orders_2(X0,X6,X8)
            | ~ r1_orders_2(X0,X5,X8)
            | ~ m1_subset_1(X8,u1_struct_0(X0)) )
        & r1_orders_2(X0,X6,sK11(X0,X5,X6))
        & r1_orders_2(X0,X5,sK11(X0,X5,X6))
        & m1_subset_1(sK11(X0,X5,X6),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f66,plain,(
    ! [X0] :
      ( ( ( v1_lattice3(X0)
          | ? [X1] :
              ( ? [X2] :
                  ( ! [X3] :
                      ( ? [X4] :
                          ( ~ r1_orders_2(X0,X3,X4)
                          & r1_orders_2(X0,X2,X4)
                          & r1_orders_2(X0,X1,X4)
                          & m1_subset_1(X4,u1_struct_0(X0)) )
                      | ~ r1_orders_2(X0,X2,X3)
                      | ~ r1_orders_2(X0,X1,X3)
                      | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                  & m1_subset_1(X2,u1_struct_0(X0)) )
              & m1_subset_1(X1,u1_struct_0(X0)) ) )
        & ( ! [X5] :
              ( ! [X6] :
                  ( ? [X7] :
                      ( ! [X8] :
                          ( r1_orders_2(X0,X7,X8)
                          | ~ r1_orders_2(X0,X6,X8)
                          | ~ r1_orders_2(X0,X5,X8)
                          | ~ m1_subset_1(X8,u1_struct_0(X0)) )
                      & r1_orders_2(X0,X6,X7)
                      & r1_orders_2(X0,X5,X7)
                      & m1_subset_1(X7,u1_struct_0(X0)) )
                  | ~ m1_subset_1(X6,u1_struct_0(X0)) )
              | ~ m1_subset_1(X5,u1_struct_0(X0)) )
          | ~ v1_lattice3(X0) ) )
      | ~ l1_orders_2(X0) ) ),
    inference(rectify,[],[f65])).

fof(f65,plain,(
    ! [X0] :
      ( ( ( v1_lattice3(X0)
          | ? [X1] :
              ( ? [X2] :
                  ( ! [X3] :
                      ( ? [X4] :
                          ( ~ r1_orders_2(X0,X3,X4)
                          & r1_orders_2(X0,X2,X4)
                          & r1_orders_2(X0,X1,X4)
                          & m1_subset_1(X4,u1_struct_0(X0)) )
                      | ~ r1_orders_2(X0,X2,X3)
                      | ~ r1_orders_2(X0,X1,X3)
                      | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                  & m1_subset_1(X2,u1_struct_0(X0)) )
              & m1_subset_1(X1,u1_struct_0(X0)) ) )
        & ( ! [X1] :
              ( ! [X2] :
                  ( ? [X3] :
                      ( ! [X4] :
                          ( r1_orders_2(X0,X3,X4)
                          | ~ r1_orders_2(X0,X2,X4)
                          | ~ r1_orders_2(X0,X1,X4)
                          | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                      & r1_orders_2(X0,X2,X3)
                      & r1_orders_2(X0,X1,X3)
                      & m1_subset_1(X3,u1_struct_0(X0)) )
                  | ~ m1_subset_1(X2,u1_struct_0(X0)) )
              | ~ m1_subset_1(X1,u1_struct_0(X0)) )
          | ~ v1_lattice3(X0) ) )
      | ~ l1_orders_2(X0) ) ),
    inference(nnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( ( v1_lattice3(X0)
      <=> ! [X1] :
            ( ! [X2] :
                ( ? [X3] :
                    ( ! [X4] :
                        ( r1_orders_2(X0,X3,X4)
                        | ~ r1_orders_2(X0,X2,X4)
                        | ~ r1_orders_2(X0,X1,X4)
                        | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                    & r1_orders_2(X0,X2,X3)
                    & r1_orders_2(X0,X1,X3)
                    & m1_subset_1(X3,u1_struct_0(X0)) )
                | ~ m1_subset_1(X2,u1_struct_0(X0)) )
            | ~ m1_subset_1(X1,u1_struct_0(X0)) ) )
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( ( v1_lattice3(X0)
      <=> ! [X1] :
            ( ! [X2] :
                ( ? [X3] :
                    ( ! [X4] :
                        ( r1_orders_2(X0,X3,X4)
                        | ~ r1_orders_2(X0,X2,X4)
                        | ~ r1_orders_2(X0,X1,X4)
                        | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                    & r1_orders_2(X0,X2,X3)
                    & r1_orders_2(X0,X1,X3)
                    & m1_subset_1(X3,u1_struct_0(X0)) )
                | ~ m1_subset_1(X2,u1_struct_0(X0)) )
            | ~ m1_subset_1(X1,u1_struct_0(X0)) ) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ( v1_lattice3(X0)
      <=> ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => ? [X3] :
                    ( ! [X4] :
                        ( m1_subset_1(X4,u1_struct_0(X0))
                       => ( ( r1_orders_2(X0,X2,X4)
                            & r1_orders_2(X0,X1,X4) )
                         => r1_orders_2(X0,X3,X4) ) )
                    & r1_orders_2(X0,X2,X3)
                    & r1_orders_2(X0,X1,X3)
                    & m1_subset_1(X3,u1_struct_0(X0)) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/yellow_0__t22_yellow_0.p',d10_lattice3)).

fof(f1821,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X0,u1_struct_0(X1))
      | ~ v5_orders_2(X1)
      | ~ l1_orders_2(X1)
      | sP0(X1,X2,X0)
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ v1_lattice3(X1)
      | ~ m1_subset_1(sK11(X1,X2,X0),u1_struct_0(X1)) ) ),
    inference(subsumption_resolution,[],[f1820,f103])).

fof(f103,plain,(
    ! [X6,X0,X5] :
      ( r1_orders_2(X0,X6,sK11(X0,X5,X6))
      | ~ m1_subset_1(X6,u1_struct_0(X0))
      | ~ m1_subset_1(X5,u1_struct_0(X0))
      | ~ v1_lattice3(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f71])).

fof(f1820,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X0,u1_struct_0(X1))
      | ~ v5_orders_2(X1)
      | ~ l1_orders_2(X1)
      | sP0(X1,X2,X0)
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ v1_lattice3(X1)
      | ~ r1_orders_2(X1,X0,sK11(X1,X2,X0))
      | ~ m1_subset_1(sK11(X1,X2,X0),u1_struct_0(X1)) ) ),
    inference(subsumption_resolution,[],[f1819,f102])).

fof(f102,plain,(
    ! [X6,X0,X5] :
      ( r1_orders_2(X0,X5,sK11(X0,X5,X6))
      | ~ m1_subset_1(X6,u1_struct_0(X0))
      | ~ m1_subset_1(X5,u1_struct_0(X0))
      | ~ v1_lattice3(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f71])).

fof(f1819,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X0,u1_struct_0(X1))
      | ~ v5_orders_2(X1)
      | ~ l1_orders_2(X1)
      | sP0(X1,X2,X0)
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ v1_lattice3(X1)
      | ~ r1_orders_2(X1,X2,sK11(X1,X2,X0))
      | ~ r1_orders_2(X1,X0,sK11(X1,X2,X0))
      | ~ m1_subset_1(sK11(X1,X2,X0),u1_struct_0(X1)) ) ),
    inference(duplicate_literal_removal,[],[f1810])).

fof(f1810,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X0,u1_struct_0(X1))
      | ~ v5_orders_2(X1)
      | ~ l1_orders_2(X1)
      | sP0(X1,X2,X0)
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ v1_lattice3(X1)
      | sP0(X1,X2,X0)
      | ~ r1_orders_2(X1,X2,sK11(X1,X2,X0))
      | ~ r1_orders_2(X1,X0,sK11(X1,X2,X0))
      | ~ m1_subset_1(sK11(X1,X2,X0),u1_struct_0(X1))
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ m1_subset_1(X0,u1_struct_0(X1))
      | ~ v5_orders_2(X1)
      | ~ l1_orders_2(X1) ) ),
    inference(resolution,[],[f998,f97])).

fof(f97,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(sK7(X0,X1,X2,X3),u1_struct_0(X0))
      | sP0(X0,X2,X1)
      | ~ r1_orders_2(X0,X2,X3)
      | ~ r1_orders_2(X0,X1,X3)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ v5_orders_2(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f64])).

fof(f64,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( sP0(X0,X2,X1)
              | ! [X3] :
                  ( ( ~ r1_orders_2(X0,X3,sK7(X0,X1,X2,X3))
                    & r1_orders_2(X0,X2,sK7(X0,X1,X2,X3))
                    & r1_orders_2(X0,X1,sK7(X0,X1,X2,X3))
                    & m1_subset_1(sK7(X0,X1,X2,X3),u1_struct_0(X0)) )
                  | ~ r1_orders_2(X0,X2,X3)
                  | ~ r1_orders_2(X0,X1,X3)
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ v5_orders_2(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f48,f63])).

fof(f63,plain,(
    ! [X3,X2,X1,X0] :
      ( ? [X4] :
          ( ~ r1_orders_2(X0,X3,X4)
          & r1_orders_2(X0,X2,X4)
          & r1_orders_2(X0,X1,X4)
          & m1_subset_1(X4,u1_struct_0(X0)) )
     => ( ~ r1_orders_2(X0,X3,sK7(X0,X1,X2,X3))
        & r1_orders_2(X0,X2,sK7(X0,X1,X2,X3))
        & r1_orders_2(X0,X1,sK7(X0,X1,X2,X3))
        & m1_subset_1(sK7(X0,X1,X2,X3),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f48,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( sP0(X0,X2,X1)
              | ! [X3] :
                  ( ? [X4] :
                      ( ~ r1_orders_2(X0,X3,X4)
                      & r1_orders_2(X0,X2,X4)
                      & r1_orders_2(X0,X1,X4)
                      & m1_subset_1(X4,u1_struct_0(X0)) )
                  | ~ r1_orders_2(X0,X2,X3)
                  | ~ r1_orders_2(X0,X1,X3)
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ v5_orders_2(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(definition_folding,[],[f30,f47])).

fof(f47,plain,(
    ! [X0,X2,X1] :
      ( ! [X5] :
          ( ( k10_lattice3(X0,X1,X2) = X5
          <=> ( ! [X6] :
                  ( r1_orders_2(X0,X5,X6)
                  | ~ r1_orders_2(X0,X2,X6)
                  | ~ r1_orders_2(X0,X1,X6)
                  | ~ m1_subset_1(X6,u1_struct_0(X0)) )
              & r1_orders_2(X0,X2,X5)
              & r1_orders_2(X0,X1,X5) ) )
          | ~ m1_subset_1(X5,u1_struct_0(X0)) )
      | ~ sP0(X0,X2,X1) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X5] :
                  ( ( k10_lattice3(X0,X1,X2) = X5
                  <=> ( ! [X6] :
                          ( r1_orders_2(X0,X5,X6)
                          | ~ r1_orders_2(X0,X2,X6)
                          | ~ r1_orders_2(X0,X1,X6)
                          | ~ m1_subset_1(X6,u1_struct_0(X0)) )
                      & r1_orders_2(X0,X2,X5)
                      & r1_orders_2(X0,X1,X5) ) )
                  | ~ m1_subset_1(X5,u1_struct_0(X0)) )
              | ! [X3] :
                  ( ? [X4] :
                      ( ~ r1_orders_2(X0,X3,X4)
                      & r1_orders_2(X0,X2,X4)
                      & r1_orders_2(X0,X1,X4)
                      & m1_subset_1(X4,u1_struct_0(X0)) )
                  | ~ r1_orders_2(X0,X2,X3)
                  | ~ r1_orders_2(X0,X1,X3)
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ v5_orders_2(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X5] :
                  ( ( k10_lattice3(X0,X1,X2) = X5
                  <=> ( ! [X6] :
                          ( r1_orders_2(X0,X5,X6)
                          | ~ r1_orders_2(X0,X2,X6)
                          | ~ r1_orders_2(X0,X1,X6)
                          | ~ m1_subset_1(X6,u1_struct_0(X0)) )
                      & r1_orders_2(X0,X2,X5)
                      & r1_orders_2(X0,X1,X5) ) )
                  | ~ m1_subset_1(X5,u1_struct_0(X0)) )
              | ! [X3] :
                  ( ? [X4] :
                      ( ~ r1_orders_2(X0,X3,X4)
                      & r1_orders_2(X0,X2,X4)
                      & r1_orders_2(X0,X1,X4)
                      & m1_subset_1(X4,u1_struct_0(X0)) )
                  | ~ r1_orders_2(X0,X2,X3)
                  | ~ r1_orders_2(X0,X1,X3)
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ v5_orders_2(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f23,plain,(
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
                         => ( ( r1_orders_2(X0,X2,X4)
                              & r1_orders_2(X0,X1,X4) )
                           => r1_orders_2(X0,X3,X4) ) )
                      & r1_orders_2(X0,X2,X3)
                      & r1_orders_2(X0,X1,X3)
                      & m1_subset_1(X3,u1_struct_0(X0)) )
                 => ! [X5] :
                      ( m1_subset_1(X5,u1_struct_0(X0))
                     => ( k10_lattice3(X0,X1,X2) = X5
                      <=> ( ! [X6] :
                              ( m1_subset_1(X6,u1_struct_0(X0))
                             => ( ( r1_orders_2(X0,X2,X6)
                                  & r1_orders_2(X0,X1,X6) )
                               => r1_orders_2(X0,X5,X6) ) )
                          & r1_orders_2(X0,X2,X5)
                          & r1_orders_2(X0,X1,X5) ) ) ) ) ) ) ) ) ),
    inference(rectify,[],[f6])).

fof(f6,axiom,(
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
                         => ( ( r1_orders_2(X0,X2,X4)
                              & r1_orders_2(X0,X1,X4) )
                           => r1_orders_2(X0,X3,X4) ) )
                      & r1_orders_2(X0,X2,X3)
                      & r1_orders_2(X0,X1,X3)
                      & m1_subset_1(X3,u1_struct_0(X0)) )
                 => ! [X3] :
                      ( m1_subset_1(X3,u1_struct_0(X0))
                     => ( k10_lattice3(X0,X1,X2) = X3
                      <=> ( ! [X4] :
                              ( m1_subset_1(X4,u1_struct_0(X0))
                             => ( ( r1_orders_2(X0,X2,X4)
                                  & r1_orders_2(X0,X1,X4) )
                               => r1_orders_2(X0,X3,X4) ) )
                          & r1_orders_2(X0,X2,X3)
                          & r1_orders_2(X0,X1,X3) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/yellow_0__t22_yellow_0.p',d13_lattice3)).

fof(f998,plain,(
    ! [X4,X5,X3] :
      ( ~ m1_subset_1(sK7(X4,X5,X3,sK11(X4,X3,X5)),u1_struct_0(X4))
      | ~ m1_subset_1(X5,u1_struct_0(X4))
      | ~ v5_orders_2(X4)
      | ~ l1_orders_2(X4)
      | sP0(X4,X3,X5)
      | ~ m1_subset_1(X3,u1_struct_0(X4))
      | ~ v1_lattice3(X4) ) ),
    inference(subsumption_resolution,[],[f997,f101])).

fof(f997,plain,(
    ! [X4,X5,X3] :
      ( ~ m1_subset_1(X3,u1_struct_0(X4))
      | ~ m1_subset_1(X5,u1_struct_0(X4))
      | ~ v5_orders_2(X4)
      | ~ l1_orders_2(X4)
      | sP0(X4,X3,X5)
      | ~ m1_subset_1(sK7(X4,X5,X3,sK11(X4,X3,X5)),u1_struct_0(X4))
      | ~ v1_lattice3(X4)
      | ~ m1_subset_1(sK11(X4,X3,X5),u1_struct_0(X4)) ) ),
    inference(subsumption_resolution,[],[f996,f103])).

fof(f996,plain,(
    ! [X4,X5,X3] :
      ( ~ m1_subset_1(X3,u1_struct_0(X4))
      | ~ m1_subset_1(X5,u1_struct_0(X4))
      | ~ v5_orders_2(X4)
      | ~ l1_orders_2(X4)
      | sP0(X4,X3,X5)
      | ~ m1_subset_1(sK7(X4,X5,X3,sK11(X4,X3,X5)),u1_struct_0(X4))
      | ~ v1_lattice3(X4)
      | ~ r1_orders_2(X4,X5,sK11(X4,X3,X5))
      | ~ m1_subset_1(sK11(X4,X3,X5),u1_struct_0(X4)) ) ),
    inference(subsumption_resolution,[],[f991,f102])).

fof(f991,plain,(
    ! [X4,X5,X3] :
      ( ~ m1_subset_1(X3,u1_struct_0(X4))
      | ~ m1_subset_1(X5,u1_struct_0(X4))
      | ~ v5_orders_2(X4)
      | ~ l1_orders_2(X4)
      | sP0(X4,X3,X5)
      | ~ r1_orders_2(X4,X3,sK11(X4,X3,X5))
      | ~ m1_subset_1(sK7(X4,X5,X3,sK11(X4,X3,X5)),u1_struct_0(X4))
      | ~ v1_lattice3(X4)
      | ~ r1_orders_2(X4,X5,sK11(X4,X3,X5))
      | ~ m1_subset_1(sK11(X4,X3,X5),u1_struct_0(X4)) ) ),
    inference(duplicate_literal_removal,[],[f980])).

fof(f980,plain,(
    ! [X4,X5,X3] :
      ( ~ m1_subset_1(X3,u1_struct_0(X4))
      | ~ m1_subset_1(X5,u1_struct_0(X4))
      | ~ v5_orders_2(X4)
      | ~ l1_orders_2(X4)
      | sP0(X4,X3,X5)
      | ~ r1_orders_2(X4,X3,sK11(X4,X3,X5))
      | ~ m1_subset_1(sK7(X4,X5,X3,sK11(X4,X3,X5)),u1_struct_0(X4))
      | ~ m1_subset_1(X3,u1_struct_0(X4))
      | ~ v1_lattice3(X4)
      | sP0(X4,X3,X5)
      | ~ r1_orders_2(X4,X3,sK11(X4,X3,X5))
      | ~ r1_orders_2(X4,X5,sK11(X4,X3,X5))
      | ~ m1_subset_1(sK11(X4,X3,X5),u1_struct_0(X4))
      | ~ m1_subset_1(X3,u1_struct_0(X4))
      | ~ m1_subset_1(X5,u1_struct_0(X4))
      | ~ v5_orders_2(X4)
      | ~ l1_orders_2(X4) ) ),
    inference(resolution,[],[f496,f99])).

fof(f99,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_orders_2(X0,X2,sK7(X0,X1,X2,X3))
      | sP0(X0,X2,X1)
      | ~ r1_orders_2(X0,X2,X3)
      | ~ r1_orders_2(X0,X1,X3)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ v5_orders_2(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f64])).

fof(f496,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r1_orders_2(X0,X2,sK7(X0,X3,X1,sK11(X0,X2,X3)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ v5_orders_2(X0)
      | ~ l1_orders_2(X0)
      | sP0(X0,X1,X3)
      | ~ r1_orders_2(X0,X1,sK11(X0,X2,X3))
      | ~ m1_subset_1(sK7(X0,X3,X1,sK11(X0,X2,X3)),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ v1_lattice3(X0) ) ),
    inference(subsumption_resolution,[],[f495,f101])).

fof(f495,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r1_orders_2(X0,X1,sK11(X0,X2,X3))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ v5_orders_2(X0)
      | ~ l1_orders_2(X0)
      | sP0(X0,X1,X3)
      | ~ r1_orders_2(X0,X2,sK7(X0,X3,X1,sK11(X0,X2,X3)))
      | ~ m1_subset_1(sK7(X0,X3,X1,sK11(X0,X2,X3)),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ v1_lattice3(X0)
      | ~ m1_subset_1(sK11(X0,X2,X3),u1_struct_0(X0)) ) ),
    inference(subsumption_resolution,[],[f494,f103])).

fof(f494,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r1_orders_2(X0,X1,sK11(X0,X2,X3))
      | ~ r1_orders_2(X0,X3,sK11(X0,X2,X3))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ v5_orders_2(X0)
      | ~ l1_orders_2(X0)
      | sP0(X0,X1,X3)
      | ~ r1_orders_2(X0,X2,sK7(X0,X3,X1,sK11(X0,X2,X3)))
      | ~ m1_subset_1(sK7(X0,X3,X1,sK11(X0,X2,X3)),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ v1_lattice3(X0)
      | ~ m1_subset_1(sK11(X0,X2,X3),u1_struct_0(X0)) ) ),
    inference(duplicate_literal_removal,[],[f487])).

fof(f487,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r1_orders_2(X0,X1,sK11(X0,X2,X3))
      | ~ r1_orders_2(X0,X3,sK11(X0,X2,X3))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ v5_orders_2(X0)
      | ~ l1_orders_2(X0)
      | sP0(X0,X1,X3)
      | ~ r1_orders_2(X0,X2,sK7(X0,X3,X1,sK11(X0,X2,X3)))
      | ~ m1_subset_1(sK7(X0,X3,X1,sK11(X0,X2,X3)),u1_struct_0(X0))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ v1_lattice3(X0)
      | sP0(X0,X1,X3)
      | ~ r1_orders_2(X0,X1,sK11(X0,X2,X3))
      | ~ r1_orders_2(X0,X3,sK11(X0,X2,X3))
      | ~ m1_subset_1(sK11(X0,X2,X3),u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ v5_orders_2(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(resolution,[],[f285,f98])).

fof(f98,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_orders_2(X0,X1,sK7(X0,X1,X2,X3))
      | sP0(X0,X2,X1)
      | ~ r1_orders_2(X0,X2,X3)
      | ~ r1_orders_2(X0,X1,X3)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ v5_orders_2(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f64])).

fof(f285,plain,(
    ! [X6,X10,X8,X7,X9] :
      ( ~ r1_orders_2(X6,X10,sK7(X6,X8,X7,sK11(X6,X9,X10)))
      | ~ r1_orders_2(X6,X7,sK11(X6,X9,X10))
      | ~ r1_orders_2(X6,X8,sK11(X6,X9,X10))
      | ~ m1_subset_1(X7,u1_struct_0(X6))
      | ~ m1_subset_1(X8,u1_struct_0(X6))
      | ~ v5_orders_2(X6)
      | ~ l1_orders_2(X6)
      | sP0(X6,X7,X8)
      | ~ r1_orders_2(X6,X9,sK7(X6,X8,X7,sK11(X6,X9,X10)))
      | ~ m1_subset_1(sK7(X6,X8,X7,sK11(X6,X9,X10)),u1_struct_0(X6))
      | ~ m1_subset_1(X10,u1_struct_0(X6))
      | ~ m1_subset_1(X9,u1_struct_0(X6))
      | ~ v1_lattice3(X6) ) ),
    inference(subsumption_resolution,[],[f282,f101])).

fof(f282,plain,(
    ! [X6,X10,X8,X7,X9] :
      ( sP0(X6,X7,X8)
      | ~ r1_orders_2(X6,X7,sK11(X6,X9,X10))
      | ~ r1_orders_2(X6,X8,sK11(X6,X9,X10))
      | ~ m1_subset_1(sK11(X6,X9,X10),u1_struct_0(X6))
      | ~ m1_subset_1(X7,u1_struct_0(X6))
      | ~ m1_subset_1(X8,u1_struct_0(X6))
      | ~ v5_orders_2(X6)
      | ~ l1_orders_2(X6)
      | ~ r1_orders_2(X6,X10,sK7(X6,X8,X7,sK11(X6,X9,X10)))
      | ~ r1_orders_2(X6,X9,sK7(X6,X8,X7,sK11(X6,X9,X10)))
      | ~ m1_subset_1(sK7(X6,X8,X7,sK11(X6,X9,X10)),u1_struct_0(X6))
      | ~ m1_subset_1(X10,u1_struct_0(X6))
      | ~ m1_subset_1(X9,u1_struct_0(X6))
      | ~ v1_lattice3(X6) ) ),
    inference(duplicate_literal_removal,[],[f281])).

fof(f281,plain,(
    ! [X6,X10,X8,X7,X9] :
      ( sP0(X6,X7,X8)
      | ~ r1_orders_2(X6,X7,sK11(X6,X9,X10))
      | ~ r1_orders_2(X6,X8,sK11(X6,X9,X10))
      | ~ m1_subset_1(sK11(X6,X9,X10),u1_struct_0(X6))
      | ~ m1_subset_1(X7,u1_struct_0(X6))
      | ~ m1_subset_1(X8,u1_struct_0(X6))
      | ~ v5_orders_2(X6)
      | ~ l1_orders_2(X6)
      | ~ r1_orders_2(X6,X10,sK7(X6,X8,X7,sK11(X6,X9,X10)))
      | ~ r1_orders_2(X6,X9,sK7(X6,X8,X7,sK11(X6,X9,X10)))
      | ~ m1_subset_1(sK7(X6,X8,X7,sK11(X6,X9,X10)),u1_struct_0(X6))
      | ~ m1_subset_1(X10,u1_struct_0(X6))
      | ~ m1_subset_1(X9,u1_struct_0(X6))
      | ~ v1_lattice3(X6)
      | ~ l1_orders_2(X6) ) ),
    inference(resolution,[],[f100,f104])).

fof(f104,plain,(
    ! [X6,X0,X8,X5] :
      ( r1_orders_2(X0,sK11(X0,X5,X6),X8)
      | ~ r1_orders_2(X0,X6,X8)
      | ~ r1_orders_2(X0,X5,X8)
      | ~ m1_subset_1(X8,u1_struct_0(X0))
      | ~ m1_subset_1(X6,u1_struct_0(X0))
      | ~ m1_subset_1(X5,u1_struct_0(X0))
      | ~ v1_lattice3(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f71])).

fof(f100,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r1_orders_2(X0,X3,sK7(X0,X1,X2,X3))
      | sP0(X0,X2,X1)
      | ~ r1_orders_2(X0,X2,X3)
      | ~ r1_orders_2(X0,X1,X3)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ v5_orders_2(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f64])).

fof(f7768,plain,
    ( k10_lattice3(sK1,sK2,sK3) = sK4
    | ~ sP0(sK1,sK3,sK2)
    | ~ spl14_2
    | ~ spl14_4
    | ~ spl14_14 ),
    inference(subsumption_resolution,[],[f7767,f81])).

fof(f81,plain,(
    m1_subset_1(sK4,u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f57])).

fof(f7767,plain,
    ( k10_lattice3(sK1,sK2,sK3) = sK4
    | ~ m1_subset_1(sK4,u1_struct_0(sK1))
    | ~ sP0(sK1,sK3,sK2)
    | ~ spl14_2
    | ~ spl14_4
    | ~ spl14_14 ),
    inference(subsumption_resolution,[],[f7766,f163])).

fof(f163,plain,
    ( r1_orders_2(sK1,sK2,sK4)
    | ~ spl14_2 ),
    inference(avatar_component_clause,[],[f162])).

fof(f162,plain,
    ( spl14_2
  <=> r1_orders_2(sK1,sK2,sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_2])])).

fof(f7766,plain,
    ( k10_lattice3(sK1,sK2,sK3) = sK4
    | ~ r1_orders_2(sK1,sK2,sK4)
    | ~ m1_subset_1(sK4,u1_struct_0(sK1))
    | ~ sP0(sK1,sK3,sK2)
    | ~ spl14_4
    | ~ spl14_14 ),
    inference(subsumption_resolution,[],[f7765,f159])).

fof(f159,plain,
    ( r1_orders_2(sK1,sK3,sK4)
    | ~ spl14_4 ),
    inference(avatar_component_clause,[],[f158])).

fof(f158,plain,
    ( spl14_4
  <=> r1_orders_2(sK1,sK3,sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_4])])).

fof(f7765,plain,
    ( k10_lattice3(sK1,sK2,sK3) = sK4
    | ~ r1_orders_2(sK1,sK3,sK4)
    | ~ r1_orders_2(sK1,sK2,sK4)
    | ~ m1_subset_1(sK4,u1_struct_0(sK1))
    | ~ sP0(sK1,sK3,sK2)
    | ~ spl14_14 ),
    inference(duplicate_literal_removal,[],[f7696])).

fof(f7696,plain,
    ( k10_lattice3(sK1,sK2,sK3) = sK4
    | ~ r1_orders_2(sK1,sK3,sK4)
    | ~ r1_orders_2(sK1,sK2,sK4)
    | ~ m1_subset_1(sK4,u1_struct_0(sK1))
    | k10_lattice3(sK1,sK2,sK3) = sK4
    | ~ r1_orders_2(sK1,sK3,sK4)
    | ~ r1_orders_2(sK1,sK2,sK4)
    | ~ m1_subset_1(sK4,u1_struct_0(sK1))
    | ~ sP0(sK1,sK3,sK2)
    | ~ spl14_14 ),
    inference(resolution,[],[f6929,f96])).

fof(f96,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r1_orders_2(X0,X3,sK6(X0,X1,X2,X3))
      | k10_lattice3(X0,X2,X1) = X3
      | ~ r1_orders_2(X0,X1,X3)
      | ~ r1_orders_2(X0,X2,X3)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f62])).

fof(f62,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( ( ( k10_lattice3(X0,X2,X1) = X3
              | ( ~ r1_orders_2(X0,X3,sK6(X0,X1,X2,X3))
                & r1_orders_2(X0,X1,sK6(X0,X1,X2,X3))
                & r1_orders_2(X0,X2,sK6(X0,X1,X2,X3))
                & m1_subset_1(sK6(X0,X1,X2,X3),u1_struct_0(X0)) )
              | ~ r1_orders_2(X0,X1,X3)
              | ~ r1_orders_2(X0,X2,X3) )
            & ( ( ! [X5] :
                    ( r1_orders_2(X0,X3,X5)
                    | ~ r1_orders_2(X0,X1,X5)
                    | ~ r1_orders_2(X0,X2,X5)
                    | ~ m1_subset_1(X5,u1_struct_0(X0)) )
                & r1_orders_2(X0,X1,X3)
                & r1_orders_2(X0,X2,X3) )
              | k10_lattice3(X0,X2,X1) != X3 ) )
          | ~ m1_subset_1(X3,u1_struct_0(X0)) )
      | ~ sP0(X0,X1,X2) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f60,f61])).

fof(f61,plain,(
    ! [X3,X2,X1,X0] :
      ( ? [X4] :
          ( ~ r1_orders_2(X0,X3,X4)
          & r1_orders_2(X0,X1,X4)
          & r1_orders_2(X0,X2,X4)
          & m1_subset_1(X4,u1_struct_0(X0)) )
     => ( ~ r1_orders_2(X0,X3,sK6(X0,X1,X2,X3))
        & r1_orders_2(X0,X1,sK6(X0,X1,X2,X3))
        & r1_orders_2(X0,X2,sK6(X0,X1,X2,X3))
        & m1_subset_1(sK6(X0,X1,X2,X3),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f60,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( ( ( k10_lattice3(X0,X2,X1) = X3
              | ? [X4] :
                  ( ~ r1_orders_2(X0,X3,X4)
                  & r1_orders_2(X0,X1,X4)
                  & r1_orders_2(X0,X2,X4)
                  & m1_subset_1(X4,u1_struct_0(X0)) )
              | ~ r1_orders_2(X0,X1,X3)
              | ~ r1_orders_2(X0,X2,X3) )
            & ( ( ! [X5] :
                    ( r1_orders_2(X0,X3,X5)
                    | ~ r1_orders_2(X0,X1,X5)
                    | ~ r1_orders_2(X0,X2,X5)
                    | ~ m1_subset_1(X5,u1_struct_0(X0)) )
                & r1_orders_2(X0,X1,X3)
                & r1_orders_2(X0,X2,X3) )
              | k10_lattice3(X0,X2,X1) != X3 ) )
          | ~ m1_subset_1(X3,u1_struct_0(X0)) )
      | ~ sP0(X0,X1,X2) ) ),
    inference(rectify,[],[f59])).

fof(f59,plain,(
    ! [X0,X2,X1] :
      ( ! [X5] :
          ( ( ( k10_lattice3(X0,X1,X2) = X5
              | ? [X6] :
                  ( ~ r1_orders_2(X0,X5,X6)
                  & r1_orders_2(X0,X2,X6)
                  & r1_orders_2(X0,X1,X6)
                  & m1_subset_1(X6,u1_struct_0(X0)) )
              | ~ r1_orders_2(X0,X2,X5)
              | ~ r1_orders_2(X0,X1,X5) )
            & ( ( ! [X6] :
                    ( r1_orders_2(X0,X5,X6)
                    | ~ r1_orders_2(X0,X2,X6)
                    | ~ r1_orders_2(X0,X1,X6)
                    | ~ m1_subset_1(X6,u1_struct_0(X0)) )
                & r1_orders_2(X0,X2,X5)
                & r1_orders_2(X0,X1,X5) )
              | k10_lattice3(X0,X1,X2) != X5 ) )
          | ~ m1_subset_1(X5,u1_struct_0(X0)) )
      | ~ sP0(X0,X2,X1) ) ),
    inference(flattening,[],[f58])).

fof(f58,plain,(
    ! [X0,X2,X1] :
      ( ! [X5] :
          ( ( ( k10_lattice3(X0,X1,X2) = X5
              | ? [X6] :
                  ( ~ r1_orders_2(X0,X5,X6)
                  & r1_orders_2(X0,X2,X6)
                  & r1_orders_2(X0,X1,X6)
                  & m1_subset_1(X6,u1_struct_0(X0)) )
              | ~ r1_orders_2(X0,X2,X5)
              | ~ r1_orders_2(X0,X1,X5) )
            & ( ( ! [X6] :
                    ( r1_orders_2(X0,X5,X6)
                    | ~ r1_orders_2(X0,X2,X6)
                    | ~ r1_orders_2(X0,X1,X6)
                    | ~ m1_subset_1(X6,u1_struct_0(X0)) )
                & r1_orders_2(X0,X2,X5)
                & r1_orders_2(X0,X1,X5) )
              | k10_lattice3(X0,X1,X2) != X5 ) )
          | ~ m1_subset_1(X5,u1_struct_0(X0)) )
      | ~ sP0(X0,X2,X1) ) ),
    inference(nnf_transformation,[],[f47])).

fof(f6929,plain,
    ( ! [X0] :
        ( r1_orders_2(sK1,sK4,sK6(sK1,sK3,sK2,X0))
        | k10_lattice3(sK1,sK2,sK3) = X0
        | ~ r1_orders_2(sK1,sK3,X0)
        | ~ r1_orders_2(sK1,sK2,X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK1)) )
    | ~ spl14_14 ),
    inference(subsumption_resolution,[],[f6928,f2503])).

fof(f6928,plain,
    ( ! [X0] :
        ( r1_orders_2(sK1,sK4,sK6(sK1,sK3,sK2,X0))
        | k10_lattice3(sK1,sK2,sK3) = X0
        | ~ r1_orders_2(sK1,sK3,X0)
        | ~ r1_orders_2(sK1,sK2,X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK1))
        | ~ sP0(sK1,sK3,sK2) )
    | ~ spl14_14 ),
    inference(duplicate_literal_removal,[],[f6927])).

fof(f6927,plain,
    ( ! [X0] :
        ( r1_orders_2(sK1,sK4,sK6(sK1,sK3,sK2,X0))
        | k10_lattice3(sK1,sK2,sK3) = X0
        | ~ r1_orders_2(sK1,sK3,X0)
        | ~ r1_orders_2(sK1,sK2,X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK1))
        | ~ sP0(sK1,sK3,sK2)
        | k10_lattice3(sK1,sK2,sK3) = X0
        | ~ r1_orders_2(sK1,sK3,X0)
        | ~ r1_orders_2(sK1,sK2,X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK1))
        | ~ sP0(sK1,sK3,sK2) )
    | ~ spl14_14 ),
    inference(resolution,[],[f6841,f94])).

fof(f94,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_orders_2(X0,X2,sK6(X0,X1,X2,X3))
      | k10_lattice3(X0,X2,X1) = X3
      | ~ r1_orders_2(X0,X1,X3)
      | ~ r1_orders_2(X0,X2,X3)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f62])).

fof(f6841,plain,
    ( ! [X12,X13] :
        ( ~ r1_orders_2(sK1,sK2,sK6(sK1,sK3,X12,X13))
        | r1_orders_2(sK1,sK4,sK6(sK1,sK3,X12,X13))
        | k10_lattice3(sK1,X12,sK3) = X13
        | ~ r1_orders_2(sK1,sK3,X13)
        | ~ r1_orders_2(sK1,X12,X13)
        | ~ m1_subset_1(X13,u1_struct_0(sK1))
        | ~ sP0(sK1,sK3,X12) )
    | ~ spl14_14 ),
    inference(subsumption_resolution,[],[f6803,f93])).

fof(f93,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(sK6(X0,X1,X2,X3),u1_struct_0(X0))
      | k10_lattice3(X0,X2,X1) = X3
      | ~ r1_orders_2(X0,X1,X3)
      | ~ r1_orders_2(X0,X2,X3)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f62])).

fof(f6803,plain,
    ( ! [X12,X13] :
        ( ~ m1_subset_1(sK6(sK1,sK3,X12,X13),u1_struct_0(sK1))
        | ~ r1_orders_2(sK1,sK2,sK6(sK1,sK3,X12,X13))
        | r1_orders_2(sK1,sK4,sK6(sK1,sK3,X12,X13))
        | k10_lattice3(sK1,X12,sK3) = X13
        | ~ r1_orders_2(sK1,sK3,X13)
        | ~ r1_orders_2(sK1,X12,X13)
        | ~ m1_subset_1(X13,u1_struct_0(sK1))
        | ~ sP0(sK1,sK3,X12) )
    | ~ spl14_14 ),
    inference(resolution,[],[f155,f95])).

fof(f95,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_orders_2(X0,X1,sK6(X0,X1,X2,X3))
      | k10_lattice3(X0,X2,X1) = X3
      | ~ r1_orders_2(X0,X1,X3)
      | ~ r1_orders_2(X0,X2,X3)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f62])).

fof(f155,plain,
    ( ! [X5] :
        ( ~ r1_orders_2(sK1,sK3,X5)
        | ~ m1_subset_1(X5,u1_struct_0(sK1))
        | ~ r1_orders_2(sK1,sK2,X5)
        | r1_orders_2(sK1,sK4,X5) )
    | ~ spl14_14 ),
    inference(avatar_component_clause,[],[f154])).

fof(f154,plain,
    ( spl14_14
  <=> ! [X5] :
        ( r1_orders_2(sK1,sK4,X5)
        | ~ m1_subset_1(X5,u1_struct_0(sK1))
        | ~ r1_orders_2(sK1,sK2,X5)
        | ~ r1_orders_2(sK1,sK3,X5) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_14])])).

fof(f118,plain,(
    ! [X2,X0,X1] :
      ( k13_lattice3(X0,X1,X2) = k10_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1,X2] :
      ( k13_lattice3(X0,X1,X2) = k10_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(flattening,[],[f41])).

fof(f41,plain,(
    ! [X0,X1,X2] :
      ( k13_lattice3(X0,X1,X2) = k10_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l1_orders_2(X0)
        & v1_lattice3(X0)
        & v5_orders_2(X0) )
     => k13_lattice3(X0,X1,X2) = k10_lattice3(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/yellow_0__t22_yellow_0.p',redefinition_k13_lattice3)).

fof(f6815,plain,
    ( spl14_7
    | ~ spl14_8
    | ~ spl14_10
    | ~ spl14_12
    | ~ spl14_14 ),
    inference(avatar_contradiction_clause,[],[f6814])).

fof(f6814,plain,
    ( $false
    | ~ spl14_7
    | ~ spl14_8
    | ~ spl14_10
    | ~ spl14_12
    | ~ spl14_14 ),
    inference(subsumption_resolution,[],[f6813,f136])).

fof(f136,plain,
    ( ~ r1_orders_2(sK1,sK4,sK5)
    | ~ spl14_7 ),
    inference(avatar_component_clause,[],[f135])).

fof(f135,plain,
    ( spl14_7
  <=> ~ r1_orders_2(sK1,sK4,sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_7])])).

fof(f6813,plain,
    ( r1_orders_2(sK1,sK4,sK5)
    | ~ spl14_8
    | ~ spl14_10
    | ~ spl14_12
    | ~ spl14_14 ),
    inference(subsumption_resolution,[],[f6812,f144])).

fof(f144,plain,
    ( r1_orders_2(sK1,sK2,sK5)
    | ~ spl14_10 ),
    inference(avatar_component_clause,[],[f143])).

fof(f143,plain,
    ( spl14_10
  <=> r1_orders_2(sK1,sK2,sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_10])])).

fof(f6812,plain,
    ( ~ r1_orders_2(sK1,sK2,sK5)
    | r1_orders_2(sK1,sK4,sK5)
    | ~ spl14_8
    | ~ spl14_12
    | ~ spl14_14 ),
    inference(subsumption_resolution,[],[f6791,f148])).

fof(f148,plain,
    ( m1_subset_1(sK5,u1_struct_0(sK1))
    | ~ spl14_12 ),
    inference(avatar_component_clause,[],[f147])).

fof(f147,plain,
    ( spl14_12
  <=> m1_subset_1(sK5,u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_12])])).

fof(f6791,plain,
    ( ~ m1_subset_1(sK5,u1_struct_0(sK1))
    | ~ r1_orders_2(sK1,sK2,sK5)
    | r1_orders_2(sK1,sK4,sK5)
    | ~ spl14_8
    | ~ spl14_14 ),
    inference(resolution,[],[f155,f140])).

fof(f140,plain,
    ( r1_orders_2(sK1,sK3,sK5)
    | ~ spl14_8 ),
    inference(avatar_component_clause,[],[f139])).

fof(f139,plain,
    ( spl14_8
  <=> r1_orders_2(sK1,sK3,sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_8])])).

fof(f2517,plain,(
    spl14_57 ),
    inference(avatar_contradiction_clause,[],[f2516])).

fof(f2516,plain,
    ( $false
    | ~ spl14_57 ),
    inference(subsumption_resolution,[],[f2503,f1945])).

fof(f1945,plain,
    ( ~ sP0(sK1,sK3,sK2)
    | ~ spl14_57 ),
    inference(avatar_component_clause,[],[f1944])).

fof(f1944,plain,
    ( spl14_57
  <=> ~ sP0(sK1,sK3,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_57])])).

fof(f1954,plain,
    ( ~ spl14_0
    | spl14_5 ),
    inference(avatar_contradiction_clause,[],[f1953])).

fof(f1953,plain,
    ( $false
    | ~ spl14_0
    | ~ spl14_5 ),
    inference(subsumption_resolution,[],[f133,f1952])).

fof(f1952,plain,
    ( r1_orders_2(sK1,sK3,sK4)
    | ~ spl14_0 ),
    inference(subsumption_resolution,[],[f1951,f76])).

fof(f1951,plain,
    ( r1_orders_2(sK1,sK3,sK4)
    | ~ v5_orders_2(sK1)
    | ~ spl14_0 ),
    inference(subsumption_resolution,[],[f1950,f77])).

fof(f1950,plain,
    ( r1_orders_2(sK1,sK3,sK4)
    | ~ v1_lattice3(sK1)
    | ~ v5_orders_2(sK1)
    | ~ spl14_0 ),
    inference(subsumption_resolution,[],[f1949,f78])).

fof(f1949,plain,
    ( r1_orders_2(sK1,sK3,sK4)
    | ~ l1_orders_2(sK1)
    | ~ v1_lattice3(sK1)
    | ~ v5_orders_2(sK1)
    | ~ spl14_0 ),
    inference(subsumption_resolution,[],[f1948,f80])).

fof(f1948,plain,
    ( r1_orders_2(sK1,sK3,sK4)
    | ~ m1_subset_1(sK3,u1_struct_0(sK1))
    | ~ l1_orders_2(sK1)
    | ~ v1_lattice3(sK1)
    | ~ v5_orders_2(sK1)
    | ~ spl14_0 ),
    inference(subsumption_resolution,[],[f1947,f79])).

fof(f1947,plain,
    ( r1_orders_2(sK1,sK3,sK4)
    | ~ m1_subset_1(sK2,u1_struct_0(sK1))
    | ~ m1_subset_1(sK3,u1_struct_0(sK1))
    | ~ l1_orders_2(sK1)
    | ~ v1_lattice3(sK1)
    | ~ v5_orders_2(sK1)
    | ~ spl14_0 ),
    inference(subsumption_resolution,[],[f1030,f1911])).

fof(f1911,plain,(
    sP0(sK1,sK2,sK3) ),
    inference(resolution,[],[f1881,f80])).

fof(f1881,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK1))
      | sP0(sK1,sK2,X0) ) ),
    inference(subsumption_resolution,[],[f1880,f77])).

fof(f1880,plain,(
    ! [X0] :
      ( sP0(sK1,sK2,X0)
      | ~ m1_subset_1(X0,u1_struct_0(sK1))
      | ~ v1_lattice3(sK1) ) ),
    inference(subsumption_resolution,[],[f1879,f78])).

fof(f1879,plain,(
    ! [X0] :
      ( ~ l1_orders_2(sK1)
      | sP0(sK1,sK2,X0)
      | ~ m1_subset_1(X0,u1_struct_0(sK1))
      | ~ v1_lattice3(sK1) ) ),
    inference(subsumption_resolution,[],[f1860,f76])).

fof(f1860,plain,(
    ! [X0] :
      ( ~ v5_orders_2(sK1)
      | ~ l1_orders_2(sK1)
      | sP0(sK1,sK2,X0)
      | ~ m1_subset_1(X0,u1_struct_0(sK1))
      | ~ v1_lattice3(sK1) ) ),
    inference(resolution,[],[f1822,f79])).

fof(f1030,plain,
    ( r1_orders_2(sK1,sK3,sK4)
    | ~ sP0(sK1,sK2,sK3)
    | ~ m1_subset_1(sK2,u1_struct_0(sK1))
    | ~ m1_subset_1(sK3,u1_struct_0(sK1))
    | ~ l1_orders_2(sK1)
    | ~ v1_lattice3(sK1)
    | ~ v5_orders_2(sK1)
    | ~ spl14_0 ),
    inference(superposition,[],[f549,f152])).

fof(f152,plain,
    ( k13_lattice3(sK1,sK2,sK3) = sK4
    | ~ spl14_0 ),
    inference(avatar_component_clause,[],[f151])).

fof(f151,plain,
    ( spl14_0
  <=> k13_lattice3(sK1,sK2,sK3) = sK4 ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_0])])).

fof(f549,plain,(
    ! [X2,X0,X1] :
      ( r1_orders_2(X0,X1,k13_lattice3(X0,X2,X1))
      | ~ sP0(X0,X2,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(duplicate_literal_removal,[],[f545])).

fof(f545,plain,(
    ! [X2,X0,X1] :
      ( r1_orders_2(X0,X1,k13_lattice3(X0,X2,X1))
      | ~ sP0(X0,X2,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(superposition,[],[f296,f119])).

fof(f119,plain,(
    ! [X2,X0,X1] :
      ( k13_lattice3(X0,X1,X2) = k13_lattice3(X0,X2,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0,X1,X2] :
      ( k13_lattice3(X0,X1,X2) = k13_lattice3(X0,X2,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(flattening,[],[f43])).

fof(f43,plain,(
    ! [X0,X1,X2] :
      ( k13_lattice3(X0,X1,X2) = k13_lattice3(X0,X2,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l1_orders_2(X0)
        & v1_lattice3(X0)
        & v5_orders_2(X0) )
     => k13_lattice3(X0,X1,X2) = k13_lattice3(X0,X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/yellow_0__t22_yellow_0.p',commutativity_k13_lattice3)).

fof(f296,plain,(
    ! [X2,X0,X1] :
      ( r1_orders_2(X0,X1,k13_lattice3(X0,X1,X2))
      | ~ sP0(X0,X2,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(duplicate_literal_removal,[],[f295])).

fof(f295,plain,(
    ! [X2,X0,X1] :
      ( r1_orders_2(X0,X1,k13_lattice3(X0,X1,X2))
      | ~ sP0(X0,X2,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(superposition,[],[f195,f118])).

fof(f195,plain,(
    ! [X2,X0,X1] :
      ( r1_orders_2(X0,X1,k10_lattice3(X0,X1,X2))
      | ~ sP0(X0,X2,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(resolution,[],[f124,f120])).

fof(f120,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k10_lattice3(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k10_lattice3(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f45])).

fof(f45,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k10_lattice3(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l1_orders_2(X0) )
     => m1_subset_1(k10_lattice3(X0,X1,X2),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/yellow_0__t22_yellow_0.p',dt_k10_lattice3)).

fof(f124,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(k10_lattice3(X0,X2,X1),u1_struct_0(X0))
      | r1_orders_2(X0,X2,k10_lattice3(X0,X2,X1))
      | ~ sP0(X0,X1,X2) ) ),
    inference(equality_resolution,[],[f90])).

fof(f90,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_orders_2(X0,X2,X3)
      | k10_lattice3(X0,X2,X1) != X3
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f62])).

fof(f133,plain,
    ( ~ r1_orders_2(sK1,sK3,sK4)
    | ~ spl14_5 ),
    inference(avatar_component_clause,[],[f132])).

fof(f132,plain,
    ( spl14_5
  <=> ~ r1_orders_2(sK1,sK3,sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_5])])).

fof(f1946,plain,
    ( ~ spl14_57
    | spl14_14
    | ~ spl14_0 ),
    inference(avatar_split_clause,[],[f1942,f151,f154,f1944])).

fof(f1942,plain,
    ( ! [X16] :
        ( r1_orders_2(sK1,sK4,X16)
        | ~ r1_orders_2(sK1,sK2,X16)
        | ~ m1_subset_1(X16,u1_struct_0(sK1))
        | ~ r1_orders_2(sK1,sK3,X16)
        | ~ sP0(sK1,sK3,sK2) )
    | ~ spl14_0 ),
    inference(subsumption_resolution,[],[f1941,f76])).

fof(f1941,plain,
    ( ! [X16] :
        ( r1_orders_2(sK1,sK4,X16)
        | ~ r1_orders_2(sK1,sK2,X16)
        | ~ m1_subset_1(X16,u1_struct_0(sK1))
        | ~ r1_orders_2(sK1,sK3,X16)
        | ~ sP0(sK1,sK3,sK2)
        | ~ v5_orders_2(sK1) )
    | ~ spl14_0 ),
    inference(subsumption_resolution,[],[f1940,f77])).

fof(f1940,plain,
    ( ! [X16] :
        ( r1_orders_2(sK1,sK4,X16)
        | ~ r1_orders_2(sK1,sK2,X16)
        | ~ m1_subset_1(X16,u1_struct_0(sK1))
        | ~ r1_orders_2(sK1,sK3,X16)
        | ~ sP0(sK1,sK3,sK2)
        | ~ v1_lattice3(sK1)
        | ~ v5_orders_2(sK1) )
    | ~ spl14_0 ),
    inference(subsumption_resolution,[],[f1939,f78])).

fof(f1939,plain,
    ( ! [X16] :
        ( r1_orders_2(sK1,sK4,X16)
        | ~ r1_orders_2(sK1,sK2,X16)
        | ~ m1_subset_1(X16,u1_struct_0(sK1))
        | ~ r1_orders_2(sK1,sK3,X16)
        | ~ sP0(sK1,sK3,sK2)
        | ~ l1_orders_2(sK1)
        | ~ v1_lattice3(sK1)
        | ~ v5_orders_2(sK1) )
    | ~ spl14_0 ),
    inference(subsumption_resolution,[],[f1938,f79])).

fof(f1938,plain,
    ( ! [X16] :
        ( r1_orders_2(sK1,sK4,X16)
        | ~ r1_orders_2(sK1,sK2,X16)
        | ~ m1_subset_1(X16,u1_struct_0(sK1))
        | ~ r1_orders_2(sK1,sK3,X16)
        | ~ sP0(sK1,sK3,sK2)
        | ~ m1_subset_1(sK2,u1_struct_0(sK1))
        | ~ l1_orders_2(sK1)
        | ~ v1_lattice3(sK1)
        | ~ v5_orders_2(sK1) )
    | ~ spl14_0 ),
    inference(subsumption_resolution,[],[f822,f80])).

fof(f822,plain,
    ( ! [X16] :
        ( r1_orders_2(sK1,sK4,X16)
        | ~ r1_orders_2(sK1,sK2,X16)
        | ~ m1_subset_1(X16,u1_struct_0(sK1))
        | ~ r1_orders_2(sK1,sK3,X16)
        | ~ sP0(sK1,sK3,sK2)
        | ~ m1_subset_1(sK3,u1_struct_0(sK1))
        | ~ m1_subset_1(sK2,u1_struct_0(sK1))
        | ~ l1_orders_2(sK1)
        | ~ v1_lattice3(sK1)
        | ~ v5_orders_2(sK1) )
    | ~ spl14_0 ),
    inference(superposition,[],[f441,f152])).

fof(f441,plain,(
    ! [X10,X8,X11,X9] :
      ( r1_orders_2(X8,k13_lattice3(X8,X9,X10),X11)
      | ~ r1_orders_2(X8,X9,X11)
      | ~ m1_subset_1(X11,u1_struct_0(X8))
      | ~ r1_orders_2(X8,X10,X11)
      | ~ sP0(X8,X10,X9)
      | ~ m1_subset_1(X10,u1_struct_0(X8))
      | ~ m1_subset_1(X9,u1_struct_0(X8))
      | ~ l1_orders_2(X8)
      | ~ v1_lattice3(X8)
      | ~ v5_orders_2(X8) ) ),
    inference(duplicate_literal_removal,[],[f440])).

fof(f440,plain,(
    ! [X10,X8,X11,X9] :
      ( r1_orders_2(X8,k13_lattice3(X8,X9,X10),X11)
      | ~ r1_orders_2(X8,X9,X11)
      | ~ m1_subset_1(X11,u1_struct_0(X8))
      | ~ r1_orders_2(X8,X10,X11)
      | ~ sP0(X8,X10,X9)
      | ~ m1_subset_1(X10,u1_struct_0(X8))
      | ~ m1_subset_1(X9,u1_struct_0(X8))
      | ~ l1_orders_2(X8)
      | ~ m1_subset_1(X10,u1_struct_0(X8))
      | ~ m1_subset_1(X9,u1_struct_0(X8))
      | ~ l1_orders_2(X8)
      | ~ v1_lattice3(X8)
      | ~ v5_orders_2(X8) ) ),
    inference(superposition,[],[f271,f118])).

fof(f271,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_orders_2(X0,k10_lattice3(X0,X3,X1),X2)
      | ~ r1_orders_2(X0,X3,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ r1_orders_2(X0,X1,X2)
      | ~ sP0(X0,X1,X3)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(resolution,[],[f122,f120])).

fof(f122,plain,(
    ! [X2,X0,X5,X1] :
      ( ~ m1_subset_1(k10_lattice3(X0,X2,X1),u1_struct_0(X0))
      | ~ r1_orders_2(X0,X1,X5)
      | ~ r1_orders_2(X0,X2,X5)
      | ~ m1_subset_1(X5,u1_struct_0(X0))
      | r1_orders_2(X0,k10_lattice3(X0,X2,X1),X5)
      | ~ sP0(X0,X1,X2) ) ),
    inference(equality_resolution,[],[f92])).

fof(f92,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r1_orders_2(X0,X3,X5)
      | ~ r1_orders_2(X0,X1,X5)
      | ~ r1_orders_2(X0,X2,X5)
      | ~ m1_subset_1(X5,u1_struct_0(X0))
      | k10_lattice3(X0,X2,X1) != X3
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f62])).

fof(f1923,plain,
    ( ~ spl14_0
    | spl14_3 ),
    inference(avatar_contradiction_clause,[],[f1922])).

fof(f1922,plain,
    ( $false
    | ~ spl14_0
    | ~ spl14_3 ),
    inference(subsumption_resolution,[],[f1911,f955])).

fof(f955,plain,
    ( ~ sP0(sK1,sK2,sK3)
    | ~ spl14_0
    | ~ spl14_3 ),
    inference(subsumption_resolution,[],[f954,f76])).

fof(f954,plain,
    ( ~ sP0(sK1,sK2,sK3)
    | ~ v5_orders_2(sK1)
    | ~ spl14_0
    | ~ spl14_3 ),
    inference(subsumption_resolution,[],[f953,f77])).

fof(f953,plain,
    ( ~ sP0(sK1,sK2,sK3)
    | ~ v1_lattice3(sK1)
    | ~ v5_orders_2(sK1)
    | ~ spl14_0
    | ~ spl14_3 ),
    inference(subsumption_resolution,[],[f952,f78])).

fof(f952,plain,
    ( ~ sP0(sK1,sK2,sK3)
    | ~ l1_orders_2(sK1)
    | ~ v1_lattice3(sK1)
    | ~ v5_orders_2(sK1)
    | ~ spl14_0
    | ~ spl14_3 ),
    inference(subsumption_resolution,[],[f951,f80])).

fof(f951,plain,
    ( ~ sP0(sK1,sK2,sK3)
    | ~ m1_subset_1(sK3,u1_struct_0(sK1))
    | ~ l1_orders_2(sK1)
    | ~ v1_lattice3(sK1)
    | ~ v5_orders_2(sK1)
    | ~ spl14_0
    | ~ spl14_3 ),
    inference(subsumption_resolution,[],[f950,f79])).

fof(f950,plain,
    ( ~ sP0(sK1,sK2,sK3)
    | ~ m1_subset_1(sK2,u1_struct_0(sK1))
    | ~ m1_subset_1(sK3,u1_struct_0(sK1))
    | ~ l1_orders_2(sK1)
    | ~ v1_lattice3(sK1)
    | ~ v5_orders_2(sK1)
    | ~ spl14_0
    | ~ spl14_3 ),
    inference(subsumption_resolution,[],[f943,f130])).

fof(f130,plain,
    ( ~ r1_orders_2(sK1,sK2,sK4)
    | ~ spl14_3 ),
    inference(avatar_component_clause,[],[f129])).

fof(f129,plain,
    ( spl14_3
  <=> ~ r1_orders_2(sK1,sK2,sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_3])])).

fof(f943,plain,
    ( r1_orders_2(sK1,sK2,sK4)
    | ~ sP0(sK1,sK2,sK3)
    | ~ m1_subset_1(sK2,u1_struct_0(sK1))
    | ~ m1_subset_1(sK3,u1_struct_0(sK1))
    | ~ l1_orders_2(sK1)
    | ~ v1_lattice3(sK1)
    | ~ v5_orders_2(sK1)
    | ~ spl14_0 ),
    inference(superposition,[],[f541,f152])).

fof(f541,plain,(
    ! [X2,X0,X1] :
      ( r1_orders_2(X0,X2,k13_lattice3(X0,X2,X1))
      | ~ sP0(X0,X2,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(duplicate_literal_removal,[],[f537])).

fof(f537,plain,(
    ! [X2,X0,X1] :
      ( r1_orders_2(X0,X2,k13_lattice3(X0,X2,X1))
      | ~ sP0(X0,X2,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(superposition,[],[f294,f119])).

fof(f294,plain,(
    ! [X2,X0,X1] :
      ( r1_orders_2(X0,X2,k13_lattice3(X0,X1,X2))
      | ~ sP0(X0,X2,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(duplicate_literal_removal,[],[f293])).

fof(f293,plain,(
    ! [X2,X0,X1] :
      ( r1_orders_2(X0,X2,k13_lattice3(X0,X1,X2))
      | ~ sP0(X0,X2,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(superposition,[],[f194,f118])).

fof(f194,plain,(
    ! [X2,X0,X1] :
      ( r1_orders_2(X0,X1,k10_lattice3(X0,X2,X1))
      | ~ sP0(X0,X1,X2)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(resolution,[],[f123,f120])).

fof(f123,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(k10_lattice3(X0,X2,X1),u1_struct_0(X0))
      | r1_orders_2(X0,X1,k10_lattice3(X0,X2,X1))
      | ~ sP0(X0,X1,X2) ) ),
    inference(equality_resolution,[],[f91])).

fof(f91,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_orders_2(X0,X1,X3)
      | k10_lattice3(X0,X2,X1) != X3
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f62])).

fof(f164,plain,
    ( spl14_0
    | spl14_2 ),
    inference(avatar_split_clause,[],[f82,f162,f151])).

fof(f82,plain,
    ( r1_orders_2(sK1,sK2,sK4)
    | k13_lattice3(sK1,sK2,sK3) = sK4 ),
    inference(cnf_transformation,[],[f57])).

fof(f160,plain,
    ( spl14_0
    | spl14_4 ),
    inference(avatar_split_clause,[],[f83,f158,f151])).

fof(f83,plain,
    ( r1_orders_2(sK1,sK3,sK4)
    | k13_lattice3(sK1,sK2,sK3) = sK4 ),
    inference(cnf_transformation,[],[f57])).

fof(f156,plain,
    ( spl14_0
    | spl14_14 ),
    inference(avatar_split_clause,[],[f84,f154,f151])).

fof(f84,plain,(
    ! [X5] :
      ( r1_orders_2(sK1,sK4,X5)
      | ~ r1_orders_2(sK1,sK3,X5)
      | ~ r1_orders_2(sK1,sK2,X5)
      | ~ m1_subset_1(X5,u1_struct_0(sK1))
      | k13_lattice3(sK1,sK2,sK3) = sK4 ) ),
    inference(cnf_transformation,[],[f57])).

fof(f149,plain,
    ( ~ spl14_1
    | ~ spl14_3
    | ~ spl14_5
    | spl14_12 ),
    inference(avatar_split_clause,[],[f85,f147,f132,f129,f126])).

fof(f85,plain,
    ( m1_subset_1(sK5,u1_struct_0(sK1))
    | ~ r1_orders_2(sK1,sK3,sK4)
    | ~ r1_orders_2(sK1,sK2,sK4)
    | k13_lattice3(sK1,sK2,sK3) != sK4 ),
    inference(cnf_transformation,[],[f57])).

fof(f145,plain,
    ( ~ spl14_1
    | ~ spl14_3
    | ~ spl14_5
    | spl14_10 ),
    inference(avatar_split_clause,[],[f86,f143,f132,f129,f126])).

fof(f86,plain,
    ( r1_orders_2(sK1,sK2,sK5)
    | ~ r1_orders_2(sK1,sK3,sK4)
    | ~ r1_orders_2(sK1,sK2,sK4)
    | k13_lattice3(sK1,sK2,sK3) != sK4 ),
    inference(cnf_transformation,[],[f57])).

fof(f141,plain,
    ( ~ spl14_1
    | ~ spl14_3
    | ~ spl14_5
    | spl14_8 ),
    inference(avatar_split_clause,[],[f87,f139,f132,f129,f126])).

fof(f87,plain,
    ( r1_orders_2(sK1,sK3,sK5)
    | ~ r1_orders_2(sK1,sK3,sK4)
    | ~ r1_orders_2(sK1,sK2,sK4)
    | k13_lattice3(sK1,sK2,sK3) != sK4 ),
    inference(cnf_transformation,[],[f57])).

fof(f137,plain,
    ( ~ spl14_1
    | ~ spl14_3
    | ~ spl14_5
    | ~ spl14_7 ),
    inference(avatar_split_clause,[],[f88,f135,f132,f129,f126])).

fof(f88,plain,
    ( ~ r1_orders_2(sK1,sK4,sK5)
    | ~ r1_orders_2(sK1,sK3,sK4)
    | ~ r1_orders_2(sK1,sK2,sK4)
    | k13_lattice3(sK1,sK2,sK3) != sK4 ),
    inference(cnf_transformation,[],[f57])).
%------------------------------------------------------------------------------
