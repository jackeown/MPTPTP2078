%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : yellow_0__t41_yellow_0.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:41:42 EDT 2019

% Result     : Theorem 1.01s
% Output     : Refutation 1.01s
% Verified   : 
% Statistics : Number of formulae       :  188 ( 765 expanded)
%              Number of leaves         :   19 ( 197 expanded)
%              Depth                    :   37
%              Number of atoms          : 1489 (6943 expanded)
%              Number of equality atoms :   92 ( 436 expanded)
%              Maximal formula depth    :   27 (  11 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f5552,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f199,f211,f5543])).

fof(f5543,plain,(
    spl11_7 ),
    inference(avatar_contradiction_clause,[],[f5542])).

fof(f5542,plain,
    ( $false
    | ~ spl11_7 ),
    inference(subsumption_resolution,[],[f5541,f115])).

fof(f115,plain,(
    m1_subset_1(sK2,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f87])).

fof(f87,plain,
    ( k1_yellow_0(sK0,k7_domain_1(u1_struct_0(sK0),sK1,sK2)) != k13_lattice3(sK0,sK1,sK2)
    & m1_subset_1(sK2,u1_struct_0(sK0))
    & m1_subset_1(sK1,u1_struct_0(sK0))
    & l1_orders_2(sK0)
    & v1_lattice3(sK0)
    & v5_orders_2(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f45,f86,f85,f84])).

fof(f84,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( k1_yellow_0(X0,k7_domain_1(u1_struct_0(X0),X1,X2)) != k13_lattice3(X0,X1,X2)
                & m1_subset_1(X2,u1_struct_0(X0)) )
            & m1_subset_1(X1,u1_struct_0(X0)) )
        & l1_orders_2(X0)
        & v1_lattice3(X0)
        & v5_orders_2(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( k1_yellow_0(sK0,k7_domain_1(u1_struct_0(sK0),X1,X2)) != k13_lattice3(sK0,X1,X2)
              & m1_subset_1(X2,u1_struct_0(sK0)) )
          & m1_subset_1(X1,u1_struct_0(sK0)) )
      & l1_orders_2(sK0)
      & v1_lattice3(sK0)
      & v5_orders_2(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f85,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( k1_yellow_0(X0,k7_domain_1(u1_struct_0(X0),X1,X2)) != k13_lattice3(X0,X1,X2)
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
     => ( ? [X2] :
            ( k1_yellow_0(X0,k7_domain_1(u1_struct_0(X0),sK1,X2)) != k13_lattice3(X0,sK1,X2)
            & m1_subset_1(X2,u1_struct_0(X0)) )
        & m1_subset_1(sK1,u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f86,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( k1_yellow_0(X0,k7_domain_1(u1_struct_0(X0),X1,X2)) != k13_lattice3(X0,X1,X2)
          & m1_subset_1(X2,u1_struct_0(X0)) )
     => ( k1_yellow_0(X0,k7_domain_1(u1_struct_0(X0),X1,sK2)) != k13_lattice3(X0,X1,sK2)
        & m1_subset_1(sK2,u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f45,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( k1_yellow_0(X0,k7_domain_1(u1_struct_0(X0),X1,X2)) != k13_lattice3(X0,X1,X2)
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_orders_2(X0)
      & v1_lattice3(X0)
      & v5_orders_2(X0) ) ),
    inference(flattening,[],[f44])).

fof(f44,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( k1_yellow_0(X0,k7_domain_1(u1_struct_0(X0),X1,X2)) != k13_lattice3(X0,X1,X2)
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_orders_2(X0)
      & v1_lattice3(X0)
      & v5_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f42])).

fof(f42,plain,(
    ~ ! [X0] :
        ( ( l1_orders_2(X0)
          & v1_lattice3(X0)
          & v5_orders_2(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => k1_yellow_0(X0,k7_domain_1(u1_struct_0(X0),X1,X2)) = k13_lattice3(X0,X1,X2) ) ) ) ),
    inference(pure_predicate_removal,[],[f41])).

fof(f41,plain,(
    ~ ! [X0] :
        ( ( l1_orders_2(X0)
          & v1_lattice3(X0)
          & v5_orders_2(X0)
          & v3_orders_2(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => k1_yellow_0(X0,k7_domain_1(u1_struct_0(X0),X1,X2)) = k13_lattice3(X0,X1,X2) ) ) ) ),
    inference(pure_predicate_removal,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_orders_2(X0)
          & v1_lattice3(X0)
          & v5_orders_2(X0)
          & v4_orders_2(X0)
          & v3_orders_2(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => k1_yellow_0(X0,k7_domain_1(u1_struct_0(X0),X1,X2)) = k13_lattice3(X0,X1,X2) ) ) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v1_lattice3(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => k1_yellow_0(X0,k7_domain_1(u1_struct_0(X0),X1,X2)) = k13_lattice3(X0,X1,X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/yellow_0__t41_yellow_0.p',t41_yellow_0)).

fof(f5541,plain,
    ( ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ spl11_7 ),
    inference(subsumption_resolution,[],[f5540,f112])).

fof(f112,plain,(
    v1_lattice3(sK0) ),
    inference(cnf_transformation,[],[f87])).

fof(f5540,plain,
    ( ~ v1_lattice3(sK0)
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ spl11_7 ),
    inference(subsumption_resolution,[],[f5539,f114])).

fof(f114,plain,(
    m1_subset_1(sK1,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f87])).

fof(f5539,plain,
    ( ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ v1_lattice3(sK0)
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ spl11_7 ),
    inference(subsumption_resolution,[],[f5538,f111])).

fof(f111,plain,(
    v5_orders_2(sK0) ),
    inference(cnf_transformation,[],[f87])).

fof(f5538,plain,
    ( ~ v5_orders_2(sK0)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ v1_lattice3(sK0)
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ spl11_7 ),
    inference(subsumption_resolution,[],[f5533,f113])).

fof(f113,plain,(
    l1_orders_2(sK0) ),
    inference(cnf_transformation,[],[f87])).

fof(f5533,plain,
    ( ~ l1_orders_2(sK0)
    | ~ v5_orders_2(sK0)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ v1_lattice3(sK0)
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ spl11_7 ),
    inference(resolution,[],[f5392,f4045])).

fof(f4045,plain,(
    ! [X125,X123,X124] :
      ( r2_lattice3(X123,k2_tarski(X124,X125),k13_lattice3(X123,X124,X125))
      | ~ l1_orders_2(X123)
      | ~ v5_orders_2(X123)
      | ~ m1_subset_1(X124,u1_struct_0(X123))
      | ~ v1_lattice3(X123)
      | ~ m1_subset_1(X125,u1_struct_0(X123)) ) ),
    inference(subsumption_resolution,[],[f3972,f3873])).

fof(f3873,plain,(
    ! [X2,X0,X1] :
      ( r1_yellow_0(X1,k2_tarski(X2,X0))
      | ~ l1_orders_2(X1)
      | ~ v1_lattice3(X1)
      | ~ v5_orders_2(X1)
      | ~ m1_subset_1(X0,u1_struct_0(X1))
      | ~ m1_subset_1(X2,u1_struct_0(X1)) ) ),
    inference(subsumption_resolution,[],[f3872,f156])).

fof(f156,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k13_lattice3(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f74])).

fof(f74,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k13_lattice3(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(flattening,[],[f73])).

fof(f73,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k13_lattice3(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l1_orders_2(X0)
        & v1_lattice3(X0)
        & v5_orders_2(X0) )
     => m1_subset_1(k13_lattice3(X0,X1,X2),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/yellow_0__t41_yellow_0.p',dt_k13_lattice3)).

fof(f3872,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X0,u1_struct_0(X1))
      | ~ l1_orders_2(X1)
      | ~ v1_lattice3(X1)
      | ~ v5_orders_2(X1)
      | r1_yellow_0(X1,k2_tarski(X2,X0))
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ m1_subset_1(k13_lattice3(X1,X0,X2),u1_struct_0(X1)) ) ),
    inference(subsumption_resolution,[],[f3871,f298])).

fof(f298,plain,(
    ! [X2,X0,X1] :
      ( r1_orders_2(X0,X1,k13_lattice3(X0,X2,X1))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(duplicate_literal_removal,[],[f293])).

fof(f293,plain,(
    ! [X2,X0,X1] :
      ( r1_orders_2(X0,X1,k13_lattice3(X0,X2,X1))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(resolution,[],[f170,f156])).

fof(f170,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(k13_lattice3(X0,X1,X2),u1_struct_0(X0))
      | r1_orders_2(X0,X2,k13_lattice3(X0,X1,X2))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(equality_resolution,[],[f133])).

fof(f133,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_orders_2(X0,X2,X3)
      | k13_lattice3(X0,X1,X2) != X3
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f97])).

fof(f97,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ( k13_lattice3(X0,X1,X2) = X3
                      | ( ~ r1_orders_2(X0,X3,sK4(X0,X1,X2,X3))
                        & r1_orders_2(X0,X2,sK4(X0,X1,X2,X3))
                        & r1_orders_2(X0,X1,sK4(X0,X1,X2,X3))
                        & m1_subset_1(sK4(X0,X1,X2,X3),u1_struct_0(X0)) )
                      | ~ r1_orders_2(X0,X2,X3)
                      | ~ r1_orders_2(X0,X1,X3) )
                    & ( ( ! [X5] :
                            ( r1_orders_2(X0,X3,X5)
                            | ~ r1_orders_2(X0,X2,X5)
                            | ~ r1_orders_2(X0,X1,X5)
                            | ~ m1_subset_1(X5,u1_struct_0(X0)) )
                        & r1_orders_2(X0,X2,X3)
                        & r1_orders_2(X0,X1,X3) )
                      | k13_lattice3(X0,X1,X2) != X3 ) )
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f95,f96])).

fof(f96,plain,(
    ! [X3,X2,X1,X0] :
      ( ? [X4] :
          ( ~ r1_orders_2(X0,X3,X4)
          & r1_orders_2(X0,X2,X4)
          & r1_orders_2(X0,X1,X4)
          & m1_subset_1(X4,u1_struct_0(X0)) )
     => ( ~ r1_orders_2(X0,X3,sK4(X0,X1,X2,X3))
        & r1_orders_2(X0,X2,sK4(X0,X1,X2,X3))
        & r1_orders_2(X0,X1,sK4(X0,X1,X2,X3))
        & m1_subset_1(sK4(X0,X1,X2,X3),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f95,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ( k13_lattice3(X0,X1,X2) = X3
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
                      | k13_lattice3(X0,X1,X2) != X3 ) )
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(rectify,[],[f94])).

fof(f94,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ( k13_lattice3(X0,X1,X2) = X3
                      | ? [X4] :
                          ( ~ r1_orders_2(X0,X3,X4)
                          & r1_orders_2(X0,X2,X4)
                          & r1_orders_2(X0,X1,X4)
                          & m1_subset_1(X4,u1_struct_0(X0)) )
                      | ~ r1_orders_2(X0,X2,X3)
                      | ~ r1_orders_2(X0,X1,X3) )
                    & ( ( ! [X4] :
                            ( r1_orders_2(X0,X3,X4)
                            | ~ r1_orders_2(X0,X2,X4)
                            | ~ r1_orders_2(X0,X1,X4)
                            | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                        & r1_orders_2(X0,X2,X3)
                        & r1_orders_2(X0,X1,X3) )
                      | k13_lattice3(X0,X1,X2) != X3 ) )
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(flattening,[],[f93])).

fof(f93,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ( k13_lattice3(X0,X1,X2) = X3
                      | ? [X4] :
                          ( ~ r1_orders_2(X0,X3,X4)
                          & r1_orders_2(X0,X2,X4)
                          & r1_orders_2(X0,X1,X4)
                          & m1_subset_1(X4,u1_struct_0(X0)) )
                      | ~ r1_orders_2(X0,X2,X3)
                      | ~ r1_orders_2(X0,X1,X3) )
                    & ( ( ! [X4] :
                            ( r1_orders_2(X0,X3,X4)
                            | ~ r1_orders_2(X0,X2,X4)
                            | ~ r1_orders_2(X0,X1,X4)
                            | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                        & r1_orders_2(X0,X2,X3)
                        & r1_orders_2(X0,X1,X3) )
                      | k13_lattice3(X0,X1,X2) != X3 ) )
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(nnf_transformation,[],[f57])).

fof(f57,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( k13_lattice3(X0,X1,X2) = X3
                  <=> ( ! [X4] :
                          ( r1_orders_2(X0,X3,X4)
                          | ~ r1_orders_2(X0,X2,X4)
                          | ~ r1_orders_2(X0,X1,X4)
                          | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                      & r1_orders_2(X0,X2,X3)
                      & r1_orders_2(X0,X1,X3) ) )
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(flattening,[],[f56])).

fof(f56,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( k13_lattice3(X0,X1,X2) = X3
                  <=> ( ! [X4] :
                          ( r1_orders_2(X0,X3,X4)
                          | ~ r1_orders_2(X0,X2,X4)
                          | ~ r1_orders_2(X0,X1,X4)
                          | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                      & r1_orders_2(X0,X2,X3)
                      & r1_orders_2(X0,X1,X3) ) )
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f26])).

fof(f26,axiom,(
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
    file('/export/starexec/sandbox/benchmark/yellow_0__t41_yellow_0.p',t22_yellow_0)).

fof(f3871,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X0,u1_struct_0(X1))
      | ~ l1_orders_2(X1)
      | ~ v1_lattice3(X1)
      | ~ v5_orders_2(X1)
      | r1_yellow_0(X1,k2_tarski(X2,X0))
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ r1_orders_2(X1,X2,k13_lattice3(X1,X0,X2))
      | ~ m1_subset_1(k13_lattice3(X1,X0,X2),u1_struct_0(X1)) ) ),
    inference(subsumption_resolution,[],[f3870,f304])).

fof(f304,plain,(
    ! [X2,X0,X1] :
      ( r1_orders_2(X0,X1,k13_lattice3(X0,X1,X2))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(duplicate_literal_removal,[],[f299])).

fof(f299,plain,(
    ! [X2,X0,X1] :
      ( r1_orders_2(X0,X1,k13_lattice3(X0,X1,X2))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(resolution,[],[f171,f156])).

fof(f171,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(k13_lattice3(X0,X1,X2),u1_struct_0(X0))
      | r1_orders_2(X0,X1,k13_lattice3(X0,X1,X2))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(equality_resolution,[],[f132])).

fof(f132,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_orders_2(X0,X1,X3)
      | k13_lattice3(X0,X1,X2) != X3
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f97])).

fof(f3870,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X0,u1_struct_0(X1))
      | ~ l1_orders_2(X1)
      | ~ v1_lattice3(X1)
      | ~ v5_orders_2(X1)
      | r1_yellow_0(X1,k2_tarski(X2,X0))
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ r1_orders_2(X1,X0,k13_lattice3(X1,X0,X2))
      | ~ r1_orders_2(X1,X2,k13_lattice3(X1,X0,X2))
      | ~ m1_subset_1(k13_lattice3(X1,X0,X2),u1_struct_0(X1)) ) ),
    inference(duplicate_literal_removal,[],[f3859])).

fof(f3859,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X0,u1_struct_0(X1))
      | ~ l1_orders_2(X1)
      | ~ v1_lattice3(X1)
      | ~ v5_orders_2(X1)
      | r1_yellow_0(X1,k2_tarski(X2,X0))
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ r1_orders_2(X1,X0,k13_lattice3(X1,X0,X2))
      | ~ r1_orders_2(X1,X2,k13_lattice3(X1,X0,X2))
      | ~ m1_subset_1(X0,u1_struct_0(X1))
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ m1_subset_1(k13_lattice3(X1,X0,X2),u1_struct_0(X1))
      | ~ l1_orders_2(X1) ) ),
    inference(resolution,[],[f1692,f124])).

fof(f124,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_lattice3(X0,k2_tarski(X2,X3),X1)
      | ~ r1_orders_2(X0,X3,X1)
      | ~ r1_orders_2(X0,X2,X1)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f50,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ( r2_lattice3(X0,k2_tarski(X2,X3),X1)
                      | ~ r1_orders_2(X0,X3,X1)
                      | ~ r1_orders_2(X0,X2,X1) )
                    & ( ( r1_orders_2(X0,X3,X1)
                        & r1_orders_2(X0,X2,X1) )
                      | ~ r2_lattice3(X0,k2_tarski(X2,X3),X1) )
                    & ( r1_lattice3(X0,k2_tarski(X2,X3),X1)
                      | ~ r1_orders_2(X0,X1,X3)
                      | ~ r1_orders_2(X0,X1,X2) )
                    & ( ( r1_orders_2(X0,X1,X3)
                        & r1_orders_2(X0,X1,X2) )
                      | ~ r1_lattice3(X0,k2_tarski(X2,X3),X1) ) )
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f49])).

fof(f49,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ( r2_lattice3(X0,k2_tarski(X2,X3),X1)
                      | ~ r1_orders_2(X0,X3,X1)
                      | ~ r1_orders_2(X0,X2,X1) )
                    & ( ( r1_orders_2(X0,X3,X1)
                        & r1_orders_2(X0,X2,X1) )
                      | ~ r2_lattice3(X0,k2_tarski(X2,X3),X1) )
                    & ( r1_lattice3(X0,k2_tarski(X2,X3),X1)
                      | ~ r1_orders_2(X0,X1,X3)
                      | ~ r1_orders_2(X0,X1,X2) )
                    & ( ( r1_orders_2(X0,X1,X3)
                        & r1_orders_2(X0,X1,X2) )
                      | ~ r1_lattice3(X0,k2_tarski(X2,X3),X1) ) )
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f34])).

fof(f34,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ! [X3] :
                  ( m1_subset_1(X3,u1_struct_0(X0))
                 => ( ( ( r1_orders_2(X0,X3,X1)
                        & r1_orders_2(X0,X2,X1) )
                     => r2_lattice3(X0,k2_tarski(X2,X3),X1) )
                    & ( r2_lattice3(X0,k2_tarski(X2,X3),X1)
                     => ( r1_orders_2(X0,X3,X1)
                        & r1_orders_2(X0,X2,X1) ) )
                    & ( ( r1_orders_2(X0,X1,X3)
                        & r1_orders_2(X0,X1,X2) )
                     => r1_lattice3(X0,k2_tarski(X2,X3),X1) )
                    & ( r1_lattice3(X0,k2_tarski(X2,X3),X1)
                     => ( r1_orders_2(X0,X1,X3)
                        & r1_orders_2(X0,X1,X2) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/yellow_0__t41_yellow_0.p',t8_yellow_0)).

fof(f1692,plain,(
    ! [X10,X11,X9] :
      ( ~ r2_lattice3(X10,k2_tarski(X9,X11),k13_lattice3(X10,X11,X9))
      | ~ m1_subset_1(X11,u1_struct_0(X10))
      | ~ l1_orders_2(X10)
      | ~ v1_lattice3(X10)
      | ~ v5_orders_2(X10)
      | r1_yellow_0(X10,k2_tarski(X9,X11))
      | ~ m1_subset_1(X9,u1_struct_0(X10)) ) ),
    inference(subsumption_resolution,[],[f1685,f156])).

fof(f1685,plain,(
    ! [X10,X11,X9] :
      ( ~ m1_subset_1(X9,u1_struct_0(X10))
      | ~ m1_subset_1(X11,u1_struct_0(X10))
      | ~ l1_orders_2(X10)
      | ~ v1_lattice3(X10)
      | ~ v5_orders_2(X10)
      | r1_yellow_0(X10,k2_tarski(X9,X11))
      | ~ r2_lattice3(X10,k2_tarski(X9,X11),k13_lattice3(X10,X11,X9))
      | ~ m1_subset_1(k13_lattice3(X10,X11,X9),u1_struct_0(X10)) ) ),
    inference(duplicate_literal_removal,[],[f1668])).

fof(f1668,plain,(
    ! [X10,X11,X9] :
      ( ~ m1_subset_1(X9,u1_struct_0(X10))
      | ~ m1_subset_1(X11,u1_struct_0(X10))
      | ~ l1_orders_2(X10)
      | ~ v1_lattice3(X10)
      | ~ v5_orders_2(X10)
      | r1_yellow_0(X10,k2_tarski(X9,X11))
      | ~ r2_lattice3(X10,k2_tarski(X9,X11),k13_lattice3(X10,X11,X9))
      | ~ m1_subset_1(X11,u1_struct_0(X10))
      | ~ m1_subset_1(X11,u1_struct_0(X10))
      | ~ m1_subset_1(X9,u1_struct_0(X10))
      | ~ l1_orders_2(X10)
      | r1_yellow_0(X10,k2_tarski(X9,X11))
      | ~ r2_lattice3(X10,k2_tarski(X9,X11),k13_lattice3(X10,X11,X9))
      | ~ m1_subset_1(k13_lattice3(X10,X11,X9),u1_struct_0(X10))
      | ~ v5_orders_2(X10) ) ),
    inference(resolution,[],[f826,f266])).

fof(f266,plain,(
    ! [X6,X4,X5,X3] :
      ( r1_orders_2(X3,X4,sK5(X3,k2_tarski(X5,X4),X6))
      | ~ m1_subset_1(X4,u1_struct_0(X3))
      | ~ m1_subset_1(X5,u1_struct_0(X3))
      | ~ l1_orders_2(X3)
      | r1_yellow_0(X3,k2_tarski(X5,X4))
      | ~ r2_lattice3(X3,k2_tarski(X5,X4),X6)
      | ~ m1_subset_1(X6,u1_struct_0(X3))
      | ~ v5_orders_2(X3) ) ),
    inference(subsumption_resolution,[],[f263,f142])).

fof(f142,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(sK5(X0,X1,X2),u1_struct_0(X0))
      | r1_yellow_0(X0,X1)
      | ~ r2_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f102])).

fof(f102,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_yellow_0(X0,X1)
            | ! [X2] :
                ( ( ~ r1_orders_2(X0,X2,sK5(X0,X1,X2))
                  & r2_lattice3(X0,X1,sK5(X0,X1,X2))
                  & m1_subset_1(sK5(X0,X1,X2),u1_struct_0(X0)) )
                | ~ r2_lattice3(X0,X1,X2)
                | ~ m1_subset_1(X2,u1_struct_0(X0)) ) )
          & ( ( ! [X5] :
                  ( r1_orders_2(X0,sK6(X0,X1),X5)
                  | ~ r2_lattice3(X0,X1,X5)
                  | ~ m1_subset_1(X5,u1_struct_0(X0)) )
              & r2_lattice3(X0,X1,sK6(X0,X1))
              & m1_subset_1(sK6(X0,X1),u1_struct_0(X0)) )
            | ~ r1_yellow_0(X0,X1) ) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6])],[f99,f101,f100])).

fof(f100,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r1_orders_2(X0,X2,X3)
          & r2_lattice3(X0,X1,X3)
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ~ r1_orders_2(X0,X2,sK5(X0,X1,X2))
        & r2_lattice3(X0,X1,sK5(X0,X1,X2))
        & m1_subset_1(sK5(X0,X1,X2),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f101,plain,(
    ! [X1,X0] :
      ( ? [X4] :
          ( ! [X5] :
              ( r1_orders_2(X0,X4,X5)
              | ~ r2_lattice3(X0,X1,X5)
              | ~ m1_subset_1(X5,u1_struct_0(X0)) )
          & r2_lattice3(X0,X1,X4)
          & m1_subset_1(X4,u1_struct_0(X0)) )
     => ( ! [X5] :
            ( r1_orders_2(X0,sK6(X0,X1),X5)
            | ~ r2_lattice3(X0,X1,X5)
            | ~ m1_subset_1(X5,u1_struct_0(X0)) )
        & r2_lattice3(X0,X1,sK6(X0,X1))
        & m1_subset_1(sK6(X0,X1),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f99,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_yellow_0(X0,X1)
            | ! [X2] :
                ( ? [X3] :
                    ( ~ r1_orders_2(X0,X2,X3)
                    & r2_lattice3(X0,X1,X3)
                    & m1_subset_1(X3,u1_struct_0(X0)) )
                | ~ r2_lattice3(X0,X1,X2)
                | ~ m1_subset_1(X2,u1_struct_0(X0)) ) )
          & ( ? [X4] :
                ( ! [X5] :
                    ( r1_orders_2(X0,X4,X5)
                    | ~ r2_lattice3(X0,X1,X5)
                    | ~ m1_subset_1(X5,u1_struct_0(X0)) )
                & r2_lattice3(X0,X1,X4)
                & m1_subset_1(X4,u1_struct_0(X0)) )
            | ~ r1_yellow_0(X0,X1) ) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(rectify,[],[f98])).

fof(f98,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_yellow_0(X0,X1)
            | ! [X2] :
                ( ? [X3] :
                    ( ~ r1_orders_2(X0,X2,X3)
                    & r2_lattice3(X0,X1,X3)
                    & m1_subset_1(X3,u1_struct_0(X0)) )
                | ~ r2_lattice3(X0,X1,X2)
                | ~ m1_subset_1(X2,u1_struct_0(X0)) ) )
          & ( ? [X2] :
                ( ! [X3] :
                    ( r1_orders_2(X0,X2,X3)
                    | ~ r2_lattice3(X0,X1,X3)
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                & r2_lattice3(X0,X1,X2)
                & m1_subset_1(X2,u1_struct_0(X0)) )
            | ~ r1_yellow_0(X0,X1) ) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(nnf_transformation,[],[f59])).

fof(f59,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_yellow_0(X0,X1)
        <=> ? [X2] :
              ( ! [X3] :
                  ( r1_orders_2(X0,X2,X3)
                  | ~ r2_lattice3(X0,X1,X3)
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              & r2_lattice3(X0,X1,X2)
              & m1_subset_1(X2,u1_struct_0(X0)) ) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(flattening,[],[f58])).

fof(f58,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_yellow_0(X0,X1)
        <=> ? [X2] :
              ( ! [X3] :
                  ( r1_orders_2(X0,X2,X3)
                  | ~ r2_lattice3(X0,X1,X3)
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              & r2_lattice3(X0,X1,X2)
              & m1_subset_1(X2,u1_struct_0(X0)) ) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f24])).

fof(f24,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0) )
     => ! [X1] :
          ( r1_yellow_0(X0,X1)
        <=> ? [X2] :
              ( ! [X3] :
                  ( m1_subset_1(X3,u1_struct_0(X0))
                 => ( r2_lattice3(X0,X1,X3)
                   => r1_orders_2(X0,X2,X3) ) )
              & r2_lattice3(X0,X1,X2)
              & m1_subset_1(X2,u1_struct_0(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/yellow_0__t41_yellow_0.p',t15_yellow_0)).

fof(f263,plain,(
    ! [X6,X4,X5,X3] :
      ( r1_orders_2(X3,X4,sK5(X3,k2_tarski(X5,X4),X6))
      | ~ m1_subset_1(X4,u1_struct_0(X3))
      | ~ m1_subset_1(X5,u1_struct_0(X3))
      | ~ m1_subset_1(sK5(X3,k2_tarski(X5,X4),X6),u1_struct_0(X3))
      | ~ l1_orders_2(X3)
      | r1_yellow_0(X3,k2_tarski(X5,X4))
      | ~ r2_lattice3(X3,k2_tarski(X5,X4),X6)
      | ~ m1_subset_1(X6,u1_struct_0(X3))
      | ~ v5_orders_2(X3) ) ),
    inference(duplicate_literal_removal,[],[f260])).

fof(f260,plain,(
    ! [X6,X4,X5,X3] :
      ( r1_orders_2(X3,X4,sK5(X3,k2_tarski(X5,X4),X6))
      | ~ m1_subset_1(X4,u1_struct_0(X3))
      | ~ m1_subset_1(X5,u1_struct_0(X3))
      | ~ m1_subset_1(sK5(X3,k2_tarski(X5,X4),X6),u1_struct_0(X3))
      | ~ l1_orders_2(X3)
      | r1_yellow_0(X3,k2_tarski(X5,X4))
      | ~ r2_lattice3(X3,k2_tarski(X5,X4),X6)
      | ~ m1_subset_1(X6,u1_struct_0(X3))
      | ~ l1_orders_2(X3)
      | ~ v5_orders_2(X3) ) ),
    inference(resolution,[],[f123,f143])).

fof(f143,plain,(
    ! [X2,X0,X1] :
      ( r2_lattice3(X0,X1,sK5(X0,X1,X2))
      | r1_yellow_0(X0,X1)
      | ~ r2_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f102])).

fof(f123,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_lattice3(X0,k2_tarski(X2,X3),X1)
      | r1_orders_2(X0,X3,X1)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f826,plain,(
    ! [X6,X4,X7,X5] :
      ( ~ r1_orders_2(X4,X5,sK5(X4,k2_tarski(X6,X7),k13_lattice3(X4,X5,X6)))
      | ~ m1_subset_1(X6,u1_struct_0(X4))
      | ~ m1_subset_1(X5,u1_struct_0(X4))
      | ~ l1_orders_2(X4)
      | ~ v1_lattice3(X4)
      | ~ v5_orders_2(X4)
      | r1_yellow_0(X4,k2_tarski(X6,X7))
      | ~ r2_lattice3(X4,k2_tarski(X6,X7),k13_lattice3(X4,X5,X6))
      | ~ m1_subset_1(X7,u1_struct_0(X4)) ) ),
    inference(subsumption_resolution,[],[f823,f156])).

fof(f823,plain,(
    ! [X6,X4,X7,X5] :
      ( ~ r1_orders_2(X4,X5,sK5(X4,k2_tarski(X6,X7),k13_lattice3(X4,X5,X6)))
      | ~ m1_subset_1(X6,u1_struct_0(X4))
      | ~ m1_subset_1(X5,u1_struct_0(X4))
      | ~ l1_orders_2(X4)
      | ~ v1_lattice3(X4)
      | ~ v5_orders_2(X4)
      | r1_yellow_0(X4,k2_tarski(X6,X7))
      | ~ r2_lattice3(X4,k2_tarski(X6,X7),k13_lattice3(X4,X5,X6))
      | ~ m1_subset_1(X7,u1_struct_0(X4))
      | ~ m1_subset_1(k13_lattice3(X4,X5,X6),u1_struct_0(X4)) ) ),
    inference(duplicate_literal_removal,[],[f804])).

fof(f804,plain,(
    ! [X6,X4,X7,X5] :
      ( ~ r1_orders_2(X4,X5,sK5(X4,k2_tarski(X6,X7),k13_lattice3(X4,X5,X6)))
      | ~ m1_subset_1(X6,u1_struct_0(X4))
      | ~ m1_subset_1(X5,u1_struct_0(X4))
      | ~ l1_orders_2(X4)
      | ~ v1_lattice3(X4)
      | ~ v5_orders_2(X4)
      | r1_yellow_0(X4,k2_tarski(X6,X7))
      | ~ r2_lattice3(X4,k2_tarski(X6,X7),k13_lattice3(X4,X5,X6))
      | ~ m1_subset_1(X7,u1_struct_0(X4))
      | ~ m1_subset_1(X6,u1_struct_0(X4))
      | ~ l1_orders_2(X4)
      | r1_yellow_0(X4,k2_tarski(X6,X7))
      | ~ r2_lattice3(X4,k2_tarski(X6,X7),k13_lattice3(X4,X5,X6))
      | ~ m1_subset_1(k13_lattice3(X4,X5,X6),u1_struct_0(X4))
      | ~ v5_orders_2(X4) ) ),
    inference(resolution,[],[f506,f258])).

fof(f258,plain,(
    ! [X6,X4,X5,X3] :
      ( r1_orders_2(X3,X4,sK5(X3,k2_tarski(X4,X5),X6))
      | ~ m1_subset_1(X5,u1_struct_0(X3))
      | ~ m1_subset_1(X4,u1_struct_0(X3))
      | ~ l1_orders_2(X3)
      | r1_yellow_0(X3,k2_tarski(X4,X5))
      | ~ r2_lattice3(X3,k2_tarski(X4,X5),X6)
      | ~ m1_subset_1(X6,u1_struct_0(X3))
      | ~ v5_orders_2(X3) ) ),
    inference(subsumption_resolution,[],[f255,f142])).

fof(f255,plain,(
    ! [X6,X4,X5,X3] :
      ( r1_orders_2(X3,X4,sK5(X3,k2_tarski(X4,X5),X6))
      | ~ m1_subset_1(X5,u1_struct_0(X3))
      | ~ m1_subset_1(X4,u1_struct_0(X3))
      | ~ m1_subset_1(sK5(X3,k2_tarski(X4,X5),X6),u1_struct_0(X3))
      | ~ l1_orders_2(X3)
      | r1_yellow_0(X3,k2_tarski(X4,X5))
      | ~ r2_lattice3(X3,k2_tarski(X4,X5),X6)
      | ~ m1_subset_1(X6,u1_struct_0(X3))
      | ~ v5_orders_2(X3) ) ),
    inference(duplicate_literal_removal,[],[f252])).

fof(f252,plain,(
    ! [X6,X4,X5,X3] :
      ( r1_orders_2(X3,X4,sK5(X3,k2_tarski(X4,X5),X6))
      | ~ m1_subset_1(X5,u1_struct_0(X3))
      | ~ m1_subset_1(X4,u1_struct_0(X3))
      | ~ m1_subset_1(sK5(X3,k2_tarski(X4,X5),X6),u1_struct_0(X3))
      | ~ l1_orders_2(X3)
      | r1_yellow_0(X3,k2_tarski(X4,X5))
      | ~ r2_lattice3(X3,k2_tarski(X4,X5),X6)
      | ~ m1_subset_1(X6,u1_struct_0(X3))
      | ~ l1_orders_2(X3)
      | ~ v5_orders_2(X3) ) ),
    inference(resolution,[],[f122,f143])).

fof(f122,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_lattice3(X0,k2_tarski(X2,X3),X1)
      | r1_orders_2(X0,X2,X1)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f506,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r1_orders_2(X0,X3,sK5(X0,X2,k13_lattice3(X0,X1,X3)))
      | ~ r1_orders_2(X0,X1,sK5(X0,X2,k13_lattice3(X0,X1,X3)))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | r1_yellow_0(X0,X2)
      | ~ r2_lattice3(X0,X2,k13_lattice3(X0,X1,X3)) ) ),
    inference(subsumption_resolution,[],[f505,f156])).

fof(f505,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r1_orders_2(X0,X1,sK5(X0,X2,k13_lattice3(X0,X1,X3)))
      | ~ r1_orders_2(X0,X3,sK5(X0,X2,k13_lattice3(X0,X1,X3)))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | r1_yellow_0(X0,X2)
      | ~ r2_lattice3(X0,X2,k13_lattice3(X0,X1,X3))
      | ~ m1_subset_1(k13_lattice3(X0,X1,X3),u1_struct_0(X0)) ) ),
    inference(subsumption_resolution,[],[f504,f142])).

fof(f504,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r1_orders_2(X0,X1,sK5(X0,X2,k13_lattice3(X0,X1,X3)))
      | ~ m1_subset_1(sK5(X0,X2,k13_lattice3(X0,X1,X3)),u1_struct_0(X0))
      | ~ r1_orders_2(X0,X3,sK5(X0,X2,k13_lattice3(X0,X1,X3)))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | r1_yellow_0(X0,X2)
      | ~ r2_lattice3(X0,X2,k13_lattice3(X0,X1,X3))
      | ~ m1_subset_1(k13_lattice3(X0,X1,X3),u1_struct_0(X0)) ) ),
    inference(duplicate_literal_removal,[],[f491])).

fof(f491,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r1_orders_2(X0,X1,sK5(X0,X2,k13_lattice3(X0,X1,X3)))
      | ~ m1_subset_1(sK5(X0,X2,k13_lattice3(X0,X1,X3)),u1_struct_0(X0))
      | ~ r1_orders_2(X0,X3,sK5(X0,X2,k13_lattice3(X0,X1,X3)))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | r1_yellow_0(X0,X2)
      | ~ r2_lattice3(X0,X2,k13_lattice3(X0,X1,X3))
      | ~ m1_subset_1(k13_lattice3(X0,X1,X3),u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(resolution,[],[f327,f144])).

fof(f144,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_orders_2(X0,X2,sK5(X0,X1,X2))
      | r1_yellow_0(X0,X1)
      | ~ r2_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f102])).

fof(f327,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_orders_2(X0,k13_lattice3(X0,X3,X1),X2)
      | ~ r1_orders_2(X0,X3,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ r1_orders_2(X0,X1,X2)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(duplicate_literal_removal,[],[f322])).

fof(f322,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r1_orders_2(X0,X1,X2)
      | ~ r1_orders_2(X0,X3,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | r1_orders_2(X0,k13_lattice3(X0,X3,X1),X2)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(resolution,[],[f169,f156])).

fof(f169,plain,(
    ! [X2,X0,X5,X1] :
      ( ~ m1_subset_1(k13_lattice3(X0,X1,X2),u1_struct_0(X0))
      | ~ r1_orders_2(X0,X2,X5)
      | ~ r1_orders_2(X0,X1,X5)
      | ~ m1_subset_1(X5,u1_struct_0(X0))
      | r1_orders_2(X0,k13_lattice3(X0,X1,X2),X5)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(equality_resolution,[],[f134])).

fof(f134,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r1_orders_2(X0,X3,X5)
      | ~ r1_orders_2(X0,X2,X5)
      | ~ r1_orders_2(X0,X1,X5)
      | ~ m1_subset_1(X5,u1_struct_0(X0))
      | k13_lattice3(X0,X1,X2) != X3
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f97])).

fof(f3972,plain,(
    ! [X125,X123,X124] :
      ( r2_lattice3(X123,k2_tarski(X124,X125),k13_lattice3(X123,X124,X125))
      | ~ r1_yellow_0(X123,k2_tarski(X124,X125))
      | ~ l1_orders_2(X123)
      | ~ v5_orders_2(X123)
      | ~ m1_subset_1(X124,u1_struct_0(X123))
      | ~ v1_lattice3(X123)
      | ~ m1_subset_1(X125,u1_struct_0(X123)) ) ),
    inference(duplicate_literal_removal,[],[f3941])).

fof(f3941,plain,(
    ! [X125,X123,X124] :
      ( r2_lattice3(X123,k2_tarski(X124,X125),k13_lattice3(X123,X124,X125))
      | ~ r1_yellow_0(X123,k2_tarski(X124,X125))
      | ~ l1_orders_2(X123)
      | ~ v5_orders_2(X123)
      | ~ m1_subset_1(X124,u1_struct_0(X123))
      | ~ l1_orders_2(X123)
      | ~ v1_lattice3(X123)
      | ~ v5_orders_2(X123)
      | ~ m1_subset_1(X125,u1_struct_0(X123))
      | ~ r1_yellow_0(X123,k2_tarski(X124,X125)) ) ),
    inference(superposition,[],[f140,f1987])).

fof(f1987,plain,(
    ! [X2,X0,X1] :
      ( k13_lattice3(X1,X2,X0) = sK6(X1,k2_tarski(X2,X0))
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l1_orders_2(X1)
      | ~ v1_lattice3(X1)
      | ~ v5_orders_2(X1)
      | ~ m1_subset_1(X0,u1_struct_0(X1))
      | ~ r1_yellow_0(X1,k2_tarski(X2,X0)) ) ),
    inference(subsumption_resolution,[],[f1986,f139])).

fof(f139,plain,(
    ! [X0,X1] :
      ( m1_subset_1(sK6(X0,X1),u1_struct_0(X0))
      | ~ r1_yellow_0(X0,X1)
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f102])).

fof(f1986,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X0,u1_struct_0(X1))
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l1_orders_2(X1)
      | ~ v1_lattice3(X1)
      | ~ v5_orders_2(X1)
      | k13_lattice3(X1,X2,X0) = sK6(X1,k2_tarski(X2,X0))
      | ~ r1_yellow_0(X1,k2_tarski(X2,X0))
      | ~ m1_subset_1(sK6(X1,k2_tarski(X2,X0)),u1_struct_0(X1)) ) ),
    inference(subsumption_resolution,[],[f1985,f265])).

fof(f265,plain,(
    ! [X2,X0,X1] :
      ( r1_orders_2(X0,X1,sK6(X0,k2_tarski(X2,X1)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ r1_yellow_0(X0,k2_tarski(X2,X1))
      | ~ v5_orders_2(X0) ) ),
    inference(subsumption_resolution,[],[f264,f139])).

fof(f264,plain,(
    ! [X2,X0,X1] :
      ( r1_orders_2(X0,X1,sK6(X0,k2_tarski(X2,X1)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(sK6(X0,k2_tarski(X2,X1)),u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ r1_yellow_0(X0,k2_tarski(X2,X1))
      | ~ v5_orders_2(X0) ) ),
    inference(duplicate_literal_removal,[],[f259])).

fof(f259,plain,(
    ! [X2,X0,X1] :
      ( r1_orders_2(X0,X1,sK6(X0,k2_tarski(X2,X1)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(sK6(X0,k2_tarski(X2,X1)),u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ r1_yellow_0(X0,k2_tarski(X2,X1))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(resolution,[],[f123,f140])).

fof(f1985,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X0,u1_struct_0(X1))
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l1_orders_2(X1)
      | ~ v1_lattice3(X1)
      | ~ v5_orders_2(X1)
      | k13_lattice3(X1,X2,X0) = sK6(X1,k2_tarski(X2,X0))
      | ~ r1_yellow_0(X1,k2_tarski(X2,X0))
      | ~ r1_orders_2(X1,X0,sK6(X1,k2_tarski(X2,X0)))
      | ~ m1_subset_1(sK6(X1,k2_tarski(X2,X0)),u1_struct_0(X1)) ) ),
    inference(subsumption_resolution,[],[f1984,f257])).

fof(f257,plain,(
    ! [X2,X0,X1] :
      ( r1_orders_2(X0,X1,sK6(X0,k2_tarski(X1,X2)))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ r1_yellow_0(X0,k2_tarski(X1,X2))
      | ~ v5_orders_2(X0) ) ),
    inference(subsumption_resolution,[],[f256,f139])).

fof(f256,plain,(
    ! [X2,X0,X1] :
      ( r1_orders_2(X0,X1,sK6(X0,k2_tarski(X1,X2)))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(sK6(X0,k2_tarski(X1,X2)),u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ r1_yellow_0(X0,k2_tarski(X1,X2))
      | ~ v5_orders_2(X0) ) ),
    inference(duplicate_literal_removal,[],[f251])).

fof(f251,plain,(
    ! [X2,X0,X1] :
      ( r1_orders_2(X0,X1,sK6(X0,k2_tarski(X1,X2)))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(sK6(X0,k2_tarski(X1,X2)),u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ r1_yellow_0(X0,k2_tarski(X1,X2))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(resolution,[],[f122,f140])).

fof(f1984,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X0,u1_struct_0(X1))
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l1_orders_2(X1)
      | ~ v1_lattice3(X1)
      | ~ v5_orders_2(X1)
      | k13_lattice3(X1,X2,X0) = sK6(X1,k2_tarski(X2,X0))
      | ~ r1_yellow_0(X1,k2_tarski(X2,X0))
      | ~ r1_orders_2(X1,X2,sK6(X1,k2_tarski(X2,X0)))
      | ~ r1_orders_2(X1,X0,sK6(X1,k2_tarski(X2,X0)))
      | ~ m1_subset_1(sK6(X1,k2_tarski(X2,X0)),u1_struct_0(X1)) ) ),
    inference(duplicate_literal_removal,[],[f1971])).

fof(f1971,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X0,u1_struct_0(X1))
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l1_orders_2(X1)
      | ~ v1_lattice3(X1)
      | ~ v5_orders_2(X1)
      | k13_lattice3(X1,X2,X0) = sK6(X1,k2_tarski(X2,X0))
      | ~ r1_yellow_0(X1,k2_tarski(X2,X0))
      | ~ r1_orders_2(X1,X2,sK6(X1,k2_tarski(X2,X0)))
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | k13_lattice3(X1,X2,X0) = sK6(X1,k2_tarski(X2,X0))
      | ~ r1_orders_2(X1,X0,sK6(X1,k2_tarski(X2,X0)))
      | ~ r1_orders_2(X1,X2,sK6(X1,k2_tarski(X2,X0)))
      | ~ m1_subset_1(sK6(X1,k2_tarski(X2,X0)),u1_struct_0(X1))
      | ~ m1_subset_1(X0,u1_struct_0(X1))
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l1_orders_2(X1)
      | ~ v1_lattice3(X1)
      | ~ v5_orders_2(X1) ) ),
    inference(resolution,[],[f988,f136])).

fof(f136,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_orders_2(X0,X1,sK4(X0,X1,X2,X3))
      | k13_lattice3(X0,X1,X2) = X3
      | ~ r1_orders_2(X0,X2,X3)
      | ~ r1_orders_2(X0,X1,X3)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f97])).

fof(f988,plain,(
    ! [X6,X4,X7,X5] :
      ( ~ r1_orders_2(X4,X6,sK4(X4,X5,X7,sK6(X4,k2_tarski(X6,X7))))
      | ~ m1_subset_1(X7,u1_struct_0(X4))
      | ~ m1_subset_1(X5,u1_struct_0(X4))
      | ~ l1_orders_2(X4)
      | ~ v1_lattice3(X4)
      | ~ v5_orders_2(X4)
      | k13_lattice3(X4,X5,X7) = sK6(X4,k2_tarski(X6,X7))
      | ~ r1_yellow_0(X4,k2_tarski(X6,X7))
      | ~ r1_orders_2(X4,X5,sK6(X4,k2_tarski(X6,X7)))
      | ~ m1_subset_1(X6,u1_struct_0(X4)) ) ),
    inference(subsumption_resolution,[],[f987,f139])).

fof(f987,plain,(
    ! [X6,X4,X7,X5] :
      ( ~ r1_orders_2(X4,X5,sK6(X4,k2_tarski(X6,X7)))
      | ~ m1_subset_1(X7,u1_struct_0(X4))
      | ~ m1_subset_1(X5,u1_struct_0(X4))
      | ~ l1_orders_2(X4)
      | ~ v1_lattice3(X4)
      | ~ v5_orders_2(X4)
      | k13_lattice3(X4,X5,X7) = sK6(X4,k2_tarski(X6,X7))
      | ~ r1_yellow_0(X4,k2_tarski(X6,X7))
      | ~ r1_orders_2(X4,X6,sK4(X4,X5,X7,sK6(X4,k2_tarski(X6,X7))))
      | ~ m1_subset_1(X6,u1_struct_0(X4))
      | ~ m1_subset_1(sK6(X4,k2_tarski(X6,X7)),u1_struct_0(X4)) ) ),
    inference(subsumption_resolution,[],[f986,f265])).

fof(f986,plain,(
    ! [X6,X4,X7,X5] :
      ( ~ r1_orders_2(X4,X5,sK6(X4,k2_tarski(X6,X7)))
      | ~ m1_subset_1(X7,u1_struct_0(X4))
      | ~ m1_subset_1(X5,u1_struct_0(X4))
      | ~ l1_orders_2(X4)
      | ~ v1_lattice3(X4)
      | ~ v5_orders_2(X4)
      | k13_lattice3(X4,X5,X7) = sK6(X4,k2_tarski(X6,X7))
      | ~ r1_yellow_0(X4,k2_tarski(X6,X7))
      | ~ r1_orders_2(X4,X7,sK6(X4,k2_tarski(X6,X7)))
      | ~ r1_orders_2(X4,X6,sK4(X4,X5,X7,sK6(X4,k2_tarski(X6,X7))))
      | ~ m1_subset_1(X6,u1_struct_0(X4))
      | ~ m1_subset_1(sK6(X4,k2_tarski(X6,X7)),u1_struct_0(X4)) ) ),
    inference(subsumption_resolution,[],[f982,f135])).

fof(f135,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(sK4(X0,X1,X2,X3),u1_struct_0(X0))
      | k13_lattice3(X0,X1,X2) = X3
      | ~ r1_orders_2(X0,X2,X3)
      | ~ r1_orders_2(X0,X1,X3)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f97])).

fof(f982,plain,(
    ! [X6,X4,X7,X5] :
      ( ~ r1_orders_2(X4,X5,sK6(X4,k2_tarski(X6,X7)))
      | ~ m1_subset_1(X7,u1_struct_0(X4))
      | ~ m1_subset_1(X5,u1_struct_0(X4))
      | ~ l1_orders_2(X4)
      | ~ v1_lattice3(X4)
      | ~ v5_orders_2(X4)
      | k13_lattice3(X4,X5,X7) = sK6(X4,k2_tarski(X6,X7))
      | ~ m1_subset_1(sK4(X4,X5,X7,sK6(X4,k2_tarski(X6,X7))),u1_struct_0(X4))
      | ~ r1_yellow_0(X4,k2_tarski(X6,X7))
      | ~ r1_orders_2(X4,X7,sK6(X4,k2_tarski(X6,X7)))
      | ~ r1_orders_2(X4,X6,sK4(X4,X5,X7,sK6(X4,k2_tarski(X6,X7))))
      | ~ m1_subset_1(X6,u1_struct_0(X4))
      | ~ m1_subset_1(sK6(X4,k2_tarski(X6,X7)),u1_struct_0(X4)) ) ),
    inference(duplicate_literal_removal,[],[f971])).

fof(f971,plain,(
    ! [X6,X4,X7,X5] :
      ( ~ r1_orders_2(X4,X5,sK6(X4,k2_tarski(X6,X7)))
      | ~ m1_subset_1(X7,u1_struct_0(X4))
      | ~ m1_subset_1(X5,u1_struct_0(X4))
      | ~ l1_orders_2(X4)
      | ~ v1_lattice3(X4)
      | ~ v5_orders_2(X4)
      | k13_lattice3(X4,X5,X7) = sK6(X4,k2_tarski(X6,X7))
      | ~ m1_subset_1(sK4(X4,X5,X7,sK6(X4,k2_tarski(X6,X7))),u1_struct_0(X4))
      | ~ r1_yellow_0(X4,k2_tarski(X6,X7))
      | ~ r1_orders_2(X4,X7,sK6(X4,k2_tarski(X6,X7)))
      | ~ r1_orders_2(X4,X6,sK4(X4,X5,X7,sK6(X4,k2_tarski(X6,X7))))
      | ~ m1_subset_1(X7,u1_struct_0(X4))
      | ~ m1_subset_1(X6,u1_struct_0(X4))
      | k13_lattice3(X4,X5,X7) = sK6(X4,k2_tarski(X6,X7))
      | ~ r1_orders_2(X4,X7,sK6(X4,k2_tarski(X6,X7)))
      | ~ r1_orders_2(X4,X5,sK6(X4,k2_tarski(X6,X7)))
      | ~ m1_subset_1(sK6(X4,k2_tarski(X6,X7)),u1_struct_0(X4))
      | ~ m1_subset_1(X7,u1_struct_0(X4))
      | ~ m1_subset_1(X5,u1_struct_0(X4))
      | ~ l1_orders_2(X4)
      | ~ v1_lattice3(X4)
      | ~ v5_orders_2(X4) ) ),
    inference(resolution,[],[f551,f137])).

fof(f137,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_orders_2(X0,X2,sK4(X0,X1,X2,X3))
      | k13_lattice3(X0,X1,X2) = X3
      | ~ r1_orders_2(X0,X2,X3)
      | ~ r1_orders_2(X0,X1,X3)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f97])).

fof(f551,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ r1_orders_2(X0,X3,sK4(X0,X4,X1,sK6(X0,k2_tarski(X2,X3))))
      | ~ r1_orders_2(X0,X4,sK6(X0,k2_tarski(X2,X3)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | k13_lattice3(X0,X4,X1) = sK6(X0,k2_tarski(X2,X3))
      | ~ m1_subset_1(sK4(X0,X4,X1,sK6(X0,k2_tarski(X2,X3))),u1_struct_0(X0))
      | ~ r1_yellow_0(X0,k2_tarski(X2,X3))
      | ~ r1_orders_2(X0,X1,sK6(X0,k2_tarski(X2,X3)))
      | ~ r1_orders_2(X0,X2,sK4(X0,X4,X1,sK6(X0,k2_tarski(X2,X3))))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0)) ) ),
    inference(duplicate_literal_removal,[],[f550])).

fof(f550,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ r1_orders_2(X0,X1,sK6(X0,k2_tarski(X2,X3)))
      | ~ r1_orders_2(X0,X4,sK6(X0,k2_tarski(X2,X3)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | k13_lattice3(X0,X4,X1) = sK6(X0,k2_tarski(X2,X3))
      | ~ m1_subset_1(sK4(X0,X4,X1,sK6(X0,k2_tarski(X2,X3))),u1_struct_0(X0))
      | ~ r1_yellow_0(X0,k2_tarski(X2,X3))
      | ~ r1_orders_2(X0,X3,sK4(X0,X4,X1,sK6(X0,k2_tarski(X2,X3))))
      | ~ r1_orders_2(X0,X2,sK4(X0,X4,X1,sK6(X0,k2_tarski(X2,X3))))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(sK4(X0,X4,X1,sK6(X0,k2_tarski(X2,X3))),u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(resolution,[],[f321,f124])).

fof(f321,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_lattice3(X0,X3,sK4(X0,X1,X2,sK6(X0,X3)))
      | ~ r1_orders_2(X0,X2,sK6(X0,X3))
      | ~ r1_orders_2(X0,X1,sK6(X0,X3))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | k13_lattice3(X0,X1,X2) = sK6(X0,X3)
      | ~ m1_subset_1(sK4(X0,X1,X2,sK6(X0,X3)),u1_struct_0(X0))
      | ~ r1_yellow_0(X0,X3) ) ),
    inference(subsumption_resolution,[],[f320,f139])).

fof(f320,plain,(
    ! [X2,X0,X3,X1] :
      ( k13_lattice3(X0,X1,X2) = sK6(X0,X3)
      | ~ r1_orders_2(X0,X2,sK6(X0,X3))
      | ~ r1_orders_2(X0,X1,sK6(X0,X3))
      | ~ m1_subset_1(sK6(X0,X3),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ r2_lattice3(X0,X3,sK4(X0,X1,X2,sK6(X0,X3)))
      | ~ m1_subset_1(sK4(X0,X1,X2,sK6(X0,X3)),u1_struct_0(X0))
      | ~ r1_yellow_0(X0,X3) ) ),
    inference(duplicate_literal_removal,[],[f315])).

fof(f315,plain,(
    ! [X2,X0,X3,X1] :
      ( k13_lattice3(X0,X1,X2) = sK6(X0,X3)
      | ~ r1_orders_2(X0,X2,sK6(X0,X3))
      | ~ r1_orders_2(X0,X1,sK6(X0,X3))
      | ~ m1_subset_1(sK6(X0,X3),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ r2_lattice3(X0,X3,sK4(X0,X1,X2,sK6(X0,X3)))
      | ~ m1_subset_1(sK4(X0,X1,X2,sK6(X0,X3)),u1_struct_0(X0))
      | ~ r1_yellow_0(X0,X3)
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(resolution,[],[f138,f141])).

fof(f141,plain,(
    ! [X0,X5,X1] :
      ( r1_orders_2(X0,sK6(X0,X1),X5)
      | ~ r2_lattice3(X0,X1,X5)
      | ~ m1_subset_1(X5,u1_struct_0(X0))
      | ~ r1_yellow_0(X0,X1)
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f102])).

fof(f138,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r1_orders_2(X0,X3,sK4(X0,X1,X2,X3))
      | k13_lattice3(X0,X1,X2) = X3
      | ~ r1_orders_2(X0,X2,X3)
      | ~ r1_orders_2(X0,X1,X3)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f97])).

fof(f140,plain,(
    ! [X0,X1] :
      ( r2_lattice3(X0,X1,sK6(X0,X1))
      | ~ r1_yellow_0(X0,X1)
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f102])).

fof(f5392,plain,
    ( ~ r2_lattice3(sK0,k2_tarski(sK1,sK2),k13_lattice3(sK0,sK1,sK2))
    | ~ spl11_7 ),
    inference(subsumption_resolution,[],[f5391,f115])).

fof(f5391,plain,
    ( ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ r2_lattice3(sK0,k2_tarski(sK1,sK2),k13_lattice3(sK0,sK1,sK2))
    | ~ spl11_7 ),
    inference(subsumption_resolution,[],[f5390,f111])).

fof(f5390,plain,
    ( ~ v5_orders_2(sK0)
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ r2_lattice3(sK0,k2_tarski(sK1,sK2),k13_lattice3(sK0,sK1,sK2))
    | ~ spl11_7 ),
    inference(subsumption_resolution,[],[f5389,f112])).

fof(f5389,plain,
    ( ~ v1_lattice3(sK0)
    | ~ v5_orders_2(sK0)
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ r2_lattice3(sK0,k2_tarski(sK1,sK2),k13_lattice3(sK0,sK1,sK2))
    | ~ spl11_7 ),
    inference(subsumption_resolution,[],[f5388,f113])).

fof(f5388,plain,
    ( ~ l1_orders_2(sK0)
    | ~ v1_lattice3(sK0)
    | ~ v5_orders_2(sK0)
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ r2_lattice3(sK0,k2_tarski(sK1,sK2),k13_lattice3(sK0,sK1,sK2))
    | ~ spl11_7 ),
    inference(subsumption_resolution,[],[f5373,f114])).

fof(f5373,plain,
    ( ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | ~ v1_lattice3(sK0)
    | ~ v5_orders_2(sK0)
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ r2_lattice3(sK0,k2_tarski(sK1,sK2),k13_lattice3(sK0,sK1,sK2))
    | ~ spl11_7 ),
    inference(trivial_inequality_removal,[],[f5312])).

fof(f5312,plain,
    ( k13_lattice3(sK0,sK1,sK2) != k13_lattice3(sK0,sK1,sK2)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | ~ v1_lattice3(sK0)
    | ~ v5_orders_2(sK0)
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ r2_lattice3(sK0,k2_tarski(sK1,sK2),k13_lattice3(sK0,sK1,sK2))
    | ~ spl11_7 ),
    inference(superposition,[],[f210,f2032])).

fof(f2032,plain,(
    ! [X10,X11,X9] :
      ( k1_yellow_0(X10,k2_tarski(X11,X9)) = k13_lattice3(X10,X11,X9)
      | ~ m1_subset_1(X11,u1_struct_0(X10))
      | ~ l1_orders_2(X10)
      | ~ v1_lattice3(X10)
      | ~ v5_orders_2(X10)
      | ~ m1_subset_1(X9,u1_struct_0(X10))
      | ~ r2_lattice3(X10,k2_tarski(X11,X9),k13_lattice3(X10,X11,X9)) ) ),
    inference(subsumption_resolution,[],[f2031,f156])).

fof(f2031,plain,(
    ! [X10,X11,X9] :
      ( ~ m1_subset_1(X9,u1_struct_0(X10))
      | ~ m1_subset_1(X11,u1_struct_0(X10))
      | ~ l1_orders_2(X10)
      | ~ v1_lattice3(X10)
      | ~ v5_orders_2(X10)
      | k1_yellow_0(X10,k2_tarski(X11,X9)) = k13_lattice3(X10,X11,X9)
      | ~ r2_lattice3(X10,k2_tarski(X11,X9),k13_lattice3(X10,X11,X9))
      | ~ m1_subset_1(k13_lattice3(X10,X11,X9),u1_struct_0(X10)) ) ),
    inference(subsumption_resolution,[],[f2019,f1720])).

fof(f1720,plain,(
    ! [X4,X5,X3] :
      ( ~ r2_lattice3(X4,k2_tarski(X5,X3),k13_lattice3(X4,X5,X3))
      | ~ m1_subset_1(X5,u1_struct_0(X4))
      | ~ l1_orders_2(X4)
      | ~ v1_lattice3(X4)
      | ~ v5_orders_2(X4)
      | r1_yellow_0(X4,k2_tarski(X5,X3))
      | ~ m1_subset_1(X3,u1_struct_0(X4)) ) ),
    inference(subsumption_resolution,[],[f1718,f156])).

fof(f1718,plain,(
    ! [X4,X5,X3] :
      ( ~ m1_subset_1(X3,u1_struct_0(X4))
      | ~ m1_subset_1(X5,u1_struct_0(X4))
      | ~ l1_orders_2(X4)
      | ~ v1_lattice3(X4)
      | ~ v5_orders_2(X4)
      | r1_yellow_0(X4,k2_tarski(X5,X3))
      | ~ r2_lattice3(X4,k2_tarski(X5,X3),k13_lattice3(X4,X5,X3))
      | ~ m1_subset_1(k13_lattice3(X4,X5,X3),u1_struct_0(X4)) ) ),
    inference(duplicate_literal_removal,[],[f1697])).

fof(f1697,plain,(
    ! [X4,X5,X3] :
      ( ~ m1_subset_1(X3,u1_struct_0(X4))
      | ~ m1_subset_1(X5,u1_struct_0(X4))
      | ~ l1_orders_2(X4)
      | ~ v1_lattice3(X4)
      | ~ v5_orders_2(X4)
      | r1_yellow_0(X4,k2_tarski(X5,X3))
      | ~ r2_lattice3(X4,k2_tarski(X5,X3),k13_lattice3(X4,X5,X3))
      | ~ m1_subset_1(X5,u1_struct_0(X4))
      | ~ m1_subset_1(X3,u1_struct_0(X4))
      | ~ m1_subset_1(X5,u1_struct_0(X4))
      | ~ l1_orders_2(X4)
      | r1_yellow_0(X4,k2_tarski(X5,X3))
      | ~ r2_lattice3(X4,k2_tarski(X5,X3),k13_lattice3(X4,X5,X3))
      | ~ m1_subset_1(k13_lattice3(X4,X5,X3),u1_struct_0(X4))
      | ~ v5_orders_2(X4) ) ),
    inference(resolution,[],[f828,f258])).

fof(f828,plain,(
    ! [X14,X12,X15,X13] :
      ( ~ r1_orders_2(X12,X13,sK5(X12,k2_tarski(X14,X15),k13_lattice3(X12,X13,X15)))
      | ~ m1_subset_1(X15,u1_struct_0(X12))
      | ~ m1_subset_1(X13,u1_struct_0(X12))
      | ~ l1_orders_2(X12)
      | ~ v1_lattice3(X12)
      | ~ v5_orders_2(X12)
      | r1_yellow_0(X12,k2_tarski(X14,X15))
      | ~ r2_lattice3(X12,k2_tarski(X14,X15),k13_lattice3(X12,X13,X15))
      | ~ m1_subset_1(X14,u1_struct_0(X12)) ) ),
    inference(subsumption_resolution,[],[f821,f156])).

fof(f821,plain,(
    ! [X14,X12,X15,X13] :
      ( ~ r1_orders_2(X12,X13,sK5(X12,k2_tarski(X14,X15),k13_lattice3(X12,X13,X15)))
      | ~ m1_subset_1(X15,u1_struct_0(X12))
      | ~ m1_subset_1(X13,u1_struct_0(X12))
      | ~ l1_orders_2(X12)
      | ~ v1_lattice3(X12)
      | ~ v5_orders_2(X12)
      | r1_yellow_0(X12,k2_tarski(X14,X15))
      | ~ r2_lattice3(X12,k2_tarski(X14,X15),k13_lattice3(X12,X13,X15))
      | ~ m1_subset_1(X14,u1_struct_0(X12))
      | ~ m1_subset_1(k13_lattice3(X12,X13,X15),u1_struct_0(X12)) ) ),
    inference(duplicate_literal_removal,[],[f806])).

fof(f806,plain,(
    ! [X14,X12,X15,X13] :
      ( ~ r1_orders_2(X12,X13,sK5(X12,k2_tarski(X14,X15),k13_lattice3(X12,X13,X15)))
      | ~ m1_subset_1(X15,u1_struct_0(X12))
      | ~ m1_subset_1(X13,u1_struct_0(X12))
      | ~ l1_orders_2(X12)
      | ~ v1_lattice3(X12)
      | ~ v5_orders_2(X12)
      | r1_yellow_0(X12,k2_tarski(X14,X15))
      | ~ r2_lattice3(X12,k2_tarski(X14,X15),k13_lattice3(X12,X13,X15))
      | ~ m1_subset_1(X15,u1_struct_0(X12))
      | ~ m1_subset_1(X14,u1_struct_0(X12))
      | ~ l1_orders_2(X12)
      | r1_yellow_0(X12,k2_tarski(X14,X15))
      | ~ r2_lattice3(X12,k2_tarski(X14,X15),k13_lattice3(X12,X13,X15))
      | ~ m1_subset_1(k13_lattice3(X12,X13,X15),u1_struct_0(X12))
      | ~ v5_orders_2(X12) ) ),
    inference(resolution,[],[f506,f266])).

fof(f2019,plain,(
    ! [X10,X11,X9] :
      ( ~ m1_subset_1(X9,u1_struct_0(X10))
      | ~ m1_subset_1(X11,u1_struct_0(X10))
      | ~ l1_orders_2(X10)
      | ~ v1_lattice3(X10)
      | ~ v5_orders_2(X10)
      | k1_yellow_0(X10,k2_tarski(X11,X9)) = k13_lattice3(X10,X11,X9)
      | ~ r2_lattice3(X10,k2_tarski(X11,X9),k13_lattice3(X10,X11,X9))
      | ~ r1_yellow_0(X10,k2_tarski(X11,X9))
      | ~ m1_subset_1(k13_lattice3(X10,X11,X9),u1_struct_0(X10)) ) ),
    inference(duplicate_literal_removal,[],[f2002])).

fof(f2002,plain,(
    ! [X10,X11,X9] :
      ( ~ m1_subset_1(X9,u1_struct_0(X10))
      | ~ m1_subset_1(X11,u1_struct_0(X10))
      | ~ l1_orders_2(X10)
      | ~ v1_lattice3(X10)
      | ~ v5_orders_2(X10)
      | k1_yellow_0(X10,k2_tarski(X11,X9)) = k13_lattice3(X10,X11,X9)
      | ~ r2_lattice3(X10,k2_tarski(X11,X9),k13_lattice3(X10,X11,X9))
      | ~ r1_yellow_0(X10,k2_tarski(X11,X9))
      | ~ m1_subset_1(X11,u1_struct_0(X10))
      | ~ r2_lattice3(X10,k2_tarski(X11,X9),k13_lattice3(X10,X11,X9))
      | ~ r1_yellow_0(X10,k2_tarski(X11,X9))
      | ~ m1_subset_1(k13_lattice3(X10,X11,X9),u1_struct_0(X10))
      | ~ l1_orders_2(X10)
      | k1_yellow_0(X10,k2_tarski(X11,X9)) = k13_lattice3(X10,X11,X9)
      | ~ m1_subset_1(X9,u1_struct_0(X10))
      | ~ m1_subset_1(X11,u1_struct_0(X10)) ) ),
    inference(resolution,[],[f870,f273])).

fof(f273,plain,(
    ! [X6,X4,X7,X5] :
      ( r1_orders_2(X4,X5,sK3(X4,k2_tarski(X5,X6),X7))
      | ~ r2_lattice3(X4,k2_tarski(X5,X6),X7)
      | ~ r1_yellow_0(X4,k2_tarski(X5,X6))
      | ~ m1_subset_1(X7,u1_struct_0(X4))
      | ~ l1_orders_2(X4)
      | k1_yellow_0(X4,k2_tarski(X5,X6)) = X7
      | ~ m1_subset_1(X6,u1_struct_0(X4))
      | ~ m1_subset_1(X5,u1_struct_0(X4)) ) ),
    inference(subsumption_resolution,[],[f270,f127])).

fof(f127,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(sK3(X0,X1,X2),u1_struct_0(X0))
      | k1_yellow_0(X0,X1) = X2
      | ~ r2_lattice3(X0,X1,X2)
      | ~ r1_yellow_0(X0,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f92])).

fof(f92,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( k1_yellow_0(X0,X1) = X2
              | ( ~ r1_orders_2(X0,X2,sK3(X0,X1,X2))
                & r2_lattice3(X0,X1,sK3(X0,X1,X2))
                & m1_subset_1(sK3(X0,X1,X2),u1_struct_0(X0)) )
              | ~ r2_lattice3(X0,X1,X2) )
            & ( ( ! [X4] :
                    ( r1_orders_2(X0,X2,X4)
                    | ~ r2_lattice3(X0,X1,X4)
                    | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                & r2_lattice3(X0,X1,X2) )
              | k1_yellow_0(X0,X1) != X2 ) )
          | ~ r1_yellow_0(X0,X1)
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f90,f91])).

fof(f91,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r1_orders_2(X0,X2,X3)
          & r2_lattice3(X0,X1,X3)
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ~ r1_orders_2(X0,X2,sK3(X0,X1,X2))
        & r2_lattice3(X0,X1,sK3(X0,X1,X2))
        & m1_subset_1(sK3(X0,X1,X2),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f90,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( k1_yellow_0(X0,X1) = X2
              | ? [X3] :
                  ( ~ r1_orders_2(X0,X2,X3)
                  & r2_lattice3(X0,X1,X3)
                  & m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ r2_lattice3(X0,X1,X2) )
            & ( ( ! [X4] :
                    ( r1_orders_2(X0,X2,X4)
                    | ~ r2_lattice3(X0,X1,X4)
                    | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                & r2_lattice3(X0,X1,X2) )
              | k1_yellow_0(X0,X1) != X2 ) )
          | ~ r1_yellow_0(X0,X1)
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(rectify,[],[f89])).

fof(f89,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( k1_yellow_0(X0,X1) = X2
              | ? [X3] :
                  ( ~ r1_orders_2(X0,X2,X3)
                  & r2_lattice3(X0,X1,X3)
                  & m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ r2_lattice3(X0,X1,X2) )
            & ( ( ! [X3] :
                    ( r1_orders_2(X0,X2,X3)
                    | ~ r2_lattice3(X0,X1,X3)
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                & r2_lattice3(X0,X1,X2) )
              | k1_yellow_0(X0,X1) != X2 ) )
          | ~ r1_yellow_0(X0,X1)
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f88])).

fof(f88,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( k1_yellow_0(X0,X1) = X2
              | ? [X3] :
                  ( ~ r1_orders_2(X0,X2,X3)
                  & r2_lattice3(X0,X1,X3)
                  & m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ r2_lattice3(X0,X1,X2) )
            & ( ( ! [X3] :
                    ( r1_orders_2(X0,X2,X3)
                    | ~ r2_lattice3(X0,X1,X3)
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                & r2_lattice3(X0,X1,X2) )
              | k1_yellow_0(X0,X1) != X2 ) )
          | ~ r1_yellow_0(X0,X1)
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(nnf_transformation,[],[f52])).

fof(f52,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k1_yellow_0(X0,X1) = X2
          <=> ( ! [X3] :
                  ( r1_orders_2(X0,X2,X3)
                  | ~ r2_lattice3(X0,X1,X3)
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              & r2_lattice3(X0,X1,X2) ) )
          | ~ r1_yellow_0(X0,X1)
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f51])).

fof(f51,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k1_yellow_0(X0,X1) = X2
          <=> ( ! [X3] :
                  ( r1_orders_2(X0,X2,X3)
                  | ~ r2_lattice3(X0,X1,X3)
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              & r2_lattice3(X0,X1,X2) ) )
          | ~ r1_yellow_0(X0,X1)
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1,X2] :
          ( m1_subset_1(X2,u1_struct_0(X0))
         => ( r1_yellow_0(X0,X1)
           => ( k1_yellow_0(X0,X1) = X2
            <=> ( ! [X3] :
                    ( m1_subset_1(X3,u1_struct_0(X0))
                   => ( r2_lattice3(X0,X1,X3)
                     => r1_orders_2(X0,X2,X3) ) )
                & r2_lattice3(X0,X1,X2) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/yellow_0__t41_yellow_0.p',d9_yellow_0)).

fof(f270,plain,(
    ! [X6,X4,X7,X5] :
      ( k1_yellow_0(X4,k2_tarski(X5,X6)) = X7
      | ~ r2_lattice3(X4,k2_tarski(X5,X6),X7)
      | ~ r1_yellow_0(X4,k2_tarski(X5,X6))
      | ~ m1_subset_1(X7,u1_struct_0(X4))
      | ~ l1_orders_2(X4)
      | r1_orders_2(X4,X5,sK3(X4,k2_tarski(X5,X6),X7))
      | ~ m1_subset_1(X6,u1_struct_0(X4))
      | ~ m1_subset_1(X5,u1_struct_0(X4))
      | ~ m1_subset_1(sK3(X4,k2_tarski(X5,X6),X7),u1_struct_0(X4)) ) ),
    inference(duplicate_literal_removal,[],[f269])).

fof(f269,plain,(
    ! [X6,X4,X7,X5] :
      ( k1_yellow_0(X4,k2_tarski(X5,X6)) = X7
      | ~ r2_lattice3(X4,k2_tarski(X5,X6),X7)
      | ~ r1_yellow_0(X4,k2_tarski(X5,X6))
      | ~ m1_subset_1(X7,u1_struct_0(X4))
      | ~ l1_orders_2(X4)
      | r1_orders_2(X4,X5,sK3(X4,k2_tarski(X5,X6),X7))
      | ~ m1_subset_1(X6,u1_struct_0(X4))
      | ~ m1_subset_1(X5,u1_struct_0(X4))
      | ~ m1_subset_1(sK3(X4,k2_tarski(X5,X6),X7),u1_struct_0(X4))
      | ~ l1_orders_2(X4) ) ),
    inference(resolution,[],[f128,f122])).

fof(f128,plain,(
    ! [X2,X0,X1] :
      ( r2_lattice3(X0,X1,sK3(X0,X1,X2))
      | k1_yellow_0(X0,X1) = X2
      | ~ r2_lattice3(X0,X1,X2)
      | ~ r1_yellow_0(X0,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f92])).

fof(f870,plain,(
    ! [X6,X4,X7,X5] :
      ( ~ r1_orders_2(X4,X5,sK3(X4,k2_tarski(X6,X7),k13_lattice3(X4,X5,X7)))
      | ~ m1_subset_1(X7,u1_struct_0(X4))
      | ~ m1_subset_1(X5,u1_struct_0(X4))
      | ~ l1_orders_2(X4)
      | ~ v1_lattice3(X4)
      | ~ v5_orders_2(X4)
      | k1_yellow_0(X4,k2_tarski(X6,X7)) = k13_lattice3(X4,X5,X7)
      | ~ r2_lattice3(X4,k2_tarski(X6,X7),k13_lattice3(X4,X5,X7))
      | ~ r1_yellow_0(X4,k2_tarski(X6,X7))
      | ~ m1_subset_1(X6,u1_struct_0(X4)) ) ),
    inference(subsumption_resolution,[],[f867,f156])).

fof(f867,plain,(
    ! [X6,X4,X7,X5] :
      ( ~ r1_orders_2(X4,X5,sK3(X4,k2_tarski(X6,X7),k13_lattice3(X4,X5,X7)))
      | ~ m1_subset_1(X7,u1_struct_0(X4))
      | ~ m1_subset_1(X5,u1_struct_0(X4))
      | ~ l1_orders_2(X4)
      | ~ v1_lattice3(X4)
      | ~ v5_orders_2(X4)
      | k1_yellow_0(X4,k2_tarski(X6,X7)) = k13_lattice3(X4,X5,X7)
      | ~ r2_lattice3(X4,k2_tarski(X6,X7),k13_lattice3(X4,X5,X7))
      | ~ r1_yellow_0(X4,k2_tarski(X6,X7))
      | ~ m1_subset_1(k13_lattice3(X4,X5,X7),u1_struct_0(X4))
      | ~ m1_subset_1(X6,u1_struct_0(X4)) ) ),
    inference(duplicate_literal_removal,[],[f848])).

fof(f848,plain,(
    ! [X6,X4,X7,X5] :
      ( ~ r1_orders_2(X4,X5,sK3(X4,k2_tarski(X6,X7),k13_lattice3(X4,X5,X7)))
      | ~ m1_subset_1(X7,u1_struct_0(X4))
      | ~ m1_subset_1(X5,u1_struct_0(X4))
      | ~ l1_orders_2(X4)
      | ~ v1_lattice3(X4)
      | ~ v5_orders_2(X4)
      | k1_yellow_0(X4,k2_tarski(X6,X7)) = k13_lattice3(X4,X5,X7)
      | ~ r2_lattice3(X4,k2_tarski(X6,X7),k13_lattice3(X4,X5,X7))
      | ~ r1_yellow_0(X4,k2_tarski(X6,X7))
      | ~ r2_lattice3(X4,k2_tarski(X6,X7),k13_lattice3(X4,X5,X7))
      | ~ r1_yellow_0(X4,k2_tarski(X6,X7))
      | ~ m1_subset_1(k13_lattice3(X4,X5,X7),u1_struct_0(X4))
      | ~ l1_orders_2(X4)
      | k1_yellow_0(X4,k2_tarski(X6,X7)) = k13_lattice3(X4,X5,X7)
      | ~ m1_subset_1(X7,u1_struct_0(X4))
      | ~ m1_subset_1(X6,u1_struct_0(X4)) ) ),
    inference(resolution,[],[f508,f272])).

fof(f272,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_orders_2(X0,X2,sK3(X0,k2_tarski(X1,X2),X3))
      | ~ r2_lattice3(X0,k2_tarski(X1,X2),X3)
      | ~ r1_yellow_0(X0,k2_tarski(X1,X2))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | k1_yellow_0(X0,k2_tarski(X1,X2)) = X3
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0)) ) ),
    inference(subsumption_resolution,[],[f271,f127])).

fof(f271,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_yellow_0(X0,k2_tarski(X1,X2)) = X3
      | ~ r2_lattice3(X0,k2_tarski(X1,X2),X3)
      | ~ r1_yellow_0(X0,k2_tarski(X1,X2))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | r1_orders_2(X0,X2,sK3(X0,k2_tarski(X1,X2),X3))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(sK3(X0,k2_tarski(X1,X2),X3),u1_struct_0(X0)) ) ),
    inference(duplicate_literal_removal,[],[f268])).

fof(f268,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_yellow_0(X0,k2_tarski(X1,X2)) = X3
      | ~ r2_lattice3(X0,k2_tarski(X1,X2),X3)
      | ~ r1_yellow_0(X0,k2_tarski(X1,X2))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | r1_orders_2(X0,X2,sK3(X0,k2_tarski(X1,X2),X3))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(sK3(X0,k2_tarski(X1,X2),X3),u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(resolution,[],[f128,f123])).

fof(f508,plain,(
    ! [X6,X4,X7,X5] :
      ( ~ r1_orders_2(X4,X7,sK3(X4,X6,k13_lattice3(X4,X5,X7)))
      | ~ r1_orders_2(X4,X5,sK3(X4,X6,k13_lattice3(X4,X5,X7)))
      | ~ m1_subset_1(X7,u1_struct_0(X4))
      | ~ m1_subset_1(X5,u1_struct_0(X4))
      | ~ l1_orders_2(X4)
      | ~ v1_lattice3(X4)
      | ~ v5_orders_2(X4)
      | k1_yellow_0(X4,X6) = k13_lattice3(X4,X5,X7)
      | ~ r2_lattice3(X4,X6,k13_lattice3(X4,X5,X7))
      | ~ r1_yellow_0(X4,X6) ) ),
    inference(subsumption_resolution,[],[f507,f156])).

fof(f507,plain,(
    ! [X6,X4,X7,X5] :
      ( ~ r1_orders_2(X4,X5,sK3(X4,X6,k13_lattice3(X4,X5,X7)))
      | ~ r1_orders_2(X4,X7,sK3(X4,X6,k13_lattice3(X4,X5,X7)))
      | ~ m1_subset_1(X7,u1_struct_0(X4))
      | ~ m1_subset_1(X5,u1_struct_0(X4))
      | ~ l1_orders_2(X4)
      | ~ v1_lattice3(X4)
      | ~ v5_orders_2(X4)
      | k1_yellow_0(X4,X6) = k13_lattice3(X4,X5,X7)
      | ~ r2_lattice3(X4,X6,k13_lattice3(X4,X5,X7))
      | ~ r1_yellow_0(X4,X6)
      | ~ m1_subset_1(k13_lattice3(X4,X5,X7),u1_struct_0(X4)) ) ),
    inference(subsumption_resolution,[],[f503,f127])).

fof(f503,plain,(
    ! [X6,X4,X7,X5] :
      ( ~ r1_orders_2(X4,X5,sK3(X4,X6,k13_lattice3(X4,X5,X7)))
      | ~ m1_subset_1(sK3(X4,X6,k13_lattice3(X4,X5,X7)),u1_struct_0(X4))
      | ~ r1_orders_2(X4,X7,sK3(X4,X6,k13_lattice3(X4,X5,X7)))
      | ~ m1_subset_1(X7,u1_struct_0(X4))
      | ~ m1_subset_1(X5,u1_struct_0(X4))
      | ~ l1_orders_2(X4)
      | ~ v1_lattice3(X4)
      | ~ v5_orders_2(X4)
      | k1_yellow_0(X4,X6) = k13_lattice3(X4,X5,X7)
      | ~ r2_lattice3(X4,X6,k13_lattice3(X4,X5,X7))
      | ~ r1_yellow_0(X4,X6)
      | ~ m1_subset_1(k13_lattice3(X4,X5,X7),u1_struct_0(X4)) ) ),
    inference(duplicate_literal_removal,[],[f492])).

fof(f492,plain,(
    ! [X6,X4,X7,X5] :
      ( ~ r1_orders_2(X4,X5,sK3(X4,X6,k13_lattice3(X4,X5,X7)))
      | ~ m1_subset_1(sK3(X4,X6,k13_lattice3(X4,X5,X7)),u1_struct_0(X4))
      | ~ r1_orders_2(X4,X7,sK3(X4,X6,k13_lattice3(X4,X5,X7)))
      | ~ m1_subset_1(X7,u1_struct_0(X4))
      | ~ m1_subset_1(X5,u1_struct_0(X4))
      | ~ l1_orders_2(X4)
      | ~ v1_lattice3(X4)
      | ~ v5_orders_2(X4)
      | k1_yellow_0(X4,X6) = k13_lattice3(X4,X5,X7)
      | ~ r2_lattice3(X4,X6,k13_lattice3(X4,X5,X7))
      | ~ r1_yellow_0(X4,X6)
      | ~ m1_subset_1(k13_lattice3(X4,X5,X7),u1_struct_0(X4))
      | ~ l1_orders_2(X4) ) ),
    inference(resolution,[],[f327,f129])).

fof(f129,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_orders_2(X0,X2,sK3(X0,X1,X2))
      | k1_yellow_0(X0,X1) = X2
      | ~ r2_lattice3(X0,X1,X2)
      | ~ r1_yellow_0(X0,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f92])).

fof(f210,plain,
    ( k1_yellow_0(sK0,k2_tarski(sK1,sK2)) != k13_lattice3(sK0,sK1,sK2)
    | ~ spl11_7 ),
    inference(avatar_component_clause,[],[f209])).

fof(f209,plain,
    ( spl11_7
  <=> k1_yellow_0(sK0,k2_tarski(sK1,sK2)) != k13_lattice3(sK0,sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_7])])).

fof(f211,plain,
    ( spl11_2
    | ~ spl11_7 ),
    inference(avatar_split_clause,[],[f207,f209,f184])).

fof(f184,plain,
    ( spl11_2
  <=> v1_xboole_0(u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_2])])).

fof(f207,plain,
    ( k1_yellow_0(sK0,k2_tarski(sK1,sK2)) != k13_lattice3(sK0,sK1,sK2)
    | v1_xboole_0(u1_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f206,f114])).

fof(f206,plain,
    ( k1_yellow_0(sK0,k2_tarski(sK1,sK2)) != k13_lattice3(sK0,sK1,sK2)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | v1_xboole_0(u1_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f203,f115])).

fof(f203,plain,
    ( k1_yellow_0(sK0,k2_tarski(sK1,sK2)) != k13_lattice3(sK0,sK1,sK2)
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | v1_xboole_0(u1_struct_0(sK0)) ),
    inference(superposition,[],[f116,f154])).

fof(f154,plain,(
    ! [X2,X0,X1] :
      ( k7_domain_1(X0,X1,X2) = k2_tarski(X1,X2)
      | ~ m1_subset_1(X2,X0)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f70])).

fof(f70,plain,(
    ! [X0,X1,X2] :
      ( k7_domain_1(X0,X1,X2) = k2_tarski(X1,X2)
      | ~ m1_subset_1(X2,X0)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f69])).

fof(f69,plain,(
    ! [X0,X1,X2] :
      ( k7_domain_1(X0,X1,X2) = k2_tarski(X1,X2)
      | ~ m1_subset_1(X2,X0)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f23,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,X0)
        & m1_subset_1(X1,X0)
        & ~ v1_xboole_0(X0) )
     => k7_domain_1(X0,X1,X2) = k2_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/yellow_0__t41_yellow_0.p',redefinition_k7_domain_1)).

fof(f116,plain,(
    k1_yellow_0(sK0,k7_domain_1(u1_struct_0(sK0),sK1,sK2)) != k13_lattice3(sK0,sK1,sK2) ),
    inference(cnf_transformation,[],[f87])).

fof(f199,plain,(
    ~ spl11_2 ),
    inference(avatar_contradiction_clause,[],[f198])).

fof(f198,plain,
    ( $false
    | ~ spl11_2 ),
    inference(subsumption_resolution,[],[f197,f113])).

fof(f197,plain,
    ( ~ l1_orders_2(sK0)
    | ~ spl11_2 ),
    inference(subsumption_resolution,[],[f196,f112])).

fof(f196,plain,
    ( ~ v1_lattice3(sK0)
    | ~ l1_orders_2(sK0)
    | ~ spl11_2 ),
    inference(resolution,[],[f194,f118])).

fof(f118,plain,(
    ! [X0] :
      ( ~ v2_struct_0(X0)
      | ~ v1_lattice3(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f48,plain,(
    ! [X0] :
      ( ~ v2_struct_0(X0)
      | ~ v1_lattice3(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f47])).

fof(f47,plain,(
    ! [X0] :
      ( ~ v2_struct_0(X0)
      | ~ v1_lattice3(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f35])).

fof(f35,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ( v1_lattice3(X0)
       => ~ v2_struct_0(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/yellow_0__t41_yellow_0.p',cc1_lattice3)).

fof(f194,plain,
    ( v2_struct_0(sK0)
    | ~ spl11_2 ),
    inference(subsumption_resolution,[],[f193,f172])).

fof(f172,plain,(
    l1_struct_0(sK0) ),
    inference(resolution,[],[f117,f113])).

fof(f117,plain,(
    ! [X0] :
      ( ~ l1_orders_2(X0)
      | l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/yellow_0__t41_yellow_0.p',dt_l1_orders_2)).

fof(f193,plain,
    ( ~ l1_struct_0(sK0)
    | v2_struct_0(sK0)
    | ~ spl11_2 ),
    inference(resolution,[],[f185,f131])).

fof(f131,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f55,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f54])).

fof(f54,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f36])).

fof(f36,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/yellow_0__t41_yellow_0.p',fc2_struct_0)).

fof(f185,plain,
    ( v1_xboole_0(u1_struct_0(sK0))
    | ~ spl11_2 ),
    inference(avatar_component_clause,[],[f184])).
%------------------------------------------------------------------------------
