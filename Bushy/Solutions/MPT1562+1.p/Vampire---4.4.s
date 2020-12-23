%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : yellow_0__t40_yellow_0.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:41:42 EDT 2019

% Result     : Theorem 1.20s
% Output     : Refutation 1.20s
% Verified   : 
% Statistics : Number of formulae       :  180 ( 639 expanded)
%              Number of leaves         :   24 ( 191 expanded)
%              Depth                    :   35
%              Number of atoms          : 1184 (4917 expanded)
%              Number of equality atoms :   69 ( 509 expanded)
%              Maximal formula depth    :   21 (   9 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f10048,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f196,f208,f9752,f9774,f9797,f10040])).

fof(f10040,plain,
    ( ~ spl11_129
    | ~ spl11_131
    | ~ spl11_133
    | ~ spl11_0 ),
    inference(avatar_split_clause,[],[f10039,f191,f9730,f9727,f9724])).

fof(f9724,plain,
    ( spl11_129
  <=> ~ m1_subset_1(k12_lattice3(sK0,sK1,sK2),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_129])])).

fof(f9727,plain,
    ( spl11_131
  <=> ~ r1_orders_2(sK0,k12_lattice3(sK0,sK1,sK2),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_131])])).

fof(f9730,plain,
    ( spl11_133
  <=> ~ r1_orders_2(sK0,k12_lattice3(sK0,sK1,sK2),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_133])])).

fof(f191,plain,
    ( spl11_0
  <=> r2_hidden(sK1,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_0])])).

fof(f10039,plain,
    ( ~ r1_orders_2(sK0,k12_lattice3(sK0,sK1,sK2),sK2)
    | ~ r1_orders_2(sK0,k12_lattice3(sK0,sK1,sK2),sK1)
    | ~ m1_subset_1(k12_lattice3(sK0,sK1,sK2),u1_struct_0(sK0))
    | ~ spl11_0 ),
    inference(subsumption_resolution,[],[f10038,f119])).

fof(f119,plain,(
    l1_orders_2(sK0) ),
    inference(cnf_transformation,[],[f91])).

fof(f91,plain,
    ( k2_yellow_0(sK0,k7_domain_1(u1_struct_0(sK0),sK1,sK2)) != k12_lattice3(sK0,sK1,sK2)
    & m1_subset_1(sK2,u1_struct_0(sK0))
    & m1_subset_1(sK1,u1_struct_0(sK0))
    & l1_orders_2(sK0)
    & v2_lattice3(sK0)
    & v5_orders_2(sK0)
    & v3_orders_2(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f45,f90,f89,f88])).

fof(f88,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( k2_yellow_0(X0,k7_domain_1(u1_struct_0(X0),X1,X2)) != k12_lattice3(X0,X1,X2)
                & m1_subset_1(X2,u1_struct_0(X0)) )
            & m1_subset_1(X1,u1_struct_0(X0)) )
        & l1_orders_2(X0)
        & v2_lattice3(X0)
        & v5_orders_2(X0)
        & v3_orders_2(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( k2_yellow_0(sK0,k7_domain_1(u1_struct_0(sK0),X1,X2)) != k12_lattice3(sK0,X1,X2)
              & m1_subset_1(X2,u1_struct_0(sK0)) )
          & m1_subset_1(X1,u1_struct_0(sK0)) )
      & l1_orders_2(sK0)
      & v2_lattice3(sK0)
      & v5_orders_2(sK0)
      & v3_orders_2(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f89,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( k2_yellow_0(X0,k7_domain_1(u1_struct_0(X0),X1,X2)) != k12_lattice3(X0,X1,X2)
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
     => ( ? [X2] :
            ( k2_yellow_0(X0,k7_domain_1(u1_struct_0(X0),sK1,X2)) != k12_lattice3(X0,sK1,X2)
            & m1_subset_1(X2,u1_struct_0(X0)) )
        & m1_subset_1(sK1,u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f90,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( k2_yellow_0(X0,k7_domain_1(u1_struct_0(X0),X1,X2)) != k12_lattice3(X0,X1,X2)
          & m1_subset_1(X2,u1_struct_0(X0)) )
     => ( k2_yellow_0(X0,k7_domain_1(u1_struct_0(X0),X1,sK2)) != k12_lattice3(X0,X1,sK2)
        & m1_subset_1(sK2,u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f45,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( k2_yellow_0(X0,k7_domain_1(u1_struct_0(X0),X1,X2)) != k12_lattice3(X0,X1,X2)
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_orders_2(X0)
      & v2_lattice3(X0)
      & v5_orders_2(X0)
      & v3_orders_2(X0) ) ),
    inference(flattening,[],[f44])).

fof(f44,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( k2_yellow_0(X0,k7_domain_1(u1_struct_0(X0),X1,X2)) != k12_lattice3(X0,X1,X2)
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_orders_2(X0)
      & v2_lattice3(X0)
      & v5_orders_2(X0)
      & v3_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f42])).

fof(f42,plain,(
    ~ ! [X0] :
        ( ( l1_orders_2(X0)
          & v2_lattice3(X0)
          & v5_orders_2(X0)
          & v3_orders_2(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => k2_yellow_0(X0,k7_domain_1(u1_struct_0(X0),X1,X2)) = k12_lattice3(X0,X1,X2) ) ) ) ),
    inference(pure_predicate_removal,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_orders_2(X0)
          & v2_lattice3(X0)
          & v5_orders_2(X0)
          & v4_orders_2(X0)
          & v3_orders_2(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => k2_yellow_0(X0,k7_domain_1(u1_struct_0(X0),X1,X2)) = k12_lattice3(X0,X1,X2) ) ) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v2_lattice3(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => k2_yellow_0(X0,k7_domain_1(u1_struct_0(X0),X1,X2)) = k12_lattice3(X0,X1,X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/yellow_0__t40_yellow_0.p',t40_yellow_0)).

fof(f10038,plain,
    ( ~ r1_orders_2(sK0,k12_lattice3(sK0,sK1,sK2),sK2)
    | ~ r1_orders_2(sK0,k12_lattice3(sK0,sK1,sK2),sK1)
    | ~ m1_subset_1(k12_lattice3(sK0,sK1,sK2),u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | ~ spl11_0 ),
    inference(subsumption_resolution,[],[f10037,f120])).

fof(f120,plain,(
    m1_subset_1(sK1,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f91])).

fof(f10037,plain,
    ( ~ r1_orders_2(sK0,k12_lattice3(sK0,sK1,sK2),sK2)
    | ~ r1_orders_2(sK0,k12_lattice3(sK0,sK1,sK2),sK1)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ m1_subset_1(k12_lattice3(sK0,sK1,sK2),u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | ~ spl11_0 ),
    inference(subsumption_resolution,[],[f10032,f121])).

fof(f121,plain,(
    m1_subset_1(sK2,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f91])).

fof(f10032,plain,
    ( ~ r1_orders_2(sK0,k12_lattice3(sK0,sK1,sK2),sK2)
    | ~ r1_orders_2(sK0,k12_lattice3(sK0,sK1,sK2),sK1)
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ m1_subset_1(k12_lattice3(sK0,sK1,sK2),u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | ~ spl11_0 ),
    inference(resolution,[],[f9990,f127])).

fof(f127,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_lattice3(X0,k2_tarski(X2,X3),X1)
      | ~ r1_orders_2(X0,X1,X3)
      | ~ r1_orders_2(X0,X1,X2)
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
    inference(ennf_transformation,[],[f36])).

fof(f36,axiom,(
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
    file('/export/starexec/sandbox/benchmark/yellow_0__t40_yellow_0.p',t8_yellow_0)).

fof(f9990,plain,
    ( ~ r1_lattice3(sK0,k2_tarski(sK1,sK2),k12_lattice3(sK0,sK1,sK2))
    | ~ spl11_0 ),
    inference(subsumption_resolution,[],[f9989,f121])).

fof(f9989,plain,
    ( ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ r1_lattice3(sK0,k2_tarski(sK1,sK2),k12_lattice3(sK0,sK1,sK2))
    | ~ spl11_0 ),
    inference(subsumption_resolution,[],[f9988,f117])).

fof(f117,plain,(
    v5_orders_2(sK0) ),
    inference(cnf_transformation,[],[f91])).

fof(f9988,plain,
    ( ~ v5_orders_2(sK0)
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ r1_lattice3(sK0,k2_tarski(sK1,sK2),k12_lattice3(sK0,sK1,sK2))
    | ~ spl11_0 ),
    inference(subsumption_resolution,[],[f9987,f118])).

fof(f118,plain,(
    v2_lattice3(sK0) ),
    inference(cnf_transformation,[],[f91])).

fof(f9987,plain,
    ( ~ v2_lattice3(sK0)
    | ~ v5_orders_2(sK0)
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ r1_lattice3(sK0,k2_tarski(sK1,sK2),k12_lattice3(sK0,sK1,sK2))
    | ~ spl11_0 ),
    inference(subsumption_resolution,[],[f9986,f119])).

fof(f9986,plain,
    ( ~ l1_orders_2(sK0)
    | ~ v2_lattice3(sK0)
    | ~ v5_orders_2(sK0)
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ r1_lattice3(sK0,k2_tarski(sK1,sK2),k12_lattice3(sK0,sK1,sK2))
    | ~ spl11_0 ),
    inference(subsumption_resolution,[],[f9967,f120])).

fof(f9967,plain,
    ( ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | ~ v2_lattice3(sK0)
    | ~ v5_orders_2(sK0)
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ r1_lattice3(sK0,k2_tarski(sK1,sK2),k12_lattice3(sK0,sK1,sK2))
    | ~ spl11_0 ),
    inference(trivial_inequality_removal,[],[f9846])).

fof(f9846,plain,
    ( k12_lattice3(sK0,sK1,sK2) != k12_lattice3(sK0,sK1,sK2)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | ~ v2_lattice3(sK0)
    | ~ v5_orders_2(sK0)
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ r1_lattice3(sK0,k2_tarski(sK1,sK2),k12_lattice3(sK0,sK1,sK2))
    | ~ spl11_0 ),
    inference(superposition,[],[f221,f3678])).

fof(f3678,plain,(
    ! [X10,X11,X9] :
      ( k2_yellow_0(X10,k2_tarski(X11,X9)) = k12_lattice3(X10,X11,X9)
      | ~ m1_subset_1(X11,u1_struct_0(X10))
      | ~ l1_orders_2(X10)
      | ~ v2_lattice3(X10)
      | ~ v5_orders_2(X10)
      | ~ m1_subset_1(X9,u1_struct_0(X10))
      | ~ r1_lattice3(X10,k2_tarski(X11,X9),k12_lattice3(X10,X11,X9)) ) ),
    inference(subsumption_resolution,[],[f3677,f165])).

fof(f165,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k12_lattice3(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f78])).

fof(f78,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k12_lattice3(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(flattening,[],[f77])).

fof(f77,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k12_lattice3(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l1_orders_2(X0)
        & v2_lattice3(X0)
        & v5_orders_2(X0) )
     => m1_subset_1(k12_lattice3(X0,X1,X2),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/yellow_0__t40_yellow_0.p',dt_k12_lattice3)).

fof(f3677,plain,(
    ! [X10,X11,X9] :
      ( ~ m1_subset_1(X9,u1_struct_0(X10))
      | ~ m1_subset_1(X11,u1_struct_0(X10))
      | ~ l1_orders_2(X10)
      | ~ v2_lattice3(X10)
      | ~ v5_orders_2(X10)
      | k2_yellow_0(X10,k2_tarski(X11,X9)) = k12_lattice3(X10,X11,X9)
      | ~ r1_lattice3(X10,k2_tarski(X11,X9),k12_lattice3(X10,X11,X9))
      | ~ m1_subset_1(k12_lattice3(X10,X11,X9),u1_struct_0(X10)) ) ),
    inference(subsumption_resolution,[],[f3665,f3106])).

fof(f3106,plain,(
    ! [X4,X5,X3] :
      ( ~ r1_lattice3(X4,k2_tarski(X5,X3),k12_lattice3(X4,X5,X3))
      | ~ m1_subset_1(X5,u1_struct_0(X4))
      | ~ l1_orders_2(X4)
      | ~ v2_lattice3(X4)
      | ~ v5_orders_2(X4)
      | r2_yellow_0(X4,k2_tarski(X5,X3))
      | ~ m1_subset_1(X3,u1_struct_0(X4)) ) ),
    inference(subsumption_resolution,[],[f3104,f165])).

fof(f3104,plain,(
    ! [X4,X5,X3] :
      ( ~ m1_subset_1(X3,u1_struct_0(X4))
      | ~ m1_subset_1(X5,u1_struct_0(X4))
      | ~ l1_orders_2(X4)
      | ~ v2_lattice3(X4)
      | ~ v5_orders_2(X4)
      | r2_yellow_0(X4,k2_tarski(X5,X3))
      | ~ r1_lattice3(X4,k2_tarski(X5,X3),k12_lattice3(X4,X5,X3))
      | ~ m1_subset_1(k12_lattice3(X4,X5,X3),u1_struct_0(X4)) ) ),
    inference(duplicate_literal_removal,[],[f3083])).

fof(f3083,plain,(
    ! [X4,X5,X3] :
      ( ~ m1_subset_1(X3,u1_struct_0(X4))
      | ~ m1_subset_1(X5,u1_struct_0(X4))
      | ~ l1_orders_2(X4)
      | ~ v2_lattice3(X4)
      | ~ v5_orders_2(X4)
      | r2_yellow_0(X4,k2_tarski(X5,X3))
      | ~ r1_lattice3(X4,k2_tarski(X5,X3),k12_lattice3(X4,X5,X3))
      | ~ m1_subset_1(X5,u1_struct_0(X4))
      | ~ m1_subset_1(X3,u1_struct_0(X4))
      | ~ m1_subset_1(X5,u1_struct_0(X4))
      | ~ l1_orders_2(X4)
      | r2_yellow_0(X4,k2_tarski(X5,X3))
      | ~ r1_lattice3(X4,k2_tarski(X5,X3),k12_lattice3(X4,X5,X3))
      | ~ m1_subset_1(k12_lattice3(X4,X5,X3),u1_struct_0(X4))
      | ~ v5_orders_2(X4) ) ),
    inference(resolution,[],[f1372,f316])).

fof(f316,plain,(
    ! [X6,X4,X5,X3] :
      ( r1_orders_2(X3,sK5(X3,k2_tarski(X4,X5),X6),X4)
      | ~ m1_subset_1(X5,u1_struct_0(X3))
      | ~ m1_subset_1(X4,u1_struct_0(X3))
      | ~ l1_orders_2(X3)
      | r2_yellow_0(X3,k2_tarski(X4,X5))
      | ~ r1_lattice3(X3,k2_tarski(X4,X5),X6)
      | ~ m1_subset_1(X6,u1_struct_0(X3))
      | ~ v5_orders_2(X3) ) ),
    inference(subsumption_resolution,[],[f313,f148])).

fof(f148,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(sK5(X0,X1,X2),u1_struct_0(X0))
      | r2_yellow_0(X0,X1)
      | ~ r1_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f106])).

fof(f106,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r2_yellow_0(X0,X1)
            | ! [X2] :
                ( ( ~ r1_orders_2(X0,sK5(X0,X1,X2),X2)
                  & r1_lattice3(X0,X1,sK5(X0,X1,X2))
                  & m1_subset_1(sK5(X0,X1,X2),u1_struct_0(X0)) )
                | ~ r1_lattice3(X0,X1,X2)
                | ~ m1_subset_1(X2,u1_struct_0(X0)) ) )
          & ( ( ! [X5] :
                  ( r1_orders_2(X0,X5,sK6(X0,X1))
                  | ~ r1_lattice3(X0,X1,X5)
                  | ~ m1_subset_1(X5,u1_struct_0(X0)) )
              & r1_lattice3(X0,X1,sK6(X0,X1))
              & m1_subset_1(sK6(X0,X1),u1_struct_0(X0)) )
            | ~ r2_yellow_0(X0,X1) ) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6])],[f103,f105,f104])).

fof(f104,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r1_orders_2(X0,X3,X2)
          & r1_lattice3(X0,X1,X3)
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ~ r1_orders_2(X0,sK5(X0,X1,X2),X2)
        & r1_lattice3(X0,X1,sK5(X0,X1,X2))
        & m1_subset_1(sK5(X0,X1,X2),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f105,plain,(
    ! [X1,X0] :
      ( ? [X4] :
          ( ! [X5] :
              ( r1_orders_2(X0,X5,X4)
              | ~ r1_lattice3(X0,X1,X5)
              | ~ m1_subset_1(X5,u1_struct_0(X0)) )
          & r1_lattice3(X0,X1,X4)
          & m1_subset_1(X4,u1_struct_0(X0)) )
     => ( ! [X5] :
            ( r1_orders_2(X0,X5,sK6(X0,X1))
            | ~ r1_lattice3(X0,X1,X5)
            | ~ m1_subset_1(X5,u1_struct_0(X0)) )
        & r1_lattice3(X0,X1,sK6(X0,X1))
        & m1_subset_1(sK6(X0,X1),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f103,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r2_yellow_0(X0,X1)
            | ! [X2] :
                ( ? [X3] :
                    ( ~ r1_orders_2(X0,X3,X2)
                    & r1_lattice3(X0,X1,X3)
                    & m1_subset_1(X3,u1_struct_0(X0)) )
                | ~ r1_lattice3(X0,X1,X2)
                | ~ m1_subset_1(X2,u1_struct_0(X0)) ) )
          & ( ? [X4] :
                ( ! [X5] :
                    ( r1_orders_2(X0,X5,X4)
                    | ~ r1_lattice3(X0,X1,X5)
                    | ~ m1_subset_1(X5,u1_struct_0(X0)) )
                & r1_lattice3(X0,X1,X4)
                & m1_subset_1(X4,u1_struct_0(X0)) )
            | ~ r2_yellow_0(X0,X1) ) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(rectify,[],[f102])).

fof(f102,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r2_yellow_0(X0,X1)
            | ! [X2] :
                ( ? [X3] :
                    ( ~ r1_orders_2(X0,X3,X2)
                    & r1_lattice3(X0,X1,X3)
                    & m1_subset_1(X3,u1_struct_0(X0)) )
                | ~ r1_lattice3(X0,X1,X2)
                | ~ m1_subset_1(X2,u1_struct_0(X0)) ) )
          & ( ? [X2] :
                ( ! [X3] :
                    ( r1_orders_2(X0,X3,X2)
                    | ~ r1_lattice3(X0,X1,X3)
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                & r1_lattice3(X0,X1,X2)
                & m1_subset_1(X2,u1_struct_0(X0)) )
            | ~ r2_yellow_0(X0,X1) ) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(nnf_transformation,[],[f59])).

fof(f59,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_yellow_0(X0,X1)
        <=> ? [X2] :
              ( ! [X3] :
                  ( r1_orders_2(X0,X3,X2)
                  | ~ r1_lattice3(X0,X1,X3)
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              & r1_lattice3(X0,X1,X2)
              & m1_subset_1(X2,u1_struct_0(X0)) ) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(flattening,[],[f58])).

fof(f58,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_yellow_0(X0,X1)
        <=> ? [X2] :
              ( ! [X3] :
                  ( r1_orders_2(X0,X3,X2)
                  | ~ r1_lattice3(X0,X1,X3)
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              & r1_lattice3(X0,X1,X2)
              & m1_subset_1(X2,u1_struct_0(X0)) ) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f26])).

fof(f26,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0) )
     => ! [X1] :
          ( r2_yellow_0(X0,X1)
        <=> ? [X2] :
              ( ! [X3] :
                  ( m1_subset_1(X3,u1_struct_0(X0))
                 => ( r1_lattice3(X0,X1,X3)
                   => r1_orders_2(X0,X3,X2) ) )
              & r1_lattice3(X0,X1,X2)
              & m1_subset_1(X2,u1_struct_0(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/yellow_0__t40_yellow_0.p',t16_yellow_0)).

fof(f313,plain,(
    ! [X6,X4,X5,X3] :
      ( r1_orders_2(X3,sK5(X3,k2_tarski(X4,X5),X6),X4)
      | ~ m1_subset_1(X5,u1_struct_0(X3))
      | ~ m1_subset_1(X4,u1_struct_0(X3))
      | ~ m1_subset_1(sK5(X3,k2_tarski(X4,X5),X6),u1_struct_0(X3))
      | ~ l1_orders_2(X3)
      | r2_yellow_0(X3,k2_tarski(X4,X5))
      | ~ r1_lattice3(X3,k2_tarski(X4,X5),X6)
      | ~ m1_subset_1(X6,u1_struct_0(X3))
      | ~ v5_orders_2(X3) ) ),
    inference(duplicate_literal_removal,[],[f310])).

fof(f310,plain,(
    ! [X6,X4,X5,X3] :
      ( r1_orders_2(X3,sK5(X3,k2_tarski(X4,X5),X6),X4)
      | ~ m1_subset_1(X5,u1_struct_0(X3))
      | ~ m1_subset_1(X4,u1_struct_0(X3))
      | ~ m1_subset_1(sK5(X3,k2_tarski(X4,X5),X6),u1_struct_0(X3))
      | ~ l1_orders_2(X3)
      | r2_yellow_0(X3,k2_tarski(X4,X5))
      | ~ r1_lattice3(X3,k2_tarski(X4,X5),X6)
      | ~ m1_subset_1(X6,u1_struct_0(X3))
      | ~ l1_orders_2(X3)
      | ~ v5_orders_2(X3) ) ),
    inference(resolution,[],[f125,f149])).

fof(f149,plain,(
    ! [X2,X0,X1] :
      ( r1_lattice3(X0,X1,sK5(X0,X1,X2))
      | r2_yellow_0(X0,X1)
      | ~ r1_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f106])).

fof(f125,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r1_lattice3(X0,k2_tarski(X2,X3),X1)
      | r1_orders_2(X0,X1,X2)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f1372,plain,(
    ! [X14,X12,X15,X13] :
      ( ~ r1_orders_2(X12,sK5(X12,k2_tarski(X13,X14),k12_lattice3(X12,X15,X14)),X15)
      | ~ m1_subset_1(X14,u1_struct_0(X12))
      | ~ m1_subset_1(X15,u1_struct_0(X12))
      | ~ l1_orders_2(X12)
      | ~ v2_lattice3(X12)
      | ~ v5_orders_2(X12)
      | r2_yellow_0(X12,k2_tarski(X13,X14))
      | ~ r1_lattice3(X12,k2_tarski(X13,X14),k12_lattice3(X12,X15,X14))
      | ~ m1_subset_1(X13,u1_struct_0(X12)) ) ),
    inference(subsumption_resolution,[],[f1365,f165])).

fof(f1365,plain,(
    ! [X14,X12,X15,X13] :
      ( ~ r1_orders_2(X12,sK5(X12,k2_tarski(X13,X14),k12_lattice3(X12,X15,X14)),X15)
      | ~ m1_subset_1(X14,u1_struct_0(X12))
      | ~ m1_subset_1(X15,u1_struct_0(X12))
      | ~ l1_orders_2(X12)
      | ~ v2_lattice3(X12)
      | ~ v5_orders_2(X12)
      | r2_yellow_0(X12,k2_tarski(X13,X14))
      | ~ r1_lattice3(X12,k2_tarski(X13,X14),k12_lattice3(X12,X15,X14))
      | ~ m1_subset_1(X13,u1_struct_0(X12))
      | ~ m1_subset_1(k12_lattice3(X12,X15,X14),u1_struct_0(X12)) ) ),
    inference(duplicate_literal_removal,[],[f1350])).

fof(f1350,plain,(
    ! [X14,X12,X15,X13] :
      ( ~ r1_orders_2(X12,sK5(X12,k2_tarski(X13,X14),k12_lattice3(X12,X15,X14)),X15)
      | ~ m1_subset_1(X14,u1_struct_0(X12))
      | ~ m1_subset_1(X15,u1_struct_0(X12))
      | ~ l1_orders_2(X12)
      | ~ v2_lattice3(X12)
      | ~ v5_orders_2(X12)
      | r2_yellow_0(X12,k2_tarski(X13,X14))
      | ~ r1_lattice3(X12,k2_tarski(X13,X14),k12_lattice3(X12,X15,X14))
      | ~ m1_subset_1(X14,u1_struct_0(X12))
      | ~ m1_subset_1(X13,u1_struct_0(X12))
      | ~ l1_orders_2(X12)
      | r2_yellow_0(X12,k2_tarski(X13,X14))
      | ~ r1_lattice3(X12,k2_tarski(X13,X14),k12_lattice3(X12,X15,X14))
      | ~ m1_subset_1(k12_lattice3(X12,X15,X14),u1_struct_0(X12))
      | ~ v5_orders_2(X12) ) ),
    inference(resolution,[],[f734,f333])).

fof(f333,plain,(
    ! [X6,X4,X5,X3] :
      ( r1_orders_2(X3,sK5(X3,k2_tarski(X4,X5),X6),X5)
      | ~ m1_subset_1(X5,u1_struct_0(X3))
      | ~ m1_subset_1(X4,u1_struct_0(X3))
      | ~ l1_orders_2(X3)
      | r2_yellow_0(X3,k2_tarski(X4,X5))
      | ~ r1_lattice3(X3,k2_tarski(X4,X5),X6)
      | ~ m1_subset_1(X6,u1_struct_0(X3))
      | ~ v5_orders_2(X3) ) ),
    inference(subsumption_resolution,[],[f330,f148])).

fof(f330,plain,(
    ! [X6,X4,X5,X3] :
      ( r1_orders_2(X3,sK5(X3,k2_tarski(X4,X5),X6),X5)
      | ~ m1_subset_1(X5,u1_struct_0(X3))
      | ~ m1_subset_1(X4,u1_struct_0(X3))
      | ~ m1_subset_1(sK5(X3,k2_tarski(X4,X5),X6),u1_struct_0(X3))
      | ~ l1_orders_2(X3)
      | r2_yellow_0(X3,k2_tarski(X4,X5))
      | ~ r1_lattice3(X3,k2_tarski(X4,X5),X6)
      | ~ m1_subset_1(X6,u1_struct_0(X3))
      | ~ v5_orders_2(X3) ) ),
    inference(duplicate_literal_removal,[],[f327])).

fof(f327,plain,(
    ! [X6,X4,X5,X3] :
      ( r1_orders_2(X3,sK5(X3,k2_tarski(X4,X5),X6),X5)
      | ~ m1_subset_1(X5,u1_struct_0(X3))
      | ~ m1_subset_1(X4,u1_struct_0(X3))
      | ~ m1_subset_1(sK5(X3,k2_tarski(X4,X5),X6),u1_struct_0(X3))
      | ~ l1_orders_2(X3)
      | r2_yellow_0(X3,k2_tarski(X4,X5))
      | ~ r1_lattice3(X3,k2_tarski(X4,X5),X6)
      | ~ m1_subset_1(X6,u1_struct_0(X3))
      | ~ l1_orders_2(X3)
      | ~ v5_orders_2(X3) ) ),
    inference(resolution,[],[f126,f149])).

fof(f126,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r1_lattice3(X0,k2_tarski(X2,X3),X1)
      | r1_orders_2(X0,X1,X3)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f734,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r1_orders_2(X0,sK5(X0,X1,k12_lattice3(X0,X2,X3)),X3)
      | ~ r1_orders_2(X0,sK5(X0,X1,k12_lattice3(X0,X2,X3)),X2)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0)
      | r2_yellow_0(X0,X1)
      | ~ r1_lattice3(X0,X1,k12_lattice3(X0,X2,X3)) ) ),
    inference(subsumption_resolution,[],[f733,f165])).

fof(f733,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r1_orders_2(X0,sK5(X0,X1,k12_lattice3(X0,X2,X3)),X2)
      | ~ r1_orders_2(X0,sK5(X0,X1,k12_lattice3(X0,X2,X3)),X3)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0)
      | r2_yellow_0(X0,X1)
      | ~ r1_lattice3(X0,X1,k12_lattice3(X0,X2,X3))
      | ~ m1_subset_1(k12_lattice3(X0,X2,X3),u1_struct_0(X0)) ) ),
    inference(subsumption_resolution,[],[f732,f148])).

fof(f732,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r1_orders_2(X0,sK5(X0,X1,k12_lattice3(X0,X2,X3)),X2)
      | ~ m1_subset_1(sK5(X0,X1,k12_lattice3(X0,X2,X3)),u1_struct_0(X0))
      | ~ r1_orders_2(X0,sK5(X0,X1,k12_lattice3(X0,X2,X3)),X3)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0)
      | r2_yellow_0(X0,X1)
      | ~ r1_lattice3(X0,X1,k12_lattice3(X0,X2,X3))
      | ~ m1_subset_1(k12_lattice3(X0,X2,X3),u1_struct_0(X0)) ) ),
    inference(duplicate_literal_removal,[],[f717])).

fof(f717,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r1_orders_2(X0,sK5(X0,X1,k12_lattice3(X0,X2,X3)),X2)
      | ~ m1_subset_1(sK5(X0,X1,k12_lattice3(X0,X2,X3)),u1_struct_0(X0))
      | ~ r1_orders_2(X0,sK5(X0,X1,k12_lattice3(X0,X2,X3)),X3)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0)
      | r2_yellow_0(X0,X1)
      | ~ r1_lattice3(X0,X1,k12_lattice3(X0,X2,X3))
      | ~ m1_subset_1(k12_lattice3(X0,X2,X3),u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(resolution,[],[f436,f150])).

fof(f150,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_orders_2(X0,sK5(X0,X1,X2),X2)
      | r2_yellow_0(X0,X1)
      | ~ r1_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f106])).

fof(f436,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_orders_2(X0,X1,k12_lattice3(X0,X3,X2))
      | ~ r1_orders_2(X0,X1,X3)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ r1_orders_2(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(duplicate_literal_removal,[],[f431])).

fof(f431,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r1_orders_2(X0,X1,X2)
      | ~ r1_orders_2(X0,X1,X3)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | r1_orders_2(X0,X1,k12_lattice3(X0,X3,X2))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(resolution,[],[f179,f165])).

fof(f179,plain,(
    ! [X2,X0,X5,X1] :
      ( ~ m1_subset_1(k12_lattice3(X0,X1,X2),u1_struct_0(X0))
      | ~ r1_orders_2(X0,X5,X2)
      | ~ r1_orders_2(X0,X5,X1)
      | ~ m1_subset_1(X5,u1_struct_0(X0))
      | r1_orders_2(X0,X5,k12_lattice3(X0,X1,X2))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(equality_resolution,[],[f140])).

fof(f140,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r1_orders_2(X0,X5,X3)
      | ~ r1_orders_2(X0,X5,X2)
      | ~ r1_orders_2(X0,X5,X1)
      | ~ m1_subset_1(X5,u1_struct_0(X0))
      | k12_lattice3(X0,X1,X2) != X3
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f101])).

fof(f101,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ( k12_lattice3(X0,X1,X2) = X3
                      | ( ~ r1_orders_2(X0,sK4(X0,X1,X2,X3),X3)
                        & r1_orders_2(X0,sK4(X0,X1,X2,X3),X2)
                        & r1_orders_2(X0,sK4(X0,X1,X2,X3),X1)
                        & m1_subset_1(sK4(X0,X1,X2,X3),u1_struct_0(X0)) )
                      | ~ r1_orders_2(X0,X3,X2)
                      | ~ r1_orders_2(X0,X3,X1) )
                    & ( ( ! [X5] :
                            ( r1_orders_2(X0,X5,X3)
                            | ~ r1_orders_2(X0,X5,X2)
                            | ~ r1_orders_2(X0,X5,X1)
                            | ~ m1_subset_1(X5,u1_struct_0(X0)) )
                        & r1_orders_2(X0,X3,X2)
                        & r1_orders_2(X0,X3,X1) )
                      | k12_lattice3(X0,X1,X2) != X3 ) )
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f99,f100])).

fof(f100,plain,(
    ! [X3,X2,X1,X0] :
      ( ? [X4] :
          ( ~ r1_orders_2(X0,X4,X3)
          & r1_orders_2(X0,X4,X2)
          & r1_orders_2(X0,X4,X1)
          & m1_subset_1(X4,u1_struct_0(X0)) )
     => ( ~ r1_orders_2(X0,sK4(X0,X1,X2,X3),X3)
        & r1_orders_2(X0,sK4(X0,X1,X2,X3),X2)
        & r1_orders_2(X0,sK4(X0,X1,X2,X3),X1)
        & m1_subset_1(sK4(X0,X1,X2,X3),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f99,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ( k12_lattice3(X0,X1,X2) = X3
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
                      | k12_lattice3(X0,X1,X2) != X3 ) )
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(rectify,[],[f98])).

fof(f98,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ( k12_lattice3(X0,X1,X2) = X3
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
                      | k12_lattice3(X0,X1,X2) != X3 ) )
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(flattening,[],[f97])).

fof(f97,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ( k12_lattice3(X0,X1,X2) = X3
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
                      | k12_lattice3(X0,X1,X2) != X3 ) )
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(nnf_transformation,[],[f57])).

fof(f57,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( k12_lattice3(X0,X1,X2) = X3
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
      | ~ v5_orders_2(X0) ) ),
    inference(flattening,[],[f56])).

fof(f56,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( k12_lattice3(X0,X1,X2) = X3
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
      | ~ v5_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f28])).

fof(f28,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v2_lattice3(X0)
        & v5_orders_2(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ! [X3] :
                  ( m1_subset_1(X3,u1_struct_0(X0))
                 => ( k12_lattice3(X0,X1,X2) = X3
                  <=> ( ! [X4] :
                          ( m1_subset_1(X4,u1_struct_0(X0))
                         => ( ( r1_orders_2(X0,X4,X2)
                              & r1_orders_2(X0,X4,X1) )
                           => r1_orders_2(X0,X4,X3) ) )
                      & r1_orders_2(X0,X3,X2)
                      & r1_orders_2(X0,X3,X1) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/yellow_0__t40_yellow_0.p',t23_yellow_0)).

fof(f3665,plain,(
    ! [X10,X11,X9] :
      ( ~ m1_subset_1(X9,u1_struct_0(X10))
      | ~ m1_subset_1(X11,u1_struct_0(X10))
      | ~ l1_orders_2(X10)
      | ~ v2_lattice3(X10)
      | ~ v5_orders_2(X10)
      | k2_yellow_0(X10,k2_tarski(X11,X9)) = k12_lattice3(X10,X11,X9)
      | ~ r1_lattice3(X10,k2_tarski(X11,X9),k12_lattice3(X10,X11,X9))
      | ~ r2_yellow_0(X10,k2_tarski(X11,X9))
      | ~ m1_subset_1(k12_lattice3(X10,X11,X9),u1_struct_0(X10)) ) ),
    inference(duplicate_literal_removal,[],[f3648])).

fof(f3648,plain,(
    ! [X10,X11,X9] :
      ( ~ m1_subset_1(X9,u1_struct_0(X10))
      | ~ m1_subset_1(X11,u1_struct_0(X10))
      | ~ l1_orders_2(X10)
      | ~ v2_lattice3(X10)
      | ~ v5_orders_2(X10)
      | k2_yellow_0(X10,k2_tarski(X11,X9)) = k12_lattice3(X10,X11,X9)
      | ~ r1_lattice3(X10,k2_tarski(X11,X9),k12_lattice3(X10,X11,X9))
      | ~ r2_yellow_0(X10,k2_tarski(X11,X9))
      | ~ m1_subset_1(X11,u1_struct_0(X10))
      | ~ r1_lattice3(X10,k2_tarski(X11,X9),k12_lattice3(X10,X11,X9))
      | ~ r2_yellow_0(X10,k2_tarski(X11,X9))
      | ~ m1_subset_1(k12_lattice3(X10,X11,X9),u1_struct_0(X10))
      | ~ l1_orders_2(X10)
      | k2_yellow_0(X10,k2_tarski(X11,X9)) = k12_lattice3(X10,X11,X9)
      | ~ m1_subset_1(X9,u1_struct_0(X10))
      | ~ m1_subset_1(X11,u1_struct_0(X10)) ) ),
    inference(resolution,[],[f1464,f352])).

fof(f352,plain,(
    ! [X6,X4,X7,X5] :
      ( r1_orders_2(X4,sK3(X4,k2_tarski(X5,X6),X7),X5)
      | ~ r1_lattice3(X4,k2_tarski(X5,X6),X7)
      | ~ r2_yellow_0(X4,k2_tarski(X5,X6))
      | ~ m1_subset_1(X7,u1_struct_0(X4))
      | ~ l1_orders_2(X4)
      | k2_yellow_0(X4,k2_tarski(X5,X6)) = X7
      | ~ m1_subset_1(X6,u1_struct_0(X4))
      | ~ m1_subset_1(X5,u1_struct_0(X4)) ) ),
    inference(subsumption_resolution,[],[f349,f133])).

fof(f133,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(sK3(X0,X1,X2),u1_struct_0(X0))
      | k2_yellow_0(X0,X1) = X2
      | ~ r1_lattice3(X0,X1,X2)
      | ~ r2_yellow_0(X0,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f96])).

fof(f96,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( k2_yellow_0(X0,X1) = X2
              | ( ~ r1_orders_2(X0,sK3(X0,X1,X2),X2)
                & r1_lattice3(X0,X1,sK3(X0,X1,X2))
                & m1_subset_1(sK3(X0,X1,X2),u1_struct_0(X0)) )
              | ~ r1_lattice3(X0,X1,X2) )
            & ( ( ! [X4] :
                    ( r1_orders_2(X0,X4,X2)
                    | ~ r1_lattice3(X0,X1,X4)
                    | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                & r1_lattice3(X0,X1,X2) )
              | k2_yellow_0(X0,X1) != X2 ) )
          | ~ r2_yellow_0(X0,X1)
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f94,f95])).

fof(f95,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r1_orders_2(X0,X3,X2)
          & r1_lattice3(X0,X1,X3)
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ~ r1_orders_2(X0,sK3(X0,X1,X2),X2)
        & r1_lattice3(X0,X1,sK3(X0,X1,X2))
        & m1_subset_1(sK3(X0,X1,X2),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f94,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( k2_yellow_0(X0,X1) = X2
              | ? [X3] :
                  ( ~ r1_orders_2(X0,X3,X2)
                  & r1_lattice3(X0,X1,X3)
                  & m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ r1_lattice3(X0,X1,X2) )
            & ( ( ! [X4] :
                    ( r1_orders_2(X0,X4,X2)
                    | ~ r1_lattice3(X0,X1,X4)
                    | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                & r1_lattice3(X0,X1,X2) )
              | k2_yellow_0(X0,X1) != X2 ) )
          | ~ r2_yellow_0(X0,X1)
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(rectify,[],[f93])).

fof(f93,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( k2_yellow_0(X0,X1) = X2
              | ? [X3] :
                  ( ~ r1_orders_2(X0,X3,X2)
                  & r1_lattice3(X0,X1,X3)
                  & m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ r1_lattice3(X0,X1,X2) )
            & ( ( ! [X3] :
                    ( r1_orders_2(X0,X3,X2)
                    | ~ r1_lattice3(X0,X1,X3)
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                & r1_lattice3(X0,X1,X2) )
              | k2_yellow_0(X0,X1) != X2 ) )
          | ~ r2_yellow_0(X0,X1)
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f92])).

fof(f92,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( k2_yellow_0(X0,X1) = X2
              | ? [X3] :
                  ( ~ r1_orders_2(X0,X3,X2)
                  & r1_lattice3(X0,X1,X3)
                  & m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ r1_lattice3(X0,X1,X2) )
            & ( ( ! [X3] :
                    ( r1_orders_2(X0,X3,X2)
                    | ~ r1_lattice3(X0,X1,X3)
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                & r1_lattice3(X0,X1,X2) )
              | k2_yellow_0(X0,X1) != X2 ) )
          | ~ r2_yellow_0(X0,X1)
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(nnf_transformation,[],[f52])).

fof(f52,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k2_yellow_0(X0,X1) = X2
          <=> ( ! [X3] :
                  ( r1_orders_2(X0,X3,X2)
                  | ~ r1_lattice3(X0,X1,X3)
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              & r1_lattice3(X0,X1,X2) ) )
          | ~ r2_yellow_0(X0,X1)
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f51])).

fof(f51,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k2_yellow_0(X0,X1) = X2
          <=> ( ! [X3] :
                  ( r1_orders_2(X0,X3,X2)
                  | ~ r1_lattice3(X0,X1,X3)
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              & r1_lattice3(X0,X1,X2) ) )
          | ~ r2_yellow_0(X0,X1)
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1,X2] :
          ( m1_subset_1(X2,u1_struct_0(X0))
         => ( r2_yellow_0(X0,X1)
           => ( k2_yellow_0(X0,X1) = X2
            <=> ( ! [X3] :
                    ( m1_subset_1(X3,u1_struct_0(X0))
                   => ( r1_lattice3(X0,X1,X3)
                     => r1_orders_2(X0,X3,X2) ) )
                & r1_lattice3(X0,X1,X2) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/yellow_0__t40_yellow_0.p',d10_yellow_0)).

fof(f349,plain,(
    ! [X6,X4,X7,X5] :
      ( k2_yellow_0(X4,k2_tarski(X5,X6)) = X7
      | ~ r1_lattice3(X4,k2_tarski(X5,X6),X7)
      | ~ r2_yellow_0(X4,k2_tarski(X5,X6))
      | ~ m1_subset_1(X7,u1_struct_0(X4))
      | ~ l1_orders_2(X4)
      | r1_orders_2(X4,sK3(X4,k2_tarski(X5,X6),X7),X5)
      | ~ m1_subset_1(X6,u1_struct_0(X4))
      | ~ m1_subset_1(X5,u1_struct_0(X4))
      | ~ m1_subset_1(sK3(X4,k2_tarski(X5,X6),X7),u1_struct_0(X4)) ) ),
    inference(duplicate_literal_removal,[],[f348])).

fof(f348,plain,(
    ! [X6,X4,X7,X5] :
      ( k2_yellow_0(X4,k2_tarski(X5,X6)) = X7
      | ~ r1_lattice3(X4,k2_tarski(X5,X6),X7)
      | ~ r2_yellow_0(X4,k2_tarski(X5,X6))
      | ~ m1_subset_1(X7,u1_struct_0(X4))
      | ~ l1_orders_2(X4)
      | r1_orders_2(X4,sK3(X4,k2_tarski(X5,X6),X7),X5)
      | ~ m1_subset_1(X6,u1_struct_0(X4))
      | ~ m1_subset_1(X5,u1_struct_0(X4))
      | ~ m1_subset_1(sK3(X4,k2_tarski(X5,X6),X7),u1_struct_0(X4))
      | ~ l1_orders_2(X4) ) ),
    inference(resolution,[],[f134,f125])).

fof(f134,plain,(
    ! [X2,X0,X1] :
      ( r1_lattice3(X0,X1,sK3(X0,X1,X2))
      | k2_yellow_0(X0,X1) = X2
      | ~ r1_lattice3(X0,X1,X2)
      | ~ r2_yellow_0(X0,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f96])).

fof(f1464,plain,(
    ! [X6,X4,X7,X5] :
      ( ~ r1_orders_2(X4,sK3(X4,k2_tarski(X5,X6),k12_lattice3(X4,X7,X6)),X7)
      | ~ m1_subset_1(X6,u1_struct_0(X4))
      | ~ m1_subset_1(X7,u1_struct_0(X4))
      | ~ l1_orders_2(X4)
      | ~ v2_lattice3(X4)
      | ~ v5_orders_2(X4)
      | k2_yellow_0(X4,k2_tarski(X5,X6)) = k12_lattice3(X4,X7,X6)
      | ~ r1_lattice3(X4,k2_tarski(X5,X6),k12_lattice3(X4,X7,X6))
      | ~ r2_yellow_0(X4,k2_tarski(X5,X6))
      | ~ m1_subset_1(X5,u1_struct_0(X4)) ) ),
    inference(subsumption_resolution,[],[f1461,f165])).

fof(f1461,plain,(
    ! [X6,X4,X7,X5] :
      ( ~ r1_orders_2(X4,sK3(X4,k2_tarski(X5,X6),k12_lattice3(X4,X7,X6)),X7)
      | ~ m1_subset_1(X6,u1_struct_0(X4))
      | ~ m1_subset_1(X7,u1_struct_0(X4))
      | ~ l1_orders_2(X4)
      | ~ v2_lattice3(X4)
      | ~ v5_orders_2(X4)
      | k2_yellow_0(X4,k2_tarski(X5,X6)) = k12_lattice3(X4,X7,X6)
      | ~ r1_lattice3(X4,k2_tarski(X5,X6),k12_lattice3(X4,X7,X6))
      | ~ r2_yellow_0(X4,k2_tarski(X5,X6))
      | ~ m1_subset_1(k12_lattice3(X4,X7,X6),u1_struct_0(X4))
      | ~ m1_subset_1(X5,u1_struct_0(X4)) ) ),
    inference(duplicate_literal_removal,[],[f1442])).

fof(f1442,plain,(
    ! [X6,X4,X7,X5] :
      ( ~ r1_orders_2(X4,sK3(X4,k2_tarski(X5,X6),k12_lattice3(X4,X7,X6)),X7)
      | ~ m1_subset_1(X6,u1_struct_0(X4))
      | ~ m1_subset_1(X7,u1_struct_0(X4))
      | ~ l1_orders_2(X4)
      | ~ v2_lattice3(X4)
      | ~ v5_orders_2(X4)
      | k2_yellow_0(X4,k2_tarski(X5,X6)) = k12_lattice3(X4,X7,X6)
      | ~ r1_lattice3(X4,k2_tarski(X5,X6),k12_lattice3(X4,X7,X6))
      | ~ r2_yellow_0(X4,k2_tarski(X5,X6))
      | ~ r1_lattice3(X4,k2_tarski(X5,X6),k12_lattice3(X4,X7,X6))
      | ~ r2_yellow_0(X4,k2_tarski(X5,X6))
      | ~ m1_subset_1(k12_lattice3(X4,X7,X6),u1_struct_0(X4))
      | ~ l1_orders_2(X4)
      | k2_yellow_0(X4,k2_tarski(X5,X6)) = k12_lattice3(X4,X7,X6)
      | ~ m1_subset_1(X6,u1_struct_0(X4))
      | ~ m1_subset_1(X5,u1_struct_0(X4)) ) ),
    inference(resolution,[],[f738,f351])).

fof(f351,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_orders_2(X0,sK3(X0,k2_tarski(X1,X2),X3),X2)
      | ~ r1_lattice3(X0,k2_tarski(X1,X2),X3)
      | ~ r2_yellow_0(X0,k2_tarski(X1,X2))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | k2_yellow_0(X0,k2_tarski(X1,X2)) = X3
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0)) ) ),
    inference(subsumption_resolution,[],[f350,f133])).

fof(f350,plain,(
    ! [X2,X0,X3,X1] :
      ( k2_yellow_0(X0,k2_tarski(X1,X2)) = X3
      | ~ r1_lattice3(X0,k2_tarski(X1,X2),X3)
      | ~ r2_yellow_0(X0,k2_tarski(X1,X2))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | r1_orders_2(X0,sK3(X0,k2_tarski(X1,X2),X3),X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(sK3(X0,k2_tarski(X1,X2),X3),u1_struct_0(X0)) ) ),
    inference(duplicate_literal_removal,[],[f347])).

fof(f347,plain,(
    ! [X2,X0,X3,X1] :
      ( k2_yellow_0(X0,k2_tarski(X1,X2)) = X3
      | ~ r1_lattice3(X0,k2_tarski(X1,X2),X3)
      | ~ r2_yellow_0(X0,k2_tarski(X1,X2))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | r1_orders_2(X0,sK3(X0,k2_tarski(X1,X2),X3),X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(sK3(X0,k2_tarski(X1,X2),X3),u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(resolution,[],[f134,f126])).

fof(f738,plain,(
    ! [X10,X8,X11,X9] :
      ( ~ r1_orders_2(X8,sK3(X8,X9,k12_lattice3(X8,X10,X11)),X11)
      | ~ r1_orders_2(X8,sK3(X8,X9,k12_lattice3(X8,X10,X11)),X10)
      | ~ m1_subset_1(X11,u1_struct_0(X8))
      | ~ m1_subset_1(X10,u1_struct_0(X8))
      | ~ l1_orders_2(X8)
      | ~ v2_lattice3(X8)
      | ~ v5_orders_2(X8)
      | k2_yellow_0(X8,X9) = k12_lattice3(X8,X10,X11)
      | ~ r1_lattice3(X8,X9,k12_lattice3(X8,X10,X11))
      | ~ r2_yellow_0(X8,X9) ) ),
    inference(subsumption_resolution,[],[f737,f165])).

fof(f737,plain,(
    ! [X10,X8,X11,X9] :
      ( ~ r1_orders_2(X8,sK3(X8,X9,k12_lattice3(X8,X10,X11)),X10)
      | ~ r1_orders_2(X8,sK3(X8,X9,k12_lattice3(X8,X10,X11)),X11)
      | ~ m1_subset_1(X11,u1_struct_0(X8))
      | ~ m1_subset_1(X10,u1_struct_0(X8))
      | ~ l1_orders_2(X8)
      | ~ v2_lattice3(X8)
      | ~ v5_orders_2(X8)
      | k2_yellow_0(X8,X9) = k12_lattice3(X8,X10,X11)
      | ~ r1_lattice3(X8,X9,k12_lattice3(X8,X10,X11))
      | ~ r2_yellow_0(X8,X9)
      | ~ m1_subset_1(k12_lattice3(X8,X10,X11),u1_struct_0(X8)) ) ),
    inference(subsumption_resolution,[],[f730,f133])).

fof(f730,plain,(
    ! [X10,X8,X11,X9] :
      ( ~ r1_orders_2(X8,sK3(X8,X9,k12_lattice3(X8,X10,X11)),X10)
      | ~ m1_subset_1(sK3(X8,X9,k12_lattice3(X8,X10,X11)),u1_struct_0(X8))
      | ~ r1_orders_2(X8,sK3(X8,X9,k12_lattice3(X8,X10,X11)),X11)
      | ~ m1_subset_1(X11,u1_struct_0(X8))
      | ~ m1_subset_1(X10,u1_struct_0(X8))
      | ~ l1_orders_2(X8)
      | ~ v2_lattice3(X8)
      | ~ v5_orders_2(X8)
      | k2_yellow_0(X8,X9) = k12_lattice3(X8,X10,X11)
      | ~ r1_lattice3(X8,X9,k12_lattice3(X8,X10,X11))
      | ~ r2_yellow_0(X8,X9)
      | ~ m1_subset_1(k12_lattice3(X8,X10,X11),u1_struct_0(X8)) ) ),
    inference(duplicate_literal_removal,[],[f719])).

fof(f719,plain,(
    ! [X10,X8,X11,X9] :
      ( ~ r1_orders_2(X8,sK3(X8,X9,k12_lattice3(X8,X10,X11)),X10)
      | ~ m1_subset_1(sK3(X8,X9,k12_lattice3(X8,X10,X11)),u1_struct_0(X8))
      | ~ r1_orders_2(X8,sK3(X8,X9,k12_lattice3(X8,X10,X11)),X11)
      | ~ m1_subset_1(X11,u1_struct_0(X8))
      | ~ m1_subset_1(X10,u1_struct_0(X8))
      | ~ l1_orders_2(X8)
      | ~ v2_lattice3(X8)
      | ~ v5_orders_2(X8)
      | k2_yellow_0(X8,X9) = k12_lattice3(X8,X10,X11)
      | ~ r1_lattice3(X8,X9,k12_lattice3(X8,X10,X11))
      | ~ r2_yellow_0(X8,X9)
      | ~ m1_subset_1(k12_lattice3(X8,X10,X11),u1_struct_0(X8))
      | ~ l1_orders_2(X8) ) ),
    inference(resolution,[],[f436,f135])).

fof(f135,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_orders_2(X0,sK3(X0,X1,X2),X2)
      | k2_yellow_0(X0,X1) = X2
      | ~ r1_lattice3(X0,X1,X2)
      | ~ r2_yellow_0(X0,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f96])).

fof(f221,plain,
    ( k2_yellow_0(sK0,k2_tarski(sK1,sK2)) != k12_lattice3(sK0,sK1,sK2)
    | ~ spl11_0 ),
    inference(subsumption_resolution,[],[f220,f212])).

fof(f212,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK0))
    | ~ spl11_0 ),
    inference(resolution,[],[f192,f158])).

fof(f158,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f66])).

fof(f66,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f34])).

fof(f34,axiom,(
    ! [X0,X1] :
      ~ ( v1_xboole_0(X1)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/yellow_0__t40_yellow_0.p',t7_boole)).

fof(f192,plain,
    ( r2_hidden(sK1,u1_struct_0(sK0))
    | ~ spl11_0 ),
    inference(avatar_component_clause,[],[f191])).

fof(f220,plain,
    ( k2_yellow_0(sK0,k2_tarski(sK1,sK2)) != k12_lattice3(sK0,sK1,sK2)
    | v1_xboole_0(u1_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f219,f120])).

fof(f219,plain,
    ( k2_yellow_0(sK0,k2_tarski(sK1,sK2)) != k12_lattice3(sK0,sK1,sK2)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | v1_xboole_0(u1_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f216,f121])).

fof(f216,plain,
    ( k2_yellow_0(sK0,k2_tarski(sK1,sK2)) != k12_lattice3(sK0,sK1,sK2)
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | v1_xboole_0(u1_struct_0(sK0)) ),
    inference(superposition,[],[f122,f163])).

fof(f163,plain,(
    ! [X2,X0,X1] :
      ( k7_domain_1(X0,X1,X2) = k2_tarski(X1,X2)
      | ~ m1_subset_1(X2,X0)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f74])).

fof(f74,plain,(
    ! [X0,X1,X2] :
      ( k7_domain_1(X0,X1,X2) = k2_tarski(X1,X2)
      | ~ m1_subset_1(X2,X0)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f73])).

fof(f73,plain,(
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
    file('/export/starexec/sandbox/benchmark/yellow_0__t40_yellow_0.p',redefinition_k7_domain_1)).

fof(f122,plain,(
    k2_yellow_0(sK0,k7_domain_1(u1_struct_0(sK0),sK1,sK2)) != k12_lattice3(sK0,sK1,sK2) ),
    inference(cnf_transformation,[],[f91])).

fof(f9797,plain,(
    spl11_133 ),
    inference(avatar_contradiction_clause,[],[f9796])).

fof(f9796,plain,
    ( $false
    | ~ spl11_133 ),
    inference(subsumption_resolution,[],[f9795,f117])).

fof(f9795,plain,
    ( ~ v5_orders_2(sK0)
    | ~ spl11_133 ),
    inference(subsumption_resolution,[],[f9794,f118])).

fof(f9794,plain,
    ( ~ v2_lattice3(sK0)
    | ~ v5_orders_2(sK0)
    | ~ spl11_133 ),
    inference(subsumption_resolution,[],[f9793,f119])).

fof(f9793,plain,
    ( ~ l1_orders_2(sK0)
    | ~ v2_lattice3(sK0)
    | ~ v5_orders_2(sK0)
    | ~ spl11_133 ),
    inference(subsumption_resolution,[],[f9792,f120])).

fof(f9792,plain,
    ( ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | ~ v2_lattice3(sK0)
    | ~ v5_orders_2(sK0)
    | ~ spl11_133 ),
    inference(subsumption_resolution,[],[f9783,f121])).

fof(f9783,plain,
    ( ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | ~ v2_lattice3(sK0)
    | ~ v5_orders_2(sK0)
    | ~ spl11_133 ),
    inference(resolution,[],[f9731,f392])).

fof(f392,plain,(
    ! [X2,X0,X1] :
      ( r1_orders_2(X0,k12_lattice3(X0,X1,X2),X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(duplicate_literal_removal,[],[f387])).

fof(f387,plain,(
    ! [X2,X0,X1] :
      ( r1_orders_2(X0,k12_lattice3(X0,X1,X2),X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(resolution,[],[f180,f165])).

fof(f180,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(k12_lattice3(X0,X1,X2),u1_struct_0(X0))
      | r1_orders_2(X0,k12_lattice3(X0,X1,X2),X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(equality_resolution,[],[f139])).

fof(f139,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_orders_2(X0,X3,X2)
      | k12_lattice3(X0,X1,X2) != X3
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f101])).

fof(f9731,plain,
    ( ~ r1_orders_2(sK0,k12_lattice3(sK0,sK1,sK2),sK2)
    | ~ spl11_133 ),
    inference(avatar_component_clause,[],[f9730])).

fof(f9774,plain,(
    spl11_131 ),
    inference(avatar_contradiction_clause,[],[f9773])).

fof(f9773,plain,
    ( $false
    | ~ spl11_131 ),
    inference(subsumption_resolution,[],[f9772,f117])).

fof(f9772,plain,
    ( ~ v5_orders_2(sK0)
    | ~ spl11_131 ),
    inference(subsumption_resolution,[],[f9771,f118])).

fof(f9771,plain,
    ( ~ v2_lattice3(sK0)
    | ~ v5_orders_2(sK0)
    | ~ spl11_131 ),
    inference(subsumption_resolution,[],[f9770,f119])).

fof(f9770,plain,
    ( ~ l1_orders_2(sK0)
    | ~ v2_lattice3(sK0)
    | ~ v5_orders_2(sK0)
    | ~ spl11_131 ),
    inference(subsumption_resolution,[],[f9769,f120])).

fof(f9769,plain,
    ( ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | ~ v2_lattice3(sK0)
    | ~ v5_orders_2(sK0)
    | ~ spl11_131 ),
    inference(subsumption_resolution,[],[f9762,f121])).

fof(f9762,plain,
    ( ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | ~ v2_lattice3(sK0)
    | ~ v5_orders_2(sK0)
    | ~ spl11_131 ),
    inference(resolution,[],[f9728,f400])).

fof(f400,plain,(
    ! [X2,X0,X1] :
      ( r1_orders_2(X0,k12_lattice3(X0,X1,X2),X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(duplicate_literal_removal,[],[f395])).

fof(f395,plain,(
    ! [X2,X0,X1] :
      ( r1_orders_2(X0,k12_lattice3(X0,X1,X2),X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(resolution,[],[f181,f165])).

fof(f181,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(k12_lattice3(X0,X1,X2),u1_struct_0(X0))
      | r1_orders_2(X0,k12_lattice3(X0,X1,X2),X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(equality_resolution,[],[f138])).

fof(f138,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_orders_2(X0,X3,X1)
      | k12_lattice3(X0,X1,X2) != X3
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f101])).

fof(f9728,plain,
    ( ~ r1_orders_2(sK0,k12_lattice3(sK0,sK1,sK2),sK1)
    | ~ spl11_131 ),
    inference(avatar_component_clause,[],[f9727])).

fof(f9752,plain,(
    spl11_129 ),
    inference(avatar_contradiction_clause,[],[f9751])).

fof(f9751,plain,
    ( $false
    | ~ spl11_129 ),
    inference(subsumption_resolution,[],[f9750,f117])).

fof(f9750,plain,
    ( ~ v5_orders_2(sK0)
    | ~ spl11_129 ),
    inference(subsumption_resolution,[],[f9749,f118])).

fof(f9749,plain,
    ( ~ v2_lattice3(sK0)
    | ~ v5_orders_2(sK0)
    | ~ spl11_129 ),
    inference(subsumption_resolution,[],[f9748,f119])).

fof(f9748,plain,
    ( ~ l1_orders_2(sK0)
    | ~ v2_lattice3(sK0)
    | ~ v5_orders_2(sK0)
    | ~ spl11_129 ),
    inference(subsumption_resolution,[],[f9747,f120])).

fof(f9747,plain,
    ( ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | ~ v2_lattice3(sK0)
    | ~ v5_orders_2(sK0)
    | ~ spl11_129 ),
    inference(subsumption_resolution,[],[f9740,f121])).

fof(f9740,plain,
    ( ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | ~ v2_lattice3(sK0)
    | ~ v5_orders_2(sK0)
    | ~ spl11_129 ),
    inference(resolution,[],[f9725,f165])).

fof(f9725,plain,
    ( ~ m1_subset_1(k12_lattice3(sK0,sK1,sK2),u1_struct_0(sK0))
    | ~ spl11_129 ),
    inference(avatar_component_clause,[],[f9724])).

fof(f208,plain,(
    ~ spl11_2 ),
    inference(avatar_contradiction_clause,[],[f207])).

fof(f207,plain,
    ( $false
    | ~ spl11_2 ),
    inference(subsumption_resolution,[],[f206,f119])).

fof(f206,plain,
    ( ~ l1_orders_2(sK0)
    | ~ spl11_2 ),
    inference(subsumption_resolution,[],[f205,f118])).

fof(f205,plain,
    ( ~ v2_lattice3(sK0)
    | ~ l1_orders_2(sK0)
    | ~ spl11_2 ),
    inference(resolution,[],[f202,f124])).

fof(f124,plain,(
    ! [X0] :
      ( ~ v2_struct_0(X0)
      | ~ v2_lattice3(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f48,plain,(
    ! [X0] :
      ( ~ v2_struct_0(X0)
      | ~ v2_lattice3(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f47])).

fof(f47,plain,(
    ! [X0] :
      ( ~ v2_struct_0(X0)
      | ~ v2_lattice3(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f37])).

fof(f37,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ( v2_lattice3(X0)
       => ~ v2_struct_0(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/yellow_0__t40_yellow_0.p',cc2_lattice3)).

fof(f202,plain,
    ( v2_struct_0(sK0)
    | ~ spl11_2 ),
    inference(subsumption_resolution,[],[f201,f182])).

fof(f182,plain,(
    l1_struct_0(sK0) ),
    inference(resolution,[],[f123,f119])).

fof(f123,plain,(
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
    file('/export/starexec/sandbox/benchmark/yellow_0__t40_yellow_0.p',dt_l1_orders_2)).

fof(f201,plain,
    ( ~ l1_struct_0(sK0)
    | v2_struct_0(sK0)
    | ~ spl11_2 ),
    inference(resolution,[],[f195,f137])).

fof(f137,plain,(
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
    inference(ennf_transformation,[],[f38])).

fof(f38,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/yellow_0__t40_yellow_0.p',fc2_struct_0)).

fof(f195,plain,
    ( v1_xboole_0(u1_struct_0(sK0))
    | ~ spl11_2 ),
    inference(avatar_component_clause,[],[f194])).

fof(f194,plain,
    ( spl11_2
  <=> v1_xboole_0(u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_2])])).

fof(f196,plain,
    ( spl11_0
    | spl11_2 ),
    inference(avatar_split_clause,[],[f186,f194,f191])).

fof(f186,plain,
    ( v1_xboole_0(u1_struct_0(sK0))
    | r2_hidden(sK1,u1_struct_0(sK0)) ),
    inference(resolution,[],[f156,f120])).

fof(f156,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,X1)
      | v1_xboole_0(X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f64])).

fof(f64,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f63])).

fof(f63,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f29])).

fof(f29,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/yellow_0__t40_yellow_0.p',t2_subset)).
%------------------------------------------------------------------------------
