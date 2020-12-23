%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : yellow_0__t19_yellow_0.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:41:38 EDT 2019

% Result     : Theorem 1.44s
% Output     : Refutation 1.44s
% Verified   : 
% Statistics : Number of formulae       :  345 (2043 expanded)
%              Number of leaves         :   36 ( 734 expanded)
%              Depth                    :   44
%              Number of atoms          : 2587 (26945 expanded)
%              Number of equality atoms :   85 (1998 expanded)
%              Maximal formula depth    :   25 (   9 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f10167,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f133,f137,f141,f145,f274,f320,f2061,f3023,f3033,f3106,f3122,f4763,f4884,f5356,f5371,f9562,f10166])).

fof(f10166,plain,
    ( ~ spl13_20
    | spl13_25 ),
    inference(avatar_contradiction_clause,[],[f10165])).

fof(f10165,plain,
    ( $false
    | ~ spl13_20
    | ~ spl13_25 ),
    inference(subsumption_resolution,[],[f270,f10018])).

fof(f10018,plain,
    ( sP1(sK3,sK5,sK4)
    | ~ spl13_20 ),
    inference(subsumption_resolution,[],[f10017,f79])).

fof(f79,plain,(
    v5_orders_2(sK3) ),
    inference(cnf_transformation,[],[f56])).

fof(f56,plain,
    ( ( ( ( ~ r2_yellow_0(sK3,k2_tarski(sK4,sK5))
          | k11_lattice3(sK3,sK4,sK5) != sK6 )
        & ! [X4] :
            ( r1_orders_2(sK3,X4,sK6)
            | ~ r1_orders_2(sK3,X4,sK5)
            | ~ r1_orders_2(sK3,X4,sK4)
            | ~ m1_subset_1(X4,u1_struct_0(sK3)) )
        & r1_orders_2(sK3,sK6,sK5)
        & r1_orders_2(sK3,sK6,sK4) )
      | sP0(sK6,sK3,sK5,sK4) )
    & m1_subset_1(sK6,u1_struct_0(sK3))
    & m1_subset_1(sK5,u1_struct_0(sK3))
    & m1_subset_1(sK4,u1_struct_0(sK3))
    & l1_orders_2(sK3)
    & v5_orders_2(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5,sK6])],[f45,f55,f54,f53,f52])).

fof(f52,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ? [X3] :
                    ( ( ( ( ~ r2_yellow_0(X0,k2_tarski(X1,X2))
                          | k11_lattice3(X0,X1,X2) != X3 )
                        & ! [X4] :
                            ( r1_orders_2(X0,X4,X3)
                            | ~ r1_orders_2(X0,X4,X2)
                            | ~ r1_orders_2(X0,X4,X1)
                            | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                        & r1_orders_2(X0,X3,X2)
                        & r1_orders_2(X0,X3,X1) )
                      | sP0(X3,X0,X2,X1) )
                    & m1_subset_1(X3,u1_struct_0(X0)) )
                & m1_subset_1(X2,u1_struct_0(X0)) )
            & m1_subset_1(X1,u1_struct_0(X0)) )
        & l1_orders_2(X0)
        & v5_orders_2(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( ( ( ~ r2_yellow_0(sK3,k2_tarski(X1,X2))
                        | k11_lattice3(sK3,X1,X2) != X3 )
                      & ! [X4] :
                          ( r1_orders_2(sK3,X4,X3)
                          | ~ r1_orders_2(sK3,X4,X2)
                          | ~ r1_orders_2(sK3,X4,X1)
                          | ~ m1_subset_1(X4,u1_struct_0(sK3)) )
                      & r1_orders_2(sK3,X3,X2)
                      & r1_orders_2(sK3,X3,X1) )
                    | sP0(X3,sK3,X2,X1) )
                  & m1_subset_1(X3,u1_struct_0(sK3)) )
              & m1_subset_1(X2,u1_struct_0(sK3)) )
          & m1_subset_1(X1,u1_struct_0(sK3)) )
      & l1_orders_2(sK3)
      & v5_orders_2(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f53,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( ( ( ~ r2_yellow_0(X0,k2_tarski(X1,X2))
                        | k11_lattice3(X0,X1,X2) != X3 )
                      & ! [X4] :
                          ( r1_orders_2(X0,X4,X3)
                          | ~ r1_orders_2(X0,X4,X2)
                          | ~ r1_orders_2(X0,X4,X1)
                          | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                      & r1_orders_2(X0,X3,X2)
                      & r1_orders_2(X0,X3,X1) )
                    | sP0(X3,X0,X2,X1) )
                  & m1_subset_1(X3,u1_struct_0(X0)) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
     => ( ? [X2] :
            ( ? [X3] :
                ( ( ( ( ~ r2_yellow_0(X0,k2_tarski(sK4,X2))
                      | k11_lattice3(X0,sK4,X2) != X3 )
                    & ! [X4] :
                        ( r1_orders_2(X0,X4,X3)
                        | ~ r1_orders_2(X0,X4,X2)
                        | ~ r1_orders_2(X0,X4,sK4)
                        | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                    & r1_orders_2(X0,X3,X2)
                    & r1_orders_2(X0,X3,sK4) )
                  | sP0(X3,X0,X2,sK4) )
                & m1_subset_1(X3,u1_struct_0(X0)) )
            & m1_subset_1(X2,u1_struct_0(X0)) )
        & m1_subset_1(sK4,u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f54,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ? [X3] :
              ( ( ( ( ~ r2_yellow_0(X0,k2_tarski(X1,X2))
                    | k11_lattice3(X0,X1,X2) != X3 )
                  & ! [X4] :
                      ( r1_orders_2(X0,X4,X3)
                      | ~ r1_orders_2(X0,X4,X2)
                      | ~ r1_orders_2(X0,X4,X1)
                      | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                  & r1_orders_2(X0,X3,X2)
                  & r1_orders_2(X0,X3,X1) )
                | sP0(X3,X0,X2,X1) )
              & m1_subset_1(X3,u1_struct_0(X0)) )
          & m1_subset_1(X2,u1_struct_0(X0)) )
     => ( ? [X3] :
            ( ( ( ( ~ r2_yellow_0(X0,k2_tarski(X1,sK5))
                  | k11_lattice3(X0,X1,sK5) != X3 )
                & ! [X4] :
                    ( r1_orders_2(X0,X4,X3)
                    | ~ r1_orders_2(X0,X4,sK5)
                    | ~ r1_orders_2(X0,X4,X1)
                    | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                & r1_orders_2(X0,X3,sK5)
                & r1_orders_2(X0,X3,X1) )
              | sP0(X3,X0,sK5,X1) )
            & m1_subset_1(X3,u1_struct_0(X0)) )
        & m1_subset_1(sK5,u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( ? [X3] :
          ( ( ( ( ~ r2_yellow_0(X0,k2_tarski(X1,X2))
                | k11_lattice3(X0,X1,X2) != X3 )
              & ! [X4] :
                  ( r1_orders_2(X0,X4,X3)
                  | ~ r1_orders_2(X0,X4,X2)
                  | ~ r1_orders_2(X0,X4,X1)
                  | ~ m1_subset_1(X4,u1_struct_0(X0)) )
              & r1_orders_2(X0,X3,X2)
              & r1_orders_2(X0,X3,X1) )
            | sP0(X3,X0,X2,X1) )
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ( ( ( ~ r2_yellow_0(X0,k2_tarski(X1,X2))
              | k11_lattice3(X0,X1,X2) != sK6 )
            & ! [X4] :
                ( r1_orders_2(X0,X4,sK6)
                | ~ r1_orders_2(X0,X4,X2)
                | ~ r1_orders_2(X0,X4,X1)
                | ~ m1_subset_1(X4,u1_struct_0(X0)) )
            & r1_orders_2(X0,sK6,X2)
            & r1_orders_2(X0,sK6,X1) )
          | sP0(sK6,X0,X2,X1) )
        & m1_subset_1(sK6,u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f45,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( ( ( ~ r2_yellow_0(X0,k2_tarski(X1,X2))
                        | k11_lattice3(X0,X1,X2) != X3 )
                      & ! [X4] :
                          ( r1_orders_2(X0,X4,X3)
                          | ~ r1_orders_2(X0,X4,X2)
                          | ~ r1_orders_2(X0,X4,X1)
                          | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                      & r1_orders_2(X0,X3,X2)
                      & r1_orders_2(X0,X3,X1) )
                    | sP0(X3,X0,X2,X1) )
                  & m1_subset_1(X3,u1_struct_0(X0)) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_orders_2(X0)
      & v5_orders_2(X0) ) ),
    inference(definition_folding,[],[f28,f44])).

fof(f44,plain,(
    ! [X3,X0,X2,X1] :
      ( ( ( ? [X5] :
              ( ~ r1_orders_2(X0,X5,X3)
              & r1_orders_2(X0,X5,X2)
              & r1_orders_2(X0,X5,X1)
              & m1_subset_1(X5,u1_struct_0(X0)) )
          | ~ r1_orders_2(X0,X3,X2)
          | ~ r1_orders_2(X0,X3,X1) )
        & r2_yellow_0(X0,k2_tarski(X1,X2))
        & k11_lattice3(X0,X1,X2) = X3 )
      | ~ sP0(X3,X0,X2,X1) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f28,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( ( ( ~ r2_yellow_0(X0,k2_tarski(X1,X2))
                        | k11_lattice3(X0,X1,X2) != X3 )
                      & ! [X4] :
                          ( r1_orders_2(X0,X4,X3)
                          | ~ r1_orders_2(X0,X4,X2)
                          | ~ r1_orders_2(X0,X4,X1)
                          | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                      & r1_orders_2(X0,X3,X2)
                      & r1_orders_2(X0,X3,X1) )
                    | ( ( ? [X5] :
                            ( ~ r1_orders_2(X0,X5,X3)
                            & r1_orders_2(X0,X5,X2)
                            & r1_orders_2(X0,X5,X1)
                            & m1_subset_1(X5,u1_struct_0(X0)) )
                        | ~ r1_orders_2(X0,X3,X2)
                        | ~ r1_orders_2(X0,X3,X1) )
                      & r2_yellow_0(X0,k2_tarski(X1,X2))
                      & k11_lattice3(X0,X1,X2) = X3 ) )
                  & m1_subset_1(X3,u1_struct_0(X0)) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_orders_2(X0)
      & v5_orders_2(X0) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( ( ( ~ r2_yellow_0(X0,k2_tarski(X1,X2))
                        | k11_lattice3(X0,X1,X2) != X3 )
                      & ! [X4] :
                          ( r1_orders_2(X0,X4,X3)
                          | ~ r1_orders_2(X0,X4,X2)
                          | ~ r1_orders_2(X0,X4,X1)
                          | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                      & r1_orders_2(X0,X3,X2)
                      & r1_orders_2(X0,X3,X1) )
                    | ( ( ? [X5] :
                            ( ~ r1_orders_2(X0,X5,X3)
                            & r1_orders_2(X0,X5,X2)
                            & r1_orders_2(X0,X5,X1)
                            & m1_subset_1(X5,u1_struct_0(X0)) )
                        | ~ r1_orders_2(X0,X3,X2)
                        | ~ r1_orders_2(X0,X3,X1) )
                      & r2_yellow_0(X0,k2_tarski(X1,X2))
                      & k11_lattice3(X0,X1,X2) = X3 ) )
                  & m1_subset_1(X3,u1_struct_0(X0)) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_orders_2(X0)
      & v5_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f23,plain,(
    ~ ! [X0] :
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
    inference(rectify,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0] :
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
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
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
    file('/export/starexec/sandbox2/benchmark/yellow_0__t19_yellow_0.p',t19_yellow_0)).

fof(f10017,plain,
    ( sP1(sK3,sK5,sK4)
    | ~ v5_orders_2(sK3)
    | ~ spl13_20 ),
    inference(subsumption_resolution,[],[f10016,f80])).

fof(f80,plain,(
    l1_orders_2(sK3) ),
    inference(cnf_transformation,[],[f56])).

fof(f10016,plain,
    ( ~ l1_orders_2(sK3)
    | sP1(sK3,sK5,sK4)
    | ~ v5_orders_2(sK3)
    | ~ spl13_20 ),
    inference(subsumption_resolution,[],[f10015,f82])).

fof(f82,plain,(
    m1_subset_1(sK5,u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f56])).

fof(f10015,plain,
    ( ~ m1_subset_1(sK5,u1_struct_0(sK3))
    | ~ l1_orders_2(sK3)
    | sP1(sK3,sK5,sK4)
    | ~ v5_orders_2(sK3)
    | ~ spl13_20 ),
    inference(subsumption_resolution,[],[f2349,f81])).

fof(f81,plain,(
    m1_subset_1(sK4,u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f56])).

fof(f2349,plain,
    ( ~ m1_subset_1(sK4,u1_struct_0(sK3))
    | ~ m1_subset_1(sK5,u1_struct_0(sK3))
    | ~ l1_orders_2(sK3)
    | sP1(sK3,sK5,sK4)
    | ~ v5_orders_2(sK3)
    | ~ spl13_20 ),
    inference(resolution,[],[f2323,f1551])).

fof(f1551,plain,(
    ! [X4,X5,X3] :
      ( ~ sP1(X3,X4,X5)
      | ~ m1_subset_1(X4,u1_struct_0(X3))
      | ~ m1_subset_1(X5,u1_struct_0(X3))
      | ~ l1_orders_2(X3)
      | sP1(X3,X5,X4)
      | ~ v5_orders_2(X3) ) ),
    inference(subsumption_resolution,[],[f1550,f119])).

fof(f119,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k11_lattice3(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k11_lattice3(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f42])).

fof(f42,plain,(
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
    file('/export/starexec/sandbox2/benchmark/yellow_0__t19_yellow_0.p',dt_k11_lattice3)).

fof(f1550,plain,(
    ! [X4,X5,X3] :
      ( ~ sP1(X3,X4,X5)
      | ~ m1_subset_1(X4,u1_struct_0(X3))
      | ~ m1_subset_1(X5,u1_struct_0(X3))
      | ~ l1_orders_2(X3)
      | sP1(X3,X5,X4)
      | ~ v5_orders_2(X3)
      | ~ m1_subset_1(k11_lattice3(X3,X5,X4),u1_struct_0(X3)) ) ),
    inference(subsumption_resolution,[],[f1549,f175])).

fof(f175,plain,(
    ! [X2,X0,X1] :
      ( r1_orders_2(X0,k11_lattice3(X0,X1,X2),X2)
      | ~ sP1(X0,X2,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(resolution,[],[f122,f119])).

fof(f122,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(k11_lattice3(X0,X2,X1),u1_struct_0(X0))
      | r1_orders_2(X0,k11_lattice3(X0,X2,X1),X1)
      | ~ sP1(X0,X1,X2) ) ),
    inference(equality_resolution,[],[f90])).

fof(f90,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_orders_2(X0,X3,X1)
      | k11_lattice3(X0,X2,X1) != X3
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ sP1(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f61])).

fof(f61,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( ( ( k11_lattice3(X0,X2,X1) = X3
              | ( ~ r1_orders_2(X0,sK7(X0,X1,X2,X3),X3)
                & r1_orders_2(X0,sK7(X0,X1,X2,X3),X1)
                & r1_orders_2(X0,sK7(X0,X1,X2,X3),X2)
                & m1_subset_1(sK7(X0,X1,X2,X3),u1_struct_0(X0)) )
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
      | ~ sP1(X0,X1,X2) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f59,f60])).

fof(f60,plain,(
    ! [X3,X2,X1,X0] :
      ( ? [X4] :
          ( ~ r1_orders_2(X0,X4,X3)
          & r1_orders_2(X0,X4,X1)
          & r1_orders_2(X0,X4,X2)
          & m1_subset_1(X4,u1_struct_0(X0)) )
     => ( ~ r1_orders_2(X0,sK7(X0,X1,X2,X3),X3)
        & r1_orders_2(X0,sK7(X0,X1,X2,X3),X1)
        & r1_orders_2(X0,sK7(X0,X1,X2,X3),X2)
        & m1_subset_1(sK7(X0,X1,X2,X3),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f59,plain,(
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
      | ~ sP1(X0,X1,X2) ) ),
    inference(rectify,[],[f58])).

fof(f58,plain,(
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
      | ~ sP1(X0,X2,X1) ) ),
    inference(flattening,[],[f57])).

fof(f57,plain,(
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
      | ~ sP1(X0,X2,X1) ) ),
    inference(nnf_transformation,[],[f46])).

fof(f46,plain,(
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
      | ~ sP1(X0,X2,X1) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f1549,plain,(
    ! [X4,X5,X3] :
      ( ~ sP1(X3,X4,X5)
      | ~ m1_subset_1(X4,u1_struct_0(X3))
      | ~ m1_subset_1(X5,u1_struct_0(X3))
      | ~ l1_orders_2(X3)
      | sP1(X3,X5,X4)
      | ~ v5_orders_2(X3)
      | ~ r1_orders_2(X3,k11_lattice3(X3,X5,X4),X4)
      | ~ m1_subset_1(k11_lattice3(X3,X5,X4),u1_struct_0(X3)) ) ),
    inference(subsumption_resolution,[],[f1545,f180])).

fof(f180,plain,(
    ! [X2,X0,X1] :
      ( r1_orders_2(X0,k11_lattice3(X0,X1,X2),X1)
      | ~ sP1(X0,X2,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(resolution,[],[f123,f119])).

fof(f123,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(k11_lattice3(X0,X2,X1),u1_struct_0(X0))
      | r1_orders_2(X0,k11_lattice3(X0,X2,X1),X2)
      | ~ sP1(X0,X1,X2) ) ),
    inference(equality_resolution,[],[f89])).

fof(f89,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_orders_2(X0,X3,X2)
      | k11_lattice3(X0,X2,X1) != X3
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ sP1(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f61])).

fof(f1545,plain,(
    ! [X4,X5,X3] :
      ( ~ sP1(X3,X4,X5)
      | ~ m1_subset_1(X4,u1_struct_0(X3))
      | ~ m1_subset_1(X5,u1_struct_0(X3))
      | ~ l1_orders_2(X3)
      | sP1(X3,X5,X4)
      | ~ r1_orders_2(X3,k11_lattice3(X3,X5,X4),X5)
      | ~ v5_orders_2(X3)
      | ~ r1_orders_2(X3,k11_lattice3(X3,X5,X4),X4)
      | ~ m1_subset_1(k11_lattice3(X3,X5,X4),u1_struct_0(X3)) ) ),
    inference(duplicate_literal_removal,[],[f1532])).

fof(f1532,plain,(
    ! [X4,X5,X3] :
      ( ~ sP1(X3,X4,X5)
      | ~ m1_subset_1(X4,u1_struct_0(X3))
      | ~ m1_subset_1(X5,u1_struct_0(X3))
      | ~ l1_orders_2(X3)
      | sP1(X3,X5,X4)
      | ~ r1_orders_2(X3,k11_lattice3(X3,X5,X4),X5)
      | ~ m1_subset_1(X5,u1_struct_0(X3))
      | ~ v5_orders_2(X3)
      | sP1(X3,X5,X4)
      | ~ r1_orders_2(X3,k11_lattice3(X3,X5,X4),X5)
      | ~ r1_orders_2(X3,k11_lattice3(X3,X5,X4),X4)
      | ~ m1_subset_1(k11_lattice3(X3,X5,X4),u1_struct_0(X3))
      | ~ m1_subset_1(X5,u1_struct_0(X3))
      | ~ m1_subset_1(X4,u1_struct_0(X3))
      | ~ v5_orders_2(X3)
      | ~ l1_orders_2(X3) ) ),
    inference(resolution,[],[f1085,f98])).

fof(f98,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_orders_2(X0,sK8(X0,X1,X2,X3),X2)
      | sP1(X0,X2,X1)
      | ~ r1_orders_2(X0,X3,X2)
      | ~ r1_orders_2(X0,X3,X1)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ v5_orders_2(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f63])).

fof(f63,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( sP1(X0,X2,X1)
              | ! [X3] :
                  ( ( ~ r1_orders_2(X0,sK8(X0,X1,X2,X3),X3)
                    & r1_orders_2(X0,sK8(X0,X1,X2,X3),X2)
                    & r1_orders_2(X0,sK8(X0,X1,X2,X3),X1)
                    & m1_subset_1(sK8(X0,X1,X2,X3),u1_struct_0(X0)) )
                  | ~ r1_orders_2(X0,X3,X2)
                  | ~ r1_orders_2(X0,X3,X1)
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ v5_orders_2(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8])],[f47,f62])).

fof(f62,plain,(
    ! [X3,X2,X1,X0] :
      ( ? [X4] :
          ( ~ r1_orders_2(X0,X4,X3)
          & r1_orders_2(X0,X4,X2)
          & r1_orders_2(X0,X4,X1)
          & m1_subset_1(X4,u1_struct_0(X0)) )
     => ( ~ r1_orders_2(X0,sK8(X0,X1,X2,X3),X3)
        & r1_orders_2(X0,sK8(X0,X1,X2,X3),X2)
        & r1_orders_2(X0,sK8(X0,X1,X2,X3),X1)
        & m1_subset_1(sK8(X0,X1,X2,X3),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f47,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( sP1(X0,X2,X1)
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
    inference(definition_folding,[],[f31,f46])).

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
    inference(ennf_transformation,[],[f24])).

fof(f24,plain,(
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
    inference(rectify,[],[f5])).

fof(f5,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/yellow_0__t19_yellow_0.p',d14_lattice3)).

fof(f1085,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r1_orders_2(X0,sK8(X0,X1,X2,k11_lattice3(X0,X3,X1)),X3)
      | ~ sP1(X0,X1,X3)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | sP1(X0,X2,X1)
      | ~ r1_orders_2(X0,k11_lattice3(X0,X3,X1),X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ v5_orders_2(X0) ) ),
    inference(subsumption_resolution,[],[f1084,f119])).

fof(f1084,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r1_orders_2(X0,sK8(X0,X1,X2,k11_lattice3(X0,X3,X1)),X3)
      | ~ sP1(X0,X1,X3)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | sP1(X0,X2,X1)
      | ~ r1_orders_2(X0,k11_lattice3(X0,X3,X1),X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ v5_orders_2(X0)
      | ~ m1_subset_1(k11_lattice3(X0,X3,X1),u1_struct_0(X0)) ) ),
    inference(subsumption_resolution,[],[f1083,f175])).

fof(f1083,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r1_orders_2(X0,sK8(X0,X1,X2,k11_lattice3(X0,X3,X1)),X3)
      | ~ sP1(X0,X1,X3)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | sP1(X0,X2,X1)
      | ~ r1_orders_2(X0,k11_lattice3(X0,X3,X1),X2)
      | ~ r1_orders_2(X0,k11_lattice3(X0,X3,X1),X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ v5_orders_2(X0)
      | ~ m1_subset_1(k11_lattice3(X0,X3,X1),u1_struct_0(X0)) ) ),
    inference(duplicate_literal_removal,[],[f1068])).

fof(f1068,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r1_orders_2(X0,sK8(X0,X1,X2,k11_lattice3(X0,X3,X1)),X3)
      | ~ sP1(X0,X1,X3)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | sP1(X0,X2,X1)
      | ~ r1_orders_2(X0,k11_lattice3(X0,X3,X1),X2)
      | ~ r1_orders_2(X0,k11_lattice3(X0,X3,X1),X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ v5_orders_2(X0)
      | sP1(X0,X2,X1)
      | ~ r1_orders_2(X0,k11_lattice3(X0,X3,X1),X2)
      | ~ r1_orders_2(X0,k11_lattice3(X0,X3,X1),X1)
      | ~ m1_subset_1(k11_lattice3(X0,X3,X1),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ v5_orders_2(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(resolution,[],[f498,f97])).

fof(f97,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_orders_2(X0,sK8(X0,X1,X2,X3),X1)
      | sP1(X0,X2,X1)
      | ~ r1_orders_2(X0,X3,X2)
      | ~ r1_orders_2(X0,X3,X1)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ v5_orders_2(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f63])).

fof(f498,plain,(
    ! [X21,X19,X22,X20,X18] :
      ( ~ r1_orders_2(X18,sK8(X18,X19,X20,k11_lattice3(X18,X21,X22)),X22)
      | ~ r1_orders_2(X18,sK8(X18,X19,X20,k11_lattice3(X18,X21,X22)),X21)
      | ~ sP1(X18,X22,X21)
      | ~ m1_subset_1(X22,u1_struct_0(X18))
      | ~ m1_subset_1(X21,u1_struct_0(X18))
      | ~ l1_orders_2(X18)
      | sP1(X18,X20,X19)
      | ~ r1_orders_2(X18,k11_lattice3(X18,X21,X22),X20)
      | ~ r1_orders_2(X18,k11_lattice3(X18,X21,X22),X19)
      | ~ m1_subset_1(X20,u1_struct_0(X18))
      | ~ m1_subset_1(X19,u1_struct_0(X18))
      | ~ v5_orders_2(X18) ) ),
    inference(subsumption_resolution,[],[f497,f119])).

fof(f497,plain,(
    ! [X21,X19,X22,X20,X18] :
      ( ~ r1_orders_2(X18,sK8(X18,X19,X20,k11_lattice3(X18,X21,X22)),X21)
      | ~ r1_orders_2(X18,sK8(X18,X19,X20,k11_lattice3(X18,X21,X22)),X22)
      | ~ sP1(X18,X22,X21)
      | ~ m1_subset_1(X22,u1_struct_0(X18))
      | ~ m1_subset_1(X21,u1_struct_0(X18))
      | ~ l1_orders_2(X18)
      | sP1(X18,X20,X19)
      | ~ r1_orders_2(X18,k11_lattice3(X18,X21,X22),X20)
      | ~ r1_orders_2(X18,k11_lattice3(X18,X21,X22),X19)
      | ~ m1_subset_1(k11_lattice3(X18,X21,X22),u1_struct_0(X18))
      | ~ m1_subset_1(X20,u1_struct_0(X18))
      | ~ m1_subset_1(X19,u1_struct_0(X18))
      | ~ v5_orders_2(X18) ) ),
    inference(subsumption_resolution,[],[f487,f96])).

fof(f96,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(sK8(X0,X1,X2,X3),u1_struct_0(X0))
      | sP1(X0,X2,X1)
      | ~ r1_orders_2(X0,X3,X2)
      | ~ r1_orders_2(X0,X3,X1)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ v5_orders_2(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f63])).

fof(f487,plain,(
    ! [X21,X19,X22,X20,X18] :
      ( ~ r1_orders_2(X18,sK8(X18,X19,X20,k11_lattice3(X18,X21,X22)),X21)
      | ~ m1_subset_1(sK8(X18,X19,X20,k11_lattice3(X18,X21,X22)),u1_struct_0(X18))
      | ~ r1_orders_2(X18,sK8(X18,X19,X20,k11_lattice3(X18,X21,X22)),X22)
      | ~ sP1(X18,X22,X21)
      | ~ m1_subset_1(X22,u1_struct_0(X18))
      | ~ m1_subset_1(X21,u1_struct_0(X18))
      | ~ l1_orders_2(X18)
      | sP1(X18,X20,X19)
      | ~ r1_orders_2(X18,k11_lattice3(X18,X21,X22),X20)
      | ~ r1_orders_2(X18,k11_lattice3(X18,X21,X22),X19)
      | ~ m1_subset_1(k11_lattice3(X18,X21,X22),u1_struct_0(X18))
      | ~ m1_subset_1(X20,u1_struct_0(X18))
      | ~ m1_subset_1(X19,u1_struct_0(X18))
      | ~ v5_orders_2(X18) ) ),
    inference(duplicate_literal_removal,[],[f479])).

fof(f479,plain,(
    ! [X21,X19,X22,X20,X18] :
      ( ~ r1_orders_2(X18,sK8(X18,X19,X20,k11_lattice3(X18,X21,X22)),X21)
      | ~ m1_subset_1(sK8(X18,X19,X20,k11_lattice3(X18,X21,X22)),u1_struct_0(X18))
      | ~ r1_orders_2(X18,sK8(X18,X19,X20,k11_lattice3(X18,X21,X22)),X22)
      | ~ sP1(X18,X22,X21)
      | ~ m1_subset_1(X22,u1_struct_0(X18))
      | ~ m1_subset_1(X21,u1_struct_0(X18))
      | ~ l1_orders_2(X18)
      | sP1(X18,X20,X19)
      | ~ r1_orders_2(X18,k11_lattice3(X18,X21,X22),X20)
      | ~ r1_orders_2(X18,k11_lattice3(X18,X21,X22),X19)
      | ~ m1_subset_1(k11_lattice3(X18,X21,X22),u1_struct_0(X18))
      | ~ m1_subset_1(X20,u1_struct_0(X18))
      | ~ m1_subset_1(X19,u1_struct_0(X18))
      | ~ v5_orders_2(X18)
      | ~ l1_orders_2(X18) ) ),
    inference(resolution,[],[f259,f99])).

fof(f99,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r1_orders_2(X0,sK8(X0,X1,X2,X3),X3)
      | sP1(X0,X2,X1)
      | ~ r1_orders_2(X0,X3,X2)
      | ~ r1_orders_2(X0,X3,X1)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ v5_orders_2(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f63])).

fof(f259,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_orders_2(X0,X1,k11_lattice3(X0,X3,X2))
      | ~ r1_orders_2(X0,X1,X3)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ r1_orders_2(X0,X1,X2)
      | ~ sP1(X0,X2,X3)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(resolution,[],[f121,f119])).

fof(f121,plain,(
    ! [X2,X0,X5,X1] :
      ( ~ m1_subset_1(k11_lattice3(X0,X2,X1),u1_struct_0(X0))
      | ~ r1_orders_2(X0,X5,X1)
      | ~ r1_orders_2(X0,X5,X2)
      | ~ m1_subset_1(X5,u1_struct_0(X0))
      | r1_orders_2(X0,X5,k11_lattice3(X0,X2,X1))
      | ~ sP1(X0,X1,X2) ) ),
    inference(equality_resolution,[],[f91])).

fof(f91,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r1_orders_2(X0,X5,X3)
      | ~ r1_orders_2(X0,X5,X1)
      | ~ r1_orders_2(X0,X5,X2)
      | ~ m1_subset_1(X5,u1_struct_0(X0))
      | k11_lattice3(X0,X2,X1) != X3
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ sP1(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f61])).

fof(f2323,plain,
    ( sP1(sK3,sK4,sK5)
    | ~ spl13_20 ),
    inference(avatar_component_clause,[],[f2322])).

fof(f2322,plain,
    ( spl13_20
  <=> sP1(sK3,sK4,sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_20])])).

fof(f270,plain,
    ( ~ sP1(sK3,sK5,sK4)
    | ~ spl13_25 ),
    inference(avatar_component_clause,[],[f269])).

fof(f269,plain,
    ( spl13_25
  <=> ~ sP1(sK3,sK5,sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_25])])).

fof(f9562,plain,
    ( ~ spl13_2
    | spl13_5
    | ~ spl13_6
    | ~ spl13_8
    | ~ spl13_10
    | ~ spl13_114
    | ~ spl13_192 ),
    inference(avatar_contradiction_clause,[],[f9561])).

fof(f9561,plain,
    ( $false
    | ~ spl13_2
    | ~ spl13_5
    | ~ spl13_6
    | ~ spl13_8
    | ~ spl13_10
    | ~ spl13_114
    | ~ spl13_192 ),
    inference(subsumption_resolution,[],[f9560,f80])).

fof(f9560,plain,
    ( ~ l1_orders_2(sK3)
    | ~ spl13_2
    | ~ spl13_5
    | ~ spl13_6
    | ~ spl13_8
    | ~ spl13_10
    | ~ spl13_114
    | ~ spl13_192 ),
    inference(subsumption_resolution,[],[f9559,f83])).

fof(f83,plain,(
    m1_subset_1(sK6,u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f56])).

fof(f9559,plain,
    ( ~ m1_subset_1(sK6,u1_struct_0(sK3))
    | ~ l1_orders_2(sK3)
    | ~ spl13_2
    | ~ spl13_5
    | ~ spl13_6
    | ~ spl13_8
    | ~ spl13_10
    | ~ spl13_114
    | ~ spl13_192 ),
    inference(subsumption_resolution,[],[f9558,f81])).

fof(f9558,plain,
    ( ~ m1_subset_1(sK4,u1_struct_0(sK3))
    | ~ m1_subset_1(sK6,u1_struct_0(sK3))
    | ~ l1_orders_2(sK3)
    | ~ spl13_2
    | ~ spl13_5
    | ~ spl13_6
    | ~ spl13_8
    | ~ spl13_10
    | ~ spl13_114
    | ~ spl13_192 ),
    inference(subsumption_resolution,[],[f9557,f82])).

fof(f9557,plain,
    ( ~ m1_subset_1(sK5,u1_struct_0(sK3))
    | ~ m1_subset_1(sK4,u1_struct_0(sK3))
    | ~ m1_subset_1(sK6,u1_struct_0(sK3))
    | ~ l1_orders_2(sK3)
    | ~ spl13_2
    | ~ spl13_5
    | ~ spl13_6
    | ~ spl13_8
    | ~ spl13_10
    | ~ spl13_114
    | ~ spl13_192 ),
    inference(subsumption_resolution,[],[f9556,f144])).

fof(f144,plain,
    ( r1_orders_2(sK3,sK6,sK4)
    | ~ spl13_10 ),
    inference(avatar_component_clause,[],[f143])).

fof(f143,plain,
    ( spl13_10
  <=> r1_orders_2(sK3,sK6,sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_10])])).

fof(f9556,plain,
    ( ~ r1_orders_2(sK3,sK6,sK4)
    | ~ m1_subset_1(sK5,u1_struct_0(sK3))
    | ~ m1_subset_1(sK4,u1_struct_0(sK3))
    | ~ m1_subset_1(sK6,u1_struct_0(sK3))
    | ~ l1_orders_2(sK3)
    | ~ spl13_2
    | ~ spl13_5
    | ~ spl13_6
    | ~ spl13_8
    | ~ spl13_114
    | ~ spl13_192 ),
    inference(subsumption_resolution,[],[f9555,f140])).

fof(f140,plain,
    ( r1_orders_2(sK3,sK6,sK5)
    | ~ spl13_8 ),
    inference(avatar_component_clause,[],[f139])).

fof(f139,plain,
    ( spl13_8
  <=> r1_orders_2(sK3,sK6,sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_8])])).

fof(f9555,plain,
    ( ~ r1_orders_2(sK3,sK6,sK5)
    | ~ r1_orders_2(sK3,sK6,sK4)
    | ~ m1_subset_1(sK5,u1_struct_0(sK3))
    | ~ m1_subset_1(sK4,u1_struct_0(sK3))
    | ~ m1_subset_1(sK6,u1_struct_0(sK3))
    | ~ l1_orders_2(sK3)
    | ~ spl13_2
    | ~ spl13_5
    | ~ spl13_6
    | ~ spl13_114
    | ~ spl13_192 ),
    inference(resolution,[],[f9234,f102])).

fof(f102,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_lattice3(X0,k2_tarski(X2,X3),X1)
      | ~ r1_orders_2(X0,X1,X3)
      | ~ r1_orders_2(X0,X1,X2)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
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
    inference(flattening,[],[f32])).

fof(f32,plain,(
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
    inference(ennf_transformation,[],[f22])).

fof(f22,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/yellow_0__t19_yellow_0.p',t8_yellow_0)).

fof(f9234,plain,
    ( ~ r1_lattice3(sK3,k2_tarski(sK4,sK5),sK6)
    | ~ spl13_2
    | ~ spl13_5
    | ~ spl13_6
    | ~ spl13_114
    | ~ spl13_192 ),
    inference(subsumption_resolution,[],[f9233,f132])).

fof(f132,plain,
    ( ~ r2_yellow_0(sK3,k2_tarski(sK4,sK5))
    | ~ spl13_5 ),
    inference(avatar_component_clause,[],[f131])).

fof(f131,plain,
    ( spl13_5
  <=> ~ r2_yellow_0(sK3,k2_tarski(sK4,sK5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_5])])).

fof(f9233,plain,
    ( ~ r1_lattice3(sK3,k2_tarski(sK4,sK5),sK6)
    | r2_yellow_0(sK3,k2_tarski(sK4,sK5))
    | ~ spl13_2
    | ~ spl13_5
    | ~ spl13_6
    | ~ spl13_114
    | ~ spl13_192 ),
    inference(subsumption_resolution,[],[f9232,f83])).

fof(f9232,plain,
    ( ~ r1_lattice3(sK3,k2_tarski(sK4,sK5),sK6)
    | ~ m1_subset_1(sK6,u1_struct_0(sK3))
    | r2_yellow_0(sK3,k2_tarski(sK4,sK5))
    | ~ spl13_2
    | ~ spl13_5
    | ~ spl13_6
    | ~ spl13_114
    | ~ spl13_192 ),
    inference(duplicate_literal_removal,[],[f9180])).

fof(f9180,plain,
    ( ~ r1_lattice3(sK3,k2_tarski(sK4,sK5),sK6)
    | ~ m1_subset_1(sK6,u1_struct_0(sK3))
    | ~ r1_lattice3(sK3,k2_tarski(sK4,sK5),sK6)
    | r2_yellow_0(sK3,k2_tarski(sK4,sK5))
    | ~ spl13_2
    | ~ spl13_5
    | ~ spl13_6
    | ~ spl13_114
    | ~ spl13_192 ),
    inference(resolution,[],[f3821,f5731])).

fof(f5731,plain,
    ( ! [X38] :
        ( ~ r1_orders_2(sK3,sK9(sK3,X38,sK6),sK6)
        | ~ r1_lattice3(sK3,X38,sK6)
        | r2_yellow_0(sK3,X38) )
    | ~ spl13_2
    | ~ spl13_114
    | ~ spl13_192 ),
    inference(forward_demodulation,[],[f5730,f4962])).

fof(f4962,plain,
    ( k11_lattice3(sK3,sK6,sK6) = sK6
    | ~ spl13_192 ),
    inference(avatar_component_clause,[],[f4961])).

fof(f4961,plain,
    ( spl13_192
  <=> k11_lattice3(sK3,sK6,sK6) = sK6 ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_192])])).

fof(f5730,plain,
    ( ! [X38] :
        ( ~ r1_orders_2(sK3,sK9(sK3,X38,sK6),sK6)
        | r2_yellow_0(sK3,X38)
        | ~ r1_lattice3(sK3,X38,k11_lattice3(sK3,sK6,sK6)) )
    | ~ spl13_2
    | ~ spl13_114
    | ~ spl13_192 ),
    inference(duplicate_literal_removal,[],[f5729])).

fof(f5729,plain,
    ( ! [X38] :
        ( ~ r1_orders_2(sK3,sK9(sK3,X38,sK6),sK6)
        | ~ r1_orders_2(sK3,sK9(sK3,X38,sK6),sK6)
        | r2_yellow_0(sK3,X38)
        | ~ r1_lattice3(sK3,X38,k11_lattice3(sK3,sK6,sK6)) )
    | ~ spl13_2
    | ~ spl13_114
    | ~ spl13_192 ),
    inference(forward_demodulation,[],[f5728,f4962])).

fof(f5728,plain,
    ( ! [X38] :
        ( ~ r1_orders_2(sK3,sK9(sK3,X38,sK6),sK6)
        | ~ r1_orders_2(sK3,sK9(sK3,X38,k11_lattice3(sK3,sK6,sK6)),sK6)
        | r2_yellow_0(sK3,X38)
        | ~ r1_lattice3(sK3,X38,k11_lattice3(sK3,sK6,sK6)) )
    | ~ spl13_2
    | ~ spl13_114
    | ~ spl13_192 ),
    inference(subsumption_resolution,[],[f5727,f79])).

fof(f5727,plain,
    ( ! [X38] :
        ( ~ r1_orders_2(sK3,sK9(sK3,X38,sK6),sK6)
        | ~ r1_orders_2(sK3,sK9(sK3,X38,k11_lattice3(sK3,sK6,sK6)),sK6)
        | r2_yellow_0(sK3,X38)
        | ~ r1_lattice3(sK3,X38,k11_lattice3(sK3,sK6,sK6))
        | ~ v5_orders_2(sK3) )
    | ~ spl13_2
    | ~ spl13_114
    | ~ spl13_192 ),
    inference(subsumption_resolution,[],[f5726,f80])).

fof(f5726,plain,
    ( ! [X38] :
        ( ~ r1_orders_2(sK3,sK9(sK3,X38,sK6),sK6)
        | ~ r1_orders_2(sK3,sK9(sK3,X38,k11_lattice3(sK3,sK6,sK6)),sK6)
        | ~ l1_orders_2(sK3)
        | r2_yellow_0(sK3,X38)
        | ~ r1_lattice3(sK3,X38,k11_lattice3(sK3,sK6,sK6))
        | ~ v5_orders_2(sK3) )
    | ~ spl13_2
    | ~ spl13_114
    | ~ spl13_192 ),
    inference(subsumption_resolution,[],[f5725,f83])).

fof(f5725,plain,
    ( ! [X38] :
        ( ~ r1_orders_2(sK3,sK9(sK3,X38,sK6),sK6)
        | ~ r1_orders_2(sK3,sK9(sK3,X38,k11_lattice3(sK3,sK6,sK6)),sK6)
        | ~ m1_subset_1(sK6,u1_struct_0(sK3))
        | ~ l1_orders_2(sK3)
        | r2_yellow_0(sK3,X38)
        | ~ r1_lattice3(sK3,X38,k11_lattice3(sK3,sK6,sK6))
        | ~ v5_orders_2(sK3) )
    | ~ spl13_2
    | ~ spl13_114
    | ~ spl13_192 ),
    inference(subsumption_resolution,[],[f5569,f3134])).

fof(f3134,plain,
    ( sP1(sK3,sK6,sK6)
    | ~ spl13_2
    | ~ spl13_114 ),
    inference(subsumption_resolution,[],[f3133,f80])).

fof(f3133,plain,
    ( sP1(sK3,sK6,sK6)
    | ~ l1_orders_2(sK3)
    | ~ spl13_2
    | ~ spl13_114 ),
    inference(subsumption_resolution,[],[f3132,f79])).

fof(f3132,plain,
    ( sP1(sK3,sK6,sK6)
    | ~ v5_orders_2(sK3)
    | ~ l1_orders_2(sK3)
    | ~ spl13_2
    | ~ spl13_114 ),
    inference(subsumption_resolution,[],[f3131,f83])).

fof(f3131,plain,
    ( sP1(sK3,sK6,sK6)
    | ~ m1_subset_1(sK6,u1_struct_0(sK3))
    | ~ v5_orders_2(sK3)
    | ~ l1_orders_2(sK3)
    | ~ spl13_2
    | ~ spl13_114 ),
    inference(subsumption_resolution,[],[f3130,f3123])).

fof(f3123,plain,
    ( r1_orders_2(sK3,sK6,sK6)
    | ~ spl13_2
    | ~ spl13_114 ),
    inference(forward_demodulation,[],[f3018,f3029])).

fof(f3029,plain,
    ( k11_lattice3(sK3,sK4,sK5) = sK6
    | ~ spl13_2 ),
    inference(avatar_component_clause,[],[f3028])).

fof(f3028,plain,
    ( spl13_2
  <=> k11_lattice3(sK3,sK4,sK5) = sK6 ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_2])])).

fof(f3018,plain,
    ( r1_orders_2(sK3,k11_lattice3(sK3,sK4,sK5),sK6)
    | ~ spl13_114 ),
    inference(avatar_component_clause,[],[f3017])).

fof(f3017,plain,
    ( spl13_114
  <=> r1_orders_2(sK3,k11_lattice3(sK3,sK4,sK5),sK6) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_114])])).

fof(f3130,plain,
    ( ~ r1_orders_2(sK3,sK6,sK6)
    | sP1(sK3,sK6,sK6)
    | ~ m1_subset_1(sK6,u1_struct_0(sK3))
    | ~ v5_orders_2(sK3)
    | ~ l1_orders_2(sK3)
    | ~ spl13_2
    | ~ spl13_114 ),
    inference(duplicate_literal_removal,[],[f3127])).

fof(f3127,plain,
    ( ~ r1_orders_2(sK3,sK6,sK6)
    | sP1(sK3,sK6,sK6)
    | ~ m1_subset_1(sK6,u1_struct_0(sK3))
    | ~ m1_subset_1(sK6,u1_struct_0(sK3))
    | ~ v5_orders_2(sK3)
    | ~ l1_orders_2(sK3)
    | ~ spl13_2
    | ~ spl13_114 ),
    inference(resolution,[],[f3123,f283])).

fof(f283,plain,(
    ! [X4,X5,X3] :
      ( ~ r1_orders_2(X3,X4,X5)
      | ~ r1_orders_2(X3,X4,X4)
      | sP1(X3,X4,X5)
      | ~ m1_subset_1(X4,u1_struct_0(X3))
      | ~ m1_subset_1(X5,u1_struct_0(X3))
      | ~ v5_orders_2(X3)
      | ~ l1_orders_2(X3) ) ),
    inference(duplicate_literal_removal,[],[f280])).

fof(f280,plain,(
    ! [X4,X5,X3] :
      ( sP1(X3,X4,X5)
      | ~ r1_orders_2(X3,X4,X4)
      | ~ r1_orders_2(X3,X4,X5)
      | ~ m1_subset_1(X4,u1_struct_0(X3))
      | ~ m1_subset_1(X4,u1_struct_0(X3))
      | ~ m1_subset_1(X5,u1_struct_0(X3))
      | ~ v5_orders_2(X3)
      | ~ l1_orders_2(X3)
      | sP1(X3,X4,X5)
      | ~ r1_orders_2(X3,X4,X4)
      | ~ r1_orders_2(X3,X4,X5)
      | ~ m1_subset_1(X4,u1_struct_0(X3))
      | ~ m1_subset_1(X4,u1_struct_0(X3))
      | ~ m1_subset_1(X5,u1_struct_0(X3))
      | ~ v5_orders_2(X3)
      | ~ l1_orders_2(X3) ) ),
    inference(resolution,[],[f99,f98])).

fof(f5569,plain,
    ( ! [X38] :
        ( ~ r1_orders_2(sK3,sK9(sK3,X38,sK6),sK6)
        | ~ r1_orders_2(sK3,sK9(sK3,X38,k11_lattice3(sK3,sK6,sK6)),sK6)
        | ~ sP1(sK3,sK6,sK6)
        | ~ m1_subset_1(sK6,u1_struct_0(sK3))
        | ~ l1_orders_2(sK3)
        | r2_yellow_0(sK3,X38)
        | ~ r1_lattice3(sK3,X38,k11_lattice3(sK3,sK6,sK6))
        | ~ v5_orders_2(sK3) )
    | ~ spl13_192 ),
    inference(duplicate_literal_removal,[],[f5481])).

fof(f5481,plain,
    ( ! [X38] :
        ( ~ r1_orders_2(sK3,sK9(sK3,X38,sK6),sK6)
        | ~ r1_orders_2(sK3,sK9(sK3,X38,k11_lattice3(sK3,sK6,sK6)),sK6)
        | ~ sP1(sK3,sK6,sK6)
        | ~ m1_subset_1(sK6,u1_struct_0(sK3))
        | ~ m1_subset_1(sK6,u1_struct_0(sK3))
        | ~ l1_orders_2(sK3)
        | r2_yellow_0(sK3,X38)
        | ~ r1_lattice3(sK3,X38,k11_lattice3(sK3,sK6,sK6))
        | ~ v5_orders_2(sK3) )
    | ~ spl13_192 ),
    inference(superposition,[],[f500,f4962])).

fof(f500,plain,(
    ! [X26,X24,X23,X25] :
      ( ~ r1_orders_2(X23,sK9(X23,X24,k11_lattice3(X23,X25,X26)),X26)
      | ~ r1_orders_2(X23,sK9(X23,X24,k11_lattice3(X23,X25,X26)),X25)
      | ~ sP1(X23,X26,X25)
      | ~ m1_subset_1(X26,u1_struct_0(X23))
      | ~ m1_subset_1(X25,u1_struct_0(X23))
      | ~ l1_orders_2(X23)
      | r2_yellow_0(X23,X24)
      | ~ r1_lattice3(X23,X24,k11_lattice3(X23,X25,X26))
      | ~ v5_orders_2(X23) ) ),
    inference(subsumption_resolution,[],[f499,f119])).

fof(f499,plain,(
    ! [X26,X24,X23,X25] :
      ( ~ r1_orders_2(X23,sK9(X23,X24,k11_lattice3(X23,X25,X26)),X25)
      | ~ r1_orders_2(X23,sK9(X23,X24,k11_lattice3(X23,X25,X26)),X26)
      | ~ sP1(X23,X26,X25)
      | ~ m1_subset_1(X26,u1_struct_0(X23))
      | ~ m1_subset_1(X25,u1_struct_0(X23))
      | ~ l1_orders_2(X23)
      | r2_yellow_0(X23,X24)
      | ~ r1_lattice3(X23,X24,k11_lattice3(X23,X25,X26))
      | ~ m1_subset_1(k11_lattice3(X23,X25,X26),u1_struct_0(X23))
      | ~ v5_orders_2(X23) ) ),
    inference(subsumption_resolution,[],[f486,f109])).

fof(f109,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(sK9(X0,X1,X2),u1_struct_0(X0))
      | r2_yellow_0(X0,X1)
      | ~ r1_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f68])).

fof(f68,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r2_yellow_0(X0,X1)
            | ! [X2] :
                ( ( ~ r1_orders_2(X0,sK9(X0,X1,X2),X2)
                  & r1_lattice3(X0,X1,sK9(X0,X1,X2))
                  & m1_subset_1(sK9(X0,X1,X2),u1_struct_0(X0)) )
                | ~ r1_lattice3(X0,X1,X2)
                | ~ m1_subset_1(X2,u1_struct_0(X0)) ) )
          & ( ( ! [X5] :
                  ( r1_orders_2(X0,X5,sK10(X0,X1))
                  | ~ r1_lattice3(X0,X1,X5)
                  | ~ m1_subset_1(X5,u1_struct_0(X0)) )
              & r1_lattice3(X0,X1,sK10(X0,X1))
              & m1_subset_1(sK10(X0,X1),u1_struct_0(X0)) )
            | ~ r2_yellow_0(X0,X1) ) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK9,sK10])],[f65,f67,f66])).

fof(f66,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r1_orders_2(X0,X3,X2)
          & r1_lattice3(X0,X1,X3)
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ~ r1_orders_2(X0,sK9(X0,X1,X2),X2)
        & r1_lattice3(X0,X1,sK9(X0,X1,X2))
        & m1_subset_1(sK9(X0,X1,X2),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f67,plain,(
    ! [X1,X0] :
      ( ? [X4] :
          ( ! [X5] :
              ( r1_orders_2(X0,X5,X4)
              | ~ r1_lattice3(X0,X1,X5)
              | ~ m1_subset_1(X5,u1_struct_0(X0)) )
          & r1_lattice3(X0,X1,X4)
          & m1_subset_1(X4,u1_struct_0(X0)) )
     => ( ! [X5] :
            ( r1_orders_2(X0,X5,sK10(X0,X1))
            | ~ r1_lattice3(X0,X1,X5)
            | ~ m1_subset_1(X5,u1_struct_0(X0)) )
        & r1_lattice3(X0,X1,sK10(X0,X1))
        & m1_subset_1(sK10(X0,X1),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f65,plain,(
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
    inference(rectify,[],[f64])).

fof(f64,plain,(
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
    inference(nnf_transformation,[],[f35])).

fof(f35,plain,(
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
    inference(flattening,[],[f34])).

fof(f34,plain,(
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
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/yellow_0__t19_yellow_0.p',t16_yellow_0)).

fof(f486,plain,(
    ! [X26,X24,X23,X25] :
      ( ~ r1_orders_2(X23,sK9(X23,X24,k11_lattice3(X23,X25,X26)),X25)
      | ~ m1_subset_1(sK9(X23,X24,k11_lattice3(X23,X25,X26)),u1_struct_0(X23))
      | ~ r1_orders_2(X23,sK9(X23,X24,k11_lattice3(X23,X25,X26)),X26)
      | ~ sP1(X23,X26,X25)
      | ~ m1_subset_1(X26,u1_struct_0(X23))
      | ~ m1_subset_1(X25,u1_struct_0(X23))
      | ~ l1_orders_2(X23)
      | r2_yellow_0(X23,X24)
      | ~ r1_lattice3(X23,X24,k11_lattice3(X23,X25,X26))
      | ~ m1_subset_1(k11_lattice3(X23,X25,X26),u1_struct_0(X23))
      | ~ v5_orders_2(X23) ) ),
    inference(duplicate_literal_removal,[],[f480])).

fof(f480,plain,(
    ! [X26,X24,X23,X25] :
      ( ~ r1_orders_2(X23,sK9(X23,X24,k11_lattice3(X23,X25,X26)),X25)
      | ~ m1_subset_1(sK9(X23,X24,k11_lattice3(X23,X25,X26)),u1_struct_0(X23))
      | ~ r1_orders_2(X23,sK9(X23,X24,k11_lattice3(X23,X25,X26)),X26)
      | ~ sP1(X23,X26,X25)
      | ~ m1_subset_1(X26,u1_struct_0(X23))
      | ~ m1_subset_1(X25,u1_struct_0(X23))
      | ~ l1_orders_2(X23)
      | r2_yellow_0(X23,X24)
      | ~ r1_lattice3(X23,X24,k11_lattice3(X23,X25,X26))
      | ~ m1_subset_1(k11_lattice3(X23,X25,X26),u1_struct_0(X23))
      | ~ l1_orders_2(X23)
      | ~ v5_orders_2(X23) ) ),
    inference(resolution,[],[f259,f111])).

fof(f111,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_orders_2(X0,sK9(X0,X1,X2),X2)
      | r2_yellow_0(X0,X1)
      | ~ r1_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f68])).

fof(f3821,plain,
    ( ! [X0] :
        ( r1_orders_2(sK3,sK9(sK3,k2_tarski(sK4,sK5),X0),sK6)
        | ~ r1_lattice3(sK3,k2_tarski(sK4,sK5),X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK3)) )
    | ~ spl13_5
    | ~ spl13_6 ),
    inference(subsumption_resolution,[],[f3820,f79])).

fof(f3820,plain,
    ( ! [X0] :
        ( r1_orders_2(sK3,sK9(sK3,k2_tarski(sK4,sK5),X0),sK6)
        | ~ r1_lattice3(sK3,k2_tarski(sK4,sK5),X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK3))
        | ~ v5_orders_2(sK3) )
    | ~ spl13_5
    | ~ spl13_6 ),
    inference(subsumption_resolution,[],[f3819,f80])).

fof(f3819,plain,
    ( ! [X0] :
        ( r1_orders_2(sK3,sK9(sK3,k2_tarski(sK4,sK5),X0),sK6)
        | ~ r1_lattice3(sK3,k2_tarski(sK4,sK5),X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK3))
        | ~ l1_orders_2(sK3)
        | ~ v5_orders_2(sK3) )
    | ~ spl13_5
    | ~ spl13_6 ),
    inference(subsumption_resolution,[],[f3818,f132])).

fof(f3818,plain,
    ( ! [X0] :
        ( r1_orders_2(sK3,sK9(sK3,k2_tarski(sK4,sK5),X0),sK6)
        | ~ r1_lattice3(sK3,k2_tarski(sK4,sK5),X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK3))
        | r2_yellow_0(sK3,k2_tarski(sK4,sK5))
        | ~ l1_orders_2(sK3)
        | ~ v5_orders_2(sK3) )
    | ~ spl13_5
    | ~ spl13_6 ),
    inference(duplicate_literal_removal,[],[f3817])).

fof(f3817,plain,
    ( ! [X0] :
        ( r1_orders_2(sK3,sK9(sK3,k2_tarski(sK4,sK5),X0),sK6)
        | ~ r1_lattice3(sK3,k2_tarski(sK4,sK5),X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK3))
        | r2_yellow_0(sK3,k2_tarski(sK4,sK5))
        | ~ r1_lattice3(sK3,k2_tarski(sK4,sK5),X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK3))
        | ~ l1_orders_2(sK3)
        | ~ v5_orders_2(sK3) )
    | ~ spl13_5
    | ~ spl13_6 ),
    inference(resolution,[],[f3222,f109])).

fof(f3222,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK9(sK3,k2_tarski(sK4,sK5),X0),u1_struct_0(sK3))
        | r1_orders_2(sK3,sK9(sK3,k2_tarski(sK4,sK5),X0),sK6)
        | ~ r1_lattice3(sK3,k2_tarski(sK4,sK5),X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK3)) )
    | ~ spl13_5
    | ~ spl13_6 ),
    inference(duplicate_literal_removal,[],[f3221])).

fof(f3221,plain,
    ( ! [X0] :
        ( ~ r1_lattice3(sK3,k2_tarski(sK4,sK5),X0)
        | r1_orders_2(sK3,sK9(sK3,k2_tarski(sK4,sK5),X0),sK6)
        | ~ m1_subset_1(sK9(sK3,k2_tarski(sK4,sK5),X0),u1_struct_0(sK3))
        | ~ m1_subset_1(X0,u1_struct_0(sK3))
        | ~ r1_lattice3(sK3,k2_tarski(sK4,sK5),X0) )
    | ~ spl13_5
    | ~ spl13_6 ),
    inference(forward_demodulation,[],[f3220,f113])).

fof(f113,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/yellow_0__t19_yellow_0.p',commutativity_k2_tarski)).

fof(f3220,plain,
    ( ! [X0] :
        ( r1_orders_2(sK3,sK9(sK3,k2_tarski(sK4,sK5),X0),sK6)
        | ~ m1_subset_1(sK9(sK3,k2_tarski(sK4,sK5),X0),u1_struct_0(sK3))
        | ~ r1_lattice3(sK3,k2_tarski(sK5,sK4),X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK3))
        | ~ r1_lattice3(sK3,k2_tarski(sK4,sK5),X0) )
    | ~ spl13_5
    | ~ spl13_6 ),
    inference(subsumption_resolution,[],[f3219,f132])).

fof(f3219,plain,
    ( ! [X0] :
        ( r2_yellow_0(sK3,k2_tarski(sK4,sK5))
        | r1_orders_2(sK3,sK9(sK3,k2_tarski(sK4,sK5),X0),sK6)
        | ~ m1_subset_1(sK9(sK3,k2_tarski(sK4,sK5),X0),u1_struct_0(sK3))
        | ~ r1_lattice3(sK3,k2_tarski(sK5,sK4),X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK3))
        | ~ r1_lattice3(sK3,k2_tarski(sK4,sK5),X0) )
    | ~ spl13_5
    | ~ spl13_6 ),
    inference(forward_demodulation,[],[f3218,f113])).

fof(f3218,plain,
    ( ! [X0] :
        ( r1_orders_2(sK3,sK9(sK3,k2_tarski(sK4,sK5),X0),sK6)
        | ~ m1_subset_1(sK9(sK3,k2_tarski(sK4,sK5),X0),u1_struct_0(sK3))
        | r2_yellow_0(sK3,k2_tarski(sK5,sK4))
        | ~ r1_lattice3(sK3,k2_tarski(sK5,sK4),X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK3))
        | ~ r1_lattice3(sK3,k2_tarski(sK4,sK5),X0) )
    | ~ spl13_5
    | ~ spl13_6 ),
    inference(forward_demodulation,[],[f3217,f113])).

fof(f3217,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK9(sK3,k2_tarski(sK4,sK5),X0),u1_struct_0(sK3))
        | r1_orders_2(sK3,sK9(sK3,k2_tarski(sK5,sK4),X0),sK6)
        | r2_yellow_0(sK3,k2_tarski(sK5,sK4))
        | ~ r1_lattice3(sK3,k2_tarski(sK5,sK4),X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK3))
        | ~ r1_lattice3(sK3,k2_tarski(sK4,sK5),X0) )
    | ~ spl13_5
    | ~ spl13_6 ),
    inference(forward_demodulation,[],[f3216,f113])).

fof(f3216,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK9(sK3,k2_tarski(sK5,sK4),X0),u1_struct_0(sK3))
        | r1_orders_2(sK3,sK9(sK3,k2_tarski(sK5,sK4),X0),sK6)
        | r2_yellow_0(sK3,k2_tarski(sK5,sK4))
        | ~ r1_lattice3(sK3,k2_tarski(sK5,sK4),X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK3))
        | ~ r1_lattice3(sK3,k2_tarski(sK4,sK5),X0) )
    | ~ spl13_5
    | ~ spl13_6 ),
    inference(subsumption_resolution,[],[f3215,f79])).

fof(f3215,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK9(sK3,k2_tarski(sK5,sK4),X0),u1_struct_0(sK3))
        | r1_orders_2(sK3,sK9(sK3,k2_tarski(sK5,sK4),X0),sK6)
        | r2_yellow_0(sK3,k2_tarski(sK5,sK4))
        | ~ r1_lattice3(sK3,k2_tarski(sK5,sK4),X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK3))
        | ~ r1_lattice3(sK3,k2_tarski(sK4,sK5),X0)
        | ~ v5_orders_2(sK3) )
    | ~ spl13_5
    | ~ spl13_6 ),
    inference(subsumption_resolution,[],[f3214,f132])).

fof(f3214,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK9(sK3,k2_tarski(sK5,sK4),X0),u1_struct_0(sK3))
        | r1_orders_2(sK3,sK9(sK3,k2_tarski(sK5,sK4),X0),sK6)
        | r2_yellow_0(sK3,k2_tarski(sK5,sK4))
        | ~ r1_lattice3(sK3,k2_tarski(sK5,sK4),X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK3))
        | r2_yellow_0(sK3,k2_tarski(sK4,sK5))
        | ~ r1_lattice3(sK3,k2_tarski(sK4,sK5),X0)
        | ~ v5_orders_2(sK3) )
    | ~ spl13_6 ),
    inference(subsumption_resolution,[],[f3213,f80])).

fof(f3213,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK9(sK3,k2_tarski(sK5,sK4),X0),u1_struct_0(sK3))
        | r1_orders_2(sK3,sK9(sK3,k2_tarski(sK5,sK4),X0),sK6)
        | r2_yellow_0(sK3,k2_tarski(sK5,sK4))
        | ~ r1_lattice3(sK3,k2_tarski(sK5,sK4),X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK3))
        | ~ l1_orders_2(sK3)
        | r2_yellow_0(sK3,k2_tarski(sK4,sK5))
        | ~ r1_lattice3(sK3,k2_tarski(sK4,sK5),X0)
        | ~ v5_orders_2(sK3) )
    | ~ spl13_6 ),
    inference(subsumption_resolution,[],[f3212,f82])).

fof(f3212,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK9(sK3,k2_tarski(sK5,sK4),X0),u1_struct_0(sK3))
        | r1_orders_2(sK3,sK9(sK3,k2_tarski(sK5,sK4),X0),sK6)
        | r2_yellow_0(sK3,k2_tarski(sK5,sK4))
        | ~ r1_lattice3(sK3,k2_tarski(sK5,sK4),X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK3))
        | ~ m1_subset_1(sK5,u1_struct_0(sK3))
        | ~ l1_orders_2(sK3)
        | r2_yellow_0(sK3,k2_tarski(sK4,sK5))
        | ~ r1_lattice3(sK3,k2_tarski(sK4,sK5),X0)
        | ~ v5_orders_2(sK3) )
    | ~ spl13_6 ),
    inference(subsumption_resolution,[],[f3211,f81])).

fof(f3211,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK9(sK3,k2_tarski(sK5,sK4),X0),u1_struct_0(sK3))
        | r1_orders_2(sK3,sK9(sK3,k2_tarski(sK5,sK4),X0),sK6)
        | ~ m1_subset_1(sK4,u1_struct_0(sK3))
        | r2_yellow_0(sK3,k2_tarski(sK5,sK4))
        | ~ r1_lattice3(sK3,k2_tarski(sK5,sK4),X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK3))
        | ~ m1_subset_1(sK5,u1_struct_0(sK3))
        | ~ l1_orders_2(sK3)
        | r2_yellow_0(sK3,k2_tarski(sK4,sK5))
        | ~ r1_lattice3(sK3,k2_tarski(sK4,sK5),X0)
        | ~ v5_orders_2(sK3) )
    | ~ spl13_6 ),
    inference(duplicate_literal_removal,[],[f3206])).

fof(f3206,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK9(sK3,k2_tarski(sK5,sK4),X0),u1_struct_0(sK3))
        | r1_orders_2(sK3,sK9(sK3,k2_tarski(sK5,sK4),X0),sK6)
        | ~ m1_subset_1(sK4,u1_struct_0(sK3))
        | r2_yellow_0(sK3,k2_tarski(sK5,sK4))
        | ~ r1_lattice3(sK3,k2_tarski(sK5,sK4),X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK3))
        | ~ m1_subset_1(sK5,u1_struct_0(sK3))
        | ~ m1_subset_1(sK4,u1_struct_0(sK3))
        | ~ l1_orders_2(sK3)
        | r2_yellow_0(sK3,k2_tarski(sK4,sK5))
        | ~ r1_lattice3(sK3,k2_tarski(sK4,sK5),X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK3))
        | ~ v5_orders_2(sK3) )
    | ~ spl13_6 ),
    inference(resolution,[],[f2261,f512])).

fof(f512,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_orders_2(X2,sK9(X2,k2_tarski(X1,X0),X3),X0)
      | ~ m1_subset_1(X1,u1_struct_0(X2))
      | ~ m1_subset_1(X0,u1_struct_0(X2))
      | ~ l1_orders_2(X2)
      | r2_yellow_0(X2,k2_tarski(X0,X1))
      | ~ r1_lattice3(X2,k2_tarski(X0,X1),X3)
      | ~ m1_subset_1(X3,u1_struct_0(X2))
      | ~ v5_orders_2(X2) ) ),
    inference(superposition,[],[f210,f113])).

fof(f210,plain,(
    ! [X6,X4,X5,X3] :
      ( r1_orders_2(X3,sK9(X3,k2_tarski(X4,X5),X6),X4)
      | ~ m1_subset_1(X5,u1_struct_0(X3))
      | ~ m1_subset_1(X4,u1_struct_0(X3))
      | ~ l1_orders_2(X3)
      | r2_yellow_0(X3,k2_tarski(X4,X5))
      | ~ r1_lattice3(X3,k2_tarski(X4,X5),X6)
      | ~ m1_subset_1(X6,u1_struct_0(X3))
      | ~ v5_orders_2(X3) ) ),
    inference(subsumption_resolution,[],[f207,f109])).

fof(f207,plain,(
    ! [X6,X4,X5,X3] :
      ( r1_orders_2(X3,sK9(X3,k2_tarski(X4,X5),X6),X4)
      | ~ m1_subset_1(X5,u1_struct_0(X3))
      | ~ m1_subset_1(X4,u1_struct_0(X3))
      | ~ m1_subset_1(sK9(X3,k2_tarski(X4,X5),X6),u1_struct_0(X3))
      | ~ l1_orders_2(X3)
      | r2_yellow_0(X3,k2_tarski(X4,X5))
      | ~ r1_lattice3(X3,k2_tarski(X4,X5),X6)
      | ~ m1_subset_1(X6,u1_struct_0(X3))
      | ~ v5_orders_2(X3) ) ),
    inference(duplicate_literal_removal,[],[f204])).

fof(f204,plain,(
    ! [X6,X4,X5,X3] :
      ( r1_orders_2(X3,sK9(X3,k2_tarski(X4,X5),X6),X4)
      | ~ m1_subset_1(X5,u1_struct_0(X3))
      | ~ m1_subset_1(X4,u1_struct_0(X3))
      | ~ m1_subset_1(sK9(X3,k2_tarski(X4,X5),X6),u1_struct_0(X3))
      | ~ l1_orders_2(X3)
      | r2_yellow_0(X3,k2_tarski(X4,X5))
      | ~ r1_lattice3(X3,k2_tarski(X4,X5),X6)
      | ~ m1_subset_1(X6,u1_struct_0(X3))
      | ~ l1_orders_2(X3)
      | ~ v5_orders_2(X3) ) ),
    inference(resolution,[],[f100,f110])).

fof(f110,plain,(
    ! [X2,X0,X1] :
      ( r1_lattice3(X0,X1,sK9(X0,X1,X2))
      | r2_yellow_0(X0,X1)
      | ~ r1_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f68])).

fof(f100,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r1_lattice3(X0,k2_tarski(X2,X3),X1)
      | r1_orders_2(X0,X1,X2)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f2261,plain,
    ( ! [X24,X25] :
        ( ~ r1_orders_2(sK3,sK9(sK3,k2_tarski(sK5,X24),X25),sK4)
        | ~ m1_subset_1(sK9(sK3,k2_tarski(sK5,X24),X25),u1_struct_0(sK3))
        | r1_orders_2(sK3,sK9(sK3,k2_tarski(sK5,X24),X25),sK6)
        | ~ m1_subset_1(X24,u1_struct_0(sK3))
        | r2_yellow_0(sK3,k2_tarski(sK5,X24))
        | ~ r1_lattice3(sK3,k2_tarski(sK5,X24),X25)
        | ~ m1_subset_1(X25,u1_struct_0(sK3)) )
    | ~ spl13_6 ),
    inference(subsumption_resolution,[],[f2260,f79])).

fof(f2260,plain,
    ( ! [X24,X25] :
        ( ~ m1_subset_1(sK9(sK3,k2_tarski(sK5,X24),X25),u1_struct_0(sK3))
        | ~ r1_orders_2(sK3,sK9(sK3,k2_tarski(sK5,X24),X25),sK4)
        | r1_orders_2(sK3,sK9(sK3,k2_tarski(sK5,X24),X25),sK6)
        | ~ m1_subset_1(X24,u1_struct_0(sK3))
        | r2_yellow_0(sK3,k2_tarski(sK5,X24))
        | ~ r1_lattice3(sK3,k2_tarski(sK5,X24),X25)
        | ~ m1_subset_1(X25,u1_struct_0(sK3))
        | ~ v5_orders_2(sK3) )
    | ~ spl13_6 ),
    inference(subsumption_resolution,[],[f2259,f80])).

fof(f2259,plain,
    ( ! [X24,X25] :
        ( ~ m1_subset_1(sK9(sK3,k2_tarski(sK5,X24),X25),u1_struct_0(sK3))
        | ~ r1_orders_2(sK3,sK9(sK3,k2_tarski(sK5,X24),X25),sK4)
        | r1_orders_2(sK3,sK9(sK3,k2_tarski(sK5,X24),X25),sK6)
        | ~ m1_subset_1(X24,u1_struct_0(sK3))
        | ~ l1_orders_2(sK3)
        | r2_yellow_0(sK3,k2_tarski(sK5,X24))
        | ~ r1_lattice3(sK3,k2_tarski(sK5,X24),X25)
        | ~ m1_subset_1(X25,u1_struct_0(sK3))
        | ~ v5_orders_2(sK3) )
    | ~ spl13_6 ),
    inference(subsumption_resolution,[],[f2223,f82])).

fof(f2223,plain,
    ( ! [X24,X25] :
        ( ~ m1_subset_1(sK9(sK3,k2_tarski(sK5,X24),X25),u1_struct_0(sK3))
        | ~ r1_orders_2(sK3,sK9(sK3,k2_tarski(sK5,X24),X25),sK4)
        | r1_orders_2(sK3,sK9(sK3,k2_tarski(sK5,X24),X25),sK6)
        | ~ m1_subset_1(X24,u1_struct_0(sK3))
        | ~ m1_subset_1(sK5,u1_struct_0(sK3))
        | ~ l1_orders_2(sK3)
        | r2_yellow_0(sK3,k2_tarski(sK5,X24))
        | ~ r1_lattice3(sK3,k2_tarski(sK5,X24),X25)
        | ~ m1_subset_1(X25,u1_struct_0(sK3))
        | ~ v5_orders_2(sK3) )
    | ~ spl13_6 ),
    inference(resolution,[],[f136,f210])).

fof(f136,plain,
    ( ! [X4] :
        ( ~ r1_orders_2(sK3,X4,sK5)
        | ~ m1_subset_1(X4,u1_struct_0(sK3))
        | ~ r1_orders_2(sK3,X4,sK4)
        | r1_orders_2(sK3,X4,sK6) )
    | ~ spl13_6 ),
    inference(avatar_component_clause,[],[f135])).

fof(f135,plain,
    ( spl13_6
  <=> ! [X4] :
        ( r1_orders_2(sK3,X4,sK6)
        | ~ m1_subset_1(X4,u1_struct_0(sK3))
        | ~ r1_orders_2(sK3,X4,sK4)
        | ~ r1_orders_2(sK3,X4,sK5) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_6])])).

fof(f5371,plain,
    ( spl13_192
    | ~ spl13_147
    | ~ spl13_195
    | ~ spl13_151
    | ~ spl13_2
    | ~ spl13_24
    | ~ spl13_26
    | ~ spl13_114 ),
    inference(avatar_split_clause,[],[f5370,f3017,f272,f2335,f3028,f4333,f4964,f4327,f4961])).

fof(f4327,plain,
    ( spl13_147
  <=> ~ r1_orders_2(sK3,k11_lattice3(sK3,sK6,sK6),sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_147])])).

fof(f4964,plain,
    ( spl13_195
  <=> ~ m1_subset_1(k11_lattice3(sK3,sK6,sK6),u1_struct_0(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_195])])).

fof(f4333,plain,
    ( spl13_151
  <=> ~ r1_orders_2(sK3,k11_lattice3(sK3,sK6,sK6),sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_151])])).

fof(f2335,plain,
    ( spl13_24
  <=> sP1(sK3,sK5,sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_24])])).

fof(f272,plain,
    ( spl13_26
  <=> ! [X0] :
        ( ~ r1_orders_2(sK3,X0,sK5)
        | r1_orders_2(sK3,sK7(sK3,sK5,sK4,X0),sK6)
        | k11_lattice3(sK3,sK4,sK5) = X0
        | ~ m1_subset_1(X0,u1_struct_0(sK3))
        | ~ r1_orders_2(sK3,X0,sK4) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_26])])).

fof(f5370,plain,
    ( ~ r1_orders_2(sK3,k11_lattice3(sK3,sK6,sK6),sK5)
    | ~ m1_subset_1(k11_lattice3(sK3,sK6,sK6),u1_struct_0(sK3))
    | ~ r1_orders_2(sK3,k11_lattice3(sK3,sK6,sK6),sK4)
    | k11_lattice3(sK3,sK6,sK6) = sK6
    | ~ spl13_2
    | ~ spl13_24
    | ~ spl13_26
    | ~ spl13_114 ),
    inference(subsumption_resolution,[],[f5369,f83])).

fof(f5369,plain,
    ( ~ r1_orders_2(sK3,k11_lattice3(sK3,sK6,sK6),sK5)
    | ~ m1_subset_1(k11_lattice3(sK3,sK6,sK6),u1_struct_0(sK3))
    | ~ r1_orders_2(sK3,k11_lattice3(sK3,sK6,sK6),sK4)
    | k11_lattice3(sK3,sK6,sK6) = sK6
    | ~ m1_subset_1(sK6,u1_struct_0(sK3))
    | ~ spl13_2
    | ~ spl13_24
    | ~ spl13_26
    | ~ spl13_114 ),
    inference(subsumption_resolution,[],[f5019,f3134])).

fof(f5019,plain,
    ( ~ r1_orders_2(sK3,k11_lattice3(sK3,sK6,sK6),sK5)
    | ~ m1_subset_1(k11_lattice3(sK3,sK6,sK6),u1_struct_0(sK3))
    | ~ r1_orders_2(sK3,k11_lattice3(sK3,sK6,sK6),sK4)
    | k11_lattice3(sK3,sK6,sK6) = sK6
    | ~ sP1(sK3,sK6,sK6)
    | ~ m1_subset_1(sK6,u1_struct_0(sK3))
    | ~ spl13_2
    | ~ spl13_24
    | ~ spl13_26 ),
    inference(duplicate_literal_removal,[],[f5004])).

fof(f5004,plain,
    ( ~ r1_orders_2(sK3,k11_lattice3(sK3,sK6,sK6),sK5)
    | ~ m1_subset_1(k11_lattice3(sK3,sK6,sK6),u1_struct_0(sK3))
    | ~ r1_orders_2(sK3,k11_lattice3(sK3,sK6,sK6),sK4)
    | k11_lattice3(sK3,sK6,sK6) = sK6
    | ~ sP1(sK3,sK6,sK6)
    | ~ m1_subset_1(sK6,u1_struct_0(sK3))
    | k11_lattice3(sK3,sK6,sK6) = sK6
    | ~ r1_orders_2(sK3,k11_lattice3(sK3,sK6,sK6),sK5)
    | ~ m1_subset_1(k11_lattice3(sK3,sK6,sK6),u1_struct_0(sK3))
    | ~ r1_orders_2(sK3,k11_lattice3(sK3,sK6,sK6),sK4)
    | ~ spl13_2
    | ~ spl13_24
    | ~ spl13_26 ),
    inference(resolution,[],[f3118,f3116])).

fof(f3116,plain,
    ( ! [X0] :
        ( r1_orders_2(sK3,sK7(sK3,sK5,sK4,X0),sK6)
        | sK6 = X0
        | ~ r1_orders_2(sK3,X0,sK5)
        | ~ m1_subset_1(X0,u1_struct_0(sK3))
        | ~ r1_orders_2(sK3,X0,sK4) )
    | ~ spl13_2
    | ~ spl13_26 ),
    inference(backward_demodulation,[],[f3029,f273])).

fof(f273,plain,
    ( ! [X0] :
        ( r1_orders_2(sK3,sK7(sK3,sK5,sK4,X0),sK6)
        | ~ r1_orders_2(sK3,X0,sK5)
        | k11_lattice3(sK3,sK4,sK5) = X0
        | ~ m1_subset_1(X0,u1_struct_0(sK3))
        | ~ r1_orders_2(sK3,X0,sK4) )
    | ~ spl13_26 ),
    inference(avatar_component_clause,[],[f272])).

fof(f3118,plain,
    ( ! [X2] :
        ( ~ r1_orders_2(sK3,sK7(sK3,sK5,sK4,k11_lattice3(sK3,X2,sK6)),X2)
        | ~ r1_orders_2(sK3,k11_lattice3(sK3,X2,sK6),sK5)
        | ~ m1_subset_1(k11_lattice3(sK3,X2,sK6),u1_struct_0(sK3))
        | ~ r1_orders_2(sK3,k11_lattice3(sK3,X2,sK6),sK4)
        | k11_lattice3(sK3,X2,sK6) = sK6
        | ~ sP1(sK3,sK6,X2)
        | ~ m1_subset_1(X2,u1_struct_0(sK3)) )
    | ~ spl13_2
    | ~ spl13_24
    | ~ spl13_26 ),
    inference(backward_demodulation,[],[f3029,f2609])).

fof(f2609,plain,
    ( ! [X2] :
        ( ~ r1_orders_2(sK3,k11_lattice3(sK3,X2,sK6),sK5)
        | k11_lattice3(sK3,sK4,sK5) = k11_lattice3(sK3,X2,sK6)
        | ~ m1_subset_1(k11_lattice3(sK3,X2,sK6),u1_struct_0(sK3))
        | ~ r1_orders_2(sK3,k11_lattice3(sK3,X2,sK6),sK4)
        | ~ r1_orders_2(sK3,sK7(sK3,sK5,sK4,k11_lattice3(sK3,X2,sK6)),X2)
        | ~ sP1(sK3,sK6,X2)
        | ~ m1_subset_1(X2,u1_struct_0(sK3)) )
    | ~ spl13_24
    | ~ spl13_26 ),
    inference(subsumption_resolution,[],[f2608,f2336])).

fof(f2336,plain,
    ( sP1(sK3,sK5,sK4)
    | ~ spl13_24 ),
    inference(avatar_component_clause,[],[f2335])).

fof(f2608,plain,
    ( ! [X2] :
        ( ~ r1_orders_2(sK3,k11_lattice3(sK3,X2,sK6),sK5)
        | k11_lattice3(sK3,sK4,sK5) = k11_lattice3(sK3,X2,sK6)
        | ~ m1_subset_1(k11_lattice3(sK3,X2,sK6),u1_struct_0(sK3))
        | ~ r1_orders_2(sK3,k11_lattice3(sK3,X2,sK6),sK4)
        | ~ r1_orders_2(sK3,sK7(sK3,sK5,sK4,k11_lattice3(sK3,X2,sK6)),X2)
        | ~ sP1(sK3,sK6,X2)
        | ~ m1_subset_1(X2,u1_struct_0(sK3))
        | ~ sP1(sK3,sK5,sK4) )
    | ~ spl13_26 ),
    inference(subsumption_resolution,[],[f2607,f80])).

fof(f2607,plain,
    ( ! [X2] :
        ( ~ r1_orders_2(sK3,k11_lattice3(sK3,X2,sK6),sK5)
        | k11_lattice3(sK3,sK4,sK5) = k11_lattice3(sK3,X2,sK6)
        | ~ m1_subset_1(k11_lattice3(sK3,X2,sK6),u1_struct_0(sK3))
        | ~ r1_orders_2(sK3,k11_lattice3(sK3,X2,sK6),sK4)
        | ~ r1_orders_2(sK3,sK7(sK3,sK5,sK4,k11_lattice3(sK3,X2,sK6)),X2)
        | ~ sP1(sK3,sK6,X2)
        | ~ m1_subset_1(X2,u1_struct_0(sK3))
        | ~ l1_orders_2(sK3)
        | ~ sP1(sK3,sK5,sK4) )
    | ~ spl13_26 ),
    inference(subsumption_resolution,[],[f2597,f83])).

fof(f2597,plain,
    ( ! [X2] :
        ( ~ r1_orders_2(sK3,k11_lattice3(sK3,X2,sK6),sK5)
        | k11_lattice3(sK3,sK4,sK5) = k11_lattice3(sK3,X2,sK6)
        | ~ m1_subset_1(k11_lattice3(sK3,X2,sK6),u1_struct_0(sK3))
        | ~ r1_orders_2(sK3,k11_lattice3(sK3,X2,sK6),sK4)
        | ~ r1_orders_2(sK3,sK7(sK3,sK5,sK4,k11_lattice3(sK3,X2,sK6)),X2)
        | ~ sP1(sK3,sK6,X2)
        | ~ m1_subset_1(sK6,u1_struct_0(sK3))
        | ~ m1_subset_1(X2,u1_struct_0(sK3))
        | ~ l1_orders_2(sK3)
        | ~ sP1(sK3,sK5,sK4) )
    | ~ spl13_26 ),
    inference(duplicate_literal_removal,[],[f2589])).

fof(f2589,plain,
    ( ! [X2] :
        ( ~ r1_orders_2(sK3,k11_lattice3(sK3,X2,sK6),sK5)
        | k11_lattice3(sK3,sK4,sK5) = k11_lattice3(sK3,X2,sK6)
        | ~ m1_subset_1(k11_lattice3(sK3,X2,sK6),u1_struct_0(sK3))
        | ~ r1_orders_2(sK3,k11_lattice3(sK3,X2,sK6),sK4)
        | ~ r1_orders_2(sK3,sK7(sK3,sK5,sK4,k11_lattice3(sK3,X2,sK6)),X2)
        | ~ sP1(sK3,sK6,X2)
        | ~ m1_subset_1(sK6,u1_struct_0(sK3))
        | ~ m1_subset_1(X2,u1_struct_0(sK3))
        | ~ l1_orders_2(sK3)
        | k11_lattice3(sK3,sK4,sK5) = k11_lattice3(sK3,X2,sK6)
        | ~ r1_orders_2(sK3,k11_lattice3(sK3,X2,sK6),sK5)
        | ~ r1_orders_2(sK3,k11_lattice3(sK3,X2,sK6),sK4)
        | ~ sP1(sK3,sK5,sK4) )
    | ~ spl13_26 ),
    inference(resolution,[],[f273,f496])).

fof(f496,plain,(
    ! [X14,X17,X15,X13,X16] :
      ( ~ r1_orders_2(X13,sK7(X13,X14,X15,k11_lattice3(X13,X16,X17)),X17)
      | ~ r1_orders_2(X13,sK7(X13,X14,X15,k11_lattice3(X13,X16,X17)),X16)
      | ~ sP1(X13,X17,X16)
      | ~ m1_subset_1(X17,u1_struct_0(X13))
      | ~ m1_subset_1(X16,u1_struct_0(X13))
      | ~ l1_orders_2(X13)
      | k11_lattice3(X13,X15,X14) = k11_lattice3(X13,X16,X17)
      | ~ r1_orders_2(X13,k11_lattice3(X13,X16,X17),X14)
      | ~ r1_orders_2(X13,k11_lattice3(X13,X16,X17),X15)
      | ~ sP1(X13,X14,X15) ) ),
    inference(subsumption_resolution,[],[f495,f119])).

fof(f495,plain,(
    ! [X14,X17,X15,X13,X16] :
      ( ~ r1_orders_2(X13,sK7(X13,X14,X15,k11_lattice3(X13,X16,X17)),X16)
      | ~ r1_orders_2(X13,sK7(X13,X14,X15,k11_lattice3(X13,X16,X17)),X17)
      | ~ sP1(X13,X17,X16)
      | ~ m1_subset_1(X17,u1_struct_0(X13))
      | ~ m1_subset_1(X16,u1_struct_0(X13))
      | ~ l1_orders_2(X13)
      | k11_lattice3(X13,X15,X14) = k11_lattice3(X13,X16,X17)
      | ~ r1_orders_2(X13,k11_lattice3(X13,X16,X17),X14)
      | ~ r1_orders_2(X13,k11_lattice3(X13,X16,X17),X15)
      | ~ m1_subset_1(k11_lattice3(X13,X16,X17),u1_struct_0(X13))
      | ~ sP1(X13,X14,X15) ) ),
    inference(subsumption_resolution,[],[f478,f92])).

fof(f92,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(sK7(X0,X1,X2,X3),u1_struct_0(X0))
      | k11_lattice3(X0,X2,X1) = X3
      | ~ r1_orders_2(X0,X3,X1)
      | ~ r1_orders_2(X0,X3,X2)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ sP1(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f61])).

fof(f478,plain,(
    ! [X14,X17,X15,X13,X16] :
      ( ~ r1_orders_2(X13,sK7(X13,X14,X15,k11_lattice3(X13,X16,X17)),X16)
      | ~ m1_subset_1(sK7(X13,X14,X15,k11_lattice3(X13,X16,X17)),u1_struct_0(X13))
      | ~ r1_orders_2(X13,sK7(X13,X14,X15,k11_lattice3(X13,X16,X17)),X17)
      | ~ sP1(X13,X17,X16)
      | ~ m1_subset_1(X17,u1_struct_0(X13))
      | ~ m1_subset_1(X16,u1_struct_0(X13))
      | ~ l1_orders_2(X13)
      | k11_lattice3(X13,X15,X14) = k11_lattice3(X13,X16,X17)
      | ~ r1_orders_2(X13,k11_lattice3(X13,X16,X17),X14)
      | ~ r1_orders_2(X13,k11_lattice3(X13,X16,X17),X15)
      | ~ m1_subset_1(k11_lattice3(X13,X16,X17),u1_struct_0(X13))
      | ~ sP1(X13,X14,X15) ) ),
    inference(resolution,[],[f259,f95])).

fof(f95,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r1_orders_2(X0,sK7(X0,X1,X2,X3),X3)
      | k11_lattice3(X0,X2,X1) = X3
      | ~ r1_orders_2(X0,X3,X1)
      | ~ r1_orders_2(X0,X3,X2)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ sP1(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f61])).

fof(f5356,plain,(
    spl13_195 ),
    inference(avatar_contradiction_clause,[],[f5355])).

fof(f5355,plain,
    ( $false
    | ~ spl13_195 ),
    inference(subsumption_resolution,[],[f5354,f80])).

fof(f5354,plain,
    ( ~ l1_orders_2(sK3)
    | ~ spl13_195 ),
    inference(subsumption_resolution,[],[f5353,f83])).

fof(f5353,plain,
    ( ~ m1_subset_1(sK6,u1_struct_0(sK3))
    | ~ l1_orders_2(sK3)
    | ~ spl13_195 ),
    inference(duplicate_literal_removal,[],[f5347])).

fof(f5347,plain,
    ( ~ m1_subset_1(sK6,u1_struct_0(sK3))
    | ~ m1_subset_1(sK6,u1_struct_0(sK3))
    | ~ l1_orders_2(sK3)
    | ~ spl13_195 ),
    inference(resolution,[],[f4965,f119])).

fof(f4965,plain,
    ( ~ m1_subset_1(k11_lattice3(sK3,sK6,sK6),u1_struct_0(sK3))
    | ~ spl13_195 ),
    inference(avatar_component_clause,[],[f4964])).

fof(f4884,plain,
    ( ~ spl13_2
    | ~ spl13_8
    | ~ spl13_114
    | spl13_151 ),
    inference(avatar_contradiction_clause,[],[f4883])).

fof(f4883,plain,
    ( $false
    | ~ spl13_2
    | ~ spl13_8
    | ~ spl13_114
    | ~ spl13_151 ),
    inference(subsumption_resolution,[],[f4882,f3134])).

fof(f4882,plain,
    ( ~ sP1(sK3,sK6,sK6)
    | ~ spl13_2
    | ~ spl13_8
    | ~ spl13_114
    | ~ spl13_151 ),
    inference(subsumption_resolution,[],[f4881,f83])).

fof(f4881,plain,
    ( ~ m1_subset_1(sK6,u1_struct_0(sK3))
    | ~ sP1(sK3,sK6,sK6)
    | ~ spl13_2
    | ~ spl13_8
    | ~ spl13_114
    | ~ spl13_151 ),
    inference(subsumption_resolution,[],[f4880,f3123])).

fof(f4880,plain,
    ( ~ r1_orders_2(sK3,sK6,sK6)
    | ~ m1_subset_1(sK6,u1_struct_0(sK3))
    | ~ sP1(sK3,sK6,sK6)
    | ~ spl13_8
    | ~ spl13_151 ),
    inference(subsumption_resolution,[],[f4873,f140])).

fof(f4873,plain,
    ( ~ r1_orders_2(sK3,sK6,sK5)
    | ~ r1_orders_2(sK3,sK6,sK6)
    | ~ m1_subset_1(sK6,u1_struct_0(sK3))
    | ~ sP1(sK3,sK6,sK6)
    | ~ spl13_151 ),
    inference(duplicate_literal_removal,[],[f4871])).

fof(f4871,plain,
    ( ~ r1_orders_2(sK3,sK6,sK5)
    | ~ r1_orders_2(sK3,sK6,sK6)
    | ~ r1_orders_2(sK3,sK6,sK6)
    | ~ m1_subset_1(sK6,u1_struct_0(sK3))
    | ~ sP1(sK3,sK6,sK6)
    | ~ spl13_151 ),
    inference(superposition,[],[f4334,f256])).

fof(f256,plain,(
    ! [X4,X5,X3] :
      ( k11_lattice3(X3,X4,X5) = X5
      | ~ r1_orders_2(X3,X5,X5)
      | ~ r1_orders_2(X3,X5,X4)
      | ~ m1_subset_1(X5,u1_struct_0(X3))
      | ~ sP1(X3,X5,X4) ) ),
    inference(duplicate_literal_removal,[],[f254])).

fof(f254,plain,(
    ! [X4,X5,X3] :
      ( k11_lattice3(X3,X4,X5) = X5
      | ~ r1_orders_2(X3,X5,X5)
      | ~ r1_orders_2(X3,X5,X4)
      | ~ m1_subset_1(X5,u1_struct_0(X3))
      | ~ sP1(X3,X5,X4)
      | k11_lattice3(X3,X4,X5) = X5
      | ~ r1_orders_2(X3,X5,X5)
      | ~ r1_orders_2(X3,X5,X4)
      | ~ m1_subset_1(X5,u1_struct_0(X3))
      | ~ sP1(X3,X5,X4) ) ),
    inference(resolution,[],[f95,f94])).

fof(f94,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_orders_2(X0,sK7(X0,X1,X2,X3),X1)
      | k11_lattice3(X0,X2,X1) = X3
      | ~ r1_orders_2(X0,X3,X1)
      | ~ r1_orders_2(X0,X3,X2)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ sP1(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f61])).

fof(f4334,plain,
    ( ~ r1_orders_2(sK3,k11_lattice3(sK3,sK6,sK6),sK5)
    | ~ spl13_151 ),
    inference(avatar_component_clause,[],[f4333])).

fof(f4763,plain,
    ( ~ spl13_2
    | ~ spl13_10
    | ~ spl13_114
    | spl13_147 ),
    inference(avatar_contradiction_clause,[],[f4762])).

fof(f4762,plain,
    ( $false
    | ~ spl13_2
    | ~ spl13_10
    | ~ spl13_114
    | ~ spl13_147 ),
    inference(subsumption_resolution,[],[f4761,f3134])).

fof(f4761,plain,
    ( ~ sP1(sK3,sK6,sK6)
    | ~ spl13_2
    | ~ spl13_10
    | ~ spl13_114
    | ~ spl13_147 ),
    inference(subsumption_resolution,[],[f4760,f83])).

fof(f4760,plain,
    ( ~ m1_subset_1(sK6,u1_struct_0(sK3))
    | ~ sP1(sK3,sK6,sK6)
    | ~ spl13_2
    | ~ spl13_10
    | ~ spl13_114
    | ~ spl13_147 ),
    inference(subsumption_resolution,[],[f4759,f3123])).

fof(f4759,plain,
    ( ~ r1_orders_2(sK3,sK6,sK6)
    | ~ m1_subset_1(sK6,u1_struct_0(sK3))
    | ~ sP1(sK3,sK6,sK6)
    | ~ spl13_10
    | ~ spl13_147 ),
    inference(subsumption_resolution,[],[f4752,f144])).

fof(f4752,plain,
    ( ~ r1_orders_2(sK3,sK6,sK4)
    | ~ r1_orders_2(sK3,sK6,sK6)
    | ~ m1_subset_1(sK6,u1_struct_0(sK3))
    | ~ sP1(sK3,sK6,sK6)
    | ~ spl13_147 ),
    inference(duplicate_literal_removal,[],[f4750])).

fof(f4750,plain,
    ( ~ r1_orders_2(sK3,sK6,sK4)
    | ~ r1_orders_2(sK3,sK6,sK6)
    | ~ r1_orders_2(sK3,sK6,sK6)
    | ~ m1_subset_1(sK6,u1_struct_0(sK3))
    | ~ sP1(sK3,sK6,sK6)
    | ~ spl13_147 ),
    inference(superposition,[],[f4328,f256])).

fof(f4328,plain,
    ( ~ r1_orders_2(sK3,k11_lattice3(sK3,sK6,sK6),sK4)
    | ~ spl13_147 ),
    inference(avatar_component_clause,[],[f4327])).

fof(f3122,plain,
    ( ~ spl13_2
    | spl13_117 ),
    inference(avatar_contradiction_clause,[],[f3121])).

fof(f3121,plain,
    ( $false
    | ~ spl13_2
    | ~ spl13_117 ),
    inference(subsumption_resolution,[],[f3115,f83])).

fof(f3115,plain,
    ( ~ m1_subset_1(sK6,u1_struct_0(sK3))
    | ~ spl13_2
    | ~ spl13_117 ),
    inference(backward_demodulation,[],[f3029,f3021])).

fof(f3021,plain,
    ( ~ m1_subset_1(k11_lattice3(sK3,sK4,sK5),u1_struct_0(sK3))
    | ~ spl13_117 ),
    inference(avatar_component_clause,[],[f3020])).

fof(f3020,plain,
    ( spl13_117
  <=> ~ m1_subset_1(k11_lattice3(sK3,sK4,sK5),u1_struct_0(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_117])])).

fof(f3106,plain,
    ( ~ spl13_0
    | ~ spl13_24 ),
    inference(avatar_contradiction_clause,[],[f3105])).

fof(f3105,plain,
    ( $false
    | ~ spl13_0
    | ~ spl13_24 ),
    inference(subsumption_resolution,[],[f3104,f2336])).

fof(f3104,plain,
    ( ~ sP1(sK3,sK5,sK4)
    | ~ spl13_0 ),
    inference(subsumption_resolution,[],[f3103,f80])).

fof(f3103,plain,
    ( ~ l1_orders_2(sK3)
    | ~ sP1(sK3,sK5,sK4)
    | ~ spl13_0 ),
    inference(subsumption_resolution,[],[f3102,f81])).

fof(f3102,plain,
    ( ~ m1_subset_1(sK4,u1_struct_0(sK3))
    | ~ l1_orders_2(sK3)
    | ~ sP1(sK3,sK5,sK4)
    | ~ spl13_0 ),
    inference(subsumption_resolution,[],[f3076,f82])).

fof(f3076,plain,
    ( ~ m1_subset_1(sK5,u1_struct_0(sK3))
    | ~ m1_subset_1(sK4,u1_struct_0(sK3))
    | ~ l1_orders_2(sK3)
    | ~ sP1(sK3,sK5,sK4)
    | ~ spl13_0 ),
    inference(resolution,[],[f126,f1686])).

fof(f1686,plain,(
    ! [X6,X8,X7,X9] :
      ( ~ sP0(X9,X6,X8,X7)
      | ~ m1_subset_1(X8,u1_struct_0(X6))
      | ~ m1_subset_1(X7,u1_struct_0(X6))
      | ~ l1_orders_2(X6)
      | ~ sP1(X6,X8,X7) ) ),
    inference(duplicate_literal_removal,[],[f1685])).

fof(f1685,plain,(
    ! [X6,X8,X7,X9] :
      ( ~ sP0(X9,X6,X8,X7)
      | ~ m1_subset_1(X8,u1_struct_0(X6))
      | ~ m1_subset_1(X7,u1_struct_0(X6))
      | ~ l1_orders_2(X6)
      | ~ sP1(X6,X8,X7)
      | ~ sP0(X9,X6,X8,X7) ) ),
    inference(superposition,[],[f1525,f73])).

fof(f73,plain,(
    ! [X2,X0,X3,X1] :
      ( k11_lattice3(X1,X3,X2) = X0
      | ~ sP0(X0,X1,X2,X3) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f51,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( ( ~ r1_orders_2(X1,sK2(X0,X1,X2,X3),X0)
            & r1_orders_2(X1,sK2(X0,X1,X2,X3),X2)
            & r1_orders_2(X1,sK2(X0,X1,X2,X3),X3)
            & m1_subset_1(sK2(X0,X1,X2,X3),u1_struct_0(X1)) )
          | ~ r1_orders_2(X1,X0,X2)
          | ~ r1_orders_2(X1,X0,X3) )
        & r2_yellow_0(X1,k2_tarski(X3,X2))
        & k11_lattice3(X1,X3,X2) = X0 )
      | ~ sP0(X0,X1,X2,X3) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f49,f50])).

fof(f50,plain,(
    ! [X3,X2,X1,X0] :
      ( ? [X4] :
          ( ~ r1_orders_2(X1,X4,X0)
          & r1_orders_2(X1,X4,X2)
          & r1_orders_2(X1,X4,X3)
          & m1_subset_1(X4,u1_struct_0(X1)) )
     => ( ~ r1_orders_2(X1,sK2(X0,X1,X2,X3),X0)
        & r1_orders_2(X1,sK2(X0,X1,X2,X3),X2)
        & r1_orders_2(X1,sK2(X0,X1,X2,X3),X3)
        & m1_subset_1(sK2(X0,X1,X2,X3),u1_struct_0(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f49,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( ? [X4] :
              ( ~ r1_orders_2(X1,X4,X0)
              & r1_orders_2(X1,X4,X2)
              & r1_orders_2(X1,X4,X3)
              & m1_subset_1(X4,u1_struct_0(X1)) )
          | ~ r1_orders_2(X1,X0,X2)
          | ~ r1_orders_2(X1,X0,X3) )
        & r2_yellow_0(X1,k2_tarski(X3,X2))
        & k11_lattice3(X1,X3,X2) = X0 )
      | ~ sP0(X0,X1,X2,X3) ) ),
    inference(rectify,[],[f48])).

fof(f48,plain,(
    ! [X3,X0,X2,X1] :
      ( ( ( ? [X5] :
              ( ~ r1_orders_2(X0,X5,X3)
              & r1_orders_2(X0,X5,X2)
              & r1_orders_2(X0,X5,X1)
              & m1_subset_1(X5,u1_struct_0(X0)) )
          | ~ r1_orders_2(X0,X3,X2)
          | ~ r1_orders_2(X0,X3,X1) )
        & r2_yellow_0(X0,k2_tarski(X1,X2))
        & k11_lattice3(X0,X1,X2) = X3 )
      | ~ sP0(X3,X0,X2,X1) ) ),
    inference(nnf_transformation,[],[f44])).

fof(f1525,plain,(
    ! [X2,X0,X1] :
      ( ~ sP0(k11_lattice3(X0,X2,X1),X0,X1,X2)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ sP1(X0,X1,X2) ) ),
    inference(subsumption_resolution,[],[f1524,f334])).

fof(f334,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ sP0(X3,X0,X2,X1)
      | ~ sP1(X0,X2,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | r1_orders_2(X0,X3,X2) ) ),
    inference(superposition,[],[f175,f73])).

fof(f1524,plain,(
    ! [X2,X0,X1] :
      ( ~ sP1(X0,X1,X2)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ sP0(k11_lattice3(X0,X2,X1),X0,X1,X2)
      | ~ r1_orders_2(X0,k11_lattice3(X0,X2,X1),X1) ) ),
    inference(subsumption_resolution,[],[f1523,f335])).

fof(f335,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ sP0(X3,X0,X2,X1)
      | ~ sP1(X0,X2,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | r1_orders_2(X0,X3,X1) ) ),
    inference(superposition,[],[f180,f73])).

fof(f1523,plain,(
    ! [X2,X0,X1] :
      ( ~ sP1(X0,X1,X2)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ r1_orders_2(X0,k11_lattice3(X0,X2,X1),X2)
      | ~ sP0(k11_lattice3(X0,X2,X1),X0,X1,X2)
      | ~ r1_orders_2(X0,k11_lattice3(X0,X2,X1),X1) ) ),
    inference(duplicate_literal_removal,[],[f1508])).

fof(f1508,plain,(
    ! [X2,X0,X1] :
      ( ~ sP1(X0,X1,X2)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ r1_orders_2(X0,k11_lattice3(X0,X2,X1),X2)
      | ~ sP0(k11_lattice3(X0,X2,X1),X0,X1,X2)
      | ~ r1_orders_2(X0,k11_lattice3(X0,X2,X1),X1)
      | ~ r1_orders_2(X0,k11_lattice3(X0,X2,X1),X2)
      | ~ sP0(k11_lattice3(X0,X2,X1),X0,X1,X2) ) ),
    inference(resolution,[],[f1007,f76])).

fof(f76,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_orders_2(X1,sK2(X0,X1,X2,X3),X3)
      | ~ r1_orders_2(X1,X0,X2)
      | ~ r1_orders_2(X1,X0,X3)
      | ~ sP0(X0,X1,X2,X3) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f1007,plain,(
    ! [X6,X4,X7,X5] :
      ( ~ r1_orders_2(X4,sK2(k11_lattice3(X4,X5,X6),X4,X6,X7),X5)
      | ~ sP1(X4,X6,X5)
      | ~ m1_subset_1(X6,u1_struct_0(X4))
      | ~ m1_subset_1(X5,u1_struct_0(X4))
      | ~ l1_orders_2(X4)
      | ~ r1_orders_2(X4,k11_lattice3(X4,X5,X6),X7)
      | ~ sP0(k11_lattice3(X4,X5,X6),X4,X6,X7) ) ),
    inference(subsumption_resolution,[],[f1004,f175])).

fof(f1004,plain,(
    ! [X6,X4,X7,X5] :
      ( ~ r1_orders_2(X4,sK2(k11_lattice3(X4,X5,X6),X4,X6,X7),X5)
      | ~ sP1(X4,X6,X5)
      | ~ m1_subset_1(X6,u1_struct_0(X4))
      | ~ m1_subset_1(X5,u1_struct_0(X4))
      | ~ l1_orders_2(X4)
      | ~ r1_orders_2(X4,k11_lattice3(X4,X5,X6),X6)
      | ~ r1_orders_2(X4,k11_lattice3(X4,X5,X6),X7)
      | ~ sP0(k11_lattice3(X4,X5,X6),X4,X6,X7) ) ),
    inference(duplicate_literal_removal,[],[f991])).

fof(f991,plain,(
    ! [X6,X4,X7,X5] :
      ( ~ r1_orders_2(X4,sK2(k11_lattice3(X4,X5,X6),X4,X6,X7),X5)
      | ~ sP1(X4,X6,X5)
      | ~ m1_subset_1(X6,u1_struct_0(X4))
      | ~ m1_subset_1(X5,u1_struct_0(X4))
      | ~ l1_orders_2(X4)
      | ~ r1_orders_2(X4,k11_lattice3(X4,X5,X6),X6)
      | ~ r1_orders_2(X4,k11_lattice3(X4,X5,X6),X7)
      | ~ sP0(k11_lattice3(X4,X5,X6),X4,X6,X7)
      | ~ r1_orders_2(X4,k11_lattice3(X4,X5,X6),X6)
      | ~ r1_orders_2(X4,k11_lattice3(X4,X5,X6),X7)
      | ~ sP0(k11_lattice3(X4,X5,X6),X4,X6,X7) ) ),
    inference(resolution,[],[f494,f77])).

fof(f77,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_orders_2(X1,sK2(X0,X1,X2,X3),X2)
      | ~ r1_orders_2(X1,X0,X2)
      | ~ r1_orders_2(X1,X0,X3)
      | ~ sP0(X0,X1,X2,X3) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f494,plain,(
    ! [X12,X10,X8,X11,X9] :
      ( ~ r1_orders_2(X8,sK2(k11_lattice3(X8,X9,X10),X8,X11,X12),X10)
      | ~ r1_orders_2(X8,sK2(k11_lattice3(X8,X9,X10),X8,X11,X12),X9)
      | ~ sP1(X8,X10,X9)
      | ~ m1_subset_1(X10,u1_struct_0(X8))
      | ~ m1_subset_1(X9,u1_struct_0(X8))
      | ~ l1_orders_2(X8)
      | ~ r1_orders_2(X8,k11_lattice3(X8,X9,X10),X11)
      | ~ r1_orders_2(X8,k11_lattice3(X8,X9,X10),X12)
      | ~ sP0(k11_lattice3(X8,X9,X10),X8,X11,X12) ) ),
    inference(subsumption_resolution,[],[f477,f75])).

fof(f75,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(sK2(X0,X1,X2,X3),u1_struct_0(X1))
      | ~ r1_orders_2(X1,X0,X2)
      | ~ r1_orders_2(X1,X0,X3)
      | ~ sP0(X0,X1,X2,X3) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f477,plain,(
    ! [X12,X10,X8,X11,X9] :
      ( ~ r1_orders_2(X8,sK2(k11_lattice3(X8,X9,X10),X8,X11,X12),X9)
      | ~ m1_subset_1(sK2(k11_lattice3(X8,X9,X10),X8,X11,X12),u1_struct_0(X8))
      | ~ r1_orders_2(X8,sK2(k11_lattice3(X8,X9,X10),X8,X11,X12),X10)
      | ~ sP1(X8,X10,X9)
      | ~ m1_subset_1(X10,u1_struct_0(X8))
      | ~ m1_subset_1(X9,u1_struct_0(X8))
      | ~ l1_orders_2(X8)
      | ~ r1_orders_2(X8,k11_lattice3(X8,X9,X10),X11)
      | ~ r1_orders_2(X8,k11_lattice3(X8,X9,X10),X12)
      | ~ sP0(k11_lattice3(X8,X9,X10),X8,X11,X12) ) ),
    inference(resolution,[],[f259,f78])).

fof(f78,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r1_orders_2(X1,sK2(X0,X1,X2,X3),X0)
      | ~ r1_orders_2(X1,X0,X2)
      | ~ r1_orders_2(X1,X0,X3)
      | ~ sP0(X0,X1,X2,X3) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f126,plain,
    ( sP0(sK6,sK3,sK5,sK4)
    | ~ spl13_0 ),
    inference(avatar_component_clause,[],[f125])).

fof(f125,plain,
    ( spl13_0
  <=> sP0(sK6,sK3,sK5,sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_0])])).

fof(f3033,plain,
    ( spl13_2
    | ~ spl13_9
    | ~ spl13_10
    | ~ spl13_24
    | ~ spl13_26 ),
    inference(avatar_split_clause,[],[f3026,f272,f2335,f143,f3031,f3028])).

fof(f3031,plain,
    ( spl13_9
  <=> ~ r1_orders_2(sK3,sK6,sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_9])])).

fof(f3026,plain,
    ( ~ r1_orders_2(sK3,sK6,sK5)
    | k11_lattice3(sK3,sK4,sK5) = sK6
    | ~ spl13_10
    | ~ spl13_24
    | ~ spl13_26 ),
    inference(subsumption_resolution,[],[f3025,f2336])).

fof(f3025,plain,
    ( ~ r1_orders_2(sK3,sK6,sK5)
    | k11_lattice3(sK3,sK4,sK5) = sK6
    | ~ sP1(sK3,sK5,sK4)
    | ~ spl13_10
    | ~ spl13_26 ),
    inference(subsumption_resolution,[],[f3024,f144])).

fof(f3024,plain,
    ( ~ r1_orders_2(sK3,sK6,sK5)
    | k11_lattice3(sK3,sK4,sK5) = sK6
    | ~ r1_orders_2(sK3,sK6,sK4)
    | ~ sP1(sK3,sK5,sK4)
    | ~ spl13_26 ),
    inference(subsumption_resolution,[],[f2599,f83])).

fof(f2599,plain,
    ( ~ r1_orders_2(sK3,sK6,sK5)
    | k11_lattice3(sK3,sK4,sK5) = sK6
    | ~ m1_subset_1(sK6,u1_struct_0(sK3))
    | ~ r1_orders_2(sK3,sK6,sK4)
    | ~ sP1(sK3,sK5,sK4)
    | ~ spl13_26 ),
    inference(duplicate_literal_removal,[],[f2587])).

fof(f2587,plain,
    ( ~ r1_orders_2(sK3,sK6,sK5)
    | k11_lattice3(sK3,sK4,sK5) = sK6
    | ~ m1_subset_1(sK6,u1_struct_0(sK3))
    | ~ r1_orders_2(sK3,sK6,sK4)
    | k11_lattice3(sK3,sK4,sK5) = sK6
    | ~ r1_orders_2(sK3,sK6,sK5)
    | ~ r1_orders_2(sK3,sK6,sK4)
    | ~ m1_subset_1(sK6,u1_struct_0(sK3))
    | ~ sP1(sK3,sK5,sK4)
    | ~ spl13_26 ),
    inference(resolution,[],[f273,f95])).

fof(f3023,plain,
    ( spl13_114
    | ~ spl13_117
    | ~ spl13_6
    | ~ spl13_24 ),
    inference(avatar_split_clause,[],[f2649,f2335,f135,f3020,f3017])).

fof(f2649,plain,
    ( ~ m1_subset_1(k11_lattice3(sK3,sK4,sK5),u1_struct_0(sK3))
    | r1_orders_2(sK3,k11_lattice3(sK3,sK4,sK5),sK6)
    | ~ spl13_6
    | ~ spl13_24 ),
    inference(subsumption_resolution,[],[f2648,f80])).

fof(f2648,plain,
    ( ~ m1_subset_1(k11_lattice3(sK3,sK4,sK5),u1_struct_0(sK3))
    | r1_orders_2(sK3,k11_lattice3(sK3,sK4,sK5),sK6)
    | ~ l1_orders_2(sK3)
    | ~ spl13_6
    | ~ spl13_24 ),
    inference(subsumption_resolution,[],[f2647,f82])).

fof(f2647,plain,
    ( ~ m1_subset_1(k11_lattice3(sK3,sK4,sK5),u1_struct_0(sK3))
    | r1_orders_2(sK3,k11_lattice3(sK3,sK4,sK5),sK6)
    | ~ m1_subset_1(sK5,u1_struct_0(sK3))
    | ~ l1_orders_2(sK3)
    | ~ spl13_6
    | ~ spl13_24 ),
    inference(subsumption_resolution,[],[f2646,f81])).

fof(f2646,plain,
    ( ~ m1_subset_1(k11_lattice3(sK3,sK4,sK5),u1_struct_0(sK3))
    | r1_orders_2(sK3,k11_lattice3(sK3,sK4,sK5),sK6)
    | ~ m1_subset_1(sK4,u1_struct_0(sK3))
    | ~ m1_subset_1(sK5,u1_struct_0(sK3))
    | ~ l1_orders_2(sK3)
    | ~ spl13_6
    | ~ spl13_24 ),
    inference(subsumption_resolution,[],[f2643,f2336])).

fof(f2643,plain,
    ( ~ m1_subset_1(k11_lattice3(sK3,sK4,sK5),u1_struct_0(sK3))
    | r1_orders_2(sK3,k11_lattice3(sK3,sK4,sK5),sK6)
    | ~ sP1(sK3,sK5,sK4)
    | ~ m1_subset_1(sK4,u1_struct_0(sK3))
    | ~ m1_subset_1(sK5,u1_struct_0(sK3))
    | ~ l1_orders_2(sK3)
    | ~ spl13_6 ),
    inference(duplicate_literal_removal,[],[f2635])).

fof(f2635,plain,
    ( ~ m1_subset_1(k11_lattice3(sK3,sK4,sK5),u1_struct_0(sK3))
    | r1_orders_2(sK3,k11_lattice3(sK3,sK4,sK5),sK6)
    | ~ sP1(sK3,sK5,sK4)
    | ~ m1_subset_1(sK4,u1_struct_0(sK3))
    | ~ sP1(sK3,sK5,sK4)
    | ~ m1_subset_1(sK5,u1_struct_0(sK3))
    | ~ m1_subset_1(sK4,u1_struct_0(sK3))
    | ~ l1_orders_2(sK3)
    | ~ spl13_6 ),
    inference(resolution,[],[f2238,f180])).

fof(f2238,plain,
    ( ! [X2] :
        ( ~ r1_orders_2(sK3,k11_lattice3(sK3,X2,sK5),sK4)
        | ~ m1_subset_1(k11_lattice3(sK3,X2,sK5),u1_struct_0(sK3))
        | r1_orders_2(sK3,k11_lattice3(sK3,X2,sK5),sK6)
        | ~ sP1(sK3,sK5,X2)
        | ~ m1_subset_1(X2,u1_struct_0(sK3)) )
    | ~ spl13_6 ),
    inference(subsumption_resolution,[],[f2237,f80])).

fof(f2237,plain,
    ( ! [X2] :
        ( ~ m1_subset_1(k11_lattice3(sK3,X2,sK5),u1_struct_0(sK3))
        | ~ r1_orders_2(sK3,k11_lattice3(sK3,X2,sK5),sK4)
        | r1_orders_2(sK3,k11_lattice3(sK3,X2,sK5),sK6)
        | ~ sP1(sK3,sK5,X2)
        | ~ m1_subset_1(X2,u1_struct_0(sK3))
        | ~ l1_orders_2(sK3) )
    | ~ spl13_6 ),
    inference(subsumption_resolution,[],[f2210,f82])).

fof(f2210,plain,
    ( ! [X2] :
        ( ~ m1_subset_1(k11_lattice3(sK3,X2,sK5),u1_struct_0(sK3))
        | ~ r1_orders_2(sK3,k11_lattice3(sK3,X2,sK5),sK4)
        | r1_orders_2(sK3,k11_lattice3(sK3,X2,sK5),sK6)
        | ~ sP1(sK3,sK5,X2)
        | ~ m1_subset_1(sK5,u1_struct_0(sK3))
        | ~ m1_subset_1(X2,u1_struct_0(sK3))
        | ~ l1_orders_2(sK3) )
    | ~ spl13_6 ),
    inference(resolution,[],[f136,f175])).

fof(f2061,plain,
    ( ~ spl13_0
    | spl13_25 ),
    inference(avatar_contradiction_clause,[],[f2060])).

fof(f2060,plain,
    ( $false
    | ~ spl13_0
    | ~ spl13_25 ),
    inference(subsumption_resolution,[],[f2059,f82])).

fof(f2059,plain,
    ( ~ m1_subset_1(sK5,u1_struct_0(sK3))
    | ~ spl13_0
    | ~ spl13_25 ),
    inference(subsumption_resolution,[],[f2058,f270])).

fof(f2058,plain,
    ( sP1(sK3,sK5,sK4)
    | ~ m1_subset_1(sK5,u1_struct_0(sK3))
    | ~ spl13_0 ),
    inference(subsumption_resolution,[],[f2057,f80])).

fof(f2057,plain,
    ( ~ l1_orders_2(sK3)
    | sP1(sK3,sK5,sK4)
    | ~ m1_subset_1(sK5,u1_struct_0(sK3))
    | ~ spl13_0 ),
    inference(subsumption_resolution,[],[f2056,f79])).

fof(f2056,plain,
    ( ~ v5_orders_2(sK3)
    | ~ l1_orders_2(sK3)
    | sP1(sK3,sK5,sK4)
    | ~ m1_subset_1(sK5,u1_struct_0(sK3))
    | ~ spl13_0 ),
    inference(subsumption_resolution,[],[f2049,f81])).

fof(f2049,plain,
    ( ~ m1_subset_1(sK4,u1_struct_0(sK3))
    | ~ v5_orders_2(sK3)
    | ~ l1_orders_2(sK3)
    | sP1(sK3,sK5,sK4)
    | ~ m1_subset_1(sK5,u1_struct_0(sK3))
    | ~ spl13_0 ),
    inference(resolution,[],[f1968,f324])).

fof(f324,plain,
    ( r2_yellow_0(sK3,k2_tarski(sK4,sK5))
    | ~ spl13_0 ),
    inference(resolution,[],[f126,f74])).

fof(f74,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ sP0(X0,X1,X2,X3)
      | r2_yellow_0(X1,k2_tarski(X3,X2)) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f1968,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_yellow_0(X1,k2_tarski(X2,X0))
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ v5_orders_2(X1)
      | ~ l1_orders_2(X1)
      | sP1(X1,X0,X2)
      | ~ m1_subset_1(X0,u1_struct_0(X1)) ) ),
    inference(subsumption_resolution,[],[f1967,f106])).

fof(f106,plain,(
    ! [X0,X1] :
      ( m1_subset_1(sK10(X0,X1),u1_struct_0(X0))
      | ~ r2_yellow_0(X0,X1)
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f68])).

fof(f1967,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X0,u1_struct_0(X1))
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ v5_orders_2(X1)
      | ~ l1_orders_2(X1)
      | sP1(X1,X0,X2)
      | ~ r2_yellow_0(X1,k2_tarski(X2,X0))
      | ~ m1_subset_1(sK10(X1,k2_tarski(X2,X0)),u1_struct_0(X1)) ) ),
    inference(subsumption_resolution,[],[f1966,f219])).

fof(f219,plain,(
    ! [X2,X0,X1] :
      ( r1_orders_2(X0,sK10(X0,k2_tarski(X1,X2)),X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ r2_yellow_0(X0,k2_tarski(X1,X2))
      | ~ v5_orders_2(X0) ) ),
    inference(subsumption_resolution,[],[f218,f106])).

fof(f218,plain,(
    ! [X2,X0,X1] :
      ( r1_orders_2(X0,sK10(X0,k2_tarski(X1,X2)),X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(sK10(X0,k2_tarski(X1,X2)),u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ r2_yellow_0(X0,k2_tarski(X1,X2))
      | ~ v5_orders_2(X0) ) ),
    inference(duplicate_literal_removal,[],[f213])).

fof(f213,plain,(
    ! [X2,X0,X1] :
      ( r1_orders_2(X0,sK10(X0,k2_tarski(X1,X2)),X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(sK10(X0,k2_tarski(X1,X2)),u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ r2_yellow_0(X0,k2_tarski(X1,X2))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(resolution,[],[f101,f107])).

fof(f107,plain,(
    ! [X0,X1] :
      ( r1_lattice3(X0,X1,sK10(X0,X1))
      | ~ r2_yellow_0(X0,X1)
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f68])).

fof(f101,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r1_lattice3(X0,k2_tarski(X2,X3),X1)
      | r1_orders_2(X0,X1,X3)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f1966,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X0,u1_struct_0(X1))
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ v5_orders_2(X1)
      | ~ l1_orders_2(X1)
      | sP1(X1,X0,X2)
      | ~ r2_yellow_0(X1,k2_tarski(X2,X0))
      | ~ r1_orders_2(X1,sK10(X1,k2_tarski(X2,X0)),X0)
      | ~ m1_subset_1(sK10(X1,k2_tarski(X2,X0)),u1_struct_0(X1)) ) ),
    inference(subsumption_resolution,[],[f1965,f209])).

fof(f209,plain,(
    ! [X2,X0,X1] :
      ( r1_orders_2(X0,sK10(X0,k2_tarski(X1,X2)),X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ r2_yellow_0(X0,k2_tarski(X1,X2))
      | ~ v5_orders_2(X0) ) ),
    inference(subsumption_resolution,[],[f208,f106])).

fof(f208,plain,(
    ! [X2,X0,X1] :
      ( r1_orders_2(X0,sK10(X0,k2_tarski(X1,X2)),X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(sK10(X0,k2_tarski(X1,X2)),u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ r2_yellow_0(X0,k2_tarski(X1,X2))
      | ~ v5_orders_2(X0) ) ),
    inference(duplicate_literal_removal,[],[f203])).

fof(f203,plain,(
    ! [X2,X0,X1] :
      ( r1_orders_2(X0,sK10(X0,k2_tarski(X1,X2)),X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(sK10(X0,k2_tarski(X1,X2)),u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ r2_yellow_0(X0,k2_tarski(X1,X2))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(resolution,[],[f100,f107])).

fof(f1965,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X0,u1_struct_0(X1))
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ v5_orders_2(X1)
      | ~ l1_orders_2(X1)
      | sP1(X1,X0,X2)
      | ~ r2_yellow_0(X1,k2_tarski(X2,X0))
      | ~ r1_orders_2(X1,sK10(X1,k2_tarski(X2,X0)),X2)
      | ~ r1_orders_2(X1,sK10(X1,k2_tarski(X2,X0)),X0)
      | ~ m1_subset_1(sK10(X1,k2_tarski(X2,X0)),u1_struct_0(X1)) ) ),
    inference(duplicate_literal_removal,[],[f1953])).

fof(f1953,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X0,u1_struct_0(X1))
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ v5_orders_2(X1)
      | ~ l1_orders_2(X1)
      | sP1(X1,X0,X2)
      | ~ r2_yellow_0(X1,k2_tarski(X2,X0))
      | ~ r1_orders_2(X1,sK10(X1,k2_tarski(X2,X0)),X2)
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | sP1(X1,X0,X2)
      | ~ r1_orders_2(X1,sK10(X1,k2_tarski(X2,X0)),X0)
      | ~ r1_orders_2(X1,sK10(X1,k2_tarski(X2,X0)),X2)
      | ~ m1_subset_1(sK10(X1,k2_tarski(X2,X0)),u1_struct_0(X1))
      | ~ m1_subset_1(X0,u1_struct_0(X1))
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ v5_orders_2(X1)
      | ~ l1_orders_2(X1) ) ),
    inference(resolution,[],[f1180,f97])).

fof(f1180,plain,(
    ! [X6,X4,X7,X5] :
      ( ~ r1_orders_2(X4,sK8(X4,X7,X6,sK10(X4,k2_tarski(X5,X6))),X5)
      | ~ m1_subset_1(X6,u1_struct_0(X4))
      | ~ m1_subset_1(X7,u1_struct_0(X4))
      | ~ v5_orders_2(X4)
      | ~ l1_orders_2(X4)
      | sP1(X4,X6,X7)
      | ~ r2_yellow_0(X4,k2_tarski(X5,X6))
      | ~ r1_orders_2(X4,sK10(X4,k2_tarski(X5,X6)),X7)
      | ~ m1_subset_1(X5,u1_struct_0(X4)) ) ),
    inference(subsumption_resolution,[],[f1179,f106])).

fof(f1179,plain,(
    ! [X6,X4,X7,X5] :
      ( ~ r1_orders_2(X4,sK10(X4,k2_tarski(X5,X6)),X7)
      | ~ m1_subset_1(X6,u1_struct_0(X4))
      | ~ m1_subset_1(X7,u1_struct_0(X4))
      | ~ v5_orders_2(X4)
      | ~ l1_orders_2(X4)
      | sP1(X4,X6,X7)
      | ~ r2_yellow_0(X4,k2_tarski(X5,X6))
      | ~ r1_orders_2(X4,sK8(X4,X7,X6,sK10(X4,k2_tarski(X5,X6))),X5)
      | ~ m1_subset_1(X5,u1_struct_0(X4))
      | ~ m1_subset_1(sK10(X4,k2_tarski(X5,X6)),u1_struct_0(X4)) ) ),
    inference(subsumption_resolution,[],[f1178,f219])).

fof(f1178,plain,(
    ! [X6,X4,X7,X5] :
      ( ~ r1_orders_2(X4,sK10(X4,k2_tarski(X5,X6)),X7)
      | ~ m1_subset_1(X6,u1_struct_0(X4))
      | ~ m1_subset_1(X7,u1_struct_0(X4))
      | ~ v5_orders_2(X4)
      | ~ l1_orders_2(X4)
      | sP1(X4,X6,X7)
      | ~ r2_yellow_0(X4,k2_tarski(X5,X6))
      | ~ r1_orders_2(X4,sK10(X4,k2_tarski(X5,X6)),X6)
      | ~ r1_orders_2(X4,sK8(X4,X7,X6,sK10(X4,k2_tarski(X5,X6))),X5)
      | ~ m1_subset_1(X5,u1_struct_0(X4))
      | ~ m1_subset_1(sK10(X4,k2_tarski(X5,X6)),u1_struct_0(X4)) ) ),
    inference(subsumption_resolution,[],[f1174,f96])).

fof(f1174,plain,(
    ! [X6,X4,X7,X5] :
      ( ~ r1_orders_2(X4,sK10(X4,k2_tarski(X5,X6)),X7)
      | ~ m1_subset_1(X6,u1_struct_0(X4))
      | ~ m1_subset_1(X7,u1_struct_0(X4))
      | ~ v5_orders_2(X4)
      | ~ l1_orders_2(X4)
      | sP1(X4,X6,X7)
      | ~ m1_subset_1(sK8(X4,X7,X6,sK10(X4,k2_tarski(X5,X6))),u1_struct_0(X4))
      | ~ r2_yellow_0(X4,k2_tarski(X5,X6))
      | ~ r1_orders_2(X4,sK10(X4,k2_tarski(X5,X6)),X6)
      | ~ r1_orders_2(X4,sK8(X4,X7,X6,sK10(X4,k2_tarski(X5,X6))),X5)
      | ~ m1_subset_1(X5,u1_struct_0(X4))
      | ~ m1_subset_1(sK10(X4,k2_tarski(X5,X6)),u1_struct_0(X4)) ) ),
    inference(duplicate_literal_removal,[],[f1161])).

fof(f1161,plain,(
    ! [X6,X4,X7,X5] :
      ( ~ r1_orders_2(X4,sK10(X4,k2_tarski(X5,X6)),X7)
      | ~ m1_subset_1(X6,u1_struct_0(X4))
      | ~ m1_subset_1(X7,u1_struct_0(X4))
      | ~ v5_orders_2(X4)
      | ~ l1_orders_2(X4)
      | sP1(X4,X6,X7)
      | ~ m1_subset_1(sK8(X4,X7,X6,sK10(X4,k2_tarski(X5,X6))),u1_struct_0(X4))
      | ~ r2_yellow_0(X4,k2_tarski(X5,X6))
      | ~ r1_orders_2(X4,sK10(X4,k2_tarski(X5,X6)),X6)
      | ~ r1_orders_2(X4,sK8(X4,X7,X6,sK10(X4,k2_tarski(X5,X6))),X5)
      | ~ m1_subset_1(X6,u1_struct_0(X4))
      | ~ m1_subset_1(X5,u1_struct_0(X4))
      | sP1(X4,X6,X7)
      | ~ r1_orders_2(X4,sK10(X4,k2_tarski(X5,X6)),X6)
      | ~ r1_orders_2(X4,sK10(X4,k2_tarski(X5,X6)),X7)
      | ~ m1_subset_1(sK10(X4,k2_tarski(X5,X6)),u1_struct_0(X4))
      | ~ m1_subset_1(X6,u1_struct_0(X4))
      | ~ m1_subset_1(X7,u1_struct_0(X4))
      | ~ v5_orders_2(X4)
      | ~ l1_orders_2(X4) ) ),
    inference(resolution,[],[f537,f98])).

fof(f537,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ r1_orders_2(X0,sK8(X0,X4,X3,sK10(X0,k2_tarski(X1,X2))),X2)
      | ~ r1_orders_2(X0,sK10(X0,k2_tarski(X1,X2)),X4)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ v5_orders_2(X0)
      | ~ l1_orders_2(X0)
      | sP1(X0,X3,X4)
      | ~ m1_subset_1(sK8(X0,X4,X3,sK10(X0,k2_tarski(X1,X2))),u1_struct_0(X0))
      | ~ r2_yellow_0(X0,k2_tarski(X1,X2))
      | ~ r1_orders_2(X0,sK10(X0,k2_tarski(X1,X2)),X3)
      | ~ r1_orders_2(X0,sK8(X0,X4,X3,sK10(X0,k2_tarski(X1,X2))),X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0)) ) ),
    inference(duplicate_literal_removal,[],[f536])).

fof(f536,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ r1_orders_2(X0,sK10(X0,k2_tarski(X1,X2)),X3)
      | ~ r1_orders_2(X0,sK10(X0,k2_tarski(X1,X2)),X4)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ v5_orders_2(X0)
      | ~ l1_orders_2(X0)
      | sP1(X0,X3,X4)
      | ~ m1_subset_1(sK8(X0,X4,X3,sK10(X0,k2_tarski(X1,X2))),u1_struct_0(X0))
      | ~ r2_yellow_0(X0,k2_tarski(X1,X2))
      | ~ r1_orders_2(X0,sK8(X0,X4,X3,sK10(X0,k2_tarski(X1,X2))),X2)
      | ~ r1_orders_2(X0,sK8(X0,X4,X3,sK10(X0,k2_tarski(X1,X2))),X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(sK8(X0,X4,X3,sK10(X0,k2_tarski(X1,X2))),u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(resolution,[],[f285,f102])).

fof(f285,plain,(
    ! [X6,X8,X7,X9] :
      ( ~ r1_lattice3(X6,X9,sK8(X6,X8,X7,sK10(X6,X9)))
      | ~ r1_orders_2(X6,sK10(X6,X9),X7)
      | ~ r1_orders_2(X6,sK10(X6,X9),X8)
      | ~ m1_subset_1(X7,u1_struct_0(X6))
      | ~ m1_subset_1(X8,u1_struct_0(X6))
      | ~ v5_orders_2(X6)
      | ~ l1_orders_2(X6)
      | sP1(X6,X7,X8)
      | ~ m1_subset_1(sK8(X6,X8,X7,sK10(X6,X9)),u1_struct_0(X6))
      | ~ r2_yellow_0(X6,X9) ) ),
    inference(subsumption_resolution,[],[f282,f106])).

fof(f282,plain,(
    ! [X6,X8,X7,X9] :
      ( sP1(X6,X7,X8)
      | ~ r1_orders_2(X6,sK10(X6,X9),X7)
      | ~ r1_orders_2(X6,sK10(X6,X9),X8)
      | ~ m1_subset_1(sK10(X6,X9),u1_struct_0(X6))
      | ~ m1_subset_1(X7,u1_struct_0(X6))
      | ~ m1_subset_1(X8,u1_struct_0(X6))
      | ~ v5_orders_2(X6)
      | ~ l1_orders_2(X6)
      | ~ r1_lattice3(X6,X9,sK8(X6,X8,X7,sK10(X6,X9)))
      | ~ m1_subset_1(sK8(X6,X8,X7,sK10(X6,X9)),u1_struct_0(X6))
      | ~ r2_yellow_0(X6,X9) ) ),
    inference(duplicate_literal_removal,[],[f281])).

fof(f281,plain,(
    ! [X6,X8,X7,X9] :
      ( sP1(X6,X7,X8)
      | ~ r1_orders_2(X6,sK10(X6,X9),X7)
      | ~ r1_orders_2(X6,sK10(X6,X9),X8)
      | ~ m1_subset_1(sK10(X6,X9),u1_struct_0(X6))
      | ~ m1_subset_1(X7,u1_struct_0(X6))
      | ~ m1_subset_1(X8,u1_struct_0(X6))
      | ~ v5_orders_2(X6)
      | ~ l1_orders_2(X6)
      | ~ r1_lattice3(X6,X9,sK8(X6,X8,X7,sK10(X6,X9)))
      | ~ m1_subset_1(sK8(X6,X8,X7,sK10(X6,X9)),u1_struct_0(X6))
      | ~ r2_yellow_0(X6,X9)
      | ~ l1_orders_2(X6)
      | ~ v5_orders_2(X6) ) ),
    inference(resolution,[],[f99,f108])).

fof(f108,plain,(
    ! [X0,X5,X1] :
      ( r1_orders_2(X0,X5,sK10(X0,X1))
      | ~ r1_lattice3(X0,X1,X5)
      | ~ m1_subset_1(X5,u1_struct_0(X0))
      | ~ r2_yellow_0(X0,X1)
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f68])).

fof(f320,plain,
    ( ~ spl13_6
    | ~ spl13_8
    | ~ spl13_10
    | spl13_21 ),
    inference(avatar_contradiction_clause,[],[f319])).

fof(f319,plain,
    ( $false
    | ~ spl13_6
    | ~ spl13_8
    | ~ spl13_10
    | ~ spl13_21 ),
    inference(subsumption_resolution,[],[f318,f80])).

fof(f318,plain,
    ( ~ l1_orders_2(sK3)
    | ~ spl13_6
    | ~ spl13_8
    | ~ spl13_10
    | ~ spl13_21 ),
    inference(subsumption_resolution,[],[f317,f79])).

fof(f317,plain,
    ( ~ v5_orders_2(sK3)
    | ~ l1_orders_2(sK3)
    | ~ spl13_6
    | ~ spl13_8
    | ~ spl13_10
    | ~ spl13_21 ),
    inference(subsumption_resolution,[],[f316,f82])).

fof(f316,plain,
    ( ~ m1_subset_1(sK5,u1_struct_0(sK3))
    | ~ v5_orders_2(sK3)
    | ~ l1_orders_2(sK3)
    | ~ spl13_6
    | ~ spl13_8
    | ~ spl13_10
    | ~ spl13_21 ),
    inference(subsumption_resolution,[],[f315,f81])).

fof(f315,plain,
    ( ~ m1_subset_1(sK4,u1_struct_0(sK3))
    | ~ m1_subset_1(sK5,u1_struct_0(sK3))
    | ~ v5_orders_2(sK3)
    | ~ l1_orders_2(sK3)
    | ~ spl13_6
    | ~ spl13_8
    | ~ spl13_10
    | ~ spl13_21 ),
    inference(subsumption_resolution,[],[f314,f248])).

fof(f248,plain,
    ( ~ sP1(sK3,sK4,sK5)
    | ~ spl13_21 ),
    inference(avatar_component_clause,[],[f247])).

fof(f247,plain,
    ( spl13_21
  <=> ~ sP1(sK3,sK4,sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_21])])).

fof(f314,plain,
    ( sP1(sK3,sK4,sK5)
    | ~ m1_subset_1(sK4,u1_struct_0(sK3))
    | ~ m1_subset_1(sK5,u1_struct_0(sK3))
    | ~ v5_orders_2(sK3)
    | ~ l1_orders_2(sK3)
    | ~ spl13_6
    | ~ spl13_8
    | ~ spl13_10
    | ~ spl13_21 ),
    inference(subsumption_resolution,[],[f313,f140])).

fof(f313,plain,
    ( ~ r1_orders_2(sK3,sK6,sK5)
    | sP1(sK3,sK4,sK5)
    | ~ m1_subset_1(sK4,u1_struct_0(sK3))
    | ~ m1_subset_1(sK5,u1_struct_0(sK3))
    | ~ v5_orders_2(sK3)
    | ~ l1_orders_2(sK3)
    | ~ spl13_6
    | ~ spl13_10
    | ~ spl13_21 ),
    inference(subsumption_resolution,[],[f312,f144])).

fof(f312,plain,
    ( ~ r1_orders_2(sK3,sK6,sK4)
    | ~ r1_orders_2(sK3,sK6,sK5)
    | sP1(sK3,sK4,sK5)
    | ~ m1_subset_1(sK4,u1_struct_0(sK3))
    | ~ m1_subset_1(sK5,u1_struct_0(sK3))
    | ~ v5_orders_2(sK3)
    | ~ l1_orders_2(sK3)
    | ~ spl13_6
    | ~ spl13_21 ),
    inference(subsumption_resolution,[],[f311,f83])).

fof(f311,plain,
    ( ~ m1_subset_1(sK6,u1_struct_0(sK3))
    | ~ r1_orders_2(sK3,sK6,sK4)
    | ~ r1_orders_2(sK3,sK6,sK5)
    | sP1(sK3,sK4,sK5)
    | ~ m1_subset_1(sK4,u1_struct_0(sK3))
    | ~ m1_subset_1(sK5,u1_struct_0(sK3))
    | ~ v5_orders_2(sK3)
    | ~ l1_orders_2(sK3)
    | ~ spl13_6
    | ~ spl13_21 ),
    inference(duplicate_literal_removal,[],[f310])).

fof(f310,plain,
    ( ~ m1_subset_1(sK6,u1_struct_0(sK3))
    | ~ r1_orders_2(sK3,sK6,sK4)
    | ~ r1_orders_2(sK3,sK6,sK5)
    | sP1(sK3,sK4,sK5)
    | ~ r1_orders_2(sK3,sK6,sK4)
    | ~ r1_orders_2(sK3,sK6,sK5)
    | ~ m1_subset_1(sK6,u1_struct_0(sK3))
    | ~ m1_subset_1(sK4,u1_struct_0(sK3))
    | ~ m1_subset_1(sK5,u1_struct_0(sK3))
    | ~ v5_orders_2(sK3)
    | ~ l1_orders_2(sK3)
    | ~ spl13_6
    | ~ spl13_21 ),
    inference(resolution,[],[f299,f99])).

fof(f299,plain,
    ( ! [X0] :
        ( r1_orders_2(sK3,sK8(sK3,sK5,sK4,X0),sK6)
        | ~ m1_subset_1(X0,u1_struct_0(sK3))
        | ~ r1_orders_2(sK3,X0,sK4)
        | ~ r1_orders_2(sK3,X0,sK5) )
    | ~ spl13_6
    | ~ spl13_21 ),
    inference(subsumption_resolution,[],[f298,f80])).

fof(f298,plain,
    ( ! [X0] :
        ( ~ r1_orders_2(sK3,X0,sK5)
        | ~ m1_subset_1(X0,u1_struct_0(sK3))
        | ~ r1_orders_2(sK3,X0,sK4)
        | r1_orders_2(sK3,sK8(sK3,sK5,sK4,X0),sK6)
        | ~ l1_orders_2(sK3) )
    | ~ spl13_6
    | ~ spl13_21 ),
    inference(subsumption_resolution,[],[f297,f79])).

fof(f297,plain,
    ( ! [X0] :
        ( ~ r1_orders_2(sK3,X0,sK5)
        | ~ m1_subset_1(X0,u1_struct_0(sK3))
        | ~ r1_orders_2(sK3,X0,sK4)
        | r1_orders_2(sK3,sK8(sK3,sK5,sK4,X0),sK6)
        | ~ v5_orders_2(sK3)
        | ~ l1_orders_2(sK3) )
    | ~ spl13_6
    | ~ spl13_21 ),
    inference(subsumption_resolution,[],[f296,f82])).

fof(f296,plain,
    ( ! [X0] :
        ( ~ r1_orders_2(sK3,X0,sK5)
        | ~ m1_subset_1(X0,u1_struct_0(sK3))
        | ~ r1_orders_2(sK3,X0,sK4)
        | r1_orders_2(sK3,sK8(sK3,sK5,sK4,X0),sK6)
        | ~ m1_subset_1(sK5,u1_struct_0(sK3))
        | ~ v5_orders_2(sK3)
        | ~ l1_orders_2(sK3) )
    | ~ spl13_6
    | ~ spl13_21 ),
    inference(subsumption_resolution,[],[f295,f81])).

fof(f295,plain,
    ( ! [X0] :
        ( ~ r1_orders_2(sK3,X0,sK5)
        | ~ m1_subset_1(X0,u1_struct_0(sK3))
        | ~ r1_orders_2(sK3,X0,sK4)
        | r1_orders_2(sK3,sK8(sK3,sK5,sK4,X0),sK6)
        | ~ m1_subset_1(sK4,u1_struct_0(sK3))
        | ~ m1_subset_1(sK5,u1_struct_0(sK3))
        | ~ v5_orders_2(sK3)
        | ~ l1_orders_2(sK3) )
    | ~ spl13_6
    | ~ spl13_21 ),
    inference(subsumption_resolution,[],[f294,f248])).

fof(f294,plain,
    ( ! [X0] :
        ( ~ r1_orders_2(sK3,X0,sK5)
        | ~ m1_subset_1(X0,u1_struct_0(sK3))
        | ~ r1_orders_2(sK3,X0,sK4)
        | r1_orders_2(sK3,sK8(sK3,sK5,sK4,X0),sK6)
        | sP1(sK3,sK4,sK5)
        | ~ m1_subset_1(sK4,u1_struct_0(sK3))
        | ~ m1_subset_1(sK5,u1_struct_0(sK3))
        | ~ v5_orders_2(sK3)
        | ~ l1_orders_2(sK3) )
    | ~ spl13_6
    | ~ spl13_21 ),
    inference(duplicate_literal_removal,[],[f293])).

fof(f293,plain,
    ( ! [X0] :
        ( ~ r1_orders_2(sK3,X0,sK5)
        | ~ m1_subset_1(X0,u1_struct_0(sK3))
        | ~ r1_orders_2(sK3,X0,sK4)
        | r1_orders_2(sK3,sK8(sK3,sK5,sK4,X0),sK6)
        | sP1(sK3,sK4,sK5)
        | ~ r1_orders_2(sK3,X0,sK4)
        | ~ r1_orders_2(sK3,X0,sK5)
        | ~ m1_subset_1(X0,u1_struct_0(sK3))
        | ~ m1_subset_1(sK4,u1_struct_0(sK3))
        | ~ m1_subset_1(sK5,u1_struct_0(sK3))
        | ~ v5_orders_2(sK3)
        | ~ l1_orders_2(sK3) )
    | ~ spl13_6
    | ~ spl13_21 ),
    inference(resolution,[],[f292,f96])).

fof(f292,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK8(sK3,sK5,sK4,X0),u1_struct_0(sK3))
        | ~ r1_orders_2(sK3,X0,sK5)
        | ~ m1_subset_1(X0,u1_struct_0(sK3))
        | ~ r1_orders_2(sK3,X0,sK4)
        | r1_orders_2(sK3,sK8(sK3,sK5,sK4,X0),sK6) )
    | ~ spl13_6
    | ~ spl13_21 ),
    inference(subsumption_resolution,[],[f291,f80])).

fof(f291,plain,
    ( ! [X0] :
        ( ~ r1_orders_2(sK3,X0,sK4)
        | ~ r1_orders_2(sK3,X0,sK5)
        | ~ m1_subset_1(X0,u1_struct_0(sK3))
        | ~ m1_subset_1(sK8(sK3,sK5,sK4,X0),u1_struct_0(sK3))
        | r1_orders_2(sK3,sK8(sK3,sK5,sK4,X0),sK6)
        | ~ l1_orders_2(sK3) )
    | ~ spl13_6
    | ~ spl13_21 ),
    inference(subsumption_resolution,[],[f290,f79])).

fof(f290,plain,
    ( ! [X0] :
        ( ~ r1_orders_2(sK3,X0,sK4)
        | ~ r1_orders_2(sK3,X0,sK5)
        | ~ m1_subset_1(X0,u1_struct_0(sK3))
        | ~ m1_subset_1(sK8(sK3,sK5,sK4,X0),u1_struct_0(sK3))
        | r1_orders_2(sK3,sK8(sK3,sK5,sK4,X0),sK6)
        | ~ v5_orders_2(sK3)
        | ~ l1_orders_2(sK3) )
    | ~ spl13_6
    | ~ spl13_21 ),
    inference(subsumption_resolution,[],[f289,f82])).

fof(f289,plain,
    ( ! [X0] :
        ( ~ r1_orders_2(sK3,X0,sK4)
        | ~ r1_orders_2(sK3,X0,sK5)
        | ~ m1_subset_1(X0,u1_struct_0(sK3))
        | ~ m1_subset_1(sK8(sK3,sK5,sK4,X0),u1_struct_0(sK3))
        | r1_orders_2(sK3,sK8(sK3,sK5,sK4,X0),sK6)
        | ~ m1_subset_1(sK5,u1_struct_0(sK3))
        | ~ v5_orders_2(sK3)
        | ~ l1_orders_2(sK3) )
    | ~ spl13_6
    | ~ spl13_21 ),
    inference(subsumption_resolution,[],[f288,f248])).

fof(f288,plain,
    ( ! [X0] :
        ( ~ r1_orders_2(sK3,X0,sK4)
        | ~ r1_orders_2(sK3,X0,sK5)
        | ~ m1_subset_1(X0,u1_struct_0(sK3))
        | ~ m1_subset_1(sK8(sK3,sK5,sK4,X0),u1_struct_0(sK3))
        | sP1(sK3,sK4,sK5)
        | r1_orders_2(sK3,sK8(sK3,sK5,sK4,X0),sK6)
        | ~ m1_subset_1(sK5,u1_struct_0(sK3))
        | ~ v5_orders_2(sK3)
        | ~ l1_orders_2(sK3) )
    | ~ spl13_6 ),
    inference(subsumption_resolution,[],[f287,f81])).

fof(f287,plain,
    ( ! [X0] :
        ( ~ r1_orders_2(sK3,X0,sK4)
        | ~ r1_orders_2(sK3,X0,sK5)
        | ~ m1_subset_1(X0,u1_struct_0(sK3))
        | ~ m1_subset_1(sK4,u1_struct_0(sK3))
        | ~ m1_subset_1(sK8(sK3,sK5,sK4,X0),u1_struct_0(sK3))
        | sP1(sK3,sK4,sK5)
        | r1_orders_2(sK3,sK8(sK3,sK5,sK4,X0),sK6)
        | ~ m1_subset_1(sK5,u1_struct_0(sK3))
        | ~ v5_orders_2(sK3)
        | ~ l1_orders_2(sK3) )
    | ~ spl13_6 ),
    inference(duplicate_literal_removal,[],[f286])).

fof(f286,plain,
    ( ! [X0] :
        ( ~ r1_orders_2(sK3,X0,sK4)
        | ~ r1_orders_2(sK3,X0,sK5)
        | ~ m1_subset_1(X0,u1_struct_0(sK3))
        | ~ m1_subset_1(sK4,u1_struct_0(sK3))
        | ~ m1_subset_1(sK8(sK3,sK5,sK4,X0),u1_struct_0(sK3))
        | sP1(sK3,sK4,sK5)
        | r1_orders_2(sK3,sK8(sK3,sK5,sK4,X0),sK6)
        | sP1(sK3,sK4,sK5)
        | ~ r1_orders_2(sK3,X0,sK4)
        | ~ r1_orders_2(sK3,X0,sK5)
        | ~ m1_subset_1(X0,u1_struct_0(sK3))
        | ~ m1_subset_1(sK4,u1_struct_0(sK3))
        | ~ m1_subset_1(sK5,u1_struct_0(sK3))
        | ~ v5_orders_2(sK3)
        | ~ l1_orders_2(sK3) )
    | ~ spl13_6 ),
    inference(resolution,[],[f265,f98])).

fof(f265,plain,
    ( ! [X0,X1] :
        ( ~ r1_orders_2(sK3,sK8(sK3,sK5,X0,X1),sK4)
        | ~ r1_orders_2(sK3,X1,X0)
        | ~ r1_orders_2(sK3,X1,sK5)
        | ~ m1_subset_1(X1,u1_struct_0(sK3))
        | ~ m1_subset_1(X0,u1_struct_0(sK3))
        | ~ m1_subset_1(sK8(sK3,sK5,X0,X1),u1_struct_0(sK3))
        | sP1(sK3,X0,sK5)
        | r1_orders_2(sK3,sK8(sK3,sK5,X0,X1),sK6) )
    | ~ spl13_6 ),
    inference(subsumption_resolution,[],[f264,f80])).

fof(f264,plain,
    ( ! [X0,X1] :
        ( sP1(sK3,X0,sK5)
        | ~ r1_orders_2(sK3,X1,X0)
        | ~ r1_orders_2(sK3,X1,sK5)
        | ~ m1_subset_1(X1,u1_struct_0(sK3))
        | ~ m1_subset_1(X0,u1_struct_0(sK3))
        | ~ l1_orders_2(sK3)
        | ~ m1_subset_1(sK8(sK3,sK5,X0,X1),u1_struct_0(sK3))
        | ~ r1_orders_2(sK3,sK8(sK3,sK5,X0,X1),sK4)
        | r1_orders_2(sK3,sK8(sK3,sK5,X0,X1),sK6) )
    | ~ spl13_6 ),
    inference(subsumption_resolution,[],[f263,f79])).

fof(f263,plain,
    ( ! [X0,X1] :
        ( sP1(sK3,X0,sK5)
        | ~ r1_orders_2(sK3,X1,X0)
        | ~ r1_orders_2(sK3,X1,sK5)
        | ~ m1_subset_1(X1,u1_struct_0(sK3))
        | ~ m1_subset_1(X0,u1_struct_0(sK3))
        | ~ v5_orders_2(sK3)
        | ~ l1_orders_2(sK3)
        | ~ m1_subset_1(sK8(sK3,sK5,X0,X1),u1_struct_0(sK3))
        | ~ r1_orders_2(sK3,sK8(sK3,sK5,X0,X1),sK4)
        | r1_orders_2(sK3,sK8(sK3,sK5,X0,X1),sK6) )
    | ~ spl13_6 ),
    inference(subsumption_resolution,[],[f262,f82])).

fof(f262,plain,
    ( ! [X0,X1] :
        ( sP1(sK3,X0,sK5)
        | ~ r1_orders_2(sK3,X1,X0)
        | ~ r1_orders_2(sK3,X1,sK5)
        | ~ m1_subset_1(X1,u1_struct_0(sK3))
        | ~ m1_subset_1(X0,u1_struct_0(sK3))
        | ~ m1_subset_1(sK5,u1_struct_0(sK3))
        | ~ v5_orders_2(sK3)
        | ~ l1_orders_2(sK3)
        | ~ m1_subset_1(sK8(sK3,sK5,X0,X1),u1_struct_0(sK3))
        | ~ r1_orders_2(sK3,sK8(sK3,sK5,X0,X1),sK4)
        | r1_orders_2(sK3,sK8(sK3,sK5,X0,X1),sK6) )
    | ~ spl13_6 ),
    inference(resolution,[],[f97,f136])).

fof(f274,plain,
    ( ~ spl13_25
    | spl13_26
    | ~ spl13_6 ),
    inference(avatar_split_clause,[],[f267,f135,f272,f269])).

fof(f267,plain,
    ( ! [X0] :
        ( ~ r1_orders_2(sK3,X0,sK5)
        | ~ r1_orders_2(sK3,X0,sK4)
        | ~ m1_subset_1(X0,u1_struct_0(sK3))
        | ~ sP1(sK3,sK5,sK4)
        | k11_lattice3(sK3,sK4,sK5) = X0
        | r1_orders_2(sK3,sK7(sK3,sK5,sK4,X0),sK6) )
    | ~ spl13_6 ),
    inference(duplicate_literal_removal,[],[f266])).

fof(f266,plain,
    ( ! [X0] :
        ( ~ r1_orders_2(sK3,X0,sK5)
        | ~ r1_orders_2(sK3,X0,sK4)
        | ~ m1_subset_1(X0,u1_struct_0(sK3))
        | ~ sP1(sK3,sK5,sK4)
        | k11_lattice3(sK3,sK4,sK5) = X0
        | r1_orders_2(sK3,sK7(sK3,sK5,sK4,X0),sK6)
        | k11_lattice3(sK3,sK4,sK5) = X0
        | ~ r1_orders_2(sK3,X0,sK5)
        | ~ r1_orders_2(sK3,X0,sK4)
        | ~ m1_subset_1(X0,u1_struct_0(sK3))
        | ~ sP1(sK3,sK5,sK4) )
    | ~ spl13_6 ),
    inference(resolution,[],[f243,f93])).

fof(f93,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_orders_2(X0,sK7(X0,X1,X2,X3),X2)
      | k11_lattice3(X0,X2,X1) = X3
      | ~ r1_orders_2(X0,X3,X1)
      | ~ r1_orders_2(X0,X3,X2)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ sP1(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f61])).

fof(f243,plain,
    ( ! [X0,X1] :
        ( ~ r1_orders_2(sK3,sK7(sK3,sK5,X0,X1),sK4)
        | ~ r1_orders_2(sK3,X1,sK5)
        | ~ r1_orders_2(sK3,X1,X0)
        | ~ m1_subset_1(X1,u1_struct_0(sK3))
        | ~ sP1(sK3,sK5,X0)
        | k11_lattice3(sK3,X0,sK5) = X1
        | r1_orders_2(sK3,sK7(sK3,sK5,X0,X1),sK6) )
    | ~ spl13_6 ),
    inference(subsumption_resolution,[],[f242,f92])).

fof(f242,plain,
    ( ! [X0,X1] :
        ( k11_lattice3(sK3,X0,sK5) = X1
        | ~ r1_orders_2(sK3,X1,sK5)
        | ~ r1_orders_2(sK3,X1,X0)
        | ~ m1_subset_1(X1,u1_struct_0(sK3))
        | ~ sP1(sK3,sK5,X0)
        | ~ m1_subset_1(sK7(sK3,sK5,X0,X1),u1_struct_0(sK3))
        | ~ r1_orders_2(sK3,sK7(sK3,sK5,X0,X1),sK4)
        | r1_orders_2(sK3,sK7(sK3,sK5,X0,X1),sK6) )
    | ~ spl13_6 ),
    inference(resolution,[],[f94,f136])).

fof(f145,plain,
    ( spl13_0
    | spl13_10 ),
    inference(avatar_split_clause,[],[f84,f143,f125])).

fof(f84,plain,
    ( r1_orders_2(sK3,sK6,sK4)
    | sP0(sK6,sK3,sK5,sK4) ),
    inference(cnf_transformation,[],[f56])).

fof(f141,plain,
    ( spl13_0
    | spl13_8 ),
    inference(avatar_split_clause,[],[f85,f139,f125])).

fof(f85,plain,
    ( r1_orders_2(sK3,sK6,sK5)
    | sP0(sK6,sK3,sK5,sK4) ),
    inference(cnf_transformation,[],[f56])).

fof(f137,plain,
    ( spl13_0
    | spl13_6 ),
    inference(avatar_split_clause,[],[f86,f135,f125])).

fof(f86,plain,(
    ! [X4] :
      ( r1_orders_2(sK3,X4,sK6)
      | ~ r1_orders_2(sK3,X4,sK5)
      | ~ r1_orders_2(sK3,X4,sK4)
      | ~ m1_subset_1(X4,u1_struct_0(sK3))
      | sP0(sK6,sK3,sK5,sK4) ) ),
    inference(cnf_transformation,[],[f56])).

fof(f133,plain,
    ( spl13_0
    | ~ spl13_3
    | ~ spl13_5 ),
    inference(avatar_split_clause,[],[f87,f131,f128,f125])).

fof(f128,plain,
    ( spl13_3
  <=> k11_lattice3(sK3,sK4,sK5) != sK6 ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_3])])).

fof(f87,plain,
    ( ~ r2_yellow_0(sK3,k2_tarski(sK4,sK5))
    | k11_lattice3(sK3,sK4,sK5) != sK6
    | sP0(sK6,sK3,sK5,sK4) ),
    inference(cnf_transformation,[],[f56])).
%------------------------------------------------------------------------------
