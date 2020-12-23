%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT1651+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n029.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:46:05 EST 2020

% Result     : Theorem 3.63s
% Output     : CNFRefutation 3.63s
% Verified   : 
% Statistics : Number of formulae       :  176 (2244 expanded)
%              Number of clauses        :  106 ( 524 expanded)
%              Number of leaves         :   17 ( 594 expanded)
%              Depth                    :   41
%              Number of atoms          :  802 (16075 expanded)
%              Number of equality atoms :   99 ( 549 expanded)
%              Maximal formula depth    :   14 (   6 average)
%              Maximal clause size      :   20 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f25,plain,(
    ! [X1,X0,X2] :
      ( sP0(X1,X0,X2)
    <=> ! [X3] :
          ( ( r2_hidden(X3,X2)
          <=> ? [X4] :
                ( r2_hidden(X4,X1)
                & r1_orders_2(X0,X3,X4)
                & m1_subset_1(X4,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X3,u1_struct_0(X0)) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f30,plain,(
    ! [X1,X0,X2] :
      ( ( sP0(X1,X0,X2)
        | ? [X3] :
            ( ( ! [X4] :
                  ( ~ r2_hidden(X4,X1)
                  | ~ r1_orders_2(X0,X3,X4)
                  | ~ m1_subset_1(X4,u1_struct_0(X0)) )
              | ~ r2_hidden(X3,X2) )
            & ( ? [X4] :
                  ( r2_hidden(X4,X1)
                  & r1_orders_2(X0,X3,X4)
                  & m1_subset_1(X4,u1_struct_0(X0)) )
              | r2_hidden(X3,X2) )
            & m1_subset_1(X3,u1_struct_0(X0)) ) )
      & ( ! [X3] :
            ( ( ( r2_hidden(X3,X2)
                | ! [X4] :
                    ( ~ r2_hidden(X4,X1)
                    | ~ r1_orders_2(X0,X3,X4)
                    | ~ m1_subset_1(X4,u1_struct_0(X0)) ) )
              & ( ? [X4] :
                    ( r2_hidden(X4,X1)
                    & r1_orders_2(X0,X3,X4)
                    & m1_subset_1(X4,u1_struct_0(X0)) )
                | ~ r2_hidden(X3,X2) ) )
            | ~ m1_subset_1(X3,u1_struct_0(X0)) )
        | ~ sP0(X1,X0,X2) ) ) ),
    inference(nnf_transformation,[],[f25])).

fof(f31,plain,(
    ! [X1,X0,X2] :
      ( ( sP0(X1,X0,X2)
        | ? [X3] :
            ( ( ! [X4] :
                  ( ~ r2_hidden(X4,X1)
                  | ~ r1_orders_2(X0,X3,X4)
                  | ~ m1_subset_1(X4,u1_struct_0(X0)) )
              | ~ r2_hidden(X3,X2) )
            & ( ? [X4] :
                  ( r2_hidden(X4,X1)
                  & r1_orders_2(X0,X3,X4)
                  & m1_subset_1(X4,u1_struct_0(X0)) )
              | r2_hidden(X3,X2) )
            & m1_subset_1(X3,u1_struct_0(X0)) ) )
      & ( ! [X3] :
            ( ( ( r2_hidden(X3,X2)
                | ! [X4] :
                    ( ~ r2_hidden(X4,X1)
                    | ~ r1_orders_2(X0,X3,X4)
                    | ~ m1_subset_1(X4,u1_struct_0(X0)) ) )
              & ( ? [X4] :
                    ( r2_hidden(X4,X1)
                    & r1_orders_2(X0,X3,X4)
                    & m1_subset_1(X4,u1_struct_0(X0)) )
                | ~ r2_hidden(X3,X2) ) )
            | ~ m1_subset_1(X3,u1_struct_0(X0)) )
        | ~ sP0(X1,X0,X2) ) ) ),
    inference(flattening,[],[f30])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( ( sP0(X0,X1,X2)
        | ? [X3] :
            ( ( ! [X4] :
                  ( ~ r2_hidden(X4,X0)
                  | ~ r1_orders_2(X1,X3,X4)
                  | ~ m1_subset_1(X4,u1_struct_0(X1)) )
              | ~ r2_hidden(X3,X2) )
            & ( ? [X5] :
                  ( r2_hidden(X5,X0)
                  & r1_orders_2(X1,X3,X5)
                  & m1_subset_1(X5,u1_struct_0(X1)) )
              | r2_hidden(X3,X2) )
            & m1_subset_1(X3,u1_struct_0(X1)) ) )
      & ( ! [X6] :
            ( ( ( r2_hidden(X6,X2)
                | ! [X7] :
                    ( ~ r2_hidden(X7,X0)
                    | ~ r1_orders_2(X1,X6,X7)
                    | ~ m1_subset_1(X7,u1_struct_0(X1)) ) )
              & ( ? [X8] :
                    ( r2_hidden(X8,X0)
                    & r1_orders_2(X1,X6,X8)
                    & m1_subset_1(X8,u1_struct_0(X1)) )
                | ~ r2_hidden(X6,X2) ) )
            | ~ m1_subset_1(X6,u1_struct_0(X1)) )
        | ~ sP0(X0,X1,X2) ) ) ),
    inference(rectify,[],[f31])).

fof(f35,plain,(
    ! [X6,X1,X0] :
      ( ? [X8] :
          ( r2_hidden(X8,X0)
          & r1_orders_2(X1,X6,X8)
          & m1_subset_1(X8,u1_struct_0(X1)) )
     => ( r2_hidden(sK4(X0,X1,X6),X0)
        & r1_orders_2(X1,X6,sK4(X0,X1,X6))
        & m1_subset_1(sK4(X0,X1,X6),u1_struct_0(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,(
    ! [X3,X2,X1,X0] :
      ( ? [X5] :
          ( r2_hidden(X5,X0)
          & r1_orders_2(X1,X3,X5)
          & m1_subset_1(X5,u1_struct_0(X1)) )
     => ( r2_hidden(sK3(X0,X1,X2),X0)
        & r1_orders_2(X1,X3,sK3(X0,X1,X2))
        & m1_subset_1(sK3(X0,X1,X2),u1_struct_0(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ! [X4] :
                ( ~ r2_hidden(X4,X0)
                | ~ r1_orders_2(X1,X3,X4)
                | ~ m1_subset_1(X4,u1_struct_0(X1)) )
            | ~ r2_hidden(X3,X2) )
          & ( ? [X5] :
                ( r2_hidden(X5,X0)
                & r1_orders_2(X1,X3,X5)
                & m1_subset_1(X5,u1_struct_0(X1)) )
            | r2_hidden(X3,X2) )
          & m1_subset_1(X3,u1_struct_0(X1)) )
     => ( ( ! [X4] :
              ( ~ r2_hidden(X4,X0)
              | ~ r1_orders_2(X1,sK2(X0,X1,X2),X4)
              | ~ m1_subset_1(X4,u1_struct_0(X1)) )
          | ~ r2_hidden(sK2(X0,X1,X2),X2) )
        & ( ? [X5] :
              ( r2_hidden(X5,X0)
              & r1_orders_2(X1,sK2(X0,X1,X2),X5)
              & m1_subset_1(X5,u1_struct_0(X1)) )
          | r2_hidden(sK2(X0,X1,X2),X2) )
        & m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( ( sP0(X0,X1,X2)
        | ( ( ! [X4] :
                ( ~ r2_hidden(X4,X0)
                | ~ r1_orders_2(X1,sK2(X0,X1,X2),X4)
                | ~ m1_subset_1(X4,u1_struct_0(X1)) )
            | ~ r2_hidden(sK2(X0,X1,X2),X2) )
          & ( ( r2_hidden(sK3(X0,X1,X2),X0)
              & r1_orders_2(X1,sK2(X0,X1,X2),sK3(X0,X1,X2))
              & m1_subset_1(sK3(X0,X1,X2),u1_struct_0(X1)) )
            | r2_hidden(sK2(X0,X1,X2),X2) )
          & m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X1)) ) )
      & ( ! [X6] :
            ( ( ( r2_hidden(X6,X2)
                | ! [X7] :
                    ( ~ r2_hidden(X7,X0)
                    | ~ r1_orders_2(X1,X6,X7)
                    | ~ m1_subset_1(X7,u1_struct_0(X1)) ) )
              & ( ( r2_hidden(sK4(X0,X1,X6),X0)
                  & r1_orders_2(X1,X6,sK4(X0,X1,X6))
                  & m1_subset_1(sK4(X0,X1,X6),u1_struct_0(X1)) )
                | ~ r2_hidden(X6,X2) ) )
            | ~ m1_subset_1(X6,u1_struct_0(X1)) )
        | ~ sP0(X0,X1,X2) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f32,f35,f34,f33])).

fof(f53,plain,(
    ! [X6,X2,X0,X7,X1] :
      ( r2_hidden(X6,X2)
      | ~ r2_hidden(X7,X0)
      | ~ r1_orders_2(X1,X6,X7)
      | ~ m1_subset_1(X7,u1_struct_0(X1))
      | ~ m1_subset_1(X6,u1_struct_0(X1))
      | ~ sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f26,plain,(
    ! [X2,X0,X1] :
      ( ( k3_waybel_0(X0,X1) = X2
      <=> sP0(X1,X0,X2) )
      | ~ sP1(X2,X0,X1) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f28,plain,(
    ! [X2,X0,X1] :
      ( ( ( k3_waybel_0(X0,X1) = X2
          | ~ sP0(X1,X0,X2) )
        & ( sP0(X1,X0,X2)
          | k3_waybel_0(X0,X1) != X2 ) )
      | ~ sP1(X2,X0,X1) ) ),
    inference(nnf_transformation,[],[f26])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( ( ( k3_waybel_0(X1,X2) = X0
          | ~ sP0(X2,X1,X0) )
        & ( sP0(X2,X1,X0)
          | k3_waybel_0(X1,X2) != X0 ) )
      | ~ sP1(X0,X1,X2) ) ),
    inference(rectify,[],[f28])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( sP0(X2,X1,X0)
      | k3_waybel_0(X1,X2) != X0
      | ~ sP1(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f78,plain,(
    ! [X2,X1] :
      ( sP0(X2,X1,k3_waybel_0(X1,X2))
      | ~ sP1(k3_waybel_0(X1,X2),X1,X2) ) ),
    inference(equality_resolution,[],[f48])).

fof(f1,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( k3_waybel_0(X0,X1) = X2
              <=> ! [X3] :
                    ( m1_subset_1(X3,u1_struct_0(X0))
                   => ( r2_hidden(X3,X2)
                    <=> ? [X4] :
                          ( r2_hidden(X4,X1)
                          & r1_orders_2(X0,X3,X4)
                          & m1_subset_1(X4,u1_struct_0(X0)) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f10,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( k3_waybel_0(X0,X1) = X2
              <=> ! [X3] :
                    ( ( r2_hidden(X3,X2)
                    <=> ? [X4] :
                          ( r2_hidden(X4,X1)
                          & r1_orders_2(X0,X3,X4)
                          & m1_subset_1(X4,u1_struct_0(X0)) ) )
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( sP1(X2,X0,X1)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0) ) ),
    inference(definition_folding,[],[f10,f26,f25])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( sP1(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f8,conjecture,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( r2_lattice3(X0,X1,X2)
              <=> r2_lattice3(X0,k3_waybel_0(X0,X1),X2) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f9,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_orders_2(X0)
          & v4_orders_2(X0)
          & v3_orders_2(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => ( r2_lattice3(X0,X1,X2)
                <=> r2_lattice3(X0,k3_waybel_0(X0,X1),X2) ) ) ) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f23,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( r2_lattice3(X0,X1,X2)
              <~> r2_lattice3(X0,k3_waybel_0(X0,X1),X2) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f24,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( r2_lattice3(X0,X1,X2)
              <~> r2_lattice3(X0,k3_waybel_0(X0,X1),X2) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f23])).

fof(f42,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ~ r2_lattice3(X0,k3_waybel_0(X0,X1),X2)
                | ~ r2_lattice3(X0,X1,X2) )
              & ( r2_lattice3(X0,k3_waybel_0(X0,X1),X2)
                | r2_lattice3(X0,X1,X2) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f24])).

fof(f43,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ~ r2_lattice3(X0,k3_waybel_0(X0,X1),X2)
                | ~ r2_lattice3(X0,X1,X2) )
              & ( r2_lattice3(X0,k3_waybel_0(X0,X1),X2)
                | r2_lattice3(X0,X1,X2) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f42])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ( ~ r2_lattice3(X0,k3_waybel_0(X0,X1),X2)
            | ~ r2_lattice3(X0,X1,X2) )
          & ( r2_lattice3(X0,k3_waybel_0(X0,X1),X2)
            | r2_lattice3(X0,X1,X2) )
          & m1_subset_1(X2,u1_struct_0(X0)) )
     => ( ( ~ r2_lattice3(X0,k3_waybel_0(X0,X1),sK8)
          | ~ r2_lattice3(X0,X1,sK8) )
        & ( r2_lattice3(X0,k3_waybel_0(X0,X1),sK8)
          | r2_lattice3(X0,X1,sK8) )
        & m1_subset_1(sK8,u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f45,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ~ r2_lattice3(X0,k3_waybel_0(X0,X1),X2)
                | ~ r2_lattice3(X0,X1,X2) )
              & ( r2_lattice3(X0,k3_waybel_0(X0,X1),X2)
                | r2_lattice3(X0,X1,X2) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ? [X2] :
            ( ( ~ r2_lattice3(X0,k3_waybel_0(X0,sK7),X2)
              | ~ r2_lattice3(X0,sK7,X2) )
            & ( r2_lattice3(X0,k3_waybel_0(X0,sK7),X2)
              | r2_lattice3(X0,sK7,X2) )
            & m1_subset_1(X2,u1_struct_0(X0)) )
        & m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f44,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ( ~ r2_lattice3(X0,k3_waybel_0(X0,X1),X2)
                  | ~ r2_lattice3(X0,X1,X2) )
                & ( r2_lattice3(X0,k3_waybel_0(X0,X1),X2)
                  | r2_lattice3(X0,X1,X2) )
                & m1_subset_1(X2,u1_struct_0(X0)) )
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ( ~ r2_lattice3(sK6,k3_waybel_0(sK6,X1),X2)
                | ~ r2_lattice3(sK6,X1,X2) )
              & ( r2_lattice3(sK6,k3_waybel_0(sK6,X1),X2)
                | r2_lattice3(sK6,X1,X2) )
              & m1_subset_1(X2,u1_struct_0(sK6)) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK6))) )
      & l1_orders_2(sK6)
      & v4_orders_2(sK6)
      & v3_orders_2(sK6)
      & ~ v2_struct_0(sK6) ) ),
    introduced(choice_axiom,[])).

fof(f47,plain,
    ( ( ~ r2_lattice3(sK6,k3_waybel_0(sK6,sK7),sK8)
      | ~ r2_lattice3(sK6,sK7,sK8) )
    & ( r2_lattice3(sK6,k3_waybel_0(sK6,sK7),sK8)
      | r2_lattice3(sK6,sK7,sK8) )
    & m1_subset_1(sK8,u1_struct_0(sK6))
    & m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6)))
    & l1_orders_2(sK6)
    & v4_orders_2(sK6)
    & v3_orders_2(sK6)
    & ~ v2_struct_0(sK6) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7,sK8])],[f43,f46,f45,f44])).

fof(f74,plain,(
    m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6))) ),
    inference(cnf_transformation,[],[f47])).

fof(f73,plain,(
    l1_orders_2(sK6) ),
    inference(cnf_transformation,[],[f47])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_orders_2(X0) )
     => m1_subset_1(k3_waybel_0(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_waybel_0(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f14,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_waybel_0(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f13])).

fof(f64,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_waybel_0(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f21])).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l1_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ( r3_orders_2(X0,X1,X2)
      <=> r1_orders_2(X0,X1,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( ( r3_orders_2(X0,X1,X2)
      <=> r1_orders_2(X0,X1,X2) )
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( ( r3_orders_2(X0,X1,X2)
      <=> r1_orders_2(X0,X1,X2) )
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f15])).

fof(f41,plain,(
    ! [X0,X1,X2] :
      ( ( ( r3_orders_2(X0,X1,X2)
          | ~ r1_orders_2(X0,X1,X2) )
        & ( r1_orders_2(X0,X1,X2)
          | ~ r3_orders_2(X0,X1,X2) ) )
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f16])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( r1_orders_2(X0,X1,X2)
      | ~ r3_orders_2(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l1_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => r3_orders_2(X0,X1,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( r3_orders_2(X0,X1,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( r3_orders_2(X0,X1,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f17])).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( r3_orders_2(X0,X1,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f75,plain,(
    m1_subset_1(sK8,u1_struct_0(sK6)) ),
    inference(cnf_transformation,[],[f47])).

fof(f70,plain,(
    ~ v2_struct_0(sK6) ),
    inference(cnf_transformation,[],[f47])).

fof(f71,plain,(
    v3_orders_2(sK6) ),
    inference(cnf_transformation,[],[f47])).

fof(f2,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1,X2] :
          ( m1_subset_1(X2,u1_struct_0(X0))
         => ( r2_lattice3(X0,X1,X2)
          <=> ! [X3] :
                ( m1_subset_1(X3,u1_struct_0(X0))
               => ( r2_hidden(X3,X1)
                 => r1_orders_2(X0,X3,X2) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f11,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( r2_lattice3(X0,X1,X2)
          <=> ! [X3] :
                ( r1_orders_2(X0,X3,X2)
                | ~ r2_hidden(X3,X1)
                | ~ m1_subset_1(X3,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f12,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( r2_lattice3(X0,X1,X2)
          <=> ! [X3] :
                ( r1_orders_2(X0,X3,X2)
                | ~ r2_hidden(X3,X1)
                | ~ m1_subset_1(X3,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f11])).

fof(f37,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( r2_lattice3(X0,X1,X2)
              | ? [X3] :
                  ( ~ r1_orders_2(X0,X3,X2)
                  & r2_hidden(X3,X1)
                  & m1_subset_1(X3,u1_struct_0(X0)) ) )
            & ( ! [X3] :
                  ( r1_orders_2(X0,X3,X2)
                  | ~ r2_hidden(X3,X1)
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ r2_lattice3(X0,X1,X2) ) )
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(nnf_transformation,[],[f12])).

fof(f38,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( r2_lattice3(X0,X1,X2)
              | ? [X3] :
                  ( ~ r1_orders_2(X0,X3,X2)
                  & r2_hidden(X3,X1)
                  & m1_subset_1(X3,u1_struct_0(X0)) ) )
            & ( ! [X4] :
                  ( r1_orders_2(X0,X4,X2)
                  | ~ r2_hidden(X4,X1)
                  | ~ m1_subset_1(X4,u1_struct_0(X0)) )
              | ~ r2_lattice3(X0,X1,X2) ) )
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(rectify,[],[f37])).

fof(f39,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r1_orders_2(X0,X3,X2)
          & r2_hidden(X3,X1)
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ~ r1_orders_2(X0,sK5(X0,X1,X2),X2)
        & r2_hidden(sK5(X0,X1,X2),X1)
        & m1_subset_1(sK5(X0,X1,X2),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f40,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( r2_lattice3(X0,X1,X2)
              | ( ~ r1_orders_2(X0,sK5(X0,X1,X2),X2)
                & r2_hidden(sK5(X0,X1,X2),X1)
                & m1_subset_1(sK5(X0,X1,X2),u1_struct_0(X0)) ) )
            & ( ! [X4] :
                  ( r1_orders_2(X0,X4,X2)
                  | ~ r2_hidden(X4,X1)
                  | ~ m1_subset_1(X4,u1_struct_0(X0)) )
              | ~ r2_lattice3(X0,X1,X2) ) )
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f38,f39])).

fof(f60,plain,(
    ! [X4,X2,X0,X1] :
      ( r1_orders_2(X0,X4,X2)
      | ~ r2_hidden(X4,X1)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ r2_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f76,plain,
    ( r2_lattice3(sK6,k3_waybel_0(sK6,sK7),sK8)
    | r2_lattice3(sK6,sK7,sK8) ),
    inference(cnf_transformation,[],[f47])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( sP0(X0,X1,X2)
      | r2_hidden(sK3(X0,X1,X2),X0)
      | r2_hidden(sK2(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( r2_lattice3(X0,X1,X2)
      | ~ r1_orders_2(X0,sK5(X0,X1,X2),X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( r2_lattice3(X0,X1,X2)
      | r2_hidden(sK5(X0,X1,X2),X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f6,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
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
    inference(ennf_transformation,[],[f6])).

fof(f20,plain,(
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
    inference(flattening,[],[f19])).

fof(f68,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_orders_2(X0,X1,X3)
      | ~ r1_orders_2(X0,X2,X3)
      | ~ r1_orders_2(X0,X1,X2)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v4_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f72,plain,(
    v4_orders_2(sK6) ),
    inference(cnf_transformation,[],[f47])).

fof(f51,plain,(
    ! [X6,X2,X0,X1] :
      ( r1_orders_2(X1,X6,sK4(X0,X1,X6))
      | ~ r2_hidden(X6,X2)
      | ~ m1_subset_1(X6,u1_struct_0(X1))
      | ~ sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f52,plain,(
    ! [X6,X2,X0,X1] :
      ( r2_hidden(sK4(X0,X1,X6),X0)
      | ~ r2_hidden(X6,X2)
      | ~ m1_subset_1(X6,u1_struct_0(X1))
      | ~ sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f77,plain,
    ( ~ r2_lattice3(sK6,k3_waybel_0(sK6,sK7),sK8)
    | ~ r2_lattice3(sK6,sK7,sK8) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_7,plain,
    ( ~ r1_orders_2(X0,X1,X2)
    | ~ sP0(X3,X0,X4)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ r2_hidden(X2,X3)
    | r2_hidden(X1,X4) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_1,plain,
    ( ~ sP1(k3_waybel_0(X0,X1),X0,X1)
    | sP0(X1,X0,k3_waybel_0(X0,X1)) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_11,plain,
    ( sP1(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_orders_2(X1) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_25,negated_conjecture,
    ( m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6))) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_3240,plain,
    ( sP1(X0,sK6,sK7)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK6)))
    | ~ l1_orders_2(sK6) ),
    inference(resolution,[status(thm)],[c_11,c_25])).

cnf(c_26,negated_conjecture,
    ( l1_orders_2(sK6) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_3424,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK6)))
    | sP1(X0,sK6,sK7) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3240,c_26])).

cnf(c_3425,plain,
    ( sP1(X0,sK6,sK7)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK6))) ),
    inference(renaming,[status(thm)],[c_3424])).

cnf(c_16,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(k3_waybel_0(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_orders_2(X1) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_3442,plain,
    ( sP1(k3_waybel_0(sK6,X0),sK6,sK7)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK6)))
    | ~ l1_orders_2(sK6) ),
    inference(resolution,[status(thm)],[c_3425,c_16])).

cnf(c_3550,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK6)))
    | sP1(k3_waybel_0(sK6,X0),sK6,sK7) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3442,c_26])).

cnf(c_3551,plain,
    ( sP1(k3_waybel_0(sK6,X0),sK6,sK7)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK6))) ),
    inference(renaming,[status(thm)],[c_3550])).

cnf(c_3573,plain,
    ( sP0(sK7,sK6,k3_waybel_0(sK6,sK7))
    | ~ m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6))) ),
    inference(resolution,[status(thm)],[c_1,c_3551])).

cnf(c_1429,plain,
    ( m1_subset_1(k3_waybel_0(sK6,sK7),k1_zfmisc_1(u1_struct_0(sK6)))
    | ~ m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6)))
    | ~ l1_orders_2(sK6) ),
    inference(instantiation,[status(thm)],[c_16])).

cnf(c_1432,plain,
    ( sP1(X0,sK6,sK7)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK6)))
    | ~ m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6)))
    | ~ l1_orders_2(sK6) ),
    inference(instantiation,[status(thm)],[c_11])).

cnf(c_1560,plain,
    ( sP1(k3_waybel_0(sK6,sK7),sK6,sK7)
    | ~ m1_subset_1(k3_waybel_0(sK6,sK7),k1_zfmisc_1(u1_struct_0(sK6)))
    | ~ m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6)))
    | ~ l1_orders_2(sK6) ),
    inference(instantiation,[status(thm)],[c_1432])).

cnf(c_1708,plain,
    ( ~ sP1(k3_waybel_0(sK6,sK7),sK6,sK7)
    | sP0(sK7,sK6,k3_waybel_0(sK6,sK7)) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_3640,plain,
    ( sP0(sK7,sK6,k3_waybel_0(sK6,sK7)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3573,c_26,c_25,c_1429,c_1560,c_1708])).

cnf(c_7261,plain,
    ( ~ r1_orders_2(sK6,X0,X1)
    | ~ m1_subset_1(X0,u1_struct_0(sK6))
    | ~ m1_subset_1(X1,u1_struct_0(sK6))
    | r2_hidden(X0,k3_waybel_0(sK6,sK7))
    | ~ r2_hidden(X1,sK7) ),
    inference(resolution,[status(thm)],[c_7,c_3640])).

cnf(c_21,plain,
    ( m1_subset_1(X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r2_hidden(X0,X2) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_2192,plain,
    ( m1_subset_1(X0,u1_struct_0(sK6))
    | ~ r2_hidden(X0,sK7) ),
    inference(resolution,[status(thm)],[c_21,c_25])).

cnf(c_8145,plain,
    ( ~ r1_orders_2(sK6,X0,X1)
    | ~ m1_subset_1(X0,u1_struct_0(sK6))
    | r2_hidden(X0,k3_waybel_0(sK6,sK7))
    | ~ r2_hidden(X1,sK7) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_7261,c_2192])).

cnf(c_18,plain,
    ( ~ r3_orders_2(X0,X1,X2)
    | r1_orders_2(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | v2_struct_0(X0)
    | ~ v3_orders_2(X0)
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_19,plain,
    ( r3_orders_2(X0,X1,X1)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | v2_struct_0(X0)
    | ~ v3_orders_2(X0)
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_24,negated_conjecture,
    ( m1_subset_1(sK8,u1_struct_0(sK6)) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_5937,plain,
    ( r3_orders_2(sK6,X0,X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK6))
    | v2_struct_0(sK6)
    | ~ v3_orders_2(sK6)
    | ~ l1_orders_2(sK6) ),
    inference(resolution,[status(thm)],[c_19,c_24])).

cnf(c_1096,plain,
    ( m1_subset_1(sK8,u1_struct_0(sK6)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_1101,plain,
    ( r3_orders_2(X0,X1,X1) = iProver_top
    | m1_subset_1(X2,u1_struct_0(X0)) != iProver_top
    | m1_subset_1(X1,u1_struct_0(X0)) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | v3_orders_2(X0) != iProver_top
    | l1_orders_2(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_2905,plain,
    ( r3_orders_2(sK6,X0,X0) = iProver_top
    | m1_subset_1(X0,u1_struct_0(sK6)) != iProver_top
    | v2_struct_0(sK6) = iProver_top
    | v3_orders_2(sK6) != iProver_top
    | l1_orders_2(sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_1096,c_1101])).

cnf(c_29,negated_conjecture,
    ( ~ v2_struct_0(sK6) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_30,plain,
    ( v2_struct_0(sK6) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_28,negated_conjecture,
    ( v3_orders_2(sK6) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_31,plain,
    ( v3_orders_2(sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_33,plain,
    ( l1_orders_2(sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_3327,plain,
    ( m1_subset_1(X0,u1_struct_0(sK6)) != iProver_top
    | r3_orders_2(sK6,X0,X0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2905,c_30,c_31,c_33])).

cnf(c_3328,plain,
    ( r3_orders_2(sK6,X0,X0) = iProver_top
    | m1_subset_1(X0,u1_struct_0(sK6)) != iProver_top ),
    inference(renaming,[status(thm)],[c_3327])).

cnf(c_3329,plain,
    ( r3_orders_2(sK6,X0,X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK6)) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_3328])).

cnf(c_6120,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK6))
    | r3_orders_2(sK6,X0,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_5937,c_3329])).

cnf(c_6121,plain,
    ( r3_orders_2(sK6,X0,X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK6)) ),
    inference(renaming,[status(thm)],[c_6120])).

cnf(c_7564,plain,
    ( r1_orders_2(sK6,X0,X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK6))
    | v2_struct_0(sK6)
    | ~ v3_orders_2(sK6)
    | ~ l1_orders_2(sK6) ),
    inference(resolution,[status(thm)],[c_18,c_6121])).

cnf(c_7634,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK6))
    | r1_orders_2(sK6,X0,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_7564,c_29,c_28,c_26])).

cnf(c_7635,plain,
    ( r1_orders_2(sK6,X0,X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK6)) ),
    inference(renaming,[status(thm)],[c_7634])).

cnf(c_8187,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK6))
    | r2_hidden(X0,k3_waybel_0(sK6,sK7))
    | ~ r2_hidden(X0,sK7) ),
    inference(resolution,[status(thm)],[c_8145,c_7635])).

cnf(c_1095,plain,
    ( m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_1099,plain,
    ( m1_subset_1(X0,X1) = iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(X1)) != iProver_top
    | r2_hidden(X0,X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_1575,plain,
    ( m1_subset_1(X0,u1_struct_0(sK6)) = iProver_top
    | r2_hidden(X0,sK7) != iProver_top ),
    inference(superposition,[status(thm)],[c_1095,c_1099])).

cnf(c_1576,plain,
    ( m1_subset_1(X0,u1_struct_0(sK6))
    | ~ r2_hidden(X0,sK7) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_1575])).

cnf(c_8192,plain,
    ( r2_hidden(X0,k3_waybel_0(sK6,sK7))
    | ~ r2_hidden(X0,sK7) ),
    inference(global_propositional_subsumption,[status(thm)],[c_8187,c_1576])).

cnf(c_15,plain,
    ( ~ r2_lattice3(X0,X1,X2)
    | r1_orders_2(X0,X3,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ r2_hidden(X3,X1)
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_23,negated_conjecture,
    ( r2_lattice3(sK6,k3_waybel_0(sK6,sK7),sK8)
    | r2_lattice3(sK6,sK7,sK8) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_7244,plain,
    ( r2_lattice3(sK6,sK7,sK8)
    | r1_orders_2(sK6,X0,sK8)
    | ~ m1_subset_1(X0,u1_struct_0(sK6))
    | ~ m1_subset_1(sK8,u1_struct_0(sK6))
    | ~ r2_hidden(X0,k3_waybel_0(sK6,sK7))
    | ~ l1_orders_2(sK6) ),
    inference(resolution,[status(thm)],[c_15,c_23])).

cnf(c_1097,plain,
    ( r2_lattice3(sK6,k3_waybel_0(sK6,sK7),sK8) = iProver_top
    | r2_lattice3(sK6,sK7,sK8) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_1105,plain,
    ( r2_lattice3(X0,X1,X2) != iProver_top
    | r1_orders_2(X0,X3,X2) = iProver_top
    | m1_subset_1(X2,u1_struct_0(X0)) != iProver_top
    | m1_subset_1(X3,u1_struct_0(X0)) != iProver_top
    | r2_hidden(X3,X1) != iProver_top
    | l1_orders_2(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_4305,plain,
    ( r2_lattice3(sK6,X0,sK8) != iProver_top
    | r1_orders_2(sK6,X1,sK8) = iProver_top
    | m1_subset_1(X1,u1_struct_0(sK6)) != iProver_top
    | r2_hidden(X1,X0) != iProver_top
    | l1_orders_2(sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_1096,c_1105])).

cnf(c_4626,plain,
    ( r2_hidden(X1,X0) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK6)) != iProver_top
    | r1_orders_2(sK6,X1,sK8) = iProver_top
    | r2_lattice3(sK6,X0,sK8) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4305,c_33])).

cnf(c_4627,plain,
    ( r2_lattice3(sK6,X0,sK8) != iProver_top
    | r1_orders_2(sK6,X1,sK8) = iProver_top
    | m1_subset_1(X1,u1_struct_0(sK6)) != iProver_top
    | r2_hidden(X1,X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_4626])).

cnf(c_4636,plain,
    ( r2_lattice3(sK6,sK7,sK8) = iProver_top
    | r1_orders_2(sK6,X0,sK8) = iProver_top
    | m1_subset_1(X0,u1_struct_0(sK6)) != iProver_top
    | r2_hidden(X0,k3_waybel_0(sK6,sK7)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1097,c_4627])).

cnf(c_1104,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
    | m1_subset_1(k3_waybel_0(X1,X0),k1_zfmisc_1(u1_struct_0(X1))) = iProver_top
    | l1_orders_2(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_1771,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
    | m1_subset_1(X2,u1_struct_0(X1)) = iProver_top
    | r2_hidden(X2,k3_waybel_0(X1,X0)) != iProver_top
    | l1_orders_2(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1104,c_1099])).

cnf(c_2441,plain,
    ( m1_subset_1(X0,u1_struct_0(sK6)) = iProver_top
    | r2_hidden(X0,k3_waybel_0(sK6,sK7)) != iProver_top
    | l1_orders_2(sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_1095,c_1771])).

cnf(c_2564,plain,
    ( r2_hidden(X0,k3_waybel_0(sK6,sK7)) != iProver_top
    | m1_subset_1(X0,u1_struct_0(sK6)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2441,c_33])).

cnf(c_2565,plain,
    ( m1_subset_1(X0,u1_struct_0(sK6)) = iProver_top
    | r2_hidden(X0,k3_waybel_0(sK6,sK7)) != iProver_top ),
    inference(renaming,[status(thm)],[c_2564])).

cnf(c_4716,plain,
    ( r1_orders_2(sK6,X0,sK8) = iProver_top
    | r2_lattice3(sK6,sK7,sK8) = iProver_top
    | r2_hidden(X0,k3_waybel_0(sK6,sK7)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4636,c_2565])).

cnf(c_4717,plain,
    ( r2_lattice3(sK6,sK7,sK8) = iProver_top
    | r1_orders_2(sK6,X0,sK8) = iProver_top
    | r2_hidden(X0,k3_waybel_0(sK6,sK7)) != iProver_top ),
    inference(renaming,[status(thm)],[c_4716])).

cnf(c_4718,plain,
    ( r2_lattice3(sK6,sK7,sK8)
    | r1_orders_2(sK6,X0,sK8)
    | ~ r2_hidden(X0,k3_waybel_0(sK6,sK7)) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_4717])).

cnf(c_7569,plain,
    ( ~ r2_hidden(X0,k3_waybel_0(sK6,sK7))
    | r1_orders_2(sK6,X0,sK8)
    | r2_lattice3(sK6,sK7,sK8) ),
    inference(global_propositional_subsumption,[status(thm)],[c_7244,c_4718])).

cnf(c_7570,plain,
    ( r2_lattice3(sK6,sK7,sK8)
    | r1_orders_2(sK6,X0,sK8)
    | ~ r2_hidden(X0,k3_waybel_0(sK6,sK7)) ),
    inference(renaming,[status(thm)],[c_7569])).

cnf(c_8413,plain,
    ( r2_lattice3(sK6,sK7,sK8)
    | r1_orders_2(sK6,X0,sK8)
    | ~ r2_hidden(X0,sK7) ),
    inference(resolution,[status(thm)],[c_8192,c_7570])).

cnf(c_8430,plain,
    ( r1_orders_2(sK6,X0,sK8)
    | r1_orders_2(sK6,X1,sK8)
    | ~ m1_subset_1(X1,u1_struct_0(sK6))
    | ~ m1_subset_1(sK8,u1_struct_0(sK6))
    | ~ r2_hidden(X0,sK7)
    | ~ r2_hidden(X1,sK7)
    | ~ l1_orders_2(sK6) ),
    inference(resolution,[status(thm)],[c_8413,c_15])).

cnf(c_3,plain,
    ( sP0(X0,X1,X2)
    | r2_hidden(sK3(X0,X1,X2),X0)
    | r2_hidden(sK2(X0,X1,X2),X2) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_1117,plain,
    ( sP0(X0,X1,X2) = iProver_top
    | r2_hidden(sK3(X0,X1,X2),X0) = iProver_top
    | r2_hidden(sK2(X0,X1,X2),X2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_4725,plain,
    ( r2_lattice3(sK6,sK7,sK8) = iProver_top
    | r1_orders_2(sK6,sK3(k3_waybel_0(sK6,sK7),X0,X1),sK8) = iProver_top
    | sP0(k3_waybel_0(sK6,sK7),X0,X1) = iProver_top
    | r2_hidden(sK2(k3_waybel_0(sK6,sK7),X0,X1),X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_1117,c_4717])).

cnf(c_5998,plain,
    ( r2_lattice3(sK6,sK7,sK8) = iProver_top
    | r1_orders_2(sK6,sK3(k3_waybel_0(sK6,sK7),X0,k3_waybel_0(sK6,sK7)),sK8) = iProver_top
    | r1_orders_2(sK6,sK2(k3_waybel_0(sK6,sK7),X0,k3_waybel_0(sK6,sK7)),sK8) = iProver_top
    | sP0(k3_waybel_0(sK6,sK7),X0,k3_waybel_0(sK6,sK7)) = iProver_top ),
    inference(superposition,[status(thm)],[c_4725,c_4717])).

cnf(c_35,plain,
    ( m1_subset_1(sK8,u1_struct_0(sK6)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_12,plain,
    ( r2_lattice3(X0,X1,X2)
    | ~ r1_orders_2(X0,sK5(X0,X1,X2),X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_8425,plain,
    ( r2_lattice3(sK6,X0,sK8)
    | r2_lattice3(sK6,sK7,sK8)
    | ~ m1_subset_1(sK8,u1_struct_0(sK6))
    | ~ r2_hidden(sK5(sK6,X0,sK8),sK7)
    | ~ l1_orders_2(sK6) ),
    inference(resolution,[status(thm)],[c_8413,c_12])).

cnf(c_8864,plain,
    ( ~ r2_hidden(sK5(sK6,X0,sK8),sK7)
    | r2_lattice3(sK6,X0,sK8)
    | r2_lattice3(sK6,sK7,sK8) ),
    inference(global_propositional_subsumption,[status(thm)],[c_8425,c_26,c_24])).

cnf(c_8865,plain,
    ( r2_lattice3(sK6,X0,sK8)
    | r2_lattice3(sK6,sK7,sK8)
    | ~ r2_hidden(sK5(sK6,X0,sK8),sK7) ),
    inference(renaming,[status(thm)],[c_8864])).

cnf(c_13,plain,
    ( r2_lattice3(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | r2_hidden(sK5(X0,X1,X2),X1)
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_8886,plain,
    ( r2_lattice3(sK6,sK7,sK8)
    | ~ m1_subset_1(sK8,u1_struct_0(sK6))
    | ~ l1_orders_2(sK6) ),
    inference(resolution,[status(thm)],[c_8865,c_13])).

cnf(c_8887,plain,
    ( r2_lattice3(sK6,sK7,sK8) = iProver_top
    | m1_subset_1(sK8,u1_struct_0(sK6)) != iProver_top
    | l1_orders_2(sK6) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8886])).

cnf(c_8975,plain,
    ( r2_lattice3(sK6,sK7,sK8) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5998,c_33,c_35,c_8887])).

cnf(c_8980,plain,
    ( r1_orders_2(sK6,X0,sK8) = iProver_top
    | m1_subset_1(X0,u1_struct_0(sK6)) != iProver_top
    | r2_hidden(X0,sK7) != iProver_top ),
    inference(superposition,[status(thm)],[c_8975,c_4627])).

cnf(c_9002,plain,
    ( r1_orders_2(sK6,X0,sK8) = iProver_top
    | r2_hidden(X0,sK7) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_8980,c_1575])).

cnf(c_9004,plain,
    ( r1_orders_2(sK6,X0,sK8)
    | ~ r2_hidden(X0,sK7) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_9002])).

cnf(c_9120,plain,
    ( r1_orders_2(sK6,X0,sK8)
    | ~ r2_hidden(X0,sK7) ),
    inference(global_propositional_subsumption,[status(thm)],[c_8430,c_9004])).

cnf(c_20,plain,
    ( ~ r1_orders_2(X0,X1,X2)
    | ~ r1_orders_2(X0,X2,X3)
    | r1_orders_2(X0,X1,X3)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ v4_orders_2(X0)
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_9140,plain,
    ( ~ r1_orders_2(sK6,X0,X1)
    | r1_orders_2(sK6,X0,sK8)
    | ~ m1_subset_1(X0,u1_struct_0(sK6))
    | ~ m1_subset_1(X1,u1_struct_0(sK6))
    | ~ m1_subset_1(sK8,u1_struct_0(sK6))
    | ~ r2_hidden(X1,sK7)
    | ~ v4_orders_2(sK6)
    | ~ l1_orders_2(sK6) ),
    inference(resolution,[status(thm)],[c_9120,c_20])).

cnf(c_27,negated_conjecture,
    ( v4_orders_2(sK6) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_11122,plain,
    ( ~ m1_subset_1(X1,u1_struct_0(sK6))
    | ~ m1_subset_1(X0,u1_struct_0(sK6))
    | r1_orders_2(sK6,X0,sK8)
    | ~ r1_orders_2(sK6,X0,X1)
    | ~ r2_hidden(X1,sK7) ),
    inference(global_propositional_subsumption,[status(thm)],[c_9140,c_27,c_26,c_24])).

cnf(c_11123,plain,
    ( ~ r1_orders_2(sK6,X0,X1)
    | r1_orders_2(sK6,X0,sK8)
    | ~ m1_subset_1(X0,u1_struct_0(sK6))
    | ~ m1_subset_1(X1,u1_struct_0(sK6))
    | ~ r2_hidden(X1,sK7) ),
    inference(renaming,[status(thm)],[c_11122])).

cnf(c_11131,plain,
    ( ~ r1_orders_2(sK6,X0,X1)
    | r1_orders_2(sK6,X0,sK8)
    | ~ m1_subset_1(X0,u1_struct_0(sK6))
    | ~ r2_hidden(X1,sK7) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_11123,c_2192])).

cnf(c_9,plain,
    ( r1_orders_2(X0,X1,sK4(X2,X0,X1))
    | ~ sP0(X2,X0,X3)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ r2_hidden(X1,X3) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_5899,plain,
    ( r1_orders_2(sK6,X0,sK4(sK7,sK6,X0))
    | ~ m1_subset_1(X0,u1_struct_0(sK6))
    | ~ r2_hidden(X0,k3_waybel_0(sK6,sK7)) ),
    inference(resolution,[status(thm)],[c_9,c_3640])).

cnf(c_2566,plain,
    ( m1_subset_1(X0,u1_struct_0(sK6))
    | ~ r2_hidden(X0,k3_waybel_0(sK6,sK7)) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_2565])).

cnf(c_6309,plain,
    ( r1_orders_2(sK6,X0,sK4(sK7,sK6,X0))
    | ~ r2_hidden(X0,k3_waybel_0(sK6,sK7)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_5899,c_2566])).

cnf(c_11312,plain,
    ( r1_orders_2(sK6,X0,sK8)
    | ~ m1_subset_1(X0,u1_struct_0(sK6))
    | ~ r2_hidden(X0,k3_waybel_0(sK6,sK7))
    | ~ r2_hidden(sK4(sK7,sK6,X0),sK7) ),
    inference(resolution,[status(thm)],[c_11131,c_6309])).

cnf(c_8,plain,
    ( ~ sP0(X0,X1,X2)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ r2_hidden(X3,X2)
    | r2_hidden(sK4(X0,X1,X3),X0) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_4671,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK6))
    | ~ r2_hidden(X0,k3_waybel_0(sK6,sK7))
    | r2_hidden(sK4(sK7,sK6,X0),sK7) ),
    inference(resolution,[status(thm)],[c_8,c_3640])).

cnf(c_4923,plain,
    ( ~ r2_hidden(X0,k3_waybel_0(sK6,sK7))
    | r2_hidden(sK4(sK7,sK6,X0),sK7) ),
    inference(global_propositional_subsumption,[status(thm)],[c_4671,c_2566])).

cnf(c_11324,plain,
    ( ~ r2_hidden(X0,k3_waybel_0(sK6,sK7))
    | r1_orders_2(sK6,X0,sK8) ),
    inference(global_propositional_subsumption,[status(thm)],[c_11312,c_2566,c_4671])).

cnf(c_11325,plain,
    ( r1_orders_2(sK6,X0,sK8)
    | ~ r2_hidden(X0,k3_waybel_0(sK6,sK7)) ),
    inference(renaming,[status(thm)],[c_11324])).

cnf(c_11503,plain,
    ( r2_lattice3(X0,k3_waybel_0(sK6,sK7),X1)
    | r1_orders_2(sK6,sK5(X0,k3_waybel_0(sK6,sK7),X1),sK8)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ l1_orders_2(X0) ),
    inference(resolution,[status(thm)],[c_11325,c_13])).

cnf(c_12829,plain,
    ( r2_lattice3(sK6,k3_waybel_0(sK6,sK7),sK8)
    | ~ m1_subset_1(sK8,u1_struct_0(sK6))
    | ~ l1_orders_2(sK6) ),
    inference(resolution,[status(thm)],[c_11503,c_12])).

cnf(c_22,negated_conjecture,
    ( ~ r2_lattice3(sK6,k3_waybel_0(sK6,sK7),sK8)
    | ~ r2_lattice3(sK6,sK7,sK8) ),
    inference(cnf_transformation,[],[f77])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_12829,c_8886,c_22,c_24,c_26])).


%------------------------------------------------------------------------------
