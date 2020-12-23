%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT1656+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n032.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:46:06 EST 2020

% Result     : Theorem 3.93s
% Output     : CNFRefutation 3.93s
% Verified   : 
% Statistics : Number of formulae       :  209 (4509 expanded)
%              Number of clauses        :  138 (1055 expanded)
%              Number of leaves         :   17 (1203 expanded)
%              Depth                    :   39
%              Number of atoms          :  994 (33855 expanded)
%              Number of equality atoms :  147 ( 810 expanded)
%              Maximal formula depth    :   14 (   6 average)
%              Maximal clause size      :   20 (   4 average)
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
                & r1_orders_2(X0,X4,X3)
                & m1_subset_1(X4,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X3,u1_struct_0(X0)) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f30,plain,(
    ! [X1,X0,X2] :
      ( ( sP0(X1,X0,X2)
        | ? [X3] :
            ( ( ! [X4] :
                  ( ~ r2_hidden(X4,X1)
                  | ~ r1_orders_2(X0,X4,X3)
                  | ~ m1_subset_1(X4,u1_struct_0(X0)) )
              | ~ r2_hidden(X3,X2) )
            & ( ? [X4] :
                  ( r2_hidden(X4,X1)
                  & r1_orders_2(X0,X4,X3)
                  & m1_subset_1(X4,u1_struct_0(X0)) )
              | r2_hidden(X3,X2) )
            & m1_subset_1(X3,u1_struct_0(X0)) ) )
      & ( ! [X3] :
            ( ( ( r2_hidden(X3,X2)
                | ! [X4] :
                    ( ~ r2_hidden(X4,X1)
                    | ~ r1_orders_2(X0,X4,X3)
                    | ~ m1_subset_1(X4,u1_struct_0(X0)) ) )
              & ( ? [X4] :
                    ( r2_hidden(X4,X1)
                    & r1_orders_2(X0,X4,X3)
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
                  | ~ r1_orders_2(X0,X4,X3)
                  | ~ m1_subset_1(X4,u1_struct_0(X0)) )
              | ~ r2_hidden(X3,X2) )
            & ( ? [X4] :
                  ( r2_hidden(X4,X1)
                  & r1_orders_2(X0,X4,X3)
                  & m1_subset_1(X4,u1_struct_0(X0)) )
              | r2_hidden(X3,X2) )
            & m1_subset_1(X3,u1_struct_0(X0)) ) )
      & ( ! [X3] :
            ( ( ( r2_hidden(X3,X2)
                | ! [X4] :
                    ( ~ r2_hidden(X4,X1)
                    | ~ r1_orders_2(X0,X4,X3)
                    | ~ m1_subset_1(X4,u1_struct_0(X0)) ) )
              & ( ? [X4] :
                    ( r2_hidden(X4,X1)
                    & r1_orders_2(X0,X4,X3)
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
                  | ~ r1_orders_2(X1,X4,X3)
                  | ~ m1_subset_1(X4,u1_struct_0(X1)) )
              | ~ r2_hidden(X3,X2) )
            & ( ? [X5] :
                  ( r2_hidden(X5,X0)
                  & r1_orders_2(X1,X5,X3)
                  & m1_subset_1(X5,u1_struct_0(X1)) )
              | r2_hidden(X3,X2) )
            & m1_subset_1(X3,u1_struct_0(X1)) ) )
      & ( ! [X6] :
            ( ( ( r2_hidden(X6,X2)
                | ! [X7] :
                    ( ~ r2_hidden(X7,X0)
                    | ~ r1_orders_2(X1,X7,X6)
                    | ~ m1_subset_1(X7,u1_struct_0(X1)) ) )
              & ( ? [X8] :
                    ( r2_hidden(X8,X0)
                    & r1_orders_2(X1,X8,X6)
                    & m1_subset_1(X8,u1_struct_0(X1)) )
                | ~ r2_hidden(X6,X2) ) )
            | ~ m1_subset_1(X6,u1_struct_0(X1)) )
        | ~ sP0(X0,X1,X2) ) ) ),
    inference(rectify,[],[f31])).

fof(f35,plain,(
    ! [X6,X1,X0] :
      ( ? [X8] :
          ( r2_hidden(X8,X0)
          & r1_orders_2(X1,X8,X6)
          & m1_subset_1(X8,u1_struct_0(X1)) )
     => ( r2_hidden(sK4(X0,X1,X6),X0)
        & r1_orders_2(X1,sK4(X0,X1,X6),X6)
        & m1_subset_1(sK4(X0,X1,X6),u1_struct_0(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,(
    ! [X3,X2,X1,X0] :
      ( ? [X5] :
          ( r2_hidden(X5,X0)
          & r1_orders_2(X1,X5,X3)
          & m1_subset_1(X5,u1_struct_0(X1)) )
     => ( r2_hidden(sK3(X0,X1,X2),X0)
        & r1_orders_2(X1,sK3(X0,X1,X2),X3)
        & m1_subset_1(sK3(X0,X1,X2),u1_struct_0(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ! [X4] :
                ( ~ r2_hidden(X4,X0)
                | ~ r1_orders_2(X1,X4,X3)
                | ~ m1_subset_1(X4,u1_struct_0(X1)) )
            | ~ r2_hidden(X3,X2) )
          & ( ? [X5] :
                ( r2_hidden(X5,X0)
                & r1_orders_2(X1,X5,X3)
                & m1_subset_1(X5,u1_struct_0(X1)) )
            | r2_hidden(X3,X2) )
          & m1_subset_1(X3,u1_struct_0(X1)) )
     => ( ( ! [X4] :
              ( ~ r2_hidden(X4,X0)
              | ~ r1_orders_2(X1,X4,sK2(X0,X1,X2))
              | ~ m1_subset_1(X4,u1_struct_0(X1)) )
          | ~ r2_hidden(sK2(X0,X1,X2),X2) )
        & ( ? [X5] :
              ( r2_hidden(X5,X0)
              & r1_orders_2(X1,X5,sK2(X0,X1,X2))
              & m1_subset_1(X5,u1_struct_0(X1)) )
          | r2_hidden(sK2(X0,X1,X2),X2) )
        & m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( ( sP0(X0,X1,X2)
        | ( ( ! [X4] :
                ( ~ r2_hidden(X4,X0)
                | ~ r1_orders_2(X1,X4,sK2(X0,X1,X2))
                | ~ m1_subset_1(X4,u1_struct_0(X1)) )
            | ~ r2_hidden(sK2(X0,X1,X2),X2) )
          & ( ( r2_hidden(sK3(X0,X1,X2),X0)
              & r1_orders_2(X1,sK3(X0,X1,X2),sK2(X0,X1,X2))
              & m1_subset_1(sK3(X0,X1,X2),u1_struct_0(X1)) )
            | r2_hidden(sK2(X0,X1,X2),X2) )
          & m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X1)) ) )
      & ( ! [X6] :
            ( ( ( r2_hidden(X6,X2)
                | ! [X7] :
                    ( ~ r2_hidden(X7,X0)
                    | ~ r1_orders_2(X1,X7,X6)
                    | ~ m1_subset_1(X7,u1_struct_0(X1)) ) )
              & ( ( r2_hidden(sK4(X0,X1,X6),X0)
                  & r1_orders_2(X1,sK4(X0,X1,X6),X6)
                  & m1_subset_1(sK4(X0,X1,X6),u1_struct_0(X1)) )
                | ~ r2_hidden(X6,X2) ) )
            | ~ m1_subset_1(X6,u1_struct_0(X1)) )
        | ~ sP0(X0,X1,X2) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f32,f35,f34,f33])).

fof(f53,plain,(
    ! [X6,X2,X0,X7,X1] :
      ( r2_hidden(X6,X2)
      | ~ r2_hidden(X7,X0)
      | ~ r1_orders_2(X1,X7,X6)
      | ~ m1_subset_1(X7,u1_struct_0(X1))
      | ~ m1_subset_1(X6,u1_struct_0(X1))
      | ~ sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f1,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( k4_waybel_0(X0,X1) = X2
              <=> ! [X3] :
                    ( m1_subset_1(X3,u1_struct_0(X0))
                   => ( r2_hidden(X3,X2)
                    <=> ? [X4] :
                          ( r2_hidden(X4,X1)
                          & r1_orders_2(X0,X4,X3)
                          & m1_subset_1(X4,u1_struct_0(X0)) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f10,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( k4_waybel_0(X0,X1) = X2
              <=> ! [X3] :
                    ( ( r2_hidden(X3,X2)
                    <=> ? [X4] :
                          ( r2_hidden(X4,X1)
                          & r1_orders_2(X0,X4,X3)
                          & m1_subset_1(X4,u1_struct_0(X0)) ) )
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f26,plain,(
    ! [X2,X0,X1] :
      ( ( k4_waybel_0(X0,X1) = X2
      <=> sP0(X1,X0,X2) )
      | ~ sP1(X2,X0,X1) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

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

fof(f28,plain,(
    ! [X2,X0,X1] :
      ( ( ( k4_waybel_0(X0,X1) = X2
          | ~ sP0(X1,X0,X2) )
        & ( sP0(X1,X0,X2)
          | k4_waybel_0(X0,X1) != X2 ) )
      | ~ sP1(X2,X0,X1) ) ),
    inference(nnf_transformation,[],[f26])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( ( ( k4_waybel_0(X1,X2) = X0
          | ~ sP0(X2,X1,X0) )
        & ( sP0(X2,X1,X0)
          | k4_waybel_0(X1,X2) != X0 ) )
      | ~ sP1(X0,X1,X2) ) ),
    inference(rectify,[],[f28])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( sP0(X2,X1,X0)
      | k4_waybel_0(X1,X2) != X0
      | ~ sP1(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f78,plain,(
    ! [X2,X1] :
      ( sP0(X2,X1,k4_waybel_0(X1,X2))
      | ~ sP1(k4_waybel_0(X1,X2),X1,X2) ) ),
    inference(equality_resolution,[],[f48])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_orders_2(X0) )
     => m1_subset_1(k4_waybel_0(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k4_waybel_0(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f14,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k4_waybel_0(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f13])).

fof(f64,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k4_waybel_0(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f14])).

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
             => ( r1_lattice3(X0,X1,X2)
              <=> r1_lattice3(X0,k4_waybel_0(X0,X1),X2) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

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
               => ( r1_lattice3(X0,X1,X2)
                <=> r1_lattice3(X0,k4_waybel_0(X0,X1),X2) ) ) ) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f23,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( r1_lattice3(X0,X1,X2)
              <~> r1_lattice3(X0,k4_waybel_0(X0,X1),X2) )
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
              ( ( r1_lattice3(X0,X1,X2)
              <~> r1_lattice3(X0,k4_waybel_0(X0,X1),X2) )
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
              ( ( ~ r1_lattice3(X0,k4_waybel_0(X0,X1),X2)
                | ~ r1_lattice3(X0,X1,X2) )
              & ( r1_lattice3(X0,k4_waybel_0(X0,X1),X2)
                | r1_lattice3(X0,X1,X2) )
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
              ( ( ~ r1_lattice3(X0,k4_waybel_0(X0,X1),X2)
                | ~ r1_lattice3(X0,X1,X2) )
              & ( r1_lattice3(X0,k4_waybel_0(X0,X1),X2)
                | r1_lattice3(X0,X1,X2) )
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
          ( ( ~ r1_lattice3(X0,k4_waybel_0(X0,X1),X2)
            | ~ r1_lattice3(X0,X1,X2) )
          & ( r1_lattice3(X0,k4_waybel_0(X0,X1),X2)
            | r1_lattice3(X0,X1,X2) )
          & m1_subset_1(X2,u1_struct_0(X0)) )
     => ( ( ~ r1_lattice3(X0,k4_waybel_0(X0,X1),sK8)
          | ~ r1_lattice3(X0,X1,sK8) )
        & ( r1_lattice3(X0,k4_waybel_0(X0,X1),sK8)
          | r1_lattice3(X0,X1,sK8) )
        & m1_subset_1(sK8,u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f45,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ~ r1_lattice3(X0,k4_waybel_0(X0,X1),X2)
                | ~ r1_lattice3(X0,X1,X2) )
              & ( r1_lattice3(X0,k4_waybel_0(X0,X1),X2)
                | r1_lattice3(X0,X1,X2) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ? [X2] :
            ( ( ~ r1_lattice3(X0,k4_waybel_0(X0,sK7),X2)
              | ~ r1_lattice3(X0,sK7,X2) )
            & ( r1_lattice3(X0,k4_waybel_0(X0,sK7),X2)
              | r1_lattice3(X0,sK7,X2) )
            & m1_subset_1(X2,u1_struct_0(X0)) )
        & m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f44,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ( ~ r1_lattice3(X0,k4_waybel_0(X0,X1),X2)
                  | ~ r1_lattice3(X0,X1,X2) )
                & ( r1_lattice3(X0,k4_waybel_0(X0,X1),X2)
                  | r1_lattice3(X0,X1,X2) )
                & m1_subset_1(X2,u1_struct_0(X0)) )
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ( ~ r1_lattice3(sK6,k4_waybel_0(sK6,X1),X2)
                | ~ r1_lattice3(sK6,X1,X2) )
              & ( r1_lattice3(sK6,k4_waybel_0(sK6,X1),X2)
                | r1_lattice3(sK6,X1,X2) )
              & m1_subset_1(X2,u1_struct_0(sK6)) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK6))) )
      & l1_orders_2(sK6)
      & v4_orders_2(sK6)
      & v3_orders_2(sK6)
      & ~ v2_struct_0(sK6) ) ),
    introduced(choice_axiom,[])).

fof(f47,plain,
    ( ( ~ r1_lattice3(sK6,k4_waybel_0(sK6,sK7),sK8)
      | ~ r1_lattice3(sK6,sK7,sK8) )
    & ( r1_lattice3(sK6,k4_waybel_0(sK6,sK7),sK8)
      | r1_lattice3(sK6,sK7,sK8) )
    & m1_subset_1(sK8,u1_struct_0(sK6))
    & m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6)))
    & l1_orders_2(sK6)
    & v4_orders_2(sK6)
    & v3_orders_2(sK6)
    & ~ v2_struct_0(sK6) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7,sK8])],[f43,f46,f45,f44])).

fof(f73,plain,(
    l1_orders_2(sK6) ),
    inference(cnf_transformation,[],[f47])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

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

fof(f74,plain,(
    m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6))) ),
    inference(cnf_transformation,[],[f47])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l1_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => r3_orders_2(X0,X1,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

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

fof(f71,plain,(
    v3_orders_2(sK6) ),
    inference(cnf_transformation,[],[f47])).

fof(f70,plain,(
    ~ v2_struct_0(sK6) ),
    inference(cnf_transformation,[],[f47])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l1_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ( r3_orders_2(X0,X1,X2)
      <=> r1_orders_2(X0,X1,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

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

fof(f2,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1,X2] :
          ( m1_subset_1(X2,u1_struct_0(X0))
         => ( r1_lattice3(X0,X1,X2)
          <=> ! [X3] :
                ( m1_subset_1(X3,u1_struct_0(X0))
               => ( r2_hidden(X3,X1)
                 => r1_orders_2(X0,X2,X3) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f11,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( r1_lattice3(X0,X1,X2)
          <=> ! [X3] :
                ( r1_orders_2(X0,X2,X3)
                | ~ r2_hidden(X3,X1)
                | ~ m1_subset_1(X3,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f12,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( r1_lattice3(X0,X1,X2)
          <=> ! [X3] :
                ( r1_orders_2(X0,X2,X3)
                | ~ r2_hidden(X3,X1)
                | ~ m1_subset_1(X3,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f11])).

fof(f37,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( r1_lattice3(X0,X1,X2)
              | ? [X3] :
                  ( ~ r1_orders_2(X0,X2,X3)
                  & r2_hidden(X3,X1)
                  & m1_subset_1(X3,u1_struct_0(X0)) ) )
            & ( ! [X3] :
                  ( r1_orders_2(X0,X2,X3)
                  | ~ r2_hidden(X3,X1)
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ r1_lattice3(X0,X1,X2) ) )
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(nnf_transformation,[],[f12])).

fof(f38,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( r1_lattice3(X0,X1,X2)
              | ? [X3] :
                  ( ~ r1_orders_2(X0,X2,X3)
                  & r2_hidden(X3,X1)
                  & m1_subset_1(X3,u1_struct_0(X0)) ) )
            & ( ! [X4] :
                  ( r1_orders_2(X0,X2,X4)
                  | ~ r2_hidden(X4,X1)
                  | ~ m1_subset_1(X4,u1_struct_0(X0)) )
              | ~ r1_lattice3(X0,X1,X2) ) )
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(rectify,[],[f37])).

fof(f39,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r1_orders_2(X0,X2,X3)
          & r2_hidden(X3,X1)
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ~ r1_orders_2(X0,X2,sK5(X0,X1,X2))
        & r2_hidden(sK5(X0,X1,X2),X1)
        & m1_subset_1(sK5(X0,X1,X2),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f40,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( r1_lattice3(X0,X1,X2)
              | ( ~ r1_orders_2(X0,X2,sK5(X0,X1,X2))
                & r2_hidden(sK5(X0,X1,X2),X1)
                & m1_subset_1(sK5(X0,X1,X2),u1_struct_0(X0)) ) )
            & ( ! [X4] :
                  ( r1_orders_2(X0,X2,X4)
                  | ~ r2_hidden(X4,X1)
                  | ~ m1_subset_1(X4,u1_struct_0(X0)) )
              | ~ r1_lattice3(X0,X1,X2) ) )
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f38,f39])).

fof(f60,plain,(
    ! [X4,X2,X0,X1] :
      ( r1_orders_2(X0,X2,X4)
      | ~ r2_hidden(X4,X1)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ r1_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f76,plain,
    ( r1_lattice3(sK6,k4_waybel_0(sK6,sK7),sK8)
    | r1_lattice3(sK6,sK7,sK8) ),
    inference(cnf_transformation,[],[f47])).

fof(f75,plain,(
    m1_subset_1(sK8,u1_struct_0(sK6)) ),
    inference(cnf_transformation,[],[f47])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( r1_lattice3(X0,X1,X2)
      | ~ r1_orders_2(X0,X2,sK5(X0,X1,X2))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( r1_lattice3(X0,X1,X2)
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

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
      ( r1_orders_2(X1,sK4(X0,X1,X6),X6)
      | ~ r2_hidden(X6,X2)
      | ~ m1_subset_1(X6,u1_struct_0(X1))
      | ~ sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( sP0(X0,X1,X2)
      | r2_hidden(sK3(X0,X1,X2),X0)
      | r2_hidden(sK2(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f50,plain,(
    ! [X6,X2,X0,X1] :
      ( m1_subset_1(sK4(X0,X1,X6),u1_struct_0(X1))
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
    ( ~ r1_lattice3(sK6,k4_waybel_0(sK6,sK7),sK8)
    | ~ r1_lattice3(sK6,sK7,sK8) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_7,plain,
    ( ~ r1_orders_2(X0,X1,X2)
    | ~ sP0(X3,X0,X4)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ r2_hidden(X1,X3)
    | r2_hidden(X2,X4) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_11,plain,
    ( sP1(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_orders_2(X1) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_1,plain,
    ( ~ sP1(k4_waybel_0(X0,X1),X0,X1)
    | sP0(X1,X0,k4_waybel_0(X0,X1)) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_456,plain,
    ( sP0(X0,X1,k4_waybel_0(X1,X0))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3)))
    | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X3)))
    | ~ l1_orders_2(X3)
    | X1 != X3
    | X0 != X4
    | k4_waybel_0(X1,X0) != X2 ),
    inference(resolution_lifted,[status(thm)],[c_11,c_1])).

cnf(c_457,plain,
    ( sP0(X0,X1,k4_waybel_0(X1,X0))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(k4_waybel_0(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_orders_2(X1) ),
    inference(unflattening,[status(thm)],[c_456])).

cnf(c_16,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(k4_waybel_0(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_orders_2(X1) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_461,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | sP0(X0,X1,k4_waybel_0(X1,X0))
    | ~ l1_orders_2(X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_457,c_16])).

cnf(c_462,plain,
    ( sP0(X0,X1,k4_waybel_0(X1,X0))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_orders_2(X1) ),
    inference(renaming,[status(thm)],[c_461])).

cnf(c_26,negated_conjecture,
    ( l1_orders_2(sK6) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_586,plain,
    ( sP0(X0,X1,k4_waybel_0(X1,X0))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | sK6 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_462,c_26])).

cnf(c_587,plain,
    ( sP0(X0,sK6,k4_waybel_0(sK6,X0))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK6))) ),
    inference(unflattening,[status(thm)],[c_586])).

cnf(c_6749,plain,
    ( ~ r1_orders_2(sK6,X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK6)))
    | ~ m1_subset_1(X1,u1_struct_0(sK6))
    | ~ m1_subset_1(X0,u1_struct_0(sK6))
    | ~ r2_hidden(X0,X2)
    | r2_hidden(X1,k4_waybel_0(sK6,X2)) ),
    inference(resolution,[status(thm)],[c_7,c_587])).

cnf(c_1313,plain,
    ( ~ r1_orders_2(X0,X1,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK6)))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ r2_hidden(X1,X4)
    | r2_hidden(X2,X5)
    | X3 != X4
    | k4_waybel_0(sK6,X3) != X5
    | sK6 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_7,c_587])).

cnf(c_1314,plain,
    ( ~ r1_orders_2(sK6,X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK6)))
    | ~ m1_subset_1(X1,u1_struct_0(sK6))
    | ~ m1_subset_1(X0,u1_struct_0(sK6))
    | ~ r2_hidden(X0,X2)
    | r2_hidden(X1,k4_waybel_0(sK6,X2)) ),
    inference(unflattening,[status(thm)],[c_1313])).

cnf(c_21,plain,
    ( m1_subset_1(X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r2_hidden(X0,X2) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_1330,plain,
    ( ~ r1_orders_2(sK6,X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK6)))
    | ~ m1_subset_1(X1,u1_struct_0(sK6))
    | ~ r2_hidden(X0,X2)
    | r2_hidden(X1,k4_waybel_0(sK6,X2)) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_1314,c_21])).

cnf(c_7077,plain,
    ( ~ m1_subset_1(X1,u1_struct_0(sK6))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK6)))
    | ~ r1_orders_2(sK6,X0,X1)
    | ~ r2_hidden(X0,X2)
    | r2_hidden(X1,k4_waybel_0(sK6,X2)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_6749,c_1330])).

cnf(c_7078,plain,
    ( ~ r1_orders_2(sK6,X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK6)))
    | ~ m1_subset_1(X1,u1_struct_0(sK6))
    | ~ r2_hidden(X0,X2)
    | r2_hidden(X1,k4_waybel_0(sK6,X2)) ),
    inference(renaming,[status(thm)],[c_7077])).

cnf(c_25,negated_conjecture,
    ( m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6))) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_7105,plain,
    ( ~ r1_orders_2(sK6,X0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK6))
    | r2_hidden(X1,k4_waybel_0(sK6,sK7))
    | ~ r2_hidden(X0,sK7) ),
    inference(resolution,[status(thm)],[c_7078,c_25])).

cnf(c_19,plain,
    ( r3_orders_2(X0,X1,X1)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | v2_struct_0(X0)
    | ~ v3_orders_2(X0)
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_28,negated_conjecture,
    ( v3_orders_2(sK6) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_487,plain,
    ( r3_orders_2(X0,X1,X1)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | v2_struct_0(X0)
    | ~ l1_orders_2(X0)
    | sK6 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_19,c_28])).

cnf(c_488,plain,
    ( r3_orders_2(sK6,X0,X0)
    | ~ m1_subset_1(X1,u1_struct_0(sK6))
    | ~ m1_subset_1(X0,u1_struct_0(sK6))
    | v2_struct_0(sK6)
    | ~ l1_orders_2(sK6) ),
    inference(unflattening,[status(thm)],[c_487])).

cnf(c_29,negated_conjecture,
    ( ~ v2_struct_0(sK6) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_492,plain,
    ( r3_orders_2(sK6,X0,X0)
    | ~ m1_subset_1(X1,u1_struct_0(sK6))
    | ~ m1_subset_1(X0,u1_struct_0(sK6)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_488,c_29,c_26])).

cnf(c_18,plain,
    ( ~ r3_orders_2(X0,X1,X2)
    | r1_orders_2(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | v2_struct_0(X0)
    | ~ v3_orders_2(X0)
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_508,plain,
    ( ~ r3_orders_2(X0,X1,X2)
    | r1_orders_2(X0,X1,X2)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | v2_struct_0(X0)
    | ~ l1_orders_2(X0)
    | sK6 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_18,c_28])).

cnf(c_509,plain,
    ( ~ r3_orders_2(sK6,X0,X1)
    | r1_orders_2(sK6,X0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK6))
    | ~ m1_subset_1(X0,u1_struct_0(sK6))
    | v2_struct_0(sK6)
    | ~ l1_orders_2(sK6) ),
    inference(unflattening,[status(thm)],[c_508])).

cnf(c_513,plain,
    ( ~ r3_orders_2(sK6,X0,X1)
    | r1_orders_2(sK6,X0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK6))
    | ~ m1_subset_1(X0,u1_struct_0(sK6)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_509,c_29,c_26])).

cnf(c_567,plain,
    ( r1_orders_2(sK6,X0,X1)
    | ~ m1_subset_1(X0,u1_struct_0(sK6))
    | ~ m1_subset_1(X2,u1_struct_0(sK6))
    | ~ m1_subset_1(X1,u1_struct_0(sK6))
    | ~ m1_subset_1(X3,u1_struct_0(sK6))
    | X1 != X3
    | X0 != X3
    | sK6 != sK6 ),
    inference(resolution_lifted,[status(thm)],[c_492,c_513])).

cnf(c_568,plain,
    ( r1_orders_2(sK6,X0,X0)
    | ~ m1_subset_1(X1,u1_struct_0(sK6))
    | ~ m1_subset_1(X0,u1_struct_0(sK6)) ),
    inference(unflattening,[status(thm)],[c_567])).

cnf(c_2474,plain,
    ( r1_orders_2(sK6,X0,X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK6))
    | ~ sP1_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[sP1_iProver_split])],[c_568])).

cnf(c_2475,plain,
    ( sP1_iProver_split
    | sP0_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[])],[c_568])).

cnf(c_2473,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK6))
    | ~ sP0_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[sP0_iProver_split])],[c_568])).

cnf(c_2570,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK6))
    | r1_orders_2(sK6,X0,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2474,c_2475,c_2473])).

cnf(c_2571,plain,
    ( r1_orders_2(sK6,X0,X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK6)) ),
    inference(renaming,[status(thm)],[c_2570])).

cnf(c_7254,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK6))
    | r2_hidden(X0,k4_waybel_0(sK6,sK7))
    | ~ r2_hidden(X0,sK7) ),
    inference(resolution,[status(thm)],[c_7105,c_2571])).

cnf(c_3129,plain,
    ( m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_3133,plain,
    ( m1_subset_1(X0,X1) = iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(X1)) != iProver_top
    | r2_hidden(X0,X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_3626,plain,
    ( m1_subset_1(X0,u1_struct_0(sK6)) = iProver_top
    | r2_hidden(X0,sK7) != iProver_top ),
    inference(superposition,[status(thm)],[c_3129,c_3133])).

cnf(c_3638,plain,
    ( m1_subset_1(X0,u1_struct_0(sK6))
    | ~ r2_hidden(X0,sK7) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_3626])).

cnf(c_7287,plain,
    ( r2_hidden(X0,k4_waybel_0(sK6,sK7))
    | ~ r2_hidden(X0,sK7) ),
    inference(global_propositional_subsumption,[status(thm)],[c_7254,c_3638])).

cnf(c_15,plain,
    ( ~ r1_lattice3(X0,X1,X2)
    | r1_orders_2(X0,X2,X3)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ r2_hidden(X3,X1)
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_628,plain,
    ( ~ r1_lattice3(X0,X1,X2)
    | r1_orders_2(X0,X2,X3)
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ r2_hidden(X3,X1)
    | sK6 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_15,c_26])).

cnf(c_629,plain,
    ( ~ r1_lattice3(sK6,X0,X1)
    | r1_orders_2(sK6,X1,X2)
    | ~ m1_subset_1(X1,u1_struct_0(sK6))
    | ~ m1_subset_1(X2,u1_struct_0(sK6))
    | ~ r2_hidden(X2,X0) ),
    inference(unflattening,[status(thm)],[c_628])).

cnf(c_23,negated_conjecture,
    ( r1_lattice3(sK6,k4_waybel_0(sK6,sK7),sK8)
    | r1_lattice3(sK6,sK7,sK8) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_3487,plain,
    ( r1_lattice3(sK6,sK7,sK8)
    | r1_orders_2(sK6,sK8,X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK6))
    | ~ m1_subset_1(sK8,u1_struct_0(sK6))
    | ~ r2_hidden(X0,k4_waybel_0(sK6,sK7)) ),
    inference(resolution,[status(thm)],[c_629,c_23])).

cnf(c_24,negated_conjecture,
    ( m1_subset_1(sK8,u1_struct_0(sK6)) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_3492,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK6))
    | r1_orders_2(sK6,sK8,X0)
    | r1_lattice3(sK6,sK7,sK8)
    | ~ r2_hidden(X0,k4_waybel_0(sK6,sK7)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3487,c_24])).

cnf(c_3493,plain,
    ( r1_lattice3(sK6,sK7,sK8)
    | r1_orders_2(sK6,sK8,X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK6))
    | ~ r2_hidden(X0,k4_waybel_0(sK6,sK7)) ),
    inference(renaming,[status(thm)],[c_3492])).

cnf(c_7307,plain,
    ( r1_lattice3(sK6,sK7,sK8)
    | r1_orders_2(sK6,sK8,X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK6))
    | ~ r2_hidden(X0,sK7) ),
    inference(resolution,[status(thm)],[c_7287,c_3493])).

cnf(c_3131,plain,
    ( r1_lattice3(sK6,k4_waybel_0(sK6,sK7),sK8) = iProver_top
    | r1_lattice3(sK6,sK7,sK8) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_3130,plain,
    ( m1_subset_1(sK8,u1_struct_0(sK6)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_3121,plain,
    ( r1_lattice3(sK6,X0,X1) != iProver_top
    | r1_orders_2(sK6,X1,X2) = iProver_top
    | m1_subset_1(X2,u1_struct_0(sK6)) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK6)) != iProver_top
    | r2_hidden(X2,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_629])).

cnf(c_4110,plain,
    ( r1_lattice3(sK6,X0,X1) != iProver_top
    | r1_orders_2(sK6,X1,X2) = iProver_top
    | m1_subset_1(X1,u1_struct_0(sK6)) != iProver_top
    | r2_hidden(X2,X0) != iProver_top
    | r2_hidden(X2,sK7) != iProver_top ),
    inference(superposition,[status(thm)],[c_3626,c_3121])).

cnf(c_6904,plain,
    ( r1_lattice3(sK6,X0,sK8) != iProver_top
    | r1_orders_2(sK6,sK8,X1) = iProver_top
    | r2_hidden(X1,X0) != iProver_top
    | r2_hidden(X1,sK7) != iProver_top ),
    inference(superposition,[status(thm)],[c_3130,c_4110])).

cnf(c_7149,plain,
    ( r1_lattice3(sK6,sK7,sK8) = iProver_top
    | r1_orders_2(sK6,sK8,X0) = iProver_top
    | r2_hidden(X0,k4_waybel_0(sK6,sK7)) != iProver_top
    | r2_hidden(X0,sK7) != iProver_top ),
    inference(superposition,[status(thm)],[c_3131,c_6904])).

cnf(c_3494,plain,
    ( r1_lattice3(sK6,sK7,sK8) = iProver_top
    | r1_orders_2(sK6,sK8,X0) = iProver_top
    | m1_subset_1(X0,u1_struct_0(sK6)) != iProver_top
    | r2_hidden(X0,k4_waybel_0(sK6,sK7)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3493])).

cnf(c_616,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(k4_waybel_0(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | sK6 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_16,c_26])).

cnf(c_617,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK6)))
    | m1_subset_1(k4_waybel_0(sK6,X0),k1_zfmisc_1(u1_struct_0(sK6))) ),
    inference(unflattening,[status(thm)],[c_616])).

cnf(c_3122,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK6))) != iProver_top
    | m1_subset_1(k4_waybel_0(sK6,X0),k1_zfmisc_1(u1_struct_0(sK6))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_617])).

cnf(c_3627,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK6))) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK6)) = iProver_top
    | r2_hidden(X1,k4_waybel_0(sK6,X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3122,c_3133])).

cnf(c_5122,plain,
    ( m1_subset_1(X0,u1_struct_0(sK6)) = iProver_top
    | r2_hidden(X0,k4_waybel_0(sK6,sK7)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3129,c_3627])).

cnf(c_7154,plain,
    ( r2_hidden(X0,k4_waybel_0(sK6,sK7)) != iProver_top
    | r1_orders_2(sK6,sK8,X0) = iProver_top
    | r1_lattice3(sK6,sK7,sK8) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_7149,c_3494,c_5122])).

cnf(c_7155,plain,
    ( r1_lattice3(sK6,sK7,sK8) = iProver_top
    | r1_orders_2(sK6,sK8,X0) = iProver_top
    | r2_hidden(X0,k4_waybel_0(sK6,sK7)) != iProver_top ),
    inference(renaming,[status(thm)],[c_7154])).

cnf(c_7156,plain,
    ( r1_lattice3(sK6,sK7,sK8)
    | r1_orders_2(sK6,sK8,X0)
    | ~ r2_hidden(X0,k4_waybel_0(sK6,sK7)) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_7155])).

cnf(c_7378,plain,
    ( r1_orders_2(sK6,sK8,X0)
    | r1_lattice3(sK6,sK7,sK8)
    | ~ r2_hidden(X0,sK7) ),
    inference(global_propositional_subsumption,[status(thm)],[c_7307,c_3638,c_7156,c_7254])).

cnf(c_7379,plain,
    ( r1_lattice3(sK6,sK7,sK8)
    | r1_orders_2(sK6,sK8,X0)
    | ~ r2_hidden(X0,sK7) ),
    inference(renaming,[status(thm)],[c_7378])).

cnf(c_12,plain,
    ( r1_lattice3(X0,X1,X2)
    | ~ r1_orders_2(X0,X2,sK5(X0,X1,X2))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_677,plain,
    ( r1_lattice3(X0,X1,X2)
    | ~ r1_orders_2(X0,X2,sK5(X0,X1,X2))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | sK6 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_12,c_26])).

cnf(c_678,plain,
    ( r1_lattice3(sK6,X0,X1)
    | ~ r1_orders_2(sK6,X1,sK5(sK6,X0,X1))
    | ~ m1_subset_1(X1,u1_struct_0(sK6)) ),
    inference(unflattening,[status(thm)],[c_677])).

cnf(c_7409,plain,
    ( r1_lattice3(sK6,X0,sK8)
    | r1_lattice3(sK6,sK7,sK8)
    | ~ m1_subset_1(sK8,u1_struct_0(sK6))
    | ~ r2_hidden(sK5(sK6,X0,sK8),sK7) ),
    inference(resolution,[status(thm)],[c_7379,c_678])).

cnf(c_7541,plain,
    ( r1_lattice3(sK6,sK7,sK8)
    | r1_lattice3(sK6,X0,sK8)
    | ~ r2_hidden(sK5(sK6,X0,sK8),sK7) ),
    inference(global_propositional_subsumption,[status(thm)],[c_7409,c_24])).

cnf(c_7542,plain,
    ( r1_lattice3(sK6,X0,sK8)
    | r1_lattice3(sK6,sK7,sK8)
    | ~ r2_hidden(sK5(sK6,X0,sK8),sK7) ),
    inference(renaming,[status(thm)],[c_7541])).

cnf(c_13,plain,
    ( r1_lattice3(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | r2_hidden(sK5(X0,X1,X2),X1)
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_662,plain,
    ( r1_lattice3(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | r2_hidden(sK5(X0,X1,X2),X1)
    | sK6 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_13,c_26])).

cnf(c_663,plain,
    ( r1_lattice3(sK6,X0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK6))
    | r2_hidden(sK5(sK6,X0,X1),X0) ),
    inference(unflattening,[status(thm)],[c_662])).

cnf(c_7563,plain,
    ( r1_lattice3(sK6,sK7,sK8)
    | ~ m1_subset_1(sK8,u1_struct_0(sK6)) ),
    inference(resolution,[status(thm)],[c_7542,c_663])).

cnf(c_7566,plain,
    ( r1_lattice3(sK6,sK7,sK8) ),
    inference(global_propositional_subsumption,[status(thm)],[c_7563,c_24])).

cnf(c_7692,plain,
    ( r1_orders_2(sK6,sK8,X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK6))
    | ~ m1_subset_1(sK8,u1_struct_0(sK6))
    | ~ r2_hidden(X0,sK7) ),
    inference(resolution,[status(thm)],[c_7566,c_629])).

cnf(c_7699,plain,
    ( r1_orders_2(sK6,sK8,X0)
    | ~ r2_hidden(X0,sK7) ),
    inference(global_propositional_subsumption,[status(thm)],[c_7692,c_24,c_3638])).

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

cnf(c_27,negated_conjecture,
    ( v4_orders_2(sK6) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_403,plain,
    ( ~ r1_orders_2(X0,X1,X2)
    | ~ r1_orders_2(X0,X2,X3)
    | r1_orders_2(X0,X1,X3)
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ l1_orders_2(X0)
    | sK6 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_20,c_27])).

cnf(c_404,plain,
    ( ~ r1_orders_2(sK6,X0,X1)
    | ~ r1_orders_2(sK6,X2,X0)
    | r1_orders_2(sK6,X2,X1)
    | ~ m1_subset_1(X0,u1_struct_0(sK6))
    | ~ m1_subset_1(X2,u1_struct_0(sK6))
    | ~ m1_subset_1(X1,u1_struct_0(sK6))
    | ~ l1_orders_2(sK6) ),
    inference(unflattening,[status(thm)],[c_403])).

cnf(c_406,plain,
    ( ~ m1_subset_1(X1,u1_struct_0(sK6))
    | ~ m1_subset_1(X2,u1_struct_0(sK6))
    | ~ m1_subset_1(X0,u1_struct_0(sK6))
    | r1_orders_2(sK6,X2,X1)
    | ~ r1_orders_2(sK6,X2,X0)
    | ~ r1_orders_2(sK6,X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_404,c_26])).

cnf(c_407,plain,
    ( ~ r1_orders_2(sK6,X0,X1)
    | ~ r1_orders_2(sK6,X2,X0)
    | r1_orders_2(sK6,X2,X1)
    | ~ m1_subset_1(X2,u1_struct_0(sK6))
    | ~ m1_subset_1(X1,u1_struct_0(sK6))
    | ~ m1_subset_1(X0,u1_struct_0(sK6)) ),
    inference(renaming,[status(thm)],[c_406])).

cnf(c_7989,plain,
    ( ~ r1_orders_2(sK6,X0,X1)
    | r1_orders_2(sK6,sK8,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK6))
    | ~ m1_subset_1(X0,u1_struct_0(sK6))
    | ~ m1_subset_1(sK8,u1_struct_0(sK6))
    | ~ r2_hidden(X0,sK7) ),
    inference(resolution,[status(thm)],[c_7699,c_407])).

cnf(c_8653,plain,
    ( ~ r1_orders_2(sK6,X0,X1)
    | r1_orders_2(sK6,sK8,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK6))
    | ~ r2_hidden(X0,sK7) ),
    inference(global_propositional_subsumption,[status(thm)],[c_7989,c_24,c_3638])).

cnf(c_9,plain,
    ( r1_orders_2(X0,sK4(X1,X0,X2),X2)
    | ~ sP0(X1,X0,X3)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ r2_hidden(X2,X3) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_5822,plain,
    ( r1_orders_2(sK6,sK4(X0,sK6,X1),X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK6)))
    | ~ m1_subset_1(X1,u1_struct_0(sK6))
    | ~ r2_hidden(X1,k4_waybel_0(sK6,X0)) ),
    inference(resolution,[status(thm)],[c_9,c_587])).

cnf(c_1337,plain,
    ( r1_orders_2(X0,sK4(X1,X0,X2),X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK6)))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ r2_hidden(X2,X4)
    | X3 != X1
    | k4_waybel_0(sK6,X3) != X4
    | sK6 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_9,c_587])).

cnf(c_1338,plain,
    ( r1_orders_2(sK6,sK4(X0,sK6,X1),X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK6)))
    | ~ m1_subset_1(X1,u1_struct_0(sK6))
    | ~ r2_hidden(X1,k4_waybel_0(sK6,X0)) ),
    inference(unflattening,[status(thm)],[c_1337])).

cnf(c_3641,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK6)))
    | m1_subset_1(X1,u1_struct_0(sK6))
    | ~ r2_hidden(X1,k4_waybel_0(sK6,X0)) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_3627])).

cnf(c_5955,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK6)))
    | r1_orders_2(sK6,sK4(X0,sK6,X1),X1)
    | ~ r2_hidden(X1,k4_waybel_0(sK6,X0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_5822,c_1338,c_3641])).

cnf(c_5956,plain,
    ( r1_orders_2(sK6,sK4(X0,sK6,X1),X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK6)))
    | ~ r2_hidden(X1,k4_waybel_0(sK6,X0)) ),
    inference(renaming,[status(thm)],[c_5955])).

cnf(c_8683,plain,
    ( r1_orders_2(sK6,sK8,X0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK6)))
    | ~ m1_subset_1(X0,u1_struct_0(sK6))
    | ~ r2_hidden(X0,k4_waybel_0(sK6,X1))
    | ~ r2_hidden(sK4(X1,sK6,X0),sK7) ),
    inference(resolution,[status(thm)],[c_8653,c_5956])).

cnf(c_3,plain,
    ( sP0(X0,X1,X2)
    | r2_hidden(sK3(X0,X1,X2),X0)
    | r2_hidden(sK2(X0,X1,X2),X2) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_3141,plain,
    ( sP0(X0,X1,X2) = iProver_top
    | r2_hidden(sK3(X0,X1,X2),X0) = iProver_top
    | r2_hidden(sK2(X0,X1,X2),X2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_7163,plain,
    ( r1_lattice3(sK6,sK7,sK8) = iProver_top
    | r1_orders_2(sK6,sK8,sK3(k4_waybel_0(sK6,sK7),X0,X1)) = iProver_top
    | sP0(k4_waybel_0(sK6,sK7),X0,X1) = iProver_top
    | r2_hidden(sK2(k4_waybel_0(sK6,sK7),X0,X1),X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_3141,c_7155])).

cnf(c_35,plain,
    ( m1_subset_1(sK8,u1_struct_0(sK6)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_7564,plain,
    ( r1_lattice3(sK6,sK7,sK8) = iProver_top
    | m1_subset_1(sK8,u1_struct_0(sK6)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7563])).

cnf(c_8629,plain,
    ( r1_lattice3(sK6,sK7,sK8) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_7163,c_35,c_7564])).

cnf(c_8636,plain,
    ( r1_orders_2(sK6,sK8,X0) = iProver_top
    | r2_hidden(X0,sK7) != iProver_top ),
    inference(superposition,[status(thm)],[c_8629,c_6904])).

cnf(c_3124,plain,
    ( sP0(X0,sK6,k4_waybel_0(sK6,X0)) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK6))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_587])).

cnf(c_3135,plain,
    ( r1_orders_2(X0,sK4(X1,X0,X2),X2) = iProver_top
    | sP0(X1,X0,X3) != iProver_top
    | m1_subset_1(X2,u1_struct_0(X0)) != iProver_top
    | r2_hidden(X2,X3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_4843,plain,
    ( r1_orders_2(sK6,sK4(X0,sK6,X1),X1) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK6))) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK6)) != iProver_top
    | r2_hidden(X1,k4_waybel_0(sK6,X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3124,c_3135])).

cnf(c_5957,plain,
    ( r1_orders_2(sK6,sK4(X0,sK6,X1),X1) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK6))) != iProver_top
    | r2_hidden(X1,k4_waybel_0(sK6,X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5956])).

cnf(c_6841,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK6))) != iProver_top
    | r1_orders_2(sK6,sK4(X0,sK6,X1),X1) = iProver_top
    | r2_hidden(X1,k4_waybel_0(sK6,X0)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4843,c_5957])).

cnf(c_6842,plain,
    ( r1_orders_2(sK6,sK4(X0,sK6,X1),X1) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK6))) != iProver_top
    | r2_hidden(X1,k4_waybel_0(sK6,X0)) != iProver_top ),
    inference(renaming,[status(thm)],[c_6841])).

cnf(c_3128,plain,
    ( r1_orders_2(sK6,X0,X1) != iProver_top
    | r1_orders_2(sK6,X2,X0) != iProver_top
    | r1_orders_2(sK6,X2,X1) = iProver_top
    | m1_subset_1(X0,u1_struct_0(sK6)) != iProver_top
    | m1_subset_1(X2,u1_struct_0(sK6)) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK6)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_407])).

cnf(c_6850,plain,
    ( r1_orders_2(sK6,X0,X1) = iProver_top
    | r1_orders_2(sK6,X0,sK4(X2,sK6,X1)) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK6))) != iProver_top
    | m1_subset_1(X0,u1_struct_0(sK6)) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK6)) != iProver_top
    | m1_subset_1(sK4(X2,sK6,X1),u1_struct_0(sK6)) != iProver_top
    | r2_hidden(X1,k4_waybel_0(sK6,X2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_6842,c_3128])).

cnf(c_10,plain,
    ( ~ sP0(X0,X1,X2)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | m1_subset_1(sK4(X0,X1,X3),u1_struct_0(X1))
    | ~ r2_hidden(X3,X2) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_3134,plain,
    ( sP0(X0,X1,X2) != iProver_top
    | m1_subset_1(X3,u1_struct_0(X1)) != iProver_top
    | m1_subset_1(sK4(X0,X1,X3),u1_struct_0(X1)) = iProver_top
    | r2_hidden(X3,X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_4704,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK6))) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK6)) != iProver_top
    | m1_subset_1(sK4(X0,sK6,X1),u1_struct_0(sK6)) = iProver_top
    | r2_hidden(X1,k4_waybel_0(sK6,X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3124,c_3134])).

cnf(c_5834,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK6)))
    | ~ m1_subset_1(X1,u1_struct_0(sK6))
    | m1_subset_1(sK4(X0,sK6,X1),u1_struct_0(sK6))
    | ~ r2_hidden(X1,k4_waybel_0(sK6,X0)) ),
    inference(resolution,[status(thm)],[c_10,c_587])).

cnf(c_1217,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK6)))
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | m1_subset_1(sK4(X3,X2,X1),u1_struct_0(X2))
    | ~ r2_hidden(X1,X4)
    | X0 != X3
    | k4_waybel_0(sK6,X0) != X4
    | sK6 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_10,c_587])).

cnf(c_1218,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK6)))
    | ~ m1_subset_1(X1,u1_struct_0(sK6))
    | m1_subset_1(sK4(X0,sK6,X1),u1_struct_0(sK6))
    | ~ r2_hidden(X1,k4_waybel_0(sK6,X0)) ),
    inference(unflattening,[status(thm)],[c_1217])).

cnf(c_6019,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK6)))
    | m1_subset_1(sK4(X0,sK6,X1),u1_struct_0(sK6))
    | ~ r2_hidden(X1,k4_waybel_0(sK6,X0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_5834,c_1218,c_3641])).

cnf(c_6021,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK6))) != iProver_top
    | m1_subset_1(sK4(X0,sK6,X1),u1_struct_0(sK6)) = iProver_top
    | r2_hidden(X1,k4_waybel_0(sK6,X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6019])).

cnf(c_6688,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK6))) != iProver_top
    | m1_subset_1(sK4(X0,sK6,X1),u1_struct_0(sK6)) = iProver_top
    | r2_hidden(X1,k4_waybel_0(sK6,X0)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4704,c_6021])).

cnf(c_9610,plain,
    ( r1_orders_2(sK6,X0,X1) = iProver_top
    | r1_orders_2(sK6,X0,sK4(X2,sK6,X1)) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK6))) != iProver_top
    | m1_subset_1(X0,u1_struct_0(sK6)) != iProver_top
    | r2_hidden(X1,k4_waybel_0(sK6,X2)) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_6850,c_6688,c_3627])).

cnf(c_9614,plain,
    ( r1_orders_2(sK6,sK8,X0) = iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK6))) != iProver_top
    | m1_subset_1(sK8,u1_struct_0(sK6)) != iProver_top
    | r2_hidden(X0,k4_waybel_0(sK6,X1)) != iProver_top
    | r2_hidden(sK4(X1,sK6,X0),sK7) != iProver_top ),
    inference(superposition,[status(thm)],[c_8636,c_9610])).

cnf(c_9669,plain,
    ( r1_orders_2(sK6,sK8,X0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK6)))
    | ~ m1_subset_1(sK8,u1_struct_0(sK6))
    | ~ r2_hidden(X0,k4_waybel_0(sK6,X1))
    | ~ r2_hidden(sK4(X1,sK6,X0),sK7) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_9614])).

cnf(c_19316,plain,
    ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK6)))
    | r1_orders_2(sK6,sK8,X0)
    | ~ r2_hidden(X0,k4_waybel_0(sK6,X1))
    | ~ r2_hidden(sK4(X1,sK6,X0),sK7) ),
    inference(global_propositional_subsumption,[status(thm)],[c_8683,c_24,c_9669])).

cnf(c_19317,plain,
    ( r1_orders_2(sK6,sK8,X0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK6)))
    | ~ r2_hidden(X0,k4_waybel_0(sK6,X1))
    | ~ r2_hidden(sK4(X1,sK6,X0),sK7) ),
    inference(renaming,[status(thm)],[c_19316])).

cnf(c_8,plain,
    ( ~ sP0(X0,X1,X2)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ r2_hidden(X3,X2)
    | r2_hidden(sK4(X0,X1,X3),X0) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_5810,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK6)))
    | ~ m1_subset_1(X1,u1_struct_0(sK6))
    | ~ r2_hidden(X1,k4_waybel_0(sK6,X0))
    | r2_hidden(sK4(X0,sK6,X1),X0) ),
    inference(resolution,[status(thm)],[c_8,c_587])).

cnf(c_1235,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK6)))
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | ~ r2_hidden(X1,X3)
    | r2_hidden(sK4(X4,X2,X1),X4)
    | X0 != X4
    | k4_waybel_0(sK6,X0) != X3
    | sK6 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_8,c_587])).

cnf(c_1236,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK6)))
    | ~ m1_subset_1(X1,u1_struct_0(sK6))
    | ~ r2_hidden(X1,k4_waybel_0(sK6,X0))
    | r2_hidden(sK4(X0,sK6,X1),X0) ),
    inference(unflattening,[status(thm)],[c_1235])).

cnf(c_5924,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK6)))
    | ~ r2_hidden(X1,k4_waybel_0(sK6,X0))
    | r2_hidden(sK4(X0,sK6,X1),X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_5810,c_1236,c_3641])).

cnf(c_19342,plain,
    ( r1_orders_2(sK6,sK8,X0)
    | ~ m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6)))
    | ~ r2_hidden(X0,k4_waybel_0(sK6,sK7)) ),
    inference(resolution,[status(thm)],[c_19317,c_5924])).

cnf(c_19347,plain,
    ( r1_orders_2(sK6,sK8,X0)
    | ~ r2_hidden(X0,k4_waybel_0(sK6,sK7)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_19342,c_25])).

cnf(c_19630,plain,
    ( r1_lattice3(sK6,k4_waybel_0(sK6,sK7),X0)
    | r1_orders_2(sK6,sK8,sK5(sK6,k4_waybel_0(sK6,sK7),X0))
    | ~ m1_subset_1(X0,u1_struct_0(sK6)) ),
    inference(resolution,[status(thm)],[c_19347,c_663])).

cnf(c_19673,plain,
    ( r1_lattice3(sK6,k4_waybel_0(sK6,sK7),sK8)
    | ~ m1_subset_1(sK8,u1_struct_0(sK6)) ),
    inference(resolution,[status(thm)],[c_19630,c_678])).

cnf(c_22,negated_conjecture,
    ( ~ r1_lattice3(sK6,k4_waybel_0(sK6,sK7),sK8)
    | ~ r1_lattice3(sK6,sK7,sK8) ),
    inference(cnf_transformation,[],[f77])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_19673,c_7563,c_22,c_24])).


%------------------------------------------------------------------------------
