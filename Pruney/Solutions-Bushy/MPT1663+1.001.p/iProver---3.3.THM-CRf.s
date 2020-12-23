%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT1663+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n028.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:46:08 EST 2020

% Result     : Theorem 7.68s
% Output     : CNFRefutation 7.68s
% Verified   : 
% Statistics : Number of formulae       :  301 (1904 expanded)
%              Number of clauses        :  178 ( 429 expanded)
%              Number of leaves         :   33 ( 490 expanded)
%              Depth                    :   26
%              Number of atoms          : 1478 (21623 expanded)
%              Number of equality atoms :  265 (2426 expanded)
%              Maximal formula depth    :   14 (   6 average)
%              Maximal clause size      :   36 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f54,plain,(
    ! [X0,X1] :
      ( sP0(X0,X1)
    <=> ! [X2] :
          ( ? [X3] :
              ( r1_lattice3(X0,X2,X3)
              & r2_hidden(X3,X1)
              & m1_subset_1(X3,u1_struct_0(X0)) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
          | ~ v1_finset_1(X2) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f66,plain,(
    ! [X0,X1] :
      ( ( sP0(X0,X1)
        | ? [X2] :
            ( ! [X3] :
                ( ~ r1_lattice3(X0,X2,X3)
                | ~ r2_hidden(X3,X1)
                | ~ m1_subset_1(X3,u1_struct_0(X0)) )
            & m1_subset_1(X2,k1_zfmisc_1(X1))
            & v1_finset_1(X2) ) )
      & ( ! [X2] :
            ( ? [X3] :
                ( r1_lattice3(X0,X2,X3)
                & r2_hidden(X3,X1)
                & m1_subset_1(X3,u1_struct_0(X0)) )
            | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
            | ~ v1_finset_1(X2) )
        | ~ sP0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f54])).

fof(f67,plain,(
    ! [X0,X1] :
      ( ( sP0(X0,X1)
        | ? [X2] :
            ( ! [X3] :
                ( ~ r1_lattice3(X0,X2,X3)
                | ~ r2_hidden(X3,X1)
                | ~ m1_subset_1(X3,u1_struct_0(X0)) )
            & m1_subset_1(X2,k1_zfmisc_1(X1))
            & v1_finset_1(X2) ) )
      & ( ! [X4] :
            ( ? [X5] :
                ( r1_lattice3(X0,X4,X5)
                & r2_hidden(X5,X1)
                & m1_subset_1(X5,u1_struct_0(X0)) )
            | ~ m1_subset_1(X4,k1_zfmisc_1(X1))
            | ~ v1_finset_1(X4) )
        | ~ sP0(X0,X1) ) ) ),
    inference(rectify,[],[f66])).

fof(f69,plain,(
    ! [X4,X1,X0] :
      ( ? [X5] :
          ( r1_lattice3(X0,X4,X5)
          & r2_hidden(X5,X1)
          & m1_subset_1(X5,u1_struct_0(X0)) )
     => ( r1_lattice3(X0,X4,sK5(X0,X1,X4))
        & r2_hidden(sK5(X0,X1,X4),X1)
        & m1_subset_1(sK5(X0,X1,X4),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f68,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ! [X3] :
              ( ~ r1_lattice3(X0,X2,X3)
              | ~ r2_hidden(X3,X1)
              | ~ m1_subset_1(X3,u1_struct_0(X0)) )
          & m1_subset_1(X2,k1_zfmisc_1(X1))
          & v1_finset_1(X2) )
     => ( ! [X3] :
            ( ~ r1_lattice3(X0,sK4(X0,X1),X3)
            | ~ r2_hidden(X3,X1)
            | ~ m1_subset_1(X3,u1_struct_0(X0)) )
        & m1_subset_1(sK4(X0,X1),k1_zfmisc_1(X1))
        & v1_finset_1(sK4(X0,X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f70,plain,(
    ! [X0,X1] :
      ( ( sP0(X0,X1)
        | ( ! [X3] :
              ( ~ r1_lattice3(X0,sK4(X0,X1),X3)
              | ~ r2_hidden(X3,X1)
              | ~ m1_subset_1(X3,u1_struct_0(X0)) )
          & m1_subset_1(sK4(X0,X1),k1_zfmisc_1(X1))
          & v1_finset_1(sK4(X0,X1)) ) )
      & ( ! [X4] :
            ( ( r1_lattice3(X0,X4,sK5(X0,X1,X4))
              & r2_hidden(sK5(X0,X1,X4),X1)
              & m1_subset_1(sK5(X0,X1,X4),u1_struct_0(X0)) )
            | ~ m1_subset_1(X4,k1_zfmisc_1(X1))
            | ~ v1_finset_1(X4) )
        | ~ sP0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f67,f69,f68])).

fof(f105,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(sK5(X0,X1,X4),X1)
      | ~ m1_subset_1(X4,k1_zfmisc_1(X1))
      | ~ v1_finset_1(X4)
      | ~ sP0(X0,X1) ) ),
    inference(cnf_transformation,[],[f70])).

fof(f106,plain,(
    ! [X4,X0,X1] :
      ( r1_lattice3(X0,X4,sK5(X0,X1,X4))
      | ~ m1_subset_1(X4,k1_zfmisc_1(X1))
      | ~ v1_finset_1(X4)
      | ~ sP0(X0,X1) ) ),
    inference(cnf_transformation,[],[f70])).

fof(f12,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
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
    inference(rectify,[],[f12])).

fof(f43,plain,(
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
    inference(ennf_transformation,[],[f21])).

fof(f44,plain,(
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
    inference(flattening,[],[f43])).

fof(f71,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r1_orders_2(X0,X3,X1)
          & r1_lattice3(X0,X2,X3)
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ~ r1_orders_2(X0,sK6(X0,X1,X2),X1)
        & r1_lattice3(X0,X2,sK6(X0,X1,X2))
        & m1_subset_1(sK6(X0,X1,X2),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f72,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( r2_yellow_0(X0,X2)
                  & k2_yellow_0(X0,X2) = X1 )
                | ( ~ r1_orders_2(X0,sK6(X0,X1,X2),X1)
                  & r1_lattice3(X0,X2,sK6(X0,X1,X2))
                  & m1_subset_1(sK6(X0,X1,X2),u1_struct_0(X0)) )
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f44,f71])).

fof(f112,plain,(
    ! [X4,X2,X0,X1] :
      ( r1_orders_2(X0,X4,X1)
      | ~ r1_lattice3(X0,X2,X4)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ r2_yellow_0(X0,X2)
      | k2_yellow_0(X0,X2) != X1
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f72])).

fof(f143,plain,(
    ! [X4,X2,X0] :
      ( r1_orders_2(X0,X4,k2_yellow_0(X0,X2))
      | ~ r1_lattice3(X0,X2,X4)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ r2_yellow_0(X0,X2)
      | ~ m1_subset_1(k2_yellow_0(X0,X2),u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(equality_resolution,[],[f112])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( l1_orders_2(X0)
     => m1_subset_1(k2_yellow_0(X0,X1),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_yellow_0(X0,X1),u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f92,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_yellow_0(X0,X1),u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f19,conjecture,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v2_lattice3(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0) )
     => ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & v13_waybel_0(X1,X0)
            & ~ v1_xboole_0(X1) )
         => ( v2_waybel_0(X1,X0)
          <=> ! [X2] :
                ( ( m1_subset_1(X2,k1_zfmisc_1(X1))
                  & v1_finset_1(X2) )
               => ( k1_xboole_0 != X2
                 => r2_hidden(k2_yellow_0(X0,X2),X1) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_orders_2(X0)
          & v2_lattice3(X0)
          & v5_orders_2(X0)
          & v4_orders_2(X0)
          & v3_orders_2(X0) )
       => ! [X1] :
            ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
              & v13_waybel_0(X1,X0)
              & ~ v1_xboole_0(X1) )
           => ( v2_waybel_0(X1,X0)
            <=> ! [X2] :
                  ( ( m1_subset_1(X2,k1_zfmisc_1(X1))
                    & v1_finset_1(X2) )
                 => ( k1_xboole_0 != X2
                   => r2_hidden(k2_yellow_0(X0,X2),X1) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f19])).

fof(f52,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v2_waybel_0(X1,X0)
          <~> ! [X2] :
                ( r2_hidden(k2_yellow_0(X0,X2),X1)
                | k1_xboole_0 = X2
                | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
                | ~ v1_finset_1(X2) ) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          & v13_waybel_0(X1,X0)
          & ~ v1_xboole_0(X1) )
      & l1_orders_2(X0)
      & v2_lattice3(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f53,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v2_waybel_0(X1,X0)
          <~> ! [X2] :
                ( r2_hidden(k2_yellow_0(X0,X2),X1)
                | k1_xboole_0 = X2
                | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
                | ~ v1_finset_1(X2) ) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          & v13_waybel_0(X1,X0)
          & ~ v1_xboole_0(X1) )
      & l1_orders_2(X0)
      & v2_lattice3(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0) ) ),
    inference(flattening,[],[f52])).

fof(f78,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ? [X2] :
                ( ~ r2_hidden(k2_yellow_0(X0,X2),X1)
                & k1_xboole_0 != X2
                & m1_subset_1(X2,k1_zfmisc_1(X1))
                & v1_finset_1(X2) )
            | ~ v2_waybel_0(X1,X0) )
          & ( ! [X2] :
                ( r2_hidden(k2_yellow_0(X0,X2),X1)
                | k1_xboole_0 = X2
                | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
                | ~ v1_finset_1(X2) )
            | v2_waybel_0(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          & v13_waybel_0(X1,X0)
          & ~ v1_xboole_0(X1) )
      & l1_orders_2(X0)
      & v2_lattice3(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0) ) ),
    inference(nnf_transformation,[],[f53])).

fof(f79,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ? [X2] :
                ( ~ r2_hidden(k2_yellow_0(X0,X2),X1)
                & k1_xboole_0 != X2
                & m1_subset_1(X2,k1_zfmisc_1(X1))
                & v1_finset_1(X2) )
            | ~ v2_waybel_0(X1,X0) )
          & ( ! [X2] :
                ( r2_hidden(k2_yellow_0(X0,X2),X1)
                | k1_xboole_0 = X2
                | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
                | ~ v1_finset_1(X2) )
            | v2_waybel_0(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          & v13_waybel_0(X1,X0)
          & ~ v1_xboole_0(X1) )
      & l1_orders_2(X0)
      & v2_lattice3(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0) ) ),
    inference(flattening,[],[f78])).

fof(f80,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ? [X2] :
                ( ~ r2_hidden(k2_yellow_0(X0,X2),X1)
                & k1_xboole_0 != X2
                & m1_subset_1(X2,k1_zfmisc_1(X1))
                & v1_finset_1(X2) )
            | ~ v2_waybel_0(X1,X0) )
          & ( ! [X3] :
                ( r2_hidden(k2_yellow_0(X0,X3),X1)
                | k1_xboole_0 = X3
                | ~ m1_subset_1(X3,k1_zfmisc_1(X1))
                | ~ v1_finset_1(X3) )
            | v2_waybel_0(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          & v13_waybel_0(X1,X0)
          & ~ v1_xboole_0(X1) )
      & l1_orders_2(X0)
      & v2_lattice3(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0) ) ),
    inference(rectify,[],[f79])).

fof(f83,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ~ r2_hidden(k2_yellow_0(X0,X2),X1)
          & k1_xboole_0 != X2
          & m1_subset_1(X2,k1_zfmisc_1(X1))
          & v1_finset_1(X2) )
     => ( ~ r2_hidden(k2_yellow_0(X0,sK10),X1)
        & k1_xboole_0 != sK10
        & m1_subset_1(sK10,k1_zfmisc_1(X1))
        & v1_finset_1(sK10) ) ) ),
    introduced(choice_axiom,[])).

fof(f82,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ( ? [X2] :
                ( ~ r2_hidden(k2_yellow_0(X0,X2),X1)
                & k1_xboole_0 != X2
                & m1_subset_1(X2,k1_zfmisc_1(X1))
                & v1_finset_1(X2) )
            | ~ v2_waybel_0(X1,X0) )
          & ( ! [X3] :
                ( r2_hidden(k2_yellow_0(X0,X3),X1)
                | k1_xboole_0 = X3
                | ~ m1_subset_1(X3,k1_zfmisc_1(X1))
                | ~ v1_finset_1(X3) )
            | v2_waybel_0(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          & v13_waybel_0(X1,X0)
          & ~ v1_xboole_0(X1) )
     => ( ( ? [X2] :
              ( ~ r2_hidden(k2_yellow_0(X0,X2),sK9)
              & k1_xboole_0 != X2
              & m1_subset_1(X2,k1_zfmisc_1(sK9))
              & v1_finset_1(X2) )
          | ~ v2_waybel_0(sK9,X0) )
        & ( ! [X3] :
              ( r2_hidden(k2_yellow_0(X0,X3),sK9)
              | k1_xboole_0 = X3
              | ~ m1_subset_1(X3,k1_zfmisc_1(sK9))
              | ~ v1_finset_1(X3) )
          | v2_waybel_0(sK9,X0) )
        & m1_subset_1(sK9,k1_zfmisc_1(u1_struct_0(X0)))
        & v13_waybel_0(sK9,X0)
        & ~ v1_xboole_0(sK9) ) ) ),
    introduced(choice_axiom,[])).

fof(f81,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ( ? [X2] :
                  ( ~ r2_hidden(k2_yellow_0(X0,X2),X1)
                  & k1_xboole_0 != X2
                  & m1_subset_1(X2,k1_zfmisc_1(X1))
                  & v1_finset_1(X2) )
              | ~ v2_waybel_0(X1,X0) )
            & ( ! [X3] :
                  ( r2_hidden(k2_yellow_0(X0,X3),X1)
                  | k1_xboole_0 = X3
                  | ~ m1_subset_1(X3,k1_zfmisc_1(X1))
                  | ~ v1_finset_1(X3) )
              | v2_waybel_0(X1,X0) )
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & v13_waybel_0(X1,X0)
            & ~ v1_xboole_0(X1) )
        & l1_orders_2(X0)
        & v2_lattice3(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0) )
   => ( ? [X1] :
          ( ( ? [X2] :
                ( ~ r2_hidden(k2_yellow_0(sK8,X2),X1)
                & k1_xboole_0 != X2
                & m1_subset_1(X2,k1_zfmisc_1(X1))
                & v1_finset_1(X2) )
            | ~ v2_waybel_0(X1,sK8) )
          & ( ! [X3] :
                ( r2_hidden(k2_yellow_0(sK8,X3),X1)
                | k1_xboole_0 = X3
                | ~ m1_subset_1(X3,k1_zfmisc_1(X1))
                | ~ v1_finset_1(X3) )
            | v2_waybel_0(X1,sK8) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK8)))
          & v13_waybel_0(X1,sK8)
          & ~ v1_xboole_0(X1) )
      & l1_orders_2(sK8)
      & v2_lattice3(sK8)
      & v5_orders_2(sK8)
      & v4_orders_2(sK8)
      & v3_orders_2(sK8) ) ),
    introduced(choice_axiom,[])).

fof(f84,plain,
    ( ( ( ~ r2_hidden(k2_yellow_0(sK8,sK10),sK9)
        & k1_xboole_0 != sK10
        & m1_subset_1(sK10,k1_zfmisc_1(sK9))
        & v1_finset_1(sK10) )
      | ~ v2_waybel_0(sK9,sK8) )
    & ( ! [X3] :
          ( r2_hidden(k2_yellow_0(sK8,X3),sK9)
          | k1_xboole_0 = X3
          | ~ m1_subset_1(X3,k1_zfmisc_1(sK9))
          | ~ v1_finset_1(X3) )
      | v2_waybel_0(sK9,sK8) )
    & m1_subset_1(sK9,k1_zfmisc_1(u1_struct_0(sK8)))
    & v13_waybel_0(sK9,sK8)
    & ~ v1_xboole_0(sK9)
    & l1_orders_2(sK8)
    & v2_lattice3(sK8)
    & v5_orders_2(sK8)
    & v4_orders_2(sK8)
    & v3_orders_2(sK8) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8,sK9,sK10])],[f80,f83,f82,f81])).

fof(f132,plain,(
    v5_orders_2(sK8) ),
    inference(cnf_transformation,[],[f84])).

fof(f134,plain,(
    l1_orders_2(sK8) ),
    inference(cnf_transformation,[],[f84])).

fof(f137,plain,(
    m1_subset_1(sK9,k1_zfmisc_1(u1_struct_0(sK8))) ),
    inference(cnf_transformation,[],[f84])).

fof(f2,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v13_waybel_0(X1,X0)
          <=> ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => ! [X3] :
                    ( m1_subset_1(X3,u1_struct_0(X0))
                   => ( ( r1_orders_2(X0,X2,X3)
                        & r2_hidden(X2,X1) )
                     => r2_hidden(X3,X1) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v13_waybel_0(X1,X0)
          <=> ! [X2] :
                ( ! [X3] :
                    ( r2_hidden(X3,X1)
                    | ~ r1_orders_2(X0,X2,X3)
                    | ~ r2_hidden(X2,X1)
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                | ~ m1_subset_1(X2,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v13_waybel_0(X1,X0)
          <=> ! [X2] :
                ( ! [X3] :
                    ( r2_hidden(X3,X1)
                    | ~ r1_orders_2(X0,X2,X3)
                    | ~ r2_hidden(X2,X1)
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                | ~ m1_subset_1(X2,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f25])).

fof(f57,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v13_waybel_0(X1,X0)
              | ? [X2] :
                  ( ? [X3] :
                      ( ~ r2_hidden(X3,X1)
                      & r1_orders_2(X0,X2,X3)
                      & r2_hidden(X2,X1)
                      & m1_subset_1(X3,u1_struct_0(X0)) )
                  & m1_subset_1(X2,u1_struct_0(X0)) ) )
            & ( ! [X2] :
                  ( ! [X3] :
                      ( r2_hidden(X3,X1)
                      | ~ r1_orders_2(X0,X2,X3)
                      | ~ r2_hidden(X2,X1)
                      | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                  | ~ m1_subset_1(X2,u1_struct_0(X0)) )
              | ~ v13_waybel_0(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0) ) ),
    inference(nnf_transformation,[],[f26])).

fof(f58,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v13_waybel_0(X1,X0)
              | ? [X2] :
                  ( ? [X3] :
                      ( ~ r2_hidden(X3,X1)
                      & r1_orders_2(X0,X2,X3)
                      & r2_hidden(X2,X1)
                      & m1_subset_1(X3,u1_struct_0(X0)) )
                  & m1_subset_1(X2,u1_struct_0(X0)) ) )
            & ( ! [X4] :
                  ( ! [X5] :
                      ( r2_hidden(X5,X1)
                      | ~ r1_orders_2(X0,X4,X5)
                      | ~ r2_hidden(X4,X1)
                      | ~ m1_subset_1(X5,u1_struct_0(X0)) )
                  | ~ m1_subset_1(X4,u1_struct_0(X0)) )
              | ~ v13_waybel_0(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0) ) ),
    inference(rectify,[],[f57])).

fof(f60,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r2_hidden(X3,X1)
          & r1_orders_2(X0,X2,X3)
          & r2_hidden(X2,X1)
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ~ r2_hidden(sK3(X0,X1),X1)
        & r1_orders_2(X0,X2,sK3(X0,X1))
        & r2_hidden(X2,X1)
        & m1_subset_1(sK3(X0,X1),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f59,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ? [X3] :
              ( ~ r2_hidden(X3,X1)
              & r1_orders_2(X0,X2,X3)
              & r2_hidden(X2,X1)
              & m1_subset_1(X3,u1_struct_0(X0)) )
          & m1_subset_1(X2,u1_struct_0(X0)) )
     => ( ? [X3] :
            ( ~ r2_hidden(X3,X1)
            & r1_orders_2(X0,sK2(X0,X1),X3)
            & r2_hidden(sK2(X0,X1),X1)
            & m1_subset_1(X3,u1_struct_0(X0)) )
        & m1_subset_1(sK2(X0,X1),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f61,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v13_waybel_0(X1,X0)
              | ( ~ r2_hidden(sK3(X0,X1),X1)
                & r1_orders_2(X0,sK2(X0,X1),sK3(X0,X1))
                & r2_hidden(sK2(X0,X1),X1)
                & m1_subset_1(sK3(X0,X1),u1_struct_0(X0))
                & m1_subset_1(sK2(X0,X1),u1_struct_0(X0)) ) )
            & ( ! [X4] :
                  ( ! [X5] :
                      ( r2_hidden(X5,X1)
                      | ~ r1_orders_2(X0,X4,X5)
                      | ~ r2_hidden(X4,X1)
                      | ~ m1_subset_1(X5,u1_struct_0(X0)) )
                  | ~ m1_subset_1(X4,u1_struct_0(X0)) )
              | ~ v13_waybel_0(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f58,f60,f59])).

fof(f86,plain,(
    ! [X4,X0,X5,X1] :
      ( r2_hidden(X5,X1)
      | ~ r1_orders_2(X0,X4,X5)
      | ~ r2_hidden(X4,X1)
      | ~ m1_subset_1(X5,u1_struct_0(X0))
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ v13_waybel_0(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f61])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f45,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f46,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f45])).

fof(f121,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f136,plain,(
    v13_waybel_0(sK9,sK8) ),
    inference(cnf_transformation,[],[f84])).

fof(f142,plain,
    ( ~ r2_hidden(k2_yellow_0(sK8,sK10),sK9)
    | ~ v2_waybel_0(sK9,sK8) ),
    inference(cnf_transformation,[],[f84])).

fof(f135,plain,(
    ~ v1_xboole_0(sK9) ),
    inference(cnf_transformation,[],[f84])).

fof(f139,plain,
    ( v1_finset_1(sK10)
    | ~ v2_waybel_0(sK9,sK8) ),
    inference(cnf_transformation,[],[f84])).

fof(f140,plain,
    ( m1_subset_1(sK10,k1_zfmisc_1(sK9))
    | ~ v2_waybel_0(sK9,sK8) ),
    inference(cnf_transformation,[],[f84])).

fof(f141,plain,
    ( k1_xboole_0 != sK10
    | ~ v2_waybel_0(sK9,sK8) ),
    inference(cnf_transformation,[],[f84])).

fof(f15,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ( v2_lattice3(X0)
      <=> ! [X1] :
            ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
              & v1_finset_1(X1)
              & ~ v1_xboole_0(X1) )
           => r2_yellow_0(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f47,plain,(
    ! [X0] :
      ( ( v2_lattice3(X0)
      <=> ! [X1] :
            ( r2_yellow_0(X0,X1)
            | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            | ~ v1_finset_1(X1)
            | v1_xboole_0(X1) ) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f48,plain,(
    ! [X0] :
      ( ( v2_lattice3(X0)
      <=> ! [X1] :
            ( r2_yellow_0(X0,X1)
            | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            | ~ v1_finset_1(X1)
            | v1_xboole_0(X1) ) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f47])).

fof(f74,plain,(
    ! [X0] :
      ( ( ( v2_lattice3(X0)
          | ? [X1] :
              ( ~ r2_yellow_0(X0,X1)
              & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
              & v1_finset_1(X1)
              & ~ v1_xboole_0(X1) ) )
        & ( ! [X1] :
              ( r2_yellow_0(X0,X1)
              | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
              | ~ v1_finset_1(X1)
              | v1_xboole_0(X1) )
          | ~ v2_lattice3(X0) ) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f48])).

fof(f75,plain,(
    ! [X0] :
      ( ( ( v2_lattice3(X0)
          | ? [X1] :
              ( ~ r2_yellow_0(X0,X1)
              & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
              & v1_finset_1(X1)
              & ~ v1_xboole_0(X1) ) )
        & ( ! [X2] :
              ( r2_yellow_0(X0,X2)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
              | ~ v1_finset_1(X2)
              | v1_xboole_0(X2) )
          | ~ v2_lattice3(X0) ) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(rectify,[],[f74])).

fof(f76,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ r2_yellow_0(X0,X1)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          & v1_finset_1(X1)
          & ~ v1_xboole_0(X1) )
     => ( ~ r2_yellow_0(X0,sK7(X0))
        & m1_subset_1(sK7(X0),k1_zfmisc_1(u1_struct_0(X0)))
        & v1_finset_1(sK7(X0))
        & ~ v1_xboole_0(sK7(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f77,plain,(
    ! [X0] :
      ( ( ( v2_lattice3(X0)
          | ( ~ r2_yellow_0(X0,sK7(X0))
            & m1_subset_1(sK7(X0),k1_zfmisc_1(u1_struct_0(X0)))
            & v1_finset_1(sK7(X0))
            & ~ v1_xboole_0(sK7(X0)) ) )
        & ( ! [X2] :
              ( r2_yellow_0(X0,X2)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
              | ~ v1_finset_1(X2)
              | v1_xboole_0(X2) )
          | ~ v2_lattice3(X0) ) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f75,f76])).

fof(f122,plain,(
    ! [X2,X0] :
      ( r2_yellow_0(X0,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v1_finset_1(X2)
      | v1_xboole_0(X2)
      | ~ v2_lattice3(X0)
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f77])).

fof(f1,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ( v2_lattice3(X0)
       => ~ v2_struct_0(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0] :
      ( ~ v2_struct_0(X0)
      | ~ v2_lattice3(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f24,plain,(
    ! [X0] :
      ( ~ v2_struct_0(X0)
      | ~ v2_lattice3(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f23])).

fof(f85,plain,(
    ! [X0] :
      ( ~ v2_struct_0(X0)
      | ~ v2_lattice3(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f130,plain,(
    v3_orders_2(sK8) ),
    inference(cnf_transformation,[],[f84])).

fof(f131,plain,(
    v4_orders_2(sK8) ),
    inference(cnf_transformation,[],[f84])).

fof(f133,plain,(
    v2_lattice3(sK8) ),
    inference(cnf_transformation,[],[f84])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f73,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f13])).

fof(f119,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f73])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f38,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f37])).

fof(f99,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f120,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f73])).

fof(f55,plain,(
    ! [X1,X0] :
      ( ( ( v2_waybel_0(X1,X0)
          & ~ v1_xboole_0(X1) )
      <=> sP0(X0,X1) )
      | ~ sP1(X1,X0) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f63,plain,(
    ! [X1,X0] :
      ( ( ( ( v2_waybel_0(X1,X0)
            & ~ v1_xboole_0(X1) )
          | ~ sP0(X0,X1) )
        & ( sP0(X0,X1)
          | ~ v2_waybel_0(X1,X0)
          | v1_xboole_0(X1) ) )
      | ~ sP1(X1,X0) ) ),
    inference(nnf_transformation,[],[f55])).

fof(f64,plain,(
    ! [X1,X0] :
      ( ( ( ( v2_waybel_0(X1,X0)
            & ~ v1_xboole_0(X1) )
          | ~ sP0(X0,X1) )
        & ( sP0(X0,X1)
          | ~ v2_waybel_0(X1,X0)
          | v1_xboole_0(X1) ) )
      | ~ sP1(X1,X0) ) ),
    inference(flattening,[],[f63])).

fof(f65,plain,(
    ! [X0,X1] :
      ( ( ( ( v2_waybel_0(X0,X1)
            & ~ v1_xboole_0(X0) )
          | ~ sP0(X1,X0) )
        & ( sP0(X1,X0)
          | ~ v2_waybel_0(X0,X1)
          | v1_xboole_0(X0) ) )
      | ~ sP1(X0,X1) ) ),
    inference(rectify,[],[f64])).

fof(f101,plain,(
    ! [X0,X1] :
      ( sP0(X1,X0)
      | ~ v2_waybel_0(X0,X1)
      | v1_xboole_0(X0)
      | ~ sP1(X0,X1) ) ),
    inference(cnf_transformation,[],[f65])).

fof(f11,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v4_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( ( v2_waybel_0(X1,X0)
              & ~ v1_xboole_0(X1) )
          <=> ! [X2] :
                ( ( m1_subset_1(X2,k1_zfmisc_1(X1))
                  & v1_finset_1(X2) )
               => ? [X3] :
                    ( r1_lattice3(X0,X2,X3)
                    & r2_hidden(X3,X1)
                    & m1_subset_1(X3,u1_struct_0(X0)) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v2_waybel_0(X1,X0)
              & ~ v1_xboole_0(X1) )
          <=> ! [X2] :
                ( ? [X3] :
                    ( r1_lattice3(X0,X2,X3)
                    & r2_hidden(X3,X1)
                    & m1_subset_1(X3,u1_struct_0(X0)) )
                | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
                | ~ v1_finset_1(X2) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0)
      | ~ v4_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f42,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v2_waybel_0(X1,X0)
              & ~ v1_xboole_0(X1) )
          <=> ! [X2] :
                ( ? [X3] :
                    ( r1_lattice3(X0,X2,X3)
                    & r2_hidden(X3,X1)
                    & m1_subset_1(X3,u1_struct_0(X0)) )
                | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
                | ~ v1_finset_1(X2) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0)
      | ~ v4_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f41])).

fof(f56,plain,(
    ! [X0] :
      ( ! [X1] :
          ( sP1(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0)
      | ~ v4_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(definition_folding,[],[f42,f55,f54])).

fof(f110,plain,(
    ! [X0,X1] :
      ( sP1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v4_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f56])).

fof(f16,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f49,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f127,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f138,plain,(
    ! [X3] :
      ( r2_hidden(k2_yellow_0(sK8,X3),sK9)
      | k1_xboole_0 = X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(sK9))
      | ~ v1_finset_1(X3)
      | v2_waybel_0(sK9,sK8) ) ),
    inference(cnf_transformation,[],[f84])).

fof(f111,plain,(
    ! [X2,X0,X1] :
      ( r1_lattice3(X0,X2,X1)
      | ~ r2_yellow_0(X0,X2)
      | k2_yellow_0(X0,X2) != X1
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f72])).

fof(f144,plain,(
    ! [X2,X0] :
      ( r1_lattice3(X0,X2,k2_yellow_0(X0,X2))
      | ~ r2_yellow_0(X0,X2)
      | ~ m1_subset_1(k2_yellow_0(X0,X2),u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(equality_resolution,[],[f111])).

fof(f109,plain,(
    ! [X0,X3,X1] :
      ( sP0(X0,X1)
      | ~ r1_lattice3(X0,sK4(X0,X1),X3)
      | ~ r2_hidden(X3,X1)
      | ~ m1_subset_1(X3,u1_struct_0(X0)) ) ),
    inference(cnf_transformation,[],[f70])).

fof(f103,plain,(
    ! [X0,X1] :
      ( v2_waybel_0(X0,X1)
      | ~ sP0(X1,X0)
      | ~ sP1(X0,X1) ) ),
    inference(cnf_transformation,[],[f65])).

fof(f107,plain,(
    ! [X0,X1] :
      ( sP0(X0,X1)
      | v1_finset_1(sK4(X0,X1)) ) ),
    inference(cnf_transformation,[],[f70])).

fof(f108,plain,(
    ! [X0,X1] :
      ( sP0(X0,X1)
      | m1_subset_1(sK4(X0,X1),k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f70])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f40,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f39])).

fof(f100,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f17,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ( r1_lattice3(X0,k1_xboole_0,X1)
            & r2_lattice3(X0,k1_xboole_0,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => r1_lattice3(X0,k1_xboole_0,X1) ) ) ),
    inference(pure_predicate_removal,[],[f17])).

fof(f50,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_lattice3(X0,k1_xboole_0,X1)
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f128,plain,(
    ! [X0,X1] :
      ( r1_lattice3(X0,k1_xboole_0,X1)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X0))
        & ~ v1_xboole_0(X1)
        & ~ v1_xboole_0(X0) )
     => ! [X2] :
          ( m2_subset_1(X2,X0,X1)
        <=> m1_subset_1(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( m2_subset_1(X2,X0,X1)
        <=> m1_subset_1(X2,X1) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( m2_subset_1(X2,X0,X1)
        <=> m1_subset_1(X2,X1) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f35])).

fof(f62,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( m2_subset_1(X2,X0,X1)
            | ~ m1_subset_1(X2,X1) )
          & ( m1_subset_1(X2,X1)
            | ~ m2_subset_1(X2,X0,X1) ) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(nnf_transformation,[],[f36])).

fof(f97,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X2,X1)
      | ~ m2_subset_1(X2,X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f62])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & v13_waybel_0(X1,X0)
        & ~ v1_xboole_0(X1)
        & l1_orders_2(X0)
        & v2_lattice3(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0) )
     => m2_subset_1(o_2_8_waybel_0(X0,X1),u1_struct_0(X0),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1] :
      ( m2_subset_1(o_2_8_waybel_0(X0,X1),u1_struct_0(X0),X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v13_waybel_0(X1,X0)
      | v1_xboole_0(X1)
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f32,plain,(
    ! [X0,X1] :
      ( m2_subset_1(o_2_8_waybel_0(X0,X1),u1_struct_0(X0),X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v13_waybel_0(X1,X0)
      | v1_xboole_0(X1)
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(flattening,[],[f31])).

fof(f95,plain,(
    ! [X0,X1] :
      ( m2_subset_1(o_2_8_waybel_0(X0,X1),u1_struct_0(X0),X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v13_waybel_0(X1,X0)
      | v1_xboole_0(X1)
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f7,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f34,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f33])).

fof(f96,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f4,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f93,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X0))
        & ~ v1_xboole_0(X1)
        & ~ v1_xboole_0(X0) )
     => ! [X2] :
          ( m2_subset_1(X2,X0,X1)
         => m1_subset_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( m1_subset_1(X2,X0)
          | ~ m2_subset_1(X2,X0,X1) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( m1_subset_1(X2,X0)
          | ~ m2_subset_1(X2,X0,X1) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f29])).

fof(f94,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X2,X0)
      | ~ m2_subset_1(X2,X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f30])).

cnf(c_5104,plain,
    ( ~ r1_lattice3(X0,X1,X2)
    | r1_lattice3(X3,X4,X5)
    | X3 != X0
    | X4 != X1
    | X5 != X2 ),
    theory(equality)).

cnf(c_6981,plain,
    ( r1_lattice3(X0,X1,X2)
    | ~ r1_lattice3(sK8,k1_xboole_0,o_2_8_waybel_0(sK8,sK9))
    | X2 != o_2_8_waybel_0(sK8,sK9)
    | X0 != sK8
    | X1 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_5104])).

cnf(c_13840,plain,
    ( r1_lattice3(X0,sK4(sK8,sK9),X1)
    | ~ r1_lattice3(sK8,k1_xboole_0,o_2_8_waybel_0(sK8,sK9))
    | X1 != o_2_8_waybel_0(sK8,sK9)
    | X0 != sK8
    | sK4(sK8,sK9) != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_6981])).

cnf(c_21751,plain,
    ( r1_lattice3(X0,sK4(sK8,sK9),o_2_8_waybel_0(sK8,sK9))
    | ~ r1_lattice3(sK8,k1_xboole_0,o_2_8_waybel_0(sK8,sK9))
    | X0 != sK8
    | sK4(sK8,sK9) != k1_xboole_0
    | o_2_8_waybel_0(sK8,sK9) != o_2_8_waybel_0(sK8,sK9) ),
    inference(instantiation,[status(thm)],[c_13840])).

cnf(c_21753,plain,
    ( r1_lattice3(sK8,sK4(sK8,sK9),o_2_8_waybel_0(sK8,sK9))
    | ~ r1_lattice3(sK8,k1_xboole_0,o_2_8_waybel_0(sK8,sK9))
    | sK4(sK8,sK9) != k1_xboole_0
    | o_2_8_waybel_0(sK8,sK9) != o_2_8_waybel_0(sK8,sK9)
    | sK8 != sK8 ),
    inference(instantiation,[status(thm)],[c_21751])).

cnf(c_23,plain,
    ( ~ sP0(X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | r2_hidden(sK5(X0,X1,X2),X1)
    | ~ v1_finset_1(X2) ),
    inference(cnf_transformation,[],[f105])).

cnf(c_6180,plain,
    ( sP0(X0,X1) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(X1)) != iProver_top
    | r2_hidden(sK5(X0,X1,X2),X1) = iProver_top
    | v1_finset_1(X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_22,plain,
    ( r1_lattice3(X0,X1,sK5(X0,X2,X1))
    | ~ sP0(X0,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ v1_finset_1(X1) ),
    inference(cnf_transformation,[],[f106])).

cnf(c_6181,plain,
    ( r1_lattice3(X0,X1,sK5(X0,X2,X1)) = iProver_top
    | sP0(X0,X2) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(X2)) != iProver_top
    | v1_finset_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_32,plain,
    ( ~ r1_lattice3(X0,X1,X2)
    | r1_orders_2(X0,X2,k2_yellow_0(X0,X1))
    | ~ r2_yellow_0(X0,X1)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(k2_yellow_0(X0,X1),u1_struct_0(X0))
    | ~ v5_orders_2(X0)
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f143])).

cnf(c_7,plain,
    ( m1_subset_1(k2_yellow_0(X0,X1),u1_struct_0(X0))
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f92])).

cnf(c_348,plain,
    ( ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ r2_yellow_0(X0,X1)
    | r1_orders_2(X0,X2,k2_yellow_0(X0,X1))
    | ~ r1_lattice3(X0,X1,X2)
    | ~ v5_orders_2(X0)
    | ~ l1_orders_2(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_32,c_7])).

cnf(c_349,plain,
    ( ~ r1_lattice3(X0,X1,X2)
    | r1_orders_2(X0,X2,k2_yellow_0(X0,X1))
    | ~ r2_yellow_0(X0,X1)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ v5_orders_2(X0)
    | ~ l1_orders_2(X0) ),
    inference(renaming,[status(thm)],[c_348])).

cnf(c_55,negated_conjecture,
    ( v5_orders_2(sK8) ),
    inference(cnf_transformation,[],[f132])).

cnf(c_1244,plain,
    ( ~ r1_lattice3(X0,X1,X2)
    | r1_orders_2(X0,X2,k2_yellow_0(X0,X1))
    | ~ r2_yellow_0(X0,X1)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ l1_orders_2(X0)
    | sK8 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_349,c_55])).

cnf(c_1245,plain,
    ( ~ r1_lattice3(sK8,X0,X1)
    | r1_orders_2(sK8,X1,k2_yellow_0(sK8,X0))
    | ~ r2_yellow_0(sK8,X0)
    | ~ m1_subset_1(X1,u1_struct_0(sK8))
    | ~ l1_orders_2(sK8) ),
    inference(unflattening,[status(thm)],[c_1244])).

cnf(c_53,negated_conjecture,
    ( l1_orders_2(sK8) ),
    inference(cnf_transformation,[],[f134])).

cnf(c_1249,plain,
    ( ~ m1_subset_1(X1,u1_struct_0(sK8))
    | ~ r2_yellow_0(sK8,X0)
    | r1_orders_2(sK8,X1,k2_yellow_0(sK8,X0))
    | ~ r1_lattice3(sK8,X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1245,c_53])).

cnf(c_1250,plain,
    ( ~ r1_lattice3(sK8,X0,X1)
    | r1_orders_2(sK8,X1,k2_yellow_0(sK8,X0))
    | ~ r2_yellow_0(sK8,X0)
    | ~ m1_subset_1(X1,u1_struct_0(sK8)) ),
    inference(renaming,[status(thm)],[c_1249])).

cnf(c_6157,plain,
    ( r1_lattice3(sK8,X0,X1) != iProver_top
    | r1_orders_2(sK8,X1,k2_yellow_0(sK8,X0)) = iProver_top
    | r2_yellow_0(sK8,X0) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK8)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1250])).

cnf(c_1480,plain,
    ( m1_subset_1(k2_yellow_0(X0,X1),u1_struct_0(X0))
    | sK8 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_7,c_53])).

cnf(c_1481,plain,
    ( m1_subset_1(k2_yellow_0(sK8,X0),u1_struct_0(sK8)) ),
    inference(unflattening,[status(thm)],[c_1480])).

cnf(c_6148,plain,
    ( m1_subset_1(k2_yellow_0(sK8,X0),u1_struct_0(sK8)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1481])).

cnf(c_50,negated_conjecture,
    ( m1_subset_1(sK9,k1_zfmisc_1(u1_struct_0(sK8))) ),
    inference(cnf_transformation,[],[f137])).

cnf(c_6168,plain,
    ( m1_subset_1(sK9,k1_zfmisc_1(u1_struct_0(sK8))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_50])).

cnf(c_6,plain,
    ( ~ r1_orders_2(X0,X1,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ r2_hidden(X1,X3)
    | r2_hidden(X2,X3)
    | ~ v13_waybel_0(X3,X0)
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_1489,plain,
    ( ~ r1_orders_2(X0,X1,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ r2_hidden(X1,X3)
    | r2_hidden(X2,X3)
    | ~ v13_waybel_0(X3,X0)
    | sK8 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_6,c_53])).

cnf(c_1490,plain,
    ( ~ r1_orders_2(sK8,X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK8)))
    | ~ m1_subset_1(X1,u1_struct_0(sK8))
    | ~ m1_subset_1(X0,u1_struct_0(sK8))
    | ~ r2_hidden(X0,X2)
    | r2_hidden(X1,X2)
    | ~ v13_waybel_0(X2,sK8) ),
    inference(unflattening,[status(thm)],[c_1489])).

cnf(c_36,plain,
    ( m1_subset_1(X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r2_hidden(X0,X2) ),
    inference(cnf_transformation,[],[f121])).

cnf(c_1506,plain,
    ( ~ r1_orders_2(sK8,X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK8)))
    | ~ m1_subset_1(X1,u1_struct_0(sK8))
    | ~ r2_hidden(X0,X2)
    | r2_hidden(X1,X2)
    | ~ v13_waybel_0(X2,sK8) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_1490,c_36])).

cnf(c_6147,plain,
    ( r1_orders_2(sK8,X0,X1) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK8))) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK8)) != iProver_top
    | r2_hidden(X0,X2) != iProver_top
    | r2_hidden(X1,X2) = iProver_top
    | v13_waybel_0(X2,sK8) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1506])).

cnf(c_7509,plain,
    ( r1_orders_2(sK8,X0,X1) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK8)) != iProver_top
    | r2_hidden(X0,sK9) != iProver_top
    | r2_hidden(X1,sK9) = iProver_top
    | v13_waybel_0(sK9,sK8) != iProver_top ),
    inference(superposition,[status(thm)],[c_6168,c_6147])).

cnf(c_65,plain,
    ( m1_subset_1(sK9,k1_zfmisc_1(u1_struct_0(sK8))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_50])).

cnf(c_51,negated_conjecture,
    ( v13_waybel_0(sK9,sK8) ),
    inference(cnf_transformation,[],[f136])).

cnf(c_3015,plain,
    ( ~ r1_orders_2(sK8,X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK8)))
    | ~ m1_subset_1(X1,u1_struct_0(sK8))
    | ~ r2_hidden(X0,X2)
    | r2_hidden(X1,X2)
    | sK9 != X2
    | sK8 != sK8 ),
    inference(resolution_lifted,[status(thm)],[c_51,c_1506])).

cnf(c_3016,plain,
    ( ~ r1_orders_2(sK8,X0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK8))
    | ~ m1_subset_1(sK9,k1_zfmisc_1(u1_struct_0(sK8)))
    | ~ r2_hidden(X0,sK9)
    | r2_hidden(X1,sK9) ),
    inference(unflattening,[status(thm)],[c_3015])).

cnf(c_3017,plain,
    ( r1_orders_2(sK8,X0,X1) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK8)) != iProver_top
    | m1_subset_1(sK9,k1_zfmisc_1(u1_struct_0(sK8))) != iProver_top
    | r2_hidden(X0,sK9) != iProver_top
    | r2_hidden(X1,sK9) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3016])).

cnf(c_8055,plain,
    ( r2_hidden(X1,sK9) = iProver_top
    | r2_hidden(X0,sK9) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK8)) != iProver_top
    | r1_orders_2(sK8,X0,X1) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_7509,c_65,c_3017])).

cnf(c_8056,plain,
    ( r1_orders_2(sK8,X0,X1) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK8)) != iProver_top
    | r2_hidden(X0,sK9) != iProver_top
    | r2_hidden(X1,sK9) = iProver_top ),
    inference(renaming,[status(thm)],[c_8055])).

cnf(c_8065,plain,
    ( r1_orders_2(sK8,X0,k2_yellow_0(sK8,X1)) != iProver_top
    | r2_hidden(X0,sK9) != iProver_top
    | r2_hidden(k2_yellow_0(sK8,X1),sK9) = iProver_top ),
    inference(superposition,[status(thm)],[c_6148,c_8056])).

cnf(c_8995,plain,
    ( r1_lattice3(sK8,X0,X1) != iProver_top
    | r2_yellow_0(sK8,X0) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK8)) != iProver_top
    | r2_hidden(X1,sK9) != iProver_top
    | r2_hidden(k2_yellow_0(sK8,X0),sK9) = iProver_top ),
    inference(superposition,[status(thm)],[c_6157,c_8065])).

cnf(c_6176,plain,
    ( m1_subset_1(X0,X1) = iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(X1)) != iProver_top
    | r2_hidden(X0,X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_36])).

cnf(c_7642,plain,
    ( m1_subset_1(X0,u1_struct_0(sK8)) = iProver_top
    | r2_hidden(X0,sK9) != iProver_top ),
    inference(superposition,[status(thm)],[c_6168,c_6176])).

cnf(c_9159,plain,
    ( r1_lattice3(sK8,X0,X1) != iProver_top
    | r2_yellow_0(sK8,X0) != iProver_top
    | r2_hidden(X1,sK9) != iProver_top
    | r2_hidden(k2_yellow_0(sK8,X0),sK9) = iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_8995,c_7642])).

cnf(c_9163,plain,
    ( r2_yellow_0(sK8,X0) != iProver_top
    | sP0(sK8,X1) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r2_hidden(sK5(sK8,X1,X0),sK9) != iProver_top
    | r2_hidden(k2_yellow_0(sK8,X0),sK9) = iProver_top
    | v1_finset_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_6181,c_9159])).

cnf(c_15879,plain,
    ( r2_yellow_0(sK8,X0) != iProver_top
    | sP0(sK8,sK9) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(sK9)) != iProver_top
    | r2_hidden(k2_yellow_0(sK8,X0),sK9) = iProver_top
    | v1_finset_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_6180,c_9163])).

cnf(c_45,negated_conjecture,
    ( ~ v2_waybel_0(sK9,sK8)
    | ~ r2_hidden(k2_yellow_0(sK8,sK10),sK9) ),
    inference(cnf_transformation,[],[f142])).

cnf(c_6173,plain,
    ( v2_waybel_0(sK9,sK8) != iProver_top
    | r2_hidden(k2_yellow_0(sK8,sK10),sK9) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_45])).

cnf(c_16379,plain,
    ( r2_yellow_0(sK8,sK10) != iProver_top
    | sP0(sK8,sK9) != iProver_top
    | v2_waybel_0(sK9,sK8) != iProver_top
    | m1_subset_1(sK10,k1_zfmisc_1(sK9)) != iProver_top
    | v1_finset_1(sK10) != iProver_top ),
    inference(superposition,[status(thm)],[c_15879,c_6173])).

cnf(c_52,negated_conjecture,
    ( ~ v1_xboole_0(sK9) ),
    inference(cnf_transformation,[],[f135])).

cnf(c_63,plain,
    ( v1_xboole_0(sK9) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_52])).

cnf(c_48,negated_conjecture,
    ( ~ v2_waybel_0(sK9,sK8)
    | v1_finset_1(sK10) ),
    inference(cnf_transformation,[],[f139])).

cnf(c_69,plain,
    ( v2_waybel_0(sK9,sK8) != iProver_top
    | v1_finset_1(sK10) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_48])).

cnf(c_47,negated_conjecture,
    ( ~ v2_waybel_0(sK9,sK8)
    | m1_subset_1(sK10,k1_zfmisc_1(sK9)) ),
    inference(cnf_transformation,[],[f140])).

cnf(c_70,plain,
    ( v2_waybel_0(sK9,sK8) != iProver_top
    | m1_subset_1(sK10,k1_zfmisc_1(sK9)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_47])).

cnf(c_46,negated_conjecture,
    ( ~ v2_waybel_0(sK9,sK8)
    | k1_xboole_0 != sK10 ),
    inference(cnf_transformation,[],[f141])).

cnf(c_71,plain,
    ( k1_xboole_0 != sK10
    | v2_waybel_0(sK9,sK8) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_46])).

cnf(c_41,plain,
    ( r2_yellow_0(X0,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ v1_finset_1(X1)
    | ~ v3_orders_2(X0)
    | ~ v4_orders_2(X0)
    | ~ v5_orders_2(X0)
    | v1_xboole_0(X1)
    | ~ l1_orders_2(X0)
    | ~ v2_lattice3(X0)
    | v2_struct_0(X0) ),
    inference(cnf_transformation,[],[f122])).

cnf(c_0,plain,
    ( ~ l1_orders_2(X0)
    | ~ v2_lattice3(X0)
    | ~ v2_struct_0(X0) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_327,plain,
    ( ~ v2_lattice3(X0)
    | ~ l1_orders_2(X0)
    | v1_xboole_0(X1)
    | ~ v5_orders_2(X0)
    | ~ v4_orders_2(X0)
    | ~ v3_orders_2(X0)
    | ~ v1_finset_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | r2_yellow_0(X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_41,c_0])).

cnf(c_328,plain,
    ( r2_yellow_0(X0,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ v1_finset_1(X1)
    | ~ v3_orders_2(X0)
    | ~ v4_orders_2(X0)
    | ~ v5_orders_2(X0)
    | v1_xboole_0(X1)
    | ~ l1_orders_2(X0)
    | ~ v2_lattice3(X0) ),
    inference(renaming,[status(thm)],[c_327])).

cnf(c_57,negated_conjecture,
    ( v3_orders_2(sK8) ),
    inference(cnf_transformation,[],[f130])).

cnf(c_987,plain,
    ( r2_yellow_0(X0,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ v1_finset_1(X1)
    | ~ v4_orders_2(X0)
    | ~ v5_orders_2(X0)
    | v1_xboole_0(X1)
    | ~ l1_orders_2(X0)
    | ~ v2_lattice3(X0)
    | sK8 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_328,c_57])).

cnf(c_988,plain,
    ( r2_yellow_0(sK8,X0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK8)))
    | ~ v1_finset_1(X0)
    | ~ v4_orders_2(sK8)
    | ~ v5_orders_2(sK8)
    | v1_xboole_0(X0)
    | ~ l1_orders_2(sK8)
    | ~ v2_lattice3(sK8) ),
    inference(unflattening,[status(thm)],[c_987])).

cnf(c_56,negated_conjecture,
    ( v4_orders_2(sK8) ),
    inference(cnf_transformation,[],[f131])).

cnf(c_54,negated_conjecture,
    ( v2_lattice3(sK8) ),
    inference(cnf_transformation,[],[f133])).

cnf(c_992,plain,
    ( r2_yellow_0(sK8,X0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK8)))
    | ~ v1_finset_1(X0)
    | v1_xboole_0(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_988,c_56,c_55,c_54,c_53])).

cnf(c_2157,plain,
    ( r2_yellow_0(sK8,X0)
    | ~ v2_waybel_0(sK9,sK8)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK8)))
    | v1_xboole_0(X0)
    | sK10 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_48,c_992])).

cnf(c_2158,plain,
    ( r2_yellow_0(sK8,sK10)
    | ~ v2_waybel_0(sK9,sK8)
    | ~ m1_subset_1(sK10,k1_zfmisc_1(u1_struct_0(sK8)))
    | v1_xboole_0(sK10) ),
    inference(unflattening,[status(thm)],[c_2157])).

cnf(c_2159,plain,
    ( r2_yellow_0(sK8,sK10) = iProver_top
    | v2_waybel_0(sK9,sK8) != iProver_top
    | m1_subset_1(sK10,k1_zfmisc_1(u1_struct_0(sK8))) != iProver_top
    | v1_xboole_0(sK10) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2158])).

cnf(c_35,plain,
    ( r1_tarski(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f119])).

cnf(c_6624,plain,
    ( r1_tarski(sK9,u1_struct_0(sK8))
    | ~ m1_subset_1(sK9,k1_zfmisc_1(u1_struct_0(sK8))) ),
    inference(instantiation,[status(thm)],[c_35])).

cnf(c_6625,plain,
    ( r1_tarski(sK9,u1_struct_0(sK8)) = iProver_top
    | m1_subset_1(sK9,k1_zfmisc_1(u1_struct_0(sK8))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6624])).

cnf(c_6171,plain,
    ( v2_waybel_0(sK9,sK8) != iProver_top
    | m1_subset_1(sK10,k1_zfmisc_1(sK9)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_47])).

cnf(c_6177,plain,
    ( r1_tarski(X0,X1) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_35])).

cnf(c_6787,plain,
    ( v2_waybel_0(sK9,sK8) != iProver_top
    | r1_tarski(sK10,sK9) = iProver_top ),
    inference(superposition,[status(thm)],[c_6171,c_6177])).

cnf(c_14,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X2,X0)
    | r1_tarski(X2,X1) ),
    inference(cnf_transformation,[],[f99])).

cnf(c_6762,plain,
    ( r1_tarski(X0,u1_struct_0(sK8))
    | ~ r1_tarski(X0,sK9)
    | ~ r1_tarski(sK9,u1_struct_0(sK8)) ),
    inference(instantiation,[status(thm)],[c_14])).

cnf(c_7297,plain,
    ( ~ r1_tarski(sK9,u1_struct_0(sK8))
    | r1_tarski(sK10,u1_struct_0(sK8))
    | ~ r1_tarski(sK10,sK9) ),
    inference(instantiation,[status(thm)],[c_6762])).

cnf(c_7298,plain,
    ( r1_tarski(sK9,u1_struct_0(sK8)) != iProver_top
    | r1_tarski(sK10,u1_struct_0(sK8)) = iProver_top
    | r1_tarski(sK10,sK9) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7297])).

cnf(c_34,plain,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f120])).

cnf(c_8047,plain,
    ( ~ r1_tarski(sK10,u1_struct_0(sK8))
    | m1_subset_1(sK10,k1_zfmisc_1(u1_struct_0(sK8))) ),
    inference(instantiation,[status(thm)],[c_34])).

cnf(c_8048,plain,
    ( r1_tarski(sK10,u1_struct_0(sK8)) != iProver_top
    | m1_subset_1(sK10,k1_zfmisc_1(u1_struct_0(sK8))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8047])).

cnf(c_18,plain,
    ( ~ sP1(X0,X1)
    | sP0(X1,X0)
    | ~ v2_waybel_0(X0,X1)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f101])).

cnf(c_25,plain,
    ( sP1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v4_orders_2(X1)
    | ~ l1_orders_2(X1)
    | v2_struct_0(X1) ),
    inference(cnf_transformation,[],[f110])).

cnf(c_1066,plain,
    ( sP1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_orders_2(X1)
    | v2_struct_0(X1)
    | sK8 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_25,c_56])).

cnf(c_1067,plain,
    ( sP1(X0,sK8)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK8)))
    | ~ l1_orders_2(sK8)
    | v2_struct_0(sK8) ),
    inference(unflattening,[status(thm)],[c_1066])).

cnf(c_192,plain,
    ( ~ l1_orders_2(sK8)
    | ~ v2_lattice3(sK8)
    | ~ v2_struct_0(sK8) ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_1071,plain,
    ( sP1(X0,sK8)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK8))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1067,c_54,c_53,c_192])).

cnf(c_1100,plain,
    ( sP0(X0,X1)
    | ~ v2_waybel_0(X1,X0)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK8)))
    | v1_xboole_0(X1)
    | X2 != X1
    | sK8 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_18,c_1071])).

cnf(c_1101,plain,
    ( sP0(sK8,X0)
    | ~ v2_waybel_0(X0,sK8)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK8)))
    | v1_xboole_0(X0) ),
    inference(unflattening,[status(thm)],[c_1100])).

cnf(c_6162,plain,
    ( sP0(sK8,X0) = iProver_top
    | v2_waybel_0(X0,sK8) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK8))) != iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1101])).

cnf(c_9423,plain,
    ( sP0(sK8,sK9) = iProver_top
    | v2_waybel_0(sK9,sK8) != iProver_top
    | v1_xboole_0(sK9) = iProver_top ),
    inference(superposition,[status(thm)],[c_6168,c_6162])).

cnf(c_42,plain,
    ( ~ v1_xboole_0(X0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f127])).

cnf(c_13255,plain,
    ( ~ v1_xboole_0(sK10)
    | k1_xboole_0 = sK10 ),
    inference(instantiation,[status(thm)],[c_42])).

cnf(c_13259,plain,
    ( k1_xboole_0 = sK10
    | v1_xboole_0(sK10) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13255])).

cnf(c_16394,plain,
    ( v2_waybel_0(sK9,sK8) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_16379,c_63,c_65,c_69,c_70,c_71,c_2159,c_6625,c_6787,c_7298,c_8048,c_9423,c_13259])).

cnf(c_16396,plain,
    ( ~ v2_waybel_0(sK9,sK8) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_16394])).

cnf(c_5090,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_7869,plain,
    ( X0 != X1
    | sK4(sK8,sK9) != X1
    | sK4(sK8,sK9) = X0 ),
    inference(instantiation,[status(thm)],[c_5090])).

cnf(c_8861,plain,
    ( X0 != sK4(sK8,sK9)
    | sK4(sK8,sK9) = X0
    | sK4(sK8,sK9) != sK4(sK8,sK9) ),
    inference(instantiation,[status(thm)],[c_7869])).

cnf(c_10849,plain,
    ( sK4(sK8,sK9) != sK4(sK8,sK9)
    | sK4(sK8,sK9) = k1_xboole_0
    | k1_xboole_0 != sK4(sK8,sK9) ),
    inference(instantiation,[status(thm)],[c_8861])).

cnf(c_10522,plain,
    ( ~ v1_xboole_0(sK4(X0,sK9))
    | k1_xboole_0 = sK4(X0,sK9) ),
    inference(instantiation,[status(thm)],[c_42])).

cnf(c_10528,plain,
    ( k1_xboole_0 = sK4(X0,sK9)
    | v1_xboole_0(sK4(X0,sK9)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10522])).

cnf(c_10530,plain,
    ( k1_xboole_0 = sK4(sK8,sK9)
    | v1_xboole_0(sK4(sK8,sK9)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_10528])).

cnf(c_9250,plain,
    ( ~ r1_tarski(sK4(sK8,sK9),u1_struct_0(sK8))
    | m1_subset_1(sK4(sK8,sK9),k1_zfmisc_1(u1_struct_0(sK8))) ),
    inference(instantiation,[status(thm)],[c_34])).

cnf(c_9251,plain,
    ( r1_tarski(sK4(sK8,sK9),u1_struct_0(sK8)) != iProver_top
    | m1_subset_1(sK4(sK8,sK9),k1_zfmisc_1(u1_struct_0(sK8))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9250])).

cnf(c_49,negated_conjecture,
    ( v2_waybel_0(sK9,sK8)
    | ~ m1_subset_1(X0,k1_zfmisc_1(sK9))
    | r2_hidden(k2_yellow_0(sK8,X0),sK9)
    | ~ v1_finset_1(X0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f138])).

cnf(c_6169,plain,
    ( k1_xboole_0 = X0
    | v2_waybel_0(sK9,sK8) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(sK9)) != iProver_top
    | r2_hidden(k2_yellow_0(sK8,X0),sK9) = iProver_top
    | v1_finset_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_49])).

cnf(c_33,plain,
    ( r1_lattice3(X0,X1,k2_yellow_0(X0,X1))
    | ~ r2_yellow_0(X0,X1)
    | ~ m1_subset_1(k2_yellow_0(X0,X1),u1_struct_0(X0))
    | ~ v5_orders_2(X0)
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f144])).

cnf(c_341,plain,
    ( ~ r2_yellow_0(X0,X1)
    | r1_lattice3(X0,X1,k2_yellow_0(X0,X1))
    | ~ v5_orders_2(X0)
    | ~ l1_orders_2(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_33,c_7])).

cnf(c_342,plain,
    ( r1_lattice3(X0,X1,k2_yellow_0(X0,X1))
    | ~ r2_yellow_0(X0,X1)
    | ~ v5_orders_2(X0)
    | ~ l1_orders_2(X0) ),
    inference(renaming,[status(thm)],[c_341])).

cnf(c_1268,plain,
    ( r1_lattice3(X0,X1,k2_yellow_0(X0,X1))
    | ~ r2_yellow_0(X0,X1)
    | ~ l1_orders_2(X0)
    | sK8 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_342,c_55])).

cnf(c_1269,plain,
    ( r1_lattice3(sK8,X0,k2_yellow_0(sK8,X0))
    | ~ r2_yellow_0(sK8,X0)
    | ~ l1_orders_2(sK8) ),
    inference(unflattening,[status(thm)],[c_1268])).

cnf(c_1273,plain,
    ( ~ r2_yellow_0(sK8,X0)
    | r1_lattice3(sK8,X0,k2_yellow_0(sK8,X0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1269,c_53])).

cnf(c_1274,plain,
    ( r1_lattice3(sK8,X0,k2_yellow_0(sK8,X0))
    | ~ r2_yellow_0(sK8,X0) ),
    inference(renaming,[status(thm)],[c_1273])).

cnf(c_6156,plain,
    ( r1_lattice3(sK8,X0,k2_yellow_0(sK8,X0)) = iProver_top
    | r2_yellow_0(sK8,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1274])).

cnf(c_19,plain,
    ( ~ r1_lattice3(X0,sK4(X0,X1),X2)
    | sP0(X0,X1)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ r2_hidden(X2,X1) ),
    inference(cnf_transformation,[],[f109])).

cnf(c_6184,plain,
    ( r1_lattice3(X0,sK4(X0,X1),X2) != iProver_top
    | sP0(X0,X1) = iProver_top
    | m1_subset_1(X2,u1_struct_0(X0)) != iProver_top
    | r2_hidden(X2,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_8313,plain,
    ( r2_yellow_0(sK8,sK4(sK8,X0)) != iProver_top
    | sP0(sK8,X0) = iProver_top
    | m1_subset_1(k2_yellow_0(sK8,sK4(sK8,X0)),u1_struct_0(sK8)) != iProver_top
    | r2_hidden(k2_yellow_0(sK8,sK4(sK8,X0)),X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_6156,c_6184])).

cnf(c_9056,plain,
    ( r2_yellow_0(sK8,sK4(sK8,X0)) != iProver_top
    | sP0(sK8,X0) = iProver_top
    | r2_hidden(k2_yellow_0(sK8,sK4(sK8,X0)),X0) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_8313,c_6148])).

cnf(c_9060,plain,
    ( sK4(sK8,sK9) = k1_xboole_0
    | r2_yellow_0(sK8,sK4(sK8,sK9)) != iProver_top
    | sP0(sK8,sK9) = iProver_top
    | v2_waybel_0(sK9,sK8) = iProver_top
    | m1_subset_1(sK4(sK8,sK9),k1_zfmisc_1(sK9)) != iProver_top
    | v1_finset_1(sK4(sK8,sK9)) != iProver_top ),
    inference(superposition,[status(thm)],[c_6169,c_9056])).

cnf(c_16,plain,
    ( ~ sP1(X0,X1)
    | ~ sP0(X1,X0)
    | v2_waybel_0(X0,X1) ),
    inference(cnf_transformation,[],[f103])).

cnf(c_1133,plain,
    ( ~ sP0(X0,X1)
    | v2_waybel_0(X1,X0)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK8)))
    | X2 != X1
    | sK8 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_16,c_1071])).

cnf(c_1134,plain,
    ( ~ sP0(sK8,X0)
    | v2_waybel_0(X0,sK8)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK8))) ),
    inference(unflattening,[status(thm)],[c_1133])).

cnf(c_6606,plain,
    ( ~ sP0(sK8,sK9)
    | v2_waybel_0(sK9,sK8)
    | ~ m1_subset_1(sK9,k1_zfmisc_1(u1_struct_0(sK8))) ),
    inference(instantiation,[status(thm)],[c_1134])).

cnf(c_6607,plain,
    ( sP0(sK8,sK9) != iProver_top
    | v2_waybel_0(sK9,sK8) = iProver_top
    | m1_subset_1(sK9,k1_zfmisc_1(u1_struct_0(sK8))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6606])).

cnf(c_21,plain,
    ( sP0(X0,X1)
    | v1_finset_1(sK4(X0,X1)) ),
    inference(cnf_transformation,[],[f107])).

cnf(c_6688,plain,
    ( sP0(sK8,sK9)
    | v1_finset_1(sK4(sK8,sK9)) ),
    inference(instantiation,[status(thm)],[c_21])).

cnf(c_6689,plain,
    ( sP0(sK8,sK9) = iProver_top
    | v1_finset_1(sK4(sK8,sK9)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6688])).

cnf(c_20,plain,
    ( sP0(X0,X1)
    | m1_subset_1(sK4(X0,X1),k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f108])).

cnf(c_6687,plain,
    ( sP0(sK8,sK9)
    | m1_subset_1(sK4(sK8,sK9),k1_zfmisc_1(sK9)) ),
    inference(instantiation,[status(thm)],[c_20])).

cnf(c_6691,plain,
    ( sP0(sK8,sK9) = iProver_top
    | m1_subset_1(sK4(sK8,sK9),k1_zfmisc_1(sK9)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6687])).

cnf(c_9100,plain,
    ( r2_yellow_0(sK8,sK4(sK8,sK9)) != iProver_top
    | sK4(sK8,sK9) = k1_xboole_0
    | v2_waybel_0(sK9,sK8) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_9060,c_65,c_6607,c_6689,c_6691])).

cnf(c_9101,plain,
    ( sK4(sK8,sK9) = k1_xboole_0
    | r2_yellow_0(sK8,sK4(sK8,sK9)) != iProver_top
    | v2_waybel_0(sK9,sK8) = iProver_top ),
    inference(renaming,[status(thm)],[c_9100])).

cnf(c_5089,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_8862,plain,
    ( sK4(sK8,sK9) = sK4(sK8,sK9) ),
    inference(instantiation,[status(thm)],[c_5089])).

cnf(c_5101,plain,
    ( X0 != X1
    | o_2_8_waybel_0(X0,X2) = o_2_8_waybel_0(X1,X2) ),
    theory(equality)).

cnf(c_7631,plain,
    ( X0 != sK8
    | o_2_8_waybel_0(X0,sK9) = o_2_8_waybel_0(sK8,sK9) ),
    inference(instantiation,[status(thm)],[c_5101])).

cnf(c_7634,plain,
    ( o_2_8_waybel_0(sK8,sK9) = o_2_8_waybel_0(sK8,sK9)
    | sK8 != sK8 ),
    inference(instantiation,[status(thm)],[c_7631])).

cnf(c_7555,plain,
    ( r1_tarski(sK4(sK8,sK9),u1_struct_0(sK8))
    | ~ r1_tarski(sK4(sK8,sK9),sK9)
    | ~ r1_tarski(sK9,u1_struct_0(sK8)) ),
    inference(instantiation,[status(thm)],[c_6762])).

cnf(c_7556,plain,
    ( r1_tarski(sK4(sK8,sK9),u1_struct_0(sK8)) = iProver_top
    | r1_tarski(sK4(sK8,sK9),sK9) != iProver_top
    | r1_tarski(sK9,u1_struct_0(sK8)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7555])).

cnf(c_6686,plain,
    ( ~ r1_lattice3(sK8,sK4(sK8,sK9),X0)
    | sP0(sK8,sK9)
    | ~ m1_subset_1(X0,u1_struct_0(sK8))
    | ~ r2_hidden(X0,sK9) ),
    inference(instantiation,[status(thm)],[c_19])).

cnf(c_7474,plain,
    ( ~ r1_lattice3(sK8,sK4(sK8,sK9),o_2_8_waybel_0(sK8,sK9))
    | sP0(sK8,sK9)
    | ~ m1_subset_1(o_2_8_waybel_0(sK8,sK9),u1_struct_0(sK8))
    | ~ r2_hidden(o_2_8_waybel_0(sK8,sK9),sK9) ),
    inference(instantiation,[status(thm)],[c_6686])).

cnf(c_6891,plain,
    ( r2_yellow_0(sK8,sK4(sK8,sK9))
    | ~ m1_subset_1(sK4(sK8,sK9),k1_zfmisc_1(u1_struct_0(sK8)))
    | ~ v1_finset_1(sK4(sK8,sK9))
    | v1_xboole_0(sK4(sK8,sK9)) ),
    inference(instantiation,[status(thm)],[c_992])).

cnf(c_6895,plain,
    ( r2_yellow_0(sK8,sK4(sK8,sK9)) = iProver_top
    | m1_subset_1(sK4(sK8,sK9),k1_zfmisc_1(u1_struct_0(sK8))) != iProver_top
    | v1_finset_1(sK4(sK8,sK9)) != iProver_top
    | v1_xboole_0(sK4(sK8,sK9)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6891])).

cnf(c_6872,plain,
    ( r1_tarski(sK4(sK8,sK9),sK9)
    | ~ m1_subset_1(sK4(sK8,sK9),k1_zfmisc_1(sK9)) ),
    inference(instantiation,[status(thm)],[c_35])).

cnf(c_6873,plain,
    ( r1_tarski(sK4(sK8,sK9),sK9) = iProver_top
    | m1_subset_1(sK4(sK8,sK9),k1_zfmisc_1(sK9)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6872])).

cnf(c_15,plain,
    ( ~ m1_subset_1(X0,X1)
    | r2_hidden(X0,X1)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f100])).

cnf(c_6751,plain,
    ( ~ m1_subset_1(o_2_8_waybel_0(sK8,sK9),sK9)
    | r2_hidden(o_2_8_waybel_0(sK8,sK9),sK9)
    | v1_xboole_0(sK9) ),
    inference(instantiation,[status(thm)],[c_15])).

cnf(c_43,plain,
    ( r1_lattice3(X0,k1_xboole_0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f128])).

cnf(c_1468,plain,
    ( r1_lattice3(X0,k1_xboole_0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | sK8 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_43,c_53])).

cnf(c_1469,plain,
    ( r1_lattice3(sK8,k1_xboole_0,X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK8)) ),
    inference(unflattening,[status(thm)],[c_1468])).

cnf(c_6746,plain,
    ( r1_lattice3(sK8,k1_xboole_0,o_2_8_waybel_0(sK8,sK9))
    | ~ m1_subset_1(o_2_8_waybel_0(sK8,sK9),u1_struct_0(sK8)) ),
    inference(instantiation,[status(thm)],[c_1469])).

cnf(c_5126,plain,
    ( sK8 = sK8 ),
    inference(instantiation,[status(thm)],[c_5089])).

cnf(c_13,plain,
    ( ~ m2_subset_1(X0,X1,X2)
    | m1_subset_1(X0,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | v1_xboole_0(X1)
    | v1_xboole_0(X2) ),
    inference(cnf_transformation,[],[f97])).

cnf(c_10,plain,
    ( m2_subset_1(o_2_8_waybel_0(X0,X1),u1_struct_0(X0),X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ v13_waybel_0(X1,X0)
    | ~ v3_orders_2(X0)
    | ~ v4_orders_2(X0)
    | ~ v5_orders_2(X0)
    | v1_xboole_0(X1)
    | ~ l1_orders_2(X0)
    | ~ v2_lattice3(X0) ),
    inference(cnf_transformation,[],[f95])).

cnf(c_1019,plain,
    ( m2_subset_1(o_2_8_waybel_0(X0,X1),u1_struct_0(X0),X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ v13_waybel_0(X1,X0)
    | ~ v4_orders_2(X0)
    | ~ v5_orders_2(X0)
    | v1_xboole_0(X1)
    | ~ l1_orders_2(X0)
    | ~ v2_lattice3(X0)
    | sK8 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_10,c_57])).

cnf(c_1020,plain,
    ( m2_subset_1(o_2_8_waybel_0(sK8,X0),u1_struct_0(sK8),X0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK8)))
    | ~ v13_waybel_0(X0,sK8)
    | ~ v4_orders_2(sK8)
    | ~ v5_orders_2(sK8)
    | v1_xboole_0(X0)
    | ~ l1_orders_2(sK8)
    | ~ v2_lattice3(sK8) ),
    inference(unflattening,[status(thm)],[c_1019])).

cnf(c_1024,plain,
    ( m2_subset_1(o_2_8_waybel_0(sK8,X0),u1_struct_0(sK8),X0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK8)))
    | ~ v13_waybel_0(X0,sK8)
    | v1_xboole_0(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1020,c_56,c_55,c_54,c_53])).

cnf(c_1180,plain,
    ( m1_subset_1(X0,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK8)))
    | ~ v13_waybel_0(X3,sK8)
    | v1_xboole_0(X2)
    | v1_xboole_0(X1)
    | v1_xboole_0(X3)
    | X3 != X1
    | o_2_8_waybel_0(sK8,X3) != X0
    | u1_struct_0(sK8) != X2 ),
    inference(resolution_lifted,[status(thm)],[c_13,c_1024])).

cnf(c_1181,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK8)))
    | m1_subset_1(o_2_8_waybel_0(sK8,X0),X0)
    | ~ v13_waybel_0(X0,sK8)
    | v1_xboole_0(X0)
    | v1_xboole_0(u1_struct_0(sK8)) ),
    inference(unflattening,[status(thm)],[c_1180])).

cnf(c_11,plain,
    ( ~ v1_xboole_0(u1_struct_0(X0))
    | ~ l1_struct_0(X0)
    | v2_struct_0(X0) ),
    inference(cnf_transformation,[],[f96])).

cnf(c_163,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK8))
    | ~ l1_struct_0(sK8)
    | v2_struct_0(sK8) ),
    inference(instantiation,[status(thm)],[c_11])).

cnf(c_8,plain,
    ( l1_struct_0(X0)
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f93])).

cnf(c_170,plain,
    ( l1_struct_0(sK8)
    | ~ l1_orders_2(sK8) ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(c_1185,plain,
    ( v1_xboole_0(X0)
    | ~ v13_waybel_0(X0,sK8)
    | m1_subset_1(o_2_8_waybel_0(sK8,X0),X0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK8))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1181,c_54,c_53,c_163,c_170,c_192])).

cnf(c_1186,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK8)))
    | m1_subset_1(o_2_8_waybel_0(sK8,X0),X0)
    | ~ v13_waybel_0(X0,sK8)
    | v1_xboole_0(X0) ),
    inference(renaming,[status(thm)],[c_1185])).

cnf(c_3004,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK8)))
    | m1_subset_1(o_2_8_waybel_0(sK8,X0),X0)
    | v1_xboole_0(X0)
    | sK9 != X0
    | sK8 != sK8 ),
    inference(resolution_lifted,[status(thm)],[c_51,c_1186])).

cnf(c_3005,plain,
    ( m1_subset_1(o_2_8_waybel_0(sK8,sK9),sK9)
    | ~ m1_subset_1(sK9,k1_zfmisc_1(u1_struct_0(sK8)))
    | v1_xboole_0(sK9) ),
    inference(unflattening,[status(thm)],[c_3004])).

cnf(c_9,plain,
    ( ~ m2_subset_1(X0,X1,X2)
    | m1_subset_1(X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | v1_xboole_0(X1)
    | v1_xboole_0(X2) ),
    inference(cnf_transformation,[],[f94])).

cnf(c_1204,plain,
    ( m1_subset_1(X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK8)))
    | ~ v13_waybel_0(X3,sK8)
    | v1_xboole_0(X1)
    | v1_xboole_0(X2)
    | v1_xboole_0(X3)
    | X3 != X2
    | o_2_8_waybel_0(sK8,X3) != X0
    | u1_struct_0(sK8) != X1 ),
    inference(resolution_lifted,[status(thm)],[c_9,c_1024])).

cnf(c_1205,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK8)))
    | m1_subset_1(o_2_8_waybel_0(sK8,X0),u1_struct_0(sK8))
    | ~ v13_waybel_0(X0,sK8)
    | v1_xboole_0(X0)
    | v1_xboole_0(u1_struct_0(sK8)) ),
    inference(unflattening,[status(thm)],[c_1204])).

cnf(c_1209,plain,
    ( v1_xboole_0(X0)
    | ~ v13_waybel_0(X0,sK8)
    | m1_subset_1(o_2_8_waybel_0(sK8,X0),u1_struct_0(sK8))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK8))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1205,c_54,c_53,c_163,c_170,c_192])).

cnf(c_1210,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK8)))
    | m1_subset_1(o_2_8_waybel_0(sK8,X0),u1_struct_0(sK8))
    | ~ v13_waybel_0(X0,sK8)
    | v1_xboole_0(X0) ),
    inference(renaming,[status(thm)],[c_1209])).

cnf(c_2993,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK8)))
    | m1_subset_1(o_2_8_waybel_0(sK8,X0),u1_struct_0(sK8))
    | v1_xboole_0(X0)
    | sK9 != X0
    | sK8 != sK8 ),
    inference(resolution_lifted,[status(thm)],[c_51,c_1210])).

cnf(c_2994,plain,
    ( m1_subset_1(o_2_8_waybel_0(sK8,sK9),u1_struct_0(sK8))
    | ~ m1_subset_1(sK9,k1_zfmisc_1(u1_struct_0(sK8)))
    | v1_xboole_0(sK9) ),
    inference(unflattening,[status(thm)],[c_2993])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_21753,c_16396,c_16394,c_10849,c_10530,c_9251,c_9101,c_8862,c_7634,c_7556,c_7474,c_6895,c_6873,c_6751,c_6746,c_6691,c_6689,c_6625,c_6607,c_6606,c_5126,c_3005,c_2994,c_65,c_50,c_52])).


%------------------------------------------------------------------------------
