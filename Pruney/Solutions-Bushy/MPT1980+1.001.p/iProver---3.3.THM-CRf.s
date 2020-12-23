%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT1980+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n026.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:46:59 EST 2020

% Result     : Theorem 3.06s
% Output     : CNFRefutation 3.06s
% Verified   : 
% Statistics : Number of formulae       :  219 ( 428 expanded)
%              Number of clauses        :  104 ( 108 expanded)
%              Number of leaves         :   21 ( 115 expanded)
%              Depth                    :   15
%              Number of atoms          : 1740 (6532 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   21 (   8 average)
%              Maximal clause size      :   46 (   8 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f50,plain,(
    ! [X0] :
      ( ! [X1] :
          ( sP0(X0,X1)
        <=> ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k7_lattice3(X0))))
            & v1_waybel_7(X1,k7_lattice3(X0))
            & v12_waybel_0(X1,k7_lattice3(X0))
            & v1_waybel_0(X1,k7_lattice3(X0))
            & ~ v1_xboole_0(X1) ) )
      | ~ sP1(X0) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f52,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( sP0(X0,X1)
            | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k7_lattice3(X0))))
            | ~ v1_waybel_7(X1,k7_lattice3(X0))
            | ~ v12_waybel_0(X1,k7_lattice3(X0))
            | ~ v1_waybel_0(X1,k7_lattice3(X0))
            | v1_xboole_0(X1) )
          & ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k7_lattice3(X0))))
              & v1_waybel_7(X1,k7_lattice3(X0))
              & v12_waybel_0(X1,k7_lattice3(X0))
              & v1_waybel_0(X1,k7_lattice3(X0))
              & ~ v1_xboole_0(X1) )
            | ~ sP0(X0,X1) ) )
      | ~ sP1(X0) ) ),
    inference(nnf_transformation,[],[f50])).

fof(f53,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( sP0(X0,X1)
            | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k7_lattice3(X0))))
            | ~ v1_waybel_7(X1,k7_lattice3(X0))
            | ~ v12_waybel_0(X1,k7_lattice3(X0))
            | ~ v1_waybel_0(X1,k7_lattice3(X0))
            | v1_xboole_0(X1) )
          & ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k7_lattice3(X0))))
              & v1_waybel_7(X1,k7_lattice3(X0))
              & v12_waybel_0(X1,k7_lattice3(X0))
              & v1_waybel_0(X1,k7_lattice3(X0))
              & ~ v1_xboole_0(X1) )
            | ~ sP0(X0,X1) ) )
      | ~ sP1(X0) ) ),
    inference(flattening,[],[f52])).

fof(f83,plain,(
    ! [X0,X1] :
      ( sP0(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k7_lattice3(X0))))
      | ~ v1_waybel_7(X1,k7_lattice3(X0))
      | ~ v12_waybel_0(X1,k7_lattice3(X0))
      | ~ v1_waybel_0(X1,k7_lattice3(X0))
      | v1_xboole_0(X1)
      | ~ sP1(X0) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( ( ~ v1_xboole_0(X1)
        & ~ v1_xboole_0(X0) )
     => ( r1_subset_1(X0,X1)
       => r1_subset_1(X1,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0,X1] :
      ( r1_subset_1(X1,X0)
      | ~ r1_subset_1(X0,X1)
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f38,plain,(
    ! [X0,X1] :
      ( r1_subset_1(X1,X0)
      | ~ r1_subset_1(X0,X1)
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f37])).

fof(f77,plain,(
    ! [X0,X1] :
      ( r1_subset_1(X1,X0)
      | ~ r1_subset_1(X0,X1)
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f11,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v2_lattice3(X0)
        & v1_lattice3(X0)
        & v2_waybel_1(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0) )
     => ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & v12_waybel_0(X1,X0)
            & v1_waybel_0(X1,X0)
            & ~ v1_xboole_0(X1) )
         => ! [X2] :
              ( ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
                & v13_waybel_0(X2,X0)
                & v2_waybel_0(X2,X0)
                & ~ v1_xboole_0(X2) )
             => ~ ( ! [X3] :
                      ( ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                        & v12_waybel_0(X3,X0)
                        & v1_waybel_0(X3,X0)
                        & ~ v1_xboole_0(X3) )
                     => ~ ( r1_subset_1(X3,X2)
                          & r1_tarski(X1,X3)
                          & v1_waybel_7(X3,X0) ) )
                  & r1_subset_1(X1,X2) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f42,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ? [X3] :
                  ( r1_subset_1(X3,X2)
                  & r1_tarski(X1,X3)
                  & v1_waybel_7(X3,X0)
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                  & v12_waybel_0(X3,X0)
                  & v1_waybel_0(X3,X0)
                  & ~ v1_xboole_0(X3) )
              | ~ r1_subset_1(X1,X2)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
              | ~ v13_waybel_0(X2,X0)
              | ~ v2_waybel_0(X2,X0)
              | v1_xboole_0(X2) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ v12_waybel_0(X1,X0)
          | ~ v1_waybel_0(X1,X0)
          | v1_xboole_0(X1) )
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v1_lattice3(X0)
      | ~ v2_waybel_1(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f43,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ? [X3] :
                  ( r1_subset_1(X3,X2)
                  & r1_tarski(X1,X3)
                  & v1_waybel_7(X3,X0)
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                  & v12_waybel_0(X3,X0)
                  & v1_waybel_0(X3,X0)
                  & ~ v1_xboole_0(X3) )
              | ~ r1_subset_1(X1,X2)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
              | ~ v13_waybel_0(X2,X0)
              | ~ v2_waybel_0(X2,X0)
              | v1_xboole_0(X2) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ v12_waybel_0(X1,X0)
          | ~ v1_waybel_0(X1,X0)
          | v1_xboole_0(X1) )
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v1_lattice3(X0)
      | ~ v2_waybel_1(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(flattening,[],[f42])).

fof(f58,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( r1_subset_1(X3,X2)
          & r1_tarski(X1,X3)
          & v1_waybel_7(X3,X0)
          & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
          & v12_waybel_0(X3,X0)
          & v1_waybel_0(X3,X0)
          & ~ v1_xboole_0(X3) )
     => ( r1_subset_1(sK2(X0,X1,X2),X2)
        & r1_tarski(X1,sK2(X0,X1,X2))
        & v1_waybel_7(sK2(X0,X1,X2),X0)
        & m1_subset_1(sK2(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0)))
        & v12_waybel_0(sK2(X0,X1,X2),X0)
        & v1_waybel_0(sK2(X0,X1,X2),X0)
        & ~ v1_xboole_0(sK2(X0,X1,X2)) ) ) ),
    introduced(choice_axiom,[])).

fof(f59,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r1_subset_1(sK2(X0,X1,X2),X2)
                & r1_tarski(X1,sK2(X0,X1,X2))
                & v1_waybel_7(sK2(X0,X1,X2),X0)
                & m1_subset_1(sK2(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0)))
                & v12_waybel_0(sK2(X0,X1,X2),X0)
                & v1_waybel_0(sK2(X0,X1,X2),X0)
                & ~ v1_xboole_0(sK2(X0,X1,X2)) )
              | ~ r1_subset_1(X1,X2)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
              | ~ v13_waybel_0(X2,X0)
              | ~ v2_waybel_0(X2,X0)
              | v1_xboole_0(X2) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ v12_waybel_0(X1,X0)
          | ~ v1_waybel_0(X1,X0)
          | v1_xboole_0(X1) )
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v1_lattice3(X0)
      | ~ v2_waybel_1(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f43,f58])).

fof(f101,plain,(
    ! [X2,X0,X1] :
      ( r1_subset_1(sK2(X0,X1,X2),X2)
      | ~ r1_subset_1(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v13_waybel_0(X2,X0)
      | ~ v2_waybel_0(X2,X0)
      | v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v12_waybel_0(X1,X0)
      | ~ v1_waybel_0(X1,X0)
      | v1_xboole_0(X1)
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v1_lattice3(X0)
      | ~ v2_waybel_1(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f59])).

fof(f99,plain,(
    ! [X2,X0,X1] :
      ( v1_waybel_7(sK2(X0,X1,X2),X0)
      | ~ r1_subset_1(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v13_waybel_0(X2,X0)
      | ~ v2_waybel_0(X2,X0)
      | v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v12_waybel_0(X1,X0)
      | ~ v1_waybel_0(X1,X0)
      | v1_xboole_0(X1)
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v1_lattice3(X0)
      | ~ v2_waybel_1(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f59])).

fof(f98,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(sK2(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ r1_subset_1(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v13_waybel_0(X2,X0)
      | ~ v2_waybel_0(X2,X0)
      | v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v12_waybel_0(X1,X0)
      | ~ v1_waybel_0(X1,X0)
      | v1_xboole_0(X1)
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v1_lattice3(X0)
      | ~ v2_waybel_1(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f59])).

fof(f97,plain,(
    ! [X2,X0,X1] :
      ( v12_waybel_0(sK2(X0,X1,X2),X0)
      | ~ r1_subset_1(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v13_waybel_0(X2,X0)
      | ~ v2_waybel_0(X2,X0)
      | v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v12_waybel_0(X1,X0)
      | ~ v1_waybel_0(X1,X0)
      | v1_xboole_0(X1)
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v1_lattice3(X0)
      | ~ v2_waybel_1(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f59])).

fof(f96,plain,(
    ! [X2,X0,X1] :
      ( v1_waybel_0(sK2(X0,X1,X2),X0)
      | ~ r1_subset_1(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v13_waybel_0(X2,X0)
      | ~ v2_waybel_0(X2,X0)
      | v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v12_waybel_0(X1,X0)
      | ~ v1_waybel_0(X1,X0)
      | v1_xboole_0(X1)
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v1_lattice3(X0)
      | ~ v2_waybel_1(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f59])).

fof(f95,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(sK2(X0,X1,X2))
      | ~ r1_subset_1(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v13_waybel_0(X2,X0)
      | ~ v2_waybel_0(X2,X0)
      | v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v12_waybel_0(X1,X0)
      | ~ v1_waybel_0(X1,X0)
      | v1_xboole_0(X1)
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v1_lattice3(X0)
      | ~ v2_waybel_1(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f59])).

fof(f100,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X1,sK2(X0,X1,X2))
      | ~ r1_subset_1(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v13_waybel_0(X2,X0)
      | ~ v2_waybel_0(X2,X0)
      | v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v12_waybel_0(X1,X0)
      | ~ v1_waybel_0(X1,X0)
      | v1_xboole_0(X1)
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v1_lattice3(X0)
      | ~ v2_waybel_1(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f59])).

fof(f49,plain,(
    ! [X0,X1] :
      ( sP0(X0,X1)
    <=> ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & v2_waybel_7(X1,X0)
        & v13_waybel_0(X1,X0)
        & v2_waybel_0(X1,X0)
        & ~ v1_xboole_0(X1) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f54,plain,(
    ! [X0,X1] :
      ( ( sP0(X0,X1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ v2_waybel_7(X1,X0)
        | ~ v13_waybel_0(X1,X0)
        | ~ v2_waybel_0(X1,X0)
        | v1_xboole_0(X1) )
      & ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          & v2_waybel_7(X1,X0)
          & v13_waybel_0(X1,X0)
          & v2_waybel_0(X1,X0)
          & ~ v1_xboole_0(X1) )
        | ~ sP0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f49])).

fof(f55,plain,(
    ! [X0,X1] :
      ( ( sP0(X0,X1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ v2_waybel_7(X1,X0)
        | ~ v13_waybel_0(X1,X0)
        | ~ v2_waybel_0(X1,X0)
        | v1_xboole_0(X1) )
      & ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          & v2_waybel_7(X1,X0)
          & v13_waybel_0(X1,X0)
          & v2_waybel_0(X1,X0)
          & ~ v1_xboole_0(X1) )
        | ~ sP0(X0,X1) ) ) ),
    inference(flattening,[],[f54])).

fof(f87,plain,(
    ! [X0,X1] :
      ( v2_waybel_7(X1,X0)
      | ~ sP0(X0,X1) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f15,conjecture,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v2_lattice3(X0)
        & v1_lattice3(X0)
        & v2_waybel_1(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0) )
     => ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & v12_waybel_0(X1,X0)
            & v1_waybel_0(X1,X0)
            & ~ v1_xboole_0(X1) )
         => ! [X2] :
              ( ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
                & v13_waybel_0(X2,X0)
                & v2_waybel_0(X2,X0)
                & ~ v1_xboole_0(X2) )
             => ~ ( ! [X3] :
                      ( ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                        & v13_waybel_0(X3,X0)
                        & v2_waybel_0(X3,X0)
                        & ~ v1_xboole_0(X3) )
                     => ~ ( r1_subset_1(X1,X3)
                          & r1_tarski(X2,X3)
                          & v2_waybel_7(X3,X0) ) )
                  & r1_subset_1(X1,X2) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_orders_2(X0)
          & v2_lattice3(X0)
          & v1_lattice3(X0)
          & v2_waybel_1(X0)
          & v5_orders_2(X0)
          & v4_orders_2(X0)
          & v3_orders_2(X0) )
       => ! [X1] :
            ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
              & v12_waybel_0(X1,X0)
              & v1_waybel_0(X1,X0)
              & ~ v1_xboole_0(X1) )
           => ! [X2] :
                ( ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
                  & v13_waybel_0(X2,X0)
                  & v2_waybel_0(X2,X0)
                  & ~ v1_xboole_0(X2) )
               => ~ ( ! [X3] :
                        ( ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                          & v13_waybel_0(X3,X0)
                          & v2_waybel_0(X3,X0)
                          & ~ v1_xboole_0(X3) )
                       => ~ ( r1_subset_1(X1,X3)
                            & r1_tarski(X2,X3)
                            & v2_waybel_7(X3,X0) ) )
                    & r1_subset_1(X1,X2) ) ) ) ) ),
    inference(negated_conjecture,[],[f15])).

fof(f47,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ! [X3] :
                  ( ~ r1_subset_1(X1,X3)
                  | ~ r1_tarski(X2,X3)
                  | ~ v2_waybel_7(X3,X0)
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                  | ~ v13_waybel_0(X3,X0)
                  | ~ v2_waybel_0(X3,X0)
                  | v1_xboole_0(X3) )
              & r1_subset_1(X1,X2)
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
              & v13_waybel_0(X2,X0)
              & v2_waybel_0(X2,X0)
              & ~ v1_xboole_0(X2) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          & v12_waybel_0(X1,X0)
          & v1_waybel_0(X1,X0)
          & ~ v1_xboole_0(X1) )
      & l1_orders_2(X0)
      & v2_lattice3(X0)
      & v1_lattice3(X0)
      & v2_waybel_1(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f48,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ! [X3] :
                  ( ~ r1_subset_1(X1,X3)
                  | ~ r1_tarski(X2,X3)
                  | ~ v2_waybel_7(X3,X0)
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                  | ~ v13_waybel_0(X3,X0)
                  | ~ v2_waybel_0(X3,X0)
                  | v1_xboole_0(X3) )
              & r1_subset_1(X1,X2)
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
              & v13_waybel_0(X2,X0)
              & v2_waybel_0(X2,X0)
              & ~ v1_xboole_0(X2) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          & v12_waybel_0(X1,X0)
          & v1_waybel_0(X1,X0)
          & ~ v1_xboole_0(X1) )
      & l1_orders_2(X0)
      & v2_lattice3(X0)
      & v1_lattice3(X0)
      & v2_waybel_1(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0) ) ),
    inference(flattening,[],[f47])).

fof(f68,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ! [X3] :
              ( ~ r1_subset_1(X1,X3)
              | ~ r1_tarski(X2,X3)
              | ~ v2_waybel_7(X3,X0)
              | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
              | ~ v13_waybel_0(X3,X0)
              | ~ v2_waybel_0(X3,X0)
              | v1_xboole_0(X3) )
          & r1_subset_1(X1,X2)
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
          & v13_waybel_0(X2,X0)
          & v2_waybel_0(X2,X0)
          & ~ v1_xboole_0(X2) )
     => ( ! [X3] :
            ( ~ r1_subset_1(X1,X3)
            | ~ r1_tarski(sK5,X3)
            | ~ v2_waybel_7(X3,X0)
            | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
            | ~ v13_waybel_0(X3,X0)
            | ~ v2_waybel_0(X3,X0)
            | v1_xboole_0(X3) )
        & r1_subset_1(X1,sK5)
        & m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(X0)))
        & v13_waybel_0(sK5,X0)
        & v2_waybel_0(sK5,X0)
        & ~ v1_xboole_0(sK5) ) ) ),
    introduced(choice_axiom,[])).

fof(f67,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ! [X3] :
                  ( ~ r1_subset_1(X1,X3)
                  | ~ r1_tarski(X2,X3)
                  | ~ v2_waybel_7(X3,X0)
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                  | ~ v13_waybel_0(X3,X0)
                  | ~ v2_waybel_0(X3,X0)
                  | v1_xboole_0(X3) )
              & r1_subset_1(X1,X2)
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
              & v13_waybel_0(X2,X0)
              & v2_waybel_0(X2,X0)
              & ~ v1_xboole_0(X2) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          & v12_waybel_0(X1,X0)
          & v1_waybel_0(X1,X0)
          & ~ v1_xboole_0(X1) )
     => ( ? [X2] :
            ( ! [X3] :
                ( ~ r1_subset_1(sK4,X3)
                | ~ r1_tarski(X2,X3)
                | ~ v2_waybel_7(X3,X0)
                | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                | ~ v13_waybel_0(X3,X0)
                | ~ v2_waybel_0(X3,X0)
                | v1_xboole_0(X3) )
            & r1_subset_1(sK4,X2)
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
            & v13_waybel_0(X2,X0)
            & v2_waybel_0(X2,X0)
            & ~ v1_xboole_0(X2) )
        & m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(X0)))
        & v12_waybel_0(sK4,X0)
        & v1_waybel_0(sK4,X0)
        & ~ v1_xboole_0(sK4) ) ) ),
    introduced(choice_axiom,[])).

fof(f66,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ! [X3] :
                    ( ~ r1_subset_1(X1,X3)
                    | ~ r1_tarski(X2,X3)
                    | ~ v2_waybel_7(X3,X0)
                    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                    | ~ v13_waybel_0(X3,X0)
                    | ~ v2_waybel_0(X3,X0)
                    | v1_xboole_0(X3) )
                & r1_subset_1(X1,X2)
                & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
                & v13_waybel_0(X2,X0)
                & v2_waybel_0(X2,X0)
                & ~ v1_xboole_0(X2) )
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & v12_waybel_0(X1,X0)
            & v1_waybel_0(X1,X0)
            & ~ v1_xboole_0(X1) )
        & l1_orders_2(X0)
        & v2_lattice3(X0)
        & v1_lattice3(X0)
        & v2_waybel_1(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ! [X3] :
                  ( ~ r1_subset_1(X1,X3)
                  | ~ r1_tarski(X2,X3)
                  | ~ v2_waybel_7(X3,sK3)
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK3)))
                  | ~ v13_waybel_0(X3,sK3)
                  | ~ v2_waybel_0(X3,sK3)
                  | v1_xboole_0(X3) )
              & r1_subset_1(X1,X2)
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK3)))
              & v13_waybel_0(X2,sK3)
              & v2_waybel_0(X2,sK3)
              & ~ v1_xboole_0(X2) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3)))
          & v12_waybel_0(X1,sK3)
          & v1_waybel_0(X1,sK3)
          & ~ v1_xboole_0(X1) )
      & l1_orders_2(sK3)
      & v2_lattice3(sK3)
      & v1_lattice3(sK3)
      & v2_waybel_1(sK3)
      & v5_orders_2(sK3)
      & v4_orders_2(sK3)
      & v3_orders_2(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f69,plain,
    ( ! [X3] :
        ( ~ r1_subset_1(sK4,X3)
        | ~ r1_tarski(sK5,X3)
        | ~ v2_waybel_7(X3,sK3)
        | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK3)))
        | ~ v13_waybel_0(X3,sK3)
        | ~ v2_waybel_0(X3,sK3)
        | v1_xboole_0(X3) )
    & r1_subset_1(sK4,sK5)
    & m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK3)))
    & v13_waybel_0(sK5,sK3)
    & v2_waybel_0(sK5,sK3)
    & ~ v1_xboole_0(sK5)
    & m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3)))
    & v12_waybel_0(sK4,sK3)
    & v1_waybel_0(sK4,sK3)
    & ~ v1_xboole_0(sK4)
    & l1_orders_2(sK3)
    & v2_lattice3(sK3)
    & v1_lattice3(sK3)
    & v2_waybel_1(sK3)
    & v5_orders_2(sK3)
    & v4_orders_2(sK3)
    & v3_orders_2(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5])],[f48,f68,f67,f66])).

fof(f130,plain,(
    ! [X3] :
      ( ~ r1_subset_1(sK4,X3)
      | ~ r1_tarski(sK5,X3)
      | ~ v2_waybel_7(X3,sK3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK3)))
      | ~ v13_waybel_0(X3,sK3)
      | ~ v2_waybel_0(X3,sK3)
      | v1_xboole_0(X3) ) ),
    inference(cnf_transformation,[],[f69])).

fof(f78,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | ~ sP0(X0,X1)
      | ~ sP1(X0) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f84,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | ~ sP0(X0,X1) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f88,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ sP0(X0,X1) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f86,plain,(
    ! [X0,X1] :
      ( v13_waybel_0(X1,X0)
      | ~ sP0(X0,X1) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f85,plain,(
    ! [X0,X1] :
      ( v2_waybel_0(X1,X0)
      | ~ sP0(X0,X1) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f125,plain,(
    ~ v1_xboole_0(sK5) ),
    inference(cnf_transformation,[],[f69])).

fof(f13,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & v12_waybel_0(X1,X0) )
        <=> ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k7_lattice3(X0))))
            & v13_waybel_0(X1,k7_lattice3(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f45,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & v12_waybel_0(X1,X0) )
        <=> ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k7_lattice3(X0))))
            & v13_waybel_0(X1,k7_lattice3(X0)) ) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f62,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
              & v12_waybel_0(X1,X0) )
            | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k7_lattice3(X0))))
            | ~ v13_waybel_0(X1,k7_lattice3(X0)) )
          & ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k7_lattice3(X0))))
              & v13_waybel_0(X1,k7_lattice3(X0)) )
            | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            | ~ v12_waybel_0(X1,X0) ) )
      | ~ l1_orders_2(X0) ) ),
    inference(nnf_transformation,[],[f45])).

fof(f63,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
              & v12_waybel_0(X1,X0) )
            | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k7_lattice3(X0))))
            | ~ v13_waybel_0(X1,k7_lattice3(X0)) )
          & ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k7_lattice3(X0))))
              & v13_waybel_0(X1,k7_lattice3(X0)) )
            | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            | ~ v12_waybel_0(X1,X0) ) )
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f62])).

fof(f106,plain,(
    ! [X0,X1] :
      ( v13_waybel_0(X1,k7_lattice3(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v12_waybel_0(X1,X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f63])).

fof(f10,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & v1_waybel_0(X1,X0) )
        <=> ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k7_lattice3(X0))))
            & v2_waybel_0(X1,k7_lattice3(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & v1_waybel_0(X1,X0) )
        <=> ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k7_lattice3(X0))))
            & v2_waybel_0(X1,k7_lattice3(X0)) ) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f56,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
              & v1_waybel_0(X1,X0) )
            | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k7_lattice3(X0))))
            | ~ v2_waybel_0(X1,k7_lattice3(X0)) )
          & ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k7_lattice3(X0))))
              & v2_waybel_0(X1,k7_lattice3(X0)) )
            | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            | ~ v1_waybel_0(X1,X0) ) )
      | ~ l1_orders_2(X0) ) ),
    inference(nnf_transformation,[],[f41])).

fof(f57,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
              & v1_waybel_0(X1,X0) )
            | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k7_lattice3(X0))))
            | ~ v2_waybel_0(X1,k7_lattice3(X0)) )
          & ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k7_lattice3(X0))))
              & v2_waybel_0(X1,k7_lattice3(X0)) )
            | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            | ~ v1_waybel_0(X1,X0) ) )
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f56])).

fof(f91,plain,(
    ! [X0,X1] :
      ( v2_waybel_0(X1,k7_lattice3(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v1_waybel_0(X1,X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f92,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k7_lattice3(X0))))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v1_waybel_0(X1,X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f12,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k7_lattice3(X0))))
            & v1_waybel_0(X1,k7_lattice3(X0)) )
        <=> ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & v2_waybel_0(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k7_lattice3(X0))))
            & v1_waybel_0(X1,k7_lattice3(X0)) )
        <=> ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & v2_waybel_0(X1,X0) ) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f60,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k7_lattice3(X0))))
              & v1_waybel_0(X1,k7_lattice3(X0)) )
            | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            | ~ v2_waybel_0(X1,X0) )
          & ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
              & v2_waybel_0(X1,X0) )
            | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k7_lattice3(X0))))
            | ~ v1_waybel_0(X1,k7_lattice3(X0)) ) )
      | ~ l1_orders_2(X0) ) ),
    inference(nnf_transformation,[],[f44])).

fof(f61,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k7_lattice3(X0))))
              & v1_waybel_0(X1,k7_lattice3(X0)) )
            | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            | ~ v2_waybel_0(X1,X0) )
          & ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
              & v2_waybel_0(X1,X0) )
            | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k7_lattice3(X0))))
            | ~ v1_waybel_0(X1,k7_lattice3(X0)) ) )
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f60])).

fof(f104,plain,(
    ! [X0,X1] :
      ( v1_waybel_0(X1,k7_lattice3(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v2_waybel_0(X1,X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f61])).

fof(f126,plain,(
    v2_waybel_0(sK5,sK3) ),
    inference(cnf_transformation,[],[f69])).

fof(f14,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k7_lattice3(X0))))
            & v12_waybel_0(X1,k7_lattice3(X0)) )
        <=> ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & v13_waybel_0(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f46,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k7_lattice3(X0))))
            & v12_waybel_0(X1,k7_lattice3(X0)) )
        <=> ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & v13_waybel_0(X1,X0) ) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f64,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k7_lattice3(X0))))
              & v12_waybel_0(X1,k7_lattice3(X0)) )
            | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            | ~ v13_waybel_0(X1,X0) )
          & ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
              & v13_waybel_0(X1,X0) )
            | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k7_lattice3(X0))))
            | ~ v12_waybel_0(X1,k7_lattice3(X0)) ) )
      | ~ l1_orders_2(X0) ) ),
    inference(nnf_transformation,[],[f46])).

fof(f65,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k7_lattice3(X0))))
              & v12_waybel_0(X1,k7_lattice3(X0)) )
            | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            | ~ v13_waybel_0(X1,X0) )
          & ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
              & v13_waybel_0(X1,X0) )
            | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k7_lattice3(X0))))
            | ~ v12_waybel_0(X1,k7_lattice3(X0)) ) )
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f64])).

fof(f113,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k7_lattice3(X0))))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v13_waybel_0(X1,X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f65])).

fof(f127,plain,(
    v13_waybel_0(sK5,sK3) ),
    inference(cnf_transformation,[],[f69])).

fof(f112,plain,(
    ! [X0,X1] :
      ( v12_waybel_0(X1,k7_lattice3(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v13_waybel_0(X1,X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f65])).

fof(f1,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ( l1_orders_2(k7_lattice3(X0))
        & v1_orders_2(k7_lattice3(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0] :
      ( l1_orders_2(X0)
     => l1_orders_2(k7_lattice3(X0)) ) ),
    inference(pure_predicate_removal,[],[f1])).

fof(f24,plain,(
    ! [X0] :
      ( l1_orders_2(k7_lattice3(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f70,plain,(
    ! [X0] :
      ( l1_orders_2(k7_lattice3(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f2,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v3_orders_2(X0) )
     => ( v3_orders_2(k7_lattice3(X0))
        & v1_orders_2(k7_lattice3(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v3_orders_2(X0) )
     => v3_orders_2(k7_lattice3(X0)) ) ),
    inference(pure_predicate_removal,[],[f2])).

fof(f25,plain,(
    ! [X0] :
      ( v3_orders_2(k7_lattice3(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f26,plain,(
    ! [X0] :
      ( v3_orders_2(k7_lattice3(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(flattening,[],[f25])).

fof(f71,plain,(
    ! [X0] :
      ( v3_orders_2(k7_lattice3(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f3,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v4_orders_2(X0) )
     => ( v4_orders_2(k7_lattice3(X0))
        & v1_orders_2(k7_lattice3(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v4_orders_2(X0) )
     => v4_orders_2(k7_lattice3(X0)) ) ),
    inference(pure_predicate_removal,[],[f3])).

fof(f27,plain,(
    ! [X0] :
      ( v4_orders_2(k7_lattice3(X0))
      | ~ l1_orders_2(X0)
      | ~ v4_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f28,plain,(
    ! [X0] :
      ( v4_orders_2(k7_lattice3(X0))
      | ~ l1_orders_2(X0)
      | ~ v4_orders_2(X0) ) ),
    inference(flattening,[],[f27])).

fof(f72,plain,(
    ! [X0] :
      ( v4_orders_2(k7_lattice3(X0))
      | ~ l1_orders_2(X0)
      | ~ v4_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f4,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0) )
     => ( v5_orders_2(k7_lattice3(X0))
        & v1_orders_2(k7_lattice3(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0) )
     => v5_orders_2(k7_lattice3(X0)) ) ),
    inference(pure_predicate_removal,[],[f4])).

fof(f29,plain,(
    ! [X0] :
      ( v5_orders_2(k7_lattice3(X0))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f30,plain,(
    ! [X0] :
      ( v5_orders_2(k7_lattice3(X0))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(flattening,[],[f29])).

fof(f73,plain,(
    ! [X0] :
      ( v5_orders_2(k7_lattice3(X0))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f5,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v2_lattice3(X0) )
     => ( v1_lattice3(k7_lattice3(X0))
        & v1_orders_2(k7_lattice3(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v2_lattice3(X0) )
     => v1_lattice3(k7_lattice3(X0)) ) ),
    inference(pure_predicate_removal,[],[f5])).

fof(f31,plain,(
    ! [X0] :
      ( v1_lattice3(k7_lattice3(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f32,plain,(
    ! [X0] :
      ( v1_lattice3(k7_lattice3(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0) ) ),
    inference(flattening,[],[f31])).

fof(f74,plain,(
    ! [X0] :
      ( v1_lattice3(k7_lattice3(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f6,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v1_lattice3(X0) )
     => ( v2_lattice3(k7_lattice3(X0))
        & v1_orders_2(k7_lattice3(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v1_lattice3(X0) )
     => v2_lattice3(k7_lattice3(X0)) ) ),
    inference(pure_predicate_removal,[],[f6])).

fof(f33,plain,(
    ! [X0] :
      ( v2_lattice3(k7_lattice3(X0))
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f34,plain,(
    ! [X0] :
      ( v2_lattice3(k7_lattice3(X0))
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0) ) ),
    inference(flattening,[],[f33])).

fof(f75,plain,(
    ! [X0] :
      ( v2_lattice3(k7_lattice3(X0))
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f7,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v2_waybel_1(X0)
        & v2_lattice3(X0)
        & v1_lattice3(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0) )
     => ( v2_waybel_1(k7_lattice3(X0))
        & v1_orders_2(k7_lattice3(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v2_waybel_1(X0)
        & v2_lattice3(X0)
        & v1_lattice3(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0) )
     => v2_waybel_1(k7_lattice3(X0)) ) ),
    inference(pure_predicate_removal,[],[f7])).

fof(f35,plain,(
    ! [X0] :
      ( v2_waybel_1(k7_lattice3(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_waybel_1(X0)
      | ~ v2_lattice3(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f36,plain,(
    ! [X0] :
      ( v2_waybel_1(k7_lattice3(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_waybel_1(X0)
      | ~ v2_lattice3(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(flattening,[],[f35])).

fof(f76,plain,(
    ! [X0] :
      ( v2_waybel_1(k7_lattice3(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_waybel_1(X0)
      | ~ v2_lattice3(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f9,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v2_lattice3(X0)
        & v1_lattice3(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0) )
     => ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & v2_waybel_7(X1,X0)
            & v13_waybel_0(X1,X0)
            & v2_waybel_0(X1,X0)
            & ~ v1_xboole_0(X1) )
        <=> ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k7_lattice3(X0))))
            & v1_waybel_7(X1,k7_lattice3(X0))
            & v12_waybel_0(X1,k7_lattice3(X0))
            & v1_waybel_0(X1,k7_lattice3(X0))
            & ~ v1_xboole_0(X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & v2_waybel_7(X1,X0)
            & v13_waybel_0(X1,X0)
            & v2_waybel_0(X1,X0)
            & ~ v1_xboole_0(X1) )
        <=> ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k7_lattice3(X0))))
            & v1_waybel_7(X1,k7_lattice3(X0))
            & v12_waybel_0(X1,k7_lattice3(X0))
            & v1_waybel_0(X1,k7_lattice3(X0))
            & ~ v1_xboole_0(X1) ) )
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f40,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & v2_waybel_7(X1,X0)
            & v13_waybel_0(X1,X0)
            & v2_waybel_0(X1,X0)
            & ~ v1_xboole_0(X1) )
        <=> ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k7_lattice3(X0))))
            & v1_waybel_7(X1,k7_lattice3(X0))
            & v12_waybel_0(X1,k7_lattice3(X0))
            & v1_waybel_0(X1,k7_lattice3(X0))
            & ~ v1_xboole_0(X1) ) )
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(flattening,[],[f39])).

fof(f51,plain,(
    ! [X0] :
      ( sP1(X0)
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(definition_folding,[],[f40,f50,f49])).

fof(f90,plain,(
    ! [X0] :
      ( sP1(X0)
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f129,plain,(
    r1_subset_1(sK4,sK5) ),
    inference(cnf_transformation,[],[f69])).

fof(f128,plain,(
    m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK3))) ),
    inference(cnf_transformation,[],[f69])).

fof(f124,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3))) ),
    inference(cnf_transformation,[],[f69])).

fof(f123,plain,(
    v12_waybel_0(sK4,sK3) ),
    inference(cnf_transformation,[],[f69])).

fof(f122,plain,(
    v1_waybel_0(sK4,sK3) ),
    inference(cnf_transformation,[],[f69])).

fof(f121,plain,(
    ~ v1_xboole_0(sK4) ),
    inference(cnf_transformation,[],[f69])).

fof(f120,plain,(
    l1_orders_2(sK3) ),
    inference(cnf_transformation,[],[f69])).

fof(f119,plain,(
    v2_lattice3(sK3) ),
    inference(cnf_transformation,[],[f69])).

fof(f118,plain,(
    v1_lattice3(sK3) ),
    inference(cnf_transformation,[],[f69])).

fof(f117,plain,(
    v2_waybel_1(sK3) ),
    inference(cnf_transformation,[],[f69])).

fof(f116,plain,(
    v5_orders_2(sK3) ),
    inference(cnf_transformation,[],[f69])).

fof(f115,plain,(
    v4_orders_2(sK3) ),
    inference(cnf_transformation,[],[f69])).

fof(f114,plain,(
    v3_orders_2(sK3) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_8,plain,
    ( ~ v1_waybel_0(X0,k7_lattice3(X1))
    | ~ v12_waybel_0(X0,k7_lattice3(X1))
    | ~ v1_waybel_7(X0,k7_lattice3(X1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k7_lattice3(X1))))
    | sP0(X1,X0)
    | ~ sP1(X1)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_11950,plain,
    ( ~ v1_waybel_0(X0_54,k7_lattice3(X0_55))
    | ~ v12_waybel_0(X0_54,k7_lattice3(X0_55))
    | ~ v1_waybel_7(X0_54,k7_lattice3(X0_55))
    | ~ m1_subset_1(X0_54,k1_zfmisc_1(u1_struct_0(k7_lattice3(X0_55))))
    | sP0(X0_55,X0_54)
    | ~ sP1(X0_55)
    | v1_xboole_0(X0_54) ),
    inference(subtyping,[status(esa)],[c_8])).

cnf(c_12610,plain,
    ( ~ v1_waybel_0(sK2(k7_lattice3(X0_55),sK5,sK4),k7_lattice3(X0_55))
    | ~ v12_waybel_0(sK2(k7_lattice3(X0_55),sK5,sK4),k7_lattice3(X0_55))
    | ~ v1_waybel_7(sK2(k7_lattice3(X0_55),sK5,sK4),k7_lattice3(X0_55))
    | ~ m1_subset_1(sK2(k7_lattice3(X0_55),sK5,sK4),k1_zfmisc_1(u1_struct_0(k7_lattice3(X0_55))))
    | sP0(X0_55,sK2(k7_lattice3(X0_55),sK5,sK4))
    | ~ sP1(X0_55)
    | v1_xboole_0(sK2(k7_lattice3(X0_55),sK5,sK4)) ),
    inference(instantiation,[status(thm)],[c_11950])).

cnf(c_12617,plain,
    ( ~ v1_waybel_0(sK2(k7_lattice3(sK3),sK5,sK4),k7_lattice3(sK3))
    | ~ v12_waybel_0(sK2(k7_lattice3(sK3),sK5,sK4),k7_lattice3(sK3))
    | ~ v1_waybel_7(sK2(k7_lattice3(sK3),sK5,sK4),k7_lattice3(sK3))
    | ~ m1_subset_1(sK2(k7_lattice3(sK3),sK5,sK4),k1_zfmisc_1(u1_struct_0(k7_lattice3(sK3))))
    | sP0(sK3,sK2(k7_lattice3(sK3),sK5,sK4))
    | ~ sP1(sK3)
    | v1_xboole_0(sK2(k7_lattice3(sK3),sK5,sK4)) ),
    inference(instantiation,[status(thm)],[c_12610])).

cnf(c_7,plain,
    ( ~ r1_subset_1(X0,X1)
    | r1_subset_1(X1,X0)
    | v1_xboole_0(X0)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_11951,plain,
    ( ~ r1_subset_1(X0_54,X1_54)
    | r1_subset_1(X1_54,X0_54)
    | v1_xboole_0(X0_54)
    | v1_xboole_0(X1_54) ),
    inference(subtyping,[status(esa)],[c_7])).

cnf(c_12605,plain,
    ( ~ r1_subset_1(sK2(k7_lattice3(X0_55),sK5,sK4),sK4)
    | r1_subset_1(sK4,sK2(k7_lattice3(X0_55),sK5,sK4))
    | v1_xboole_0(sK2(k7_lattice3(X0_55),sK5,sK4))
    | v1_xboole_0(sK4) ),
    inference(instantiation,[status(thm)],[c_11951])).

cnf(c_12607,plain,
    ( ~ r1_subset_1(sK2(k7_lattice3(sK3),sK5,sK4),sK4)
    | r1_subset_1(sK4,sK2(k7_lattice3(sK3),sK5,sK4))
    | v1_xboole_0(sK2(k7_lattice3(sK3),sK5,sK4))
    | v1_xboole_0(sK4) ),
    inference(instantiation,[status(thm)],[c_12605])).

cnf(c_25,plain,
    ( ~ v2_waybel_0(X0,X1)
    | ~ v13_waybel_0(X0,X1)
    | ~ v1_waybel_0(X2,X1)
    | ~ v12_waybel_0(X2,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_subset_1(X2,X0)
    | r1_subset_1(sK2(X1,X2,X0),X0)
    | v1_xboole_0(X2)
    | v1_xboole_0(X0)
    | ~ v2_waybel_1(X1)
    | ~ v2_lattice3(X1)
    | ~ v1_lattice3(X1)
    | ~ v5_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v3_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(cnf_transformation,[],[f101])).

cnf(c_11936,plain,
    ( ~ v2_waybel_0(X0_54,X0_55)
    | ~ v13_waybel_0(X0_54,X0_55)
    | ~ v1_waybel_0(X1_54,X0_55)
    | ~ v12_waybel_0(X1_54,X0_55)
    | ~ m1_subset_1(X0_54,k1_zfmisc_1(u1_struct_0(X0_55)))
    | ~ m1_subset_1(X1_54,k1_zfmisc_1(u1_struct_0(X0_55)))
    | ~ r1_subset_1(X1_54,X0_54)
    | r1_subset_1(sK2(X0_55,X1_54,X0_54),X0_54)
    | v1_xboole_0(X0_54)
    | v1_xboole_0(X1_54)
    | ~ v2_waybel_1(X0_55)
    | ~ v2_lattice3(X0_55)
    | ~ v1_lattice3(X0_55)
    | ~ v5_orders_2(X0_55)
    | ~ v4_orders_2(X0_55)
    | ~ v3_orders_2(X0_55)
    | ~ l1_orders_2(X0_55) ),
    inference(subtyping,[status(esa)],[c_25])).

cnf(c_12325,plain,
    ( ~ v2_waybel_0(X0_54,k7_lattice3(X0_55))
    | ~ v13_waybel_0(X0_54,k7_lattice3(X0_55))
    | ~ v1_waybel_0(X1_54,k7_lattice3(X0_55))
    | ~ v12_waybel_0(X1_54,k7_lattice3(X0_55))
    | ~ m1_subset_1(X0_54,k1_zfmisc_1(u1_struct_0(k7_lattice3(X0_55))))
    | ~ m1_subset_1(X1_54,k1_zfmisc_1(u1_struct_0(k7_lattice3(X0_55))))
    | ~ r1_subset_1(X1_54,X0_54)
    | r1_subset_1(sK2(k7_lattice3(X0_55),X1_54,X0_54),X0_54)
    | v1_xboole_0(X0_54)
    | v1_xboole_0(X1_54)
    | ~ v2_waybel_1(k7_lattice3(X0_55))
    | ~ v2_lattice3(k7_lattice3(X0_55))
    | ~ v1_lattice3(k7_lattice3(X0_55))
    | ~ v5_orders_2(k7_lattice3(X0_55))
    | ~ v4_orders_2(k7_lattice3(X0_55))
    | ~ v3_orders_2(k7_lattice3(X0_55))
    | ~ l1_orders_2(k7_lattice3(X0_55)) ),
    inference(instantiation,[status(thm)],[c_11936])).

cnf(c_12471,plain,
    ( ~ v2_waybel_0(sK4,k7_lattice3(X0_55))
    | ~ v13_waybel_0(sK4,k7_lattice3(X0_55))
    | ~ v1_waybel_0(sK5,k7_lattice3(X0_55))
    | ~ v12_waybel_0(sK5,k7_lattice3(X0_55))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(k7_lattice3(X0_55))))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(k7_lattice3(X0_55))))
    | r1_subset_1(sK2(k7_lattice3(X0_55),sK5,sK4),sK4)
    | ~ r1_subset_1(sK5,sK4)
    | v1_xboole_0(sK5)
    | v1_xboole_0(sK4)
    | ~ v2_waybel_1(k7_lattice3(X0_55))
    | ~ v2_lattice3(k7_lattice3(X0_55))
    | ~ v1_lattice3(k7_lattice3(X0_55))
    | ~ v5_orders_2(k7_lattice3(X0_55))
    | ~ v4_orders_2(k7_lattice3(X0_55))
    | ~ v3_orders_2(k7_lattice3(X0_55))
    | ~ l1_orders_2(k7_lattice3(X0_55)) ),
    inference(instantiation,[status(thm)],[c_12325])).

cnf(c_12473,plain,
    ( ~ v2_waybel_0(sK4,k7_lattice3(sK3))
    | ~ v13_waybel_0(sK4,k7_lattice3(sK3))
    | ~ v1_waybel_0(sK5,k7_lattice3(sK3))
    | ~ v12_waybel_0(sK5,k7_lattice3(sK3))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(k7_lattice3(sK3))))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(k7_lattice3(sK3))))
    | r1_subset_1(sK2(k7_lattice3(sK3),sK5,sK4),sK4)
    | ~ r1_subset_1(sK5,sK4)
    | v1_xboole_0(sK5)
    | v1_xboole_0(sK4)
    | ~ v2_waybel_1(k7_lattice3(sK3))
    | ~ v2_lattice3(k7_lattice3(sK3))
    | ~ v1_lattice3(k7_lattice3(sK3))
    | ~ v5_orders_2(k7_lattice3(sK3))
    | ~ v4_orders_2(k7_lattice3(sK3))
    | ~ v3_orders_2(k7_lattice3(sK3))
    | ~ l1_orders_2(k7_lattice3(sK3)) ),
    inference(instantiation,[status(thm)],[c_12471])).

cnf(c_27,plain,
    ( ~ v2_waybel_0(X0,X1)
    | ~ v13_waybel_0(X0,X1)
    | ~ v1_waybel_0(X2,X1)
    | ~ v12_waybel_0(X2,X1)
    | v1_waybel_7(sK2(X1,X2,X0),X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_subset_1(X2,X0)
    | v1_xboole_0(X2)
    | v1_xboole_0(X0)
    | ~ v2_waybel_1(X1)
    | ~ v2_lattice3(X1)
    | ~ v1_lattice3(X1)
    | ~ v5_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v3_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(cnf_transformation,[],[f99])).

cnf(c_11935,plain,
    ( ~ v2_waybel_0(X0_54,X0_55)
    | ~ v13_waybel_0(X0_54,X0_55)
    | ~ v1_waybel_0(X1_54,X0_55)
    | ~ v12_waybel_0(X1_54,X0_55)
    | v1_waybel_7(sK2(X0_55,X1_54,X0_54),X0_55)
    | ~ m1_subset_1(X0_54,k1_zfmisc_1(u1_struct_0(X0_55)))
    | ~ m1_subset_1(X1_54,k1_zfmisc_1(u1_struct_0(X0_55)))
    | ~ r1_subset_1(X1_54,X0_54)
    | v1_xboole_0(X0_54)
    | v1_xboole_0(X1_54)
    | ~ v2_waybel_1(X0_55)
    | ~ v2_lattice3(X0_55)
    | ~ v1_lattice3(X0_55)
    | ~ v5_orders_2(X0_55)
    | ~ v4_orders_2(X0_55)
    | ~ v3_orders_2(X0_55)
    | ~ l1_orders_2(X0_55) ),
    inference(subtyping,[status(esa)],[c_27])).

cnf(c_12315,plain,
    ( ~ v2_waybel_0(X0_54,k7_lattice3(X0_55))
    | ~ v13_waybel_0(X0_54,k7_lattice3(X0_55))
    | ~ v1_waybel_0(X1_54,k7_lattice3(X0_55))
    | ~ v12_waybel_0(X1_54,k7_lattice3(X0_55))
    | v1_waybel_7(sK2(k7_lattice3(X0_55),X1_54,X0_54),k7_lattice3(X0_55))
    | ~ m1_subset_1(X0_54,k1_zfmisc_1(u1_struct_0(k7_lattice3(X0_55))))
    | ~ m1_subset_1(X1_54,k1_zfmisc_1(u1_struct_0(k7_lattice3(X0_55))))
    | ~ r1_subset_1(X1_54,X0_54)
    | v1_xboole_0(X0_54)
    | v1_xboole_0(X1_54)
    | ~ v2_waybel_1(k7_lattice3(X0_55))
    | ~ v2_lattice3(k7_lattice3(X0_55))
    | ~ v1_lattice3(k7_lattice3(X0_55))
    | ~ v5_orders_2(k7_lattice3(X0_55))
    | ~ v4_orders_2(k7_lattice3(X0_55))
    | ~ v3_orders_2(k7_lattice3(X0_55))
    | ~ l1_orders_2(k7_lattice3(X0_55)) ),
    inference(instantiation,[status(thm)],[c_11935])).

cnf(c_12456,plain,
    ( ~ v2_waybel_0(sK4,k7_lattice3(X0_55))
    | ~ v13_waybel_0(sK4,k7_lattice3(X0_55))
    | ~ v1_waybel_0(sK5,k7_lattice3(X0_55))
    | ~ v12_waybel_0(sK5,k7_lattice3(X0_55))
    | v1_waybel_7(sK2(k7_lattice3(X0_55),sK5,sK4),k7_lattice3(X0_55))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(k7_lattice3(X0_55))))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(k7_lattice3(X0_55))))
    | ~ r1_subset_1(sK5,sK4)
    | v1_xboole_0(sK5)
    | v1_xboole_0(sK4)
    | ~ v2_waybel_1(k7_lattice3(X0_55))
    | ~ v2_lattice3(k7_lattice3(X0_55))
    | ~ v1_lattice3(k7_lattice3(X0_55))
    | ~ v5_orders_2(k7_lattice3(X0_55))
    | ~ v4_orders_2(k7_lattice3(X0_55))
    | ~ v3_orders_2(k7_lattice3(X0_55))
    | ~ l1_orders_2(k7_lattice3(X0_55)) ),
    inference(instantiation,[status(thm)],[c_12315])).

cnf(c_12458,plain,
    ( ~ v2_waybel_0(sK4,k7_lattice3(sK3))
    | ~ v13_waybel_0(sK4,k7_lattice3(sK3))
    | ~ v1_waybel_0(sK5,k7_lattice3(sK3))
    | ~ v12_waybel_0(sK5,k7_lattice3(sK3))
    | v1_waybel_7(sK2(k7_lattice3(sK3),sK5,sK4),k7_lattice3(sK3))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(k7_lattice3(sK3))))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(k7_lattice3(sK3))))
    | ~ r1_subset_1(sK5,sK4)
    | v1_xboole_0(sK5)
    | v1_xboole_0(sK4)
    | ~ v2_waybel_1(k7_lattice3(sK3))
    | ~ v2_lattice3(k7_lattice3(sK3))
    | ~ v1_lattice3(k7_lattice3(sK3))
    | ~ v5_orders_2(k7_lattice3(sK3))
    | ~ v4_orders_2(k7_lattice3(sK3))
    | ~ v3_orders_2(k7_lattice3(sK3))
    | ~ l1_orders_2(k7_lattice3(sK3)) ),
    inference(instantiation,[status(thm)],[c_12456])).

cnf(c_28,plain,
    ( ~ v2_waybel_0(X0,X1)
    | ~ v13_waybel_0(X0,X1)
    | ~ v1_waybel_0(X2,X1)
    | ~ v12_waybel_0(X2,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(sK2(X1,X2,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_subset_1(X2,X0)
    | v1_xboole_0(X2)
    | v1_xboole_0(X0)
    | ~ v2_waybel_1(X1)
    | ~ v2_lattice3(X1)
    | ~ v1_lattice3(X1)
    | ~ v5_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v3_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(cnf_transformation,[],[f98])).

cnf(c_11934,plain,
    ( ~ v2_waybel_0(X0_54,X0_55)
    | ~ v13_waybel_0(X0_54,X0_55)
    | ~ v1_waybel_0(X1_54,X0_55)
    | ~ v12_waybel_0(X1_54,X0_55)
    | ~ m1_subset_1(X0_54,k1_zfmisc_1(u1_struct_0(X0_55)))
    | ~ m1_subset_1(X1_54,k1_zfmisc_1(u1_struct_0(X0_55)))
    | m1_subset_1(sK2(X0_55,X1_54,X0_54),k1_zfmisc_1(u1_struct_0(X0_55)))
    | ~ r1_subset_1(X1_54,X0_54)
    | v1_xboole_0(X0_54)
    | v1_xboole_0(X1_54)
    | ~ v2_waybel_1(X0_55)
    | ~ v2_lattice3(X0_55)
    | ~ v1_lattice3(X0_55)
    | ~ v5_orders_2(X0_55)
    | ~ v4_orders_2(X0_55)
    | ~ v3_orders_2(X0_55)
    | ~ l1_orders_2(X0_55) ),
    inference(subtyping,[status(esa)],[c_28])).

cnf(c_12305,plain,
    ( ~ v2_waybel_0(X0_54,k7_lattice3(X0_55))
    | ~ v13_waybel_0(X0_54,k7_lattice3(X0_55))
    | ~ v1_waybel_0(X1_54,k7_lattice3(X0_55))
    | ~ v12_waybel_0(X1_54,k7_lattice3(X0_55))
    | ~ m1_subset_1(X0_54,k1_zfmisc_1(u1_struct_0(k7_lattice3(X0_55))))
    | ~ m1_subset_1(X1_54,k1_zfmisc_1(u1_struct_0(k7_lattice3(X0_55))))
    | m1_subset_1(sK2(k7_lattice3(X0_55),X1_54,X0_54),k1_zfmisc_1(u1_struct_0(k7_lattice3(X0_55))))
    | ~ r1_subset_1(X1_54,X0_54)
    | v1_xboole_0(X0_54)
    | v1_xboole_0(X1_54)
    | ~ v2_waybel_1(k7_lattice3(X0_55))
    | ~ v2_lattice3(k7_lattice3(X0_55))
    | ~ v1_lattice3(k7_lattice3(X0_55))
    | ~ v5_orders_2(k7_lattice3(X0_55))
    | ~ v4_orders_2(k7_lattice3(X0_55))
    | ~ v3_orders_2(k7_lattice3(X0_55))
    | ~ l1_orders_2(k7_lattice3(X0_55)) ),
    inference(instantiation,[status(thm)],[c_11934])).

cnf(c_12441,plain,
    ( ~ v2_waybel_0(sK4,k7_lattice3(X0_55))
    | ~ v13_waybel_0(sK4,k7_lattice3(X0_55))
    | ~ v1_waybel_0(sK5,k7_lattice3(X0_55))
    | ~ v12_waybel_0(sK5,k7_lattice3(X0_55))
    | m1_subset_1(sK2(k7_lattice3(X0_55),sK5,sK4),k1_zfmisc_1(u1_struct_0(k7_lattice3(X0_55))))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(k7_lattice3(X0_55))))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(k7_lattice3(X0_55))))
    | ~ r1_subset_1(sK5,sK4)
    | v1_xboole_0(sK5)
    | v1_xboole_0(sK4)
    | ~ v2_waybel_1(k7_lattice3(X0_55))
    | ~ v2_lattice3(k7_lattice3(X0_55))
    | ~ v1_lattice3(k7_lattice3(X0_55))
    | ~ v5_orders_2(k7_lattice3(X0_55))
    | ~ v4_orders_2(k7_lattice3(X0_55))
    | ~ v3_orders_2(k7_lattice3(X0_55))
    | ~ l1_orders_2(k7_lattice3(X0_55)) ),
    inference(instantiation,[status(thm)],[c_12305])).

cnf(c_12443,plain,
    ( ~ v2_waybel_0(sK4,k7_lattice3(sK3))
    | ~ v13_waybel_0(sK4,k7_lattice3(sK3))
    | ~ v1_waybel_0(sK5,k7_lattice3(sK3))
    | ~ v12_waybel_0(sK5,k7_lattice3(sK3))
    | m1_subset_1(sK2(k7_lattice3(sK3),sK5,sK4),k1_zfmisc_1(u1_struct_0(k7_lattice3(sK3))))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(k7_lattice3(sK3))))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(k7_lattice3(sK3))))
    | ~ r1_subset_1(sK5,sK4)
    | v1_xboole_0(sK5)
    | v1_xboole_0(sK4)
    | ~ v2_waybel_1(k7_lattice3(sK3))
    | ~ v2_lattice3(k7_lattice3(sK3))
    | ~ v1_lattice3(k7_lattice3(sK3))
    | ~ v5_orders_2(k7_lattice3(sK3))
    | ~ v4_orders_2(k7_lattice3(sK3))
    | ~ v3_orders_2(k7_lattice3(sK3))
    | ~ l1_orders_2(k7_lattice3(sK3)) ),
    inference(instantiation,[status(thm)],[c_12441])).

cnf(c_29,plain,
    ( ~ v2_waybel_0(X0,X1)
    | ~ v13_waybel_0(X0,X1)
    | ~ v1_waybel_0(X2,X1)
    | ~ v12_waybel_0(X2,X1)
    | v12_waybel_0(sK2(X1,X2,X0),X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_subset_1(X2,X0)
    | v1_xboole_0(X2)
    | v1_xboole_0(X0)
    | ~ v2_waybel_1(X1)
    | ~ v2_lattice3(X1)
    | ~ v1_lattice3(X1)
    | ~ v5_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v3_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(cnf_transformation,[],[f97])).

cnf(c_11933,plain,
    ( ~ v2_waybel_0(X0_54,X0_55)
    | ~ v13_waybel_0(X0_54,X0_55)
    | ~ v1_waybel_0(X1_54,X0_55)
    | ~ v12_waybel_0(X1_54,X0_55)
    | v12_waybel_0(sK2(X0_55,X1_54,X0_54),X0_55)
    | ~ m1_subset_1(X0_54,k1_zfmisc_1(u1_struct_0(X0_55)))
    | ~ m1_subset_1(X1_54,k1_zfmisc_1(u1_struct_0(X0_55)))
    | ~ r1_subset_1(X1_54,X0_54)
    | v1_xboole_0(X0_54)
    | v1_xboole_0(X1_54)
    | ~ v2_waybel_1(X0_55)
    | ~ v2_lattice3(X0_55)
    | ~ v1_lattice3(X0_55)
    | ~ v5_orders_2(X0_55)
    | ~ v4_orders_2(X0_55)
    | ~ v3_orders_2(X0_55)
    | ~ l1_orders_2(X0_55) ),
    inference(subtyping,[status(esa)],[c_29])).

cnf(c_12295,plain,
    ( ~ v2_waybel_0(X0_54,k7_lattice3(X0_55))
    | ~ v13_waybel_0(X0_54,k7_lattice3(X0_55))
    | ~ v1_waybel_0(X1_54,k7_lattice3(X0_55))
    | ~ v12_waybel_0(X1_54,k7_lattice3(X0_55))
    | v12_waybel_0(sK2(k7_lattice3(X0_55),X1_54,X0_54),k7_lattice3(X0_55))
    | ~ m1_subset_1(X0_54,k1_zfmisc_1(u1_struct_0(k7_lattice3(X0_55))))
    | ~ m1_subset_1(X1_54,k1_zfmisc_1(u1_struct_0(k7_lattice3(X0_55))))
    | ~ r1_subset_1(X1_54,X0_54)
    | v1_xboole_0(X0_54)
    | v1_xboole_0(X1_54)
    | ~ v2_waybel_1(k7_lattice3(X0_55))
    | ~ v2_lattice3(k7_lattice3(X0_55))
    | ~ v1_lattice3(k7_lattice3(X0_55))
    | ~ v5_orders_2(k7_lattice3(X0_55))
    | ~ v4_orders_2(k7_lattice3(X0_55))
    | ~ v3_orders_2(k7_lattice3(X0_55))
    | ~ l1_orders_2(k7_lattice3(X0_55)) ),
    inference(instantiation,[status(thm)],[c_11933])).

cnf(c_12426,plain,
    ( ~ v2_waybel_0(sK4,k7_lattice3(X0_55))
    | ~ v13_waybel_0(sK4,k7_lattice3(X0_55))
    | ~ v1_waybel_0(sK5,k7_lattice3(X0_55))
    | v12_waybel_0(sK2(k7_lattice3(X0_55),sK5,sK4),k7_lattice3(X0_55))
    | ~ v12_waybel_0(sK5,k7_lattice3(X0_55))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(k7_lattice3(X0_55))))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(k7_lattice3(X0_55))))
    | ~ r1_subset_1(sK5,sK4)
    | v1_xboole_0(sK5)
    | v1_xboole_0(sK4)
    | ~ v2_waybel_1(k7_lattice3(X0_55))
    | ~ v2_lattice3(k7_lattice3(X0_55))
    | ~ v1_lattice3(k7_lattice3(X0_55))
    | ~ v5_orders_2(k7_lattice3(X0_55))
    | ~ v4_orders_2(k7_lattice3(X0_55))
    | ~ v3_orders_2(k7_lattice3(X0_55))
    | ~ l1_orders_2(k7_lattice3(X0_55)) ),
    inference(instantiation,[status(thm)],[c_12295])).

cnf(c_12428,plain,
    ( ~ v2_waybel_0(sK4,k7_lattice3(sK3))
    | ~ v13_waybel_0(sK4,k7_lattice3(sK3))
    | ~ v1_waybel_0(sK5,k7_lattice3(sK3))
    | v12_waybel_0(sK2(k7_lattice3(sK3),sK5,sK4),k7_lattice3(sK3))
    | ~ v12_waybel_0(sK5,k7_lattice3(sK3))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(k7_lattice3(sK3))))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(k7_lattice3(sK3))))
    | ~ r1_subset_1(sK5,sK4)
    | v1_xboole_0(sK5)
    | v1_xboole_0(sK4)
    | ~ v2_waybel_1(k7_lattice3(sK3))
    | ~ v2_lattice3(k7_lattice3(sK3))
    | ~ v1_lattice3(k7_lattice3(sK3))
    | ~ v5_orders_2(k7_lattice3(sK3))
    | ~ v4_orders_2(k7_lattice3(sK3))
    | ~ v3_orders_2(k7_lattice3(sK3))
    | ~ l1_orders_2(k7_lattice3(sK3)) ),
    inference(instantiation,[status(thm)],[c_12426])).

cnf(c_30,plain,
    ( ~ v2_waybel_0(X0,X1)
    | ~ v13_waybel_0(X0,X1)
    | ~ v1_waybel_0(X2,X1)
    | v1_waybel_0(sK2(X1,X2,X0),X1)
    | ~ v12_waybel_0(X2,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_subset_1(X2,X0)
    | v1_xboole_0(X2)
    | v1_xboole_0(X0)
    | ~ v2_waybel_1(X1)
    | ~ v2_lattice3(X1)
    | ~ v1_lattice3(X1)
    | ~ v5_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v3_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(cnf_transformation,[],[f96])).

cnf(c_11932,plain,
    ( ~ v2_waybel_0(X0_54,X0_55)
    | ~ v13_waybel_0(X0_54,X0_55)
    | ~ v1_waybel_0(X1_54,X0_55)
    | v1_waybel_0(sK2(X0_55,X1_54,X0_54),X0_55)
    | ~ v12_waybel_0(X1_54,X0_55)
    | ~ m1_subset_1(X0_54,k1_zfmisc_1(u1_struct_0(X0_55)))
    | ~ m1_subset_1(X1_54,k1_zfmisc_1(u1_struct_0(X0_55)))
    | ~ r1_subset_1(X1_54,X0_54)
    | v1_xboole_0(X0_54)
    | v1_xboole_0(X1_54)
    | ~ v2_waybel_1(X0_55)
    | ~ v2_lattice3(X0_55)
    | ~ v1_lattice3(X0_55)
    | ~ v5_orders_2(X0_55)
    | ~ v4_orders_2(X0_55)
    | ~ v3_orders_2(X0_55)
    | ~ l1_orders_2(X0_55) ),
    inference(subtyping,[status(esa)],[c_30])).

cnf(c_12285,plain,
    ( ~ v2_waybel_0(X0_54,k7_lattice3(X0_55))
    | ~ v13_waybel_0(X0_54,k7_lattice3(X0_55))
    | ~ v1_waybel_0(X1_54,k7_lattice3(X0_55))
    | v1_waybel_0(sK2(k7_lattice3(X0_55),X1_54,X0_54),k7_lattice3(X0_55))
    | ~ v12_waybel_0(X1_54,k7_lattice3(X0_55))
    | ~ m1_subset_1(X0_54,k1_zfmisc_1(u1_struct_0(k7_lattice3(X0_55))))
    | ~ m1_subset_1(X1_54,k1_zfmisc_1(u1_struct_0(k7_lattice3(X0_55))))
    | ~ r1_subset_1(X1_54,X0_54)
    | v1_xboole_0(X0_54)
    | v1_xboole_0(X1_54)
    | ~ v2_waybel_1(k7_lattice3(X0_55))
    | ~ v2_lattice3(k7_lattice3(X0_55))
    | ~ v1_lattice3(k7_lattice3(X0_55))
    | ~ v5_orders_2(k7_lattice3(X0_55))
    | ~ v4_orders_2(k7_lattice3(X0_55))
    | ~ v3_orders_2(k7_lattice3(X0_55))
    | ~ l1_orders_2(k7_lattice3(X0_55)) ),
    inference(instantiation,[status(thm)],[c_11932])).

cnf(c_12411,plain,
    ( ~ v2_waybel_0(sK4,k7_lattice3(X0_55))
    | ~ v13_waybel_0(sK4,k7_lattice3(X0_55))
    | v1_waybel_0(sK2(k7_lattice3(X0_55),sK5,sK4),k7_lattice3(X0_55))
    | ~ v1_waybel_0(sK5,k7_lattice3(X0_55))
    | ~ v12_waybel_0(sK5,k7_lattice3(X0_55))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(k7_lattice3(X0_55))))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(k7_lattice3(X0_55))))
    | ~ r1_subset_1(sK5,sK4)
    | v1_xboole_0(sK5)
    | v1_xboole_0(sK4)
    | ~ v2_waybel_1(k7_lattice3(X0_55))
    | ~ v2_lattice3(k7_lattice3(X0_55))
    | ~ v1_lattice3(k7_lattice3(X0_55))
    | ~ v5_orders_2(k7_lattice3(X0_55))
    | ~ v4_orders_2(k7_lattice3(X0_55))
    | ~ v3_orders_2(k7_lattice3(X0_55))
    | ~ l1_orders_2(k7_lattice3(X0_55)) ),
    inference(instantiation,[status(thm)],[c_12285])).

cnf(c_12413,plain,
    ( ~ v2_waybel_0(sK4,k7_lattice3(sK3))
    | ~ v13_waybel_0(sK4,k7_lattice3(sK3))
    | v1_waybel_0(sK2(k7_lattice3(sK3),sK5,sK4),k7_lattice3(sK3))
    | ~ v1_waybel_0(sK5,k7_lattice3(sK3))
    | ~ v12_waybel_0(sK5,k7_lattice3(sK3))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(k7_lattice3(sK3))))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(k7_lattice3(sK3))))
    | ~ r1_subset_1(sK5,sK4)
    | v1_xboole_0(sK5)
    | v1_xboole_0(sK4)
    | ~ v2_waybel_1(k7_lattice3(sK3))
    | ~ v2_lattice3(k7_lattice3(sK3))
    | ~ v1_lattice3(k7_lattice3(sK3))
    | ~ v5_orders_2(k7_lattice3(sK3))
    | ~ v4_orders_2(k7_lattice3(sK3))
    | ~ v3_orders_2(k7_lattice3(sK3))
    | ~ l1_orders_2(k7_lattice3(sK3)) ),
    inference(instantiation,[status(thm)],[c_12411])).

cnf(c_31,plain,
    ( ~ v2_waybel_0(X0,X1)
    | ~ v13_waybel_0(X0,X1)
    | ~ v1_waybel_0(X2,X1)
    | ~ v12_waybel_0(X2,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_subset_1(X2,X0)
    | v1_xboole_0(X2)
    | v1_xboole_0(X0)
    | ~ v1_xboole_0(sK2(X1,X2,X0))
    | ~ v2_waybel_1(X1)
    | ~ v2_lattice3(X1)
    | ~ v1_lattice3(X1)
    | ~ v5_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v3_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(cnf_transformation,[],[f95])).

cnf(c_11931,plain,
    ( ~ v2_waybel_0(X0_54,X0_55)
    | ~ v13_waybel_0(X0_54,X0_55)
    | ~ v1_waybel_0(X1_54,X0_55)
    | ~ v12_waybel_0(X1_54,X0_55)
    | ~ m1_subset_1(X0_54,k1_zfmisc_1(u1_struct_0(X0_55)))
    | ~ m1_subset_1(X1_54,k1_zfmisc_1(u1_struct_0(X0_55)))
    | ~ r1_subset_1(X1_54,X0_54)
    | v1_xboole_0(X0_54)
    | v1_xboole_0(X1_54)
    | ~ v1_xboole_0(sK2(X0_55,X1_54,X0_54))
    | ~ v2_waybel_1(X0_55)
    | ~ v2_lattice3(X0_55)
    | ~ v1_lattice3(X0_55)
    | ~ v5_orders_2(X0_55)
    | ~ v4_orders_2(X0_55)
    | ~ v3_orders_2(X0_55)
    | ~ l1_orders_2(X0_55) ),
    inference(subtyping,[status(esa)],[c_31])).

cnf(c_12275,plain,
    ( ~ v2_waybel_0(X0_54,k7_lattice3(X0_55))
    | ~ v13_waybel_0(X0_54,k7_lattice3(X0_55))
    | ~ v1_waybel_0(X1_54,k7_lattice3(X0_55))
    | ~ v12_waybel_0(X1_54,k7_lattice3(X0_55))
    | ~ m1_subset_1(X0_54,k1_zfmisc_1(u1_struct_0(k7_lattice3(X0_55))))
    | ~ m1_subset_1(X1_54,k1_zfmisc_1(u1_struct_0(k7_lattice3(X0_55))))
    | ~ r1_subset_1(X1_54,X0_54)
    | v1_xboole_0(X0_54)
    | v1_xboole_0(X1_54)
    | ~ v1_xboole_0(sK2(k7_lattice3(X0_55),X1_54,X0_54))
    | ~ v2_waybel_1(k7_lattice3(X0_55))
    | ~ v2_lattice3(k7_lattice3(X0_55))
    | ~ v1_lattice3(k7_lattice3(X0_55))
    | ~ v5_orders_2(k7_lattice3(X0_55))
    | ~ v4_orders_2(k7_lattice3(X0_55))
    | ~ v3_orders_2(k7_lattice3(X0_55))
    | ~ l1_orders_2(k7_lattice3(X0_55)) ),
    inference(instantiation,[status(thm)],[c_11931])).

cnf(c_12396,plain,
    ( ~ v2_waybel_0(sK4,k7_lattice3(X0_55))
    | ~ v13_waybel_0(sK4,k7_lattice3(X0_55))
    | ~ v1_waybel_0(sK5,k7_lattice3(X0_55))
    | ~ v12_waybel_0(sK5,k7_lattice3(X0_55))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(k7_lattice3(X0_55))))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(k7_lattice3(X0_55))))
    | ~ r1_subset_1(sK5,sK4)
    | ~ v1_xboole_0(sK2(k7_lattice3(X0_55),sK5,sK4))
    | v1_xboole_0(sK5)
    | v1_xboole_0(sK4)
    | ~ v2_waybel_1(k7_lattice3(X0_55))
    | ~ v2_lattice3(k7_lattice3(X0_55))
    | ~ v1_lattice3(k7_lattice3(X0_55))
    | ~ v5_orders_2(k7_lattice3(X0_55))
    | ~ v4_orders_2(k7_lattice3(X0_55))
    | ~ v3_orders_2(k7_lattice3(X0_55))
    | ~ l1_orders_2(k7_lattice3(X0_55)) ),
    inference(instantiation,[status(thm)],[c_12275])).

cnf(c_12398,plain,
    ( ~ v2_waybel_0(sK4,k7_lattice3(sK3))
    | ~ v13_waybel_0(sK4,k7_lattice3(sK3))
    | ~ v1_waybel_0(sK5,k7_lattice3(sK3))
    | ~ v12_waybel_0(sK5,k7_lattice3(sK3))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(k7_lattice3(sK3))))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(k7_lattice3(sK3))))
    | ~ r1_subset_1(sK5,sK4)
    | ~ v1_xboole_0(sK2(k7_lattice3(sK3),sK5,sK4))
    | v1_xboole_0(sK5)
    | v1_xboole_0(sK4)
    | ~ v2_waybel_1(k7_lattice3(sK3))
    | ~ v2_lattice3(k7_lattice3(sK3))
    | ~ v1_lattice3(k7_lattice3(sK3))
    | ~ v5_orders_2(k7_lattice3(sK3))
    | ~ v4_orders_2(k7_lattice3(sK3))
    | ~ v3_orders_2(k7_lattice3(sK3))
    | ~ l1_orders_2(k7_lattice3(sK3)) ),
    inference(instantiation,[status(thm)],[c_12396])).

cnf(c_26,plain,
    ( r1_tarski(X0,sK2(X1,X0,X2))
    | ~ v2_waybel_0(X2,X1)
    | ~ v13_waybel_0(X2,X1)
    | ~ v1_waybel_0(X0,X1)
    | ~ v12_waybel_0(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_subset_1(X0,X2)
    | v1_xboole_0(X0)
    | v1_xboole_0(X2)
    | ~ v2_waybel_1(X1)
    | ~ v2_lattice3(X1)
    | ~ v1_lattice3(X1)
    | ~ v5_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v3_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(cnf_transformation,[],[f100])).

cnf(c_16,plain,
    ( v2_waybel_7(X0,X1)
    | ~ sP0(X1,X0) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_44,negated_conjecture,
    ( ~ r1_tarski(sK5,X0)
    | ~ v2_waybel_0(X0,sK3)
    | ~ v13_waybel_0(X0,sK3)
    | ~ v2_waybel_7(X0,sK3)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ r1_subset_1(sK4,X0)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f130])).

cnf(c_644,plain,
    ( ~ r1_tarski(sK5,X0)
    | ~ v2_waybel_0(X0,sK3)
    | ~ v13_waybel_0(X0,sK3)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ sP0(sK3,X0)
    | ~ r1_subset_1(sK4,X0)
    | v1_xboole_0(X0) ),
    inference(resolution,[status(thm)],[c_16,c_44])).

cnf(c_13,plain,
    ( ~ sP0(X0,X1)
    | ~ sP1(X0)
    | ~ v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_19,plain,
    ( ~ sP0(X0,X1)
    | ~ v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_380,plain,
    ( ~ sP0(X0,X1)
    | ~ v1_xboole_0(X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_13,c_19])).

cnf(c_15,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ sP0(X1,X0) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_17,plain,
    ( v13_waybel_0(X0,X1)
    | ~ sP0(X1,X0) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_18,plain,
    ( v2_waybel_0(X0,X1)
    | ~ sP0(X1,X0) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_662,plain,
    ( ~ r1_tarski(sK5,X0)
    | ~ sP0(sK3,X0)
    | ~ r1_subset_1(sK4,X0) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_644,c_380,c_15,c_17,c_18])).

cnf(c_673,plain,
    ( ~ v2_waybel_0(X0,X1)
    | ~ v13_waybel_0(X0,X1)
    | ~ v1_waybel_0(sK5,X1)
    | ~ v12_waybel_0(sK5,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ sP0(sK3,sK2(X1,sK5,X0))
    | ~ r1_subset_1(sK5,X0)
    | ~ r1_subset_1(sK4,sK2(X1,sK5,X0))
    | v1_xboole_0(X0)
    | v1_xboole_0(sK5)
    | ~ v2_waybel_1(X1)
    | ~ v2_lattice3(X1)
    | ~ v1_lattice3(X1)
    | ~ v5_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v3_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(resolution,[status(thm)],[c_26,c_662])).

cnf(c_49,negated_conjecture,
    ( ~ v1_xboole_0(sK5) ),
    inference(cnf_transformation,[],[f125])).

cnf(c_677,plain,
    ( v1_xboole_0(X0)
    | ~ r1_subset_1(sK4,sK2(X1,sK5,X0))
    | ~ r1_subset_1(sK5,X0)
    | ~ sP0(sK3,sK2(X1,sK5,X0))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v12_waybel_0(sK5,X1)
    | ~ v1_waybel_0(sK5,X1)
    | ~ v13_waybel_0(X0,X1)
    | ~ v2_waybel_0(X0,X1)
    | ~ v2_waybel_1(X1)
    | ~ v2_lattice3(X1)
    | ~ v1_lattice3(X1)
    | ~ v5_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v3_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_673,c_49])).

cnf(c_678,plain,
    ( ~ v2_waybel_0(X0,X1)
    | ~ v13_waybel_0(X0,X1)
    | ~ v1_waybel_0(sK5,X1)
    | ~ v12_waybel_0(sK5,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ sP0(sK3,sK2(X1,sK5,X0))
    | ~ r1_subset_1(sK5,X0)
    | ~ r1_subset_1(sK4,sK2(X1,sK5,X0))
    | v1_xboole_0(X0)
    | ~ v2_waybel_1(X1)
    | ~ v2_lattice3(X1)
    | ~ v1_lattice3(X1)
    | ~ v5_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v3_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(renaming,[status(thm)],[c_677])).

cnf(c_11902,plain,
    ( ~ v2_waybel_0(X0_54,X0_55)
    | ~ v13_waybel_0(X0_54,X0_55)
    | ~ v1_waybel_0(sK5,X0_55)
    | ~ v12_waybel_0(sK5,X0_55)
    | ~ m1_subset_1(X0_54,k1_zfmisc_1(u1_struct_0(X0_55)))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(X0_55)))
    | ~ sP0(sK3,sK2(X0_55,sK5,X0_54))
    | ~ r1_subset_1(sK5,X0_54)
    | ~ r1_subset_1(sK4,sK2(X0_55,sK5,X0_54))
    | v1_xboole_0(X0_54)
    | ~ v2_waybel_1(X0_55)
    | ~ v2_lattice3(X0_55)
    | ~ v1_lattice3(X0_55)
    | ~ v5_orders_2(X0_55)
    | ~ v4_orders_2(X0_55)
    | ~ v3_orders_2(X0_55)
    | ~ l1_orders_2(X0_55) ),
    inference(subtyping,[status(esa)],[c_678])).

cnf(c_12332,plain,
    ( ~ v2_waybel_0(X0_54,k7_lattice3(sK3))
    | ~ v13_waybel_0(X0_54,k7_lattice3(sK3))
    | ~ v1_waybel_0(sK5,k7_lattice3(sK3))
    | ~ v12_waybel_0(sK5,k7_lattice3(sK3))
    | ~ m1_subset_1(X0_54,k1_zfmisc_1(u1_struct_0(k7_lattice3(sK3))))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(k7_lattice3(sK3))))
    | ~ sP0(sK3,sK2(k7_lattice3(sK3),sK5,X0_54))
    | ~ r1_subset_1(sK5,X0_54)
    | ~ r1_subset_1(sK4,sK2(k7_lattice3(sK3),sK5,X0_54))
    | v1_xboole_0(X0_54)
    | ~ v2_waybel_1(k7_lattice3(sK3))
    | ~ v2_lattice3(k7_lattice3(sK3))
    | ~ v1_lattice3(k7_lattice3(sK3))
    | ~ v5_orders_2(k7_lattice3(sK3))
    | ~ v4_orders_2(k7_lattice3(sK3))
    | ~ v3_orders_2(k7_lattice3(sK3))
    | ~ l1_orders_2(k7_lattice3(sK3)) ),
    inference(instantiation,[status(thm)],[c_11902])).

cnf(c_12334,plain,
    ( ~ v2_waybel_0(sK4,k7_lattice3(sK3))
    | ~ v13_waybel_0(sK4,k7_lattice3(sK3))
    | ~ v1_waybel_0(sK5,k7_lattice3(sK3))
    | ~ v12_waybel_0(sK5,k7_lattice3(sK3))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(k7_lattice3(sK3))))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(k7_lattice3(sK3))))
    | ~ sP0(sK3,sK2(k7_lattice3(sK3),sK5,sK4))
    | ~ r1_subset_1(sK5,sK4)
    | ~ r1_subset_1(sK4,sK2(k7_lattice3(sK3),sK5,sK4))
    | v1_xboole_0(sK4)
    | ~ v2_waybel_1(k7_lattice3(sK3))
    | ~ v2_lattice3(k7_lattice3(sK3))
    | ~ v1_lattice3(k7_lattice3(sK3))
    | ~ v5_orders_2(k7_lattice3(sK3))
    | ~ v4_orders_2(k7_lattice3(sK3))
    | ~ v3_orders_2(k7_lattice3(sK3))
    | ~ l1_orders_2(k7_lattice3(sK3)) ),
    inference(instantiation,[status(thm)],[c_12332])).

cnf(c_12235,plain,
    ( r1_subset_1(sK5,sK4)
    | ~ r1_subset_1(sK4,sK5)
    | v1_xboole_0(sK5)
    | v1_xboole_0(sK4) ),
    inference(instantiation,[status(thm)],[c_11951])).

cnf(c_39,plain,
    ( v13_waybel_0(X0,k7_lattice3(X1))
    | ~ v12_waybel_0(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_orders_2(X1) ),
    inference(cnf_transformation,[],[f106])).

cnf(c_11923,plain,
    ( v13_waybel_0(X0_54,k7_lattice3(X0_55))
    | ~ v12_waybel_0(X0_54,X0_55)
    | ~ m1_subset_1(X0_54,k1_zfmisc_1(u1_struct_0(X0_55)))
    | ~ l1_orders_2(X0_55) ),
    inference(subtyping,[status(esa)],[c_39])).

cnf(c_12033,plain,
    ( v13_waybel_0(sK4,k7_lattice3(sK3))
    | ~ v12_waybel_0(sK4,sK3)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ l1_orders_2(sK3) ),
    inference(instantiation,[status(thm)],[c_11923])).

cnf(c_24,plain,
    ( v2_waybel_0(X0,k7_lattice3(X1))
    | ~ v1_waybel_0(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_orders_2(X1) ),
    inference(cnf_transformation,[],[f91])).

cnf(c_11937,plain,
    ( v2_waybel_0(X0_54,k7_lattice3(X0_55))
    | ~ v1_waybel_0(X0_54,X0_55)
    | ~ m1_subset_1(X0_54,k1_zfmisc_1(u1_struct_0(X0_55)))
    | ~ l1_orders_2(X0_55) ),
    inference(subtyping,[status(esa)],[c_24])).

cnf(c_11997,plain,
    ( v2_waybel_0(sK4,k7_lattice3(sK3))
    | ~ v1_waybel_0(sK4,sK3)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ l1_orders_2(sK3) ),
    inference(instantiation,[status(thm)],[c_11937])).

cnf(c_23,plain,
    ( ~ v1_waybel_0(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k7_lattice3(X1))))
    | ~ l1_orders_2(X1) ),
    inference(cnf_transformation,[],[f92])).

cnf(c_11938,plain,
    ( ~ v1_waybel_0(X0_54,X0_55)
    | ~ m1_subset_1(X0_54,k1_zfmisc_1(u1_struct_0(X0_55)))
    | m1_subset_1(X0_54,k1_zfmisc_1(u1_struct_0(k7_lattice3(X0_55))))
    | ~ l1_orders_2(X0_55) ),
    inference(subtyping,[status(esa)],[c_23])).

cnf(c_11994,plain,
    ( ~ v1_waybel_0(sK4,sK3)
    | m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(k7_lattice3(sK3))))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ l1_orders_2(sK3) ),
    inference(instantiation,[status(thm)],[c_11938])).

cnf(c_33,plain,
    ( ~ v2_waybel_0(X0,X1)
    | v1_waybel_0(X0,k7_lattice3(X1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_orders_2(X1) ),
    inference(cnf_transformation,[],[f104])).

cnf(c_48,negated_conjecture,
    ( v2_waybel_0(sK5,sK3) ),
    inference(cnf_transformation,[],[f126])).

cnf(c_6094,plain,
    ( v1_waybel_0(sK5,k7_lattice3(sK3))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ l1_orders_2(sK3) ),
    inference(resolution,[status(thm)],[c_33,c_48])).

cnf(c_40,plain,
    ( ~ v13_waybel_0(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k7_lattice3(X1))))
    | ~ l1_orders_2(X1) ),
    inference(cnf_transformation,[],[f113])).

cnf(c_47,negated_conjecture,
    ( v13_waybel_0(sK5,sK3) ),
    inference(cnf_transformation,[],[f127])).

cnf(c_4398,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(k7_lattice3(sK3))))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ l1_orders_2(sK3) ),
    inference(resolution,[status(thm)],[c_40,c_47])).

cnf(c_41,plain,
    ( ~ v13_waybel_0(X0,X1)
    | v12_waybel_0(X0,k7_lattice3(X1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_orders_2(X1) ),
    inference(cnf_transformation,[],[f112])).

cnf(c_4388,plain,
    ( v12_waybel_0(sK5,k7_lattice3(sK3))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ l1_orders_2(sK3) ),
    inference(resolution,[status(thm)],[c_41,c_47])).

cnf(c_0,plain,
    ( ~ l1_orders_2(X0)
    | l1_orders_2(k7_lattice3(X0)) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_208,plain,
    ( l1_orders_2(k7_lattice3(sK3))
    | ~ l1_orders_2(sK3) ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_1,plain,
    ( ~ v3_orders_2(X0)
    | v3_orders_2(k7_lattice3(X0))
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_205,plain,
    ( v3_orders_2(k7_lattice3(sK3))
    | ~ v3_orders_2(sK3)
    | ~ l1_orders_2(sK3) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_2,plain,
    ( ~ v4_orders_2(X0)
    | v4_orders_2(k7_lattice3(X0))
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_202,plain,
    ( v4_orders_2(k7_lattice3(sK3))
    | ~ v4_orders_2(sK3)
    | ~ l1_orders_2(sK3) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_3,plain,
    ( ~ v5_orders_2(X0)
    | v5_orders_2(k7_lattice3(X0))
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_199,plain,
    ( v5_orders_2(k7_lattice3(sK3))
    | ~ v5_orders_2(sK3)
    | ~ l1_orders_2(sK3) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_4,plain,
    ( ~ v2_lattice3(X0)
    | v1_lattice3(k7_lattice3(X0))
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_196,plain,
    ( ~ v2_lattice3(sK3)
    | v1_lattice3(k7_lattice3(sK3))
    | ~ l1_orders_2(sK3) ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_5,plain,
    ( v2_lattice3(k7_lattice3(X0))
    | ~ v1_lattice3(X0)
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_193,plain,
    ( v2_lattice3(k7_lattice3(sK3))
    | ~ v1_lattice3(sK3)
    | ~ l1_orders_2(sK3) ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_6,plain,
    ( ~ v2_waybel_1(X0)
    | v2_waybel_1(k7_lattice3(X0))
    | ~ v2_lattice3(X0)
    | ~ v1_lattice3(X0)
    | ~ v5_orders_2(X0)
    | ~ v4_orders_2(X0)
    | ~ v3_orders_2(X0)
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_190,plain,
    ( v2_waybel_1(k7_lattice3(sK3))
    | ~ v2_waybel_1(sK3)
    | ~ v2_lattice3(sK3)
    | ~ v1_lattice3(sK3)
    | ~ v5_orders_2(sK3)
    | ~ v4_orders_2(sK3)
    | ~ v3_orders_2(sK3)
    | ~ l1_orders_2(sK3) ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_20,plain,
    ( sP1(X0)
    | ~ v2_lattice3(X0)
    | ~ v1_lattice3(X0)
    | ~ v5_orders_2(X0)
    | ~ v4_orders_2(X0)
    | ~ v3_orders_2(X0)
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f90])).

cnf(c_150,plain,
    ( sP1(sK3)
    | ~ v2_lattice3(sK3)
    | ~ v1_lattice3(sK3)
    | ~ v5_orders_2(sK3)
    | ~ v4_orders_2(sK3)
    | ~ v3_orders_2(sK3)
    | ~ l1_orders_2(sK3) ),
    inference(instantiation,[status(thm)],[c_20])).

cnf(c_45,negated_conjecture,
    ( r1_subset_1(sK4,sK5) ),
    inference(cnf_transformation,[],[f129])).

cnf(c_46,negated_conjecture,
    ( m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK3))) ),
    inference(cnf_transformation,[],[f128])).

cnf(c_50,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3))) ),
    inference(cnf_transformation,[],[f124])).

cnf(c_51,negated_conjecture,
    ( v12_waybel_0(sK4,sK3) ),
    inference(cnf_transformation,[],[f123])).

cnf(c_52,negated_conjecture,
    ( v1_waybel_0(sK4,sK3) ),
    inference(cnf_transformation,[],[f122])).

cnf(c_53,negated_conjecture,
    ( ~ v1_xboole_0(sK4) ),
    inference(cnf_transformation,[],[f121])).

cnf(c_54,negated_conjecture,
    ( l1_orders_2(sK3) ),
    inference(cnf_transformation,[],[f120])).

cnf(c_55,negated_conjecture,
    ( v2_lattice3(sK3) ),
    inference(cnf_transformation,[],[f119])).

cnf(c_56,negated_conjecture,
    ( v1_lattice3(sK3) ),
    inference(cnf_transformation,[],[f118])).

cnf(c_57,negated_conjecture,
    ( v2_waybel_1(sK3) ),
    inference(cnf_transformation,[],[f117])).

cnf(c_58,negated_conjecture,
    ( v5_orders_2(sK3) ),
    inference(cnf_transformation,[],[f116])).

cnf(c_59,negated_conjecture,
    ( v4_orders_2(sK3) ),
    inference(cnf_transformation,[],[f115])).

cnf(c_60,negated_conjecture,
    ( v3_orders_2(sK3) ),
    inference(cnf_transformation,[],[f114])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_12617,c_12607,c_12473,c_12458,c_12443,c_12428,c_12413,c_12398,c_12334,c_12235,c_12033,c_11997,c_11994,c_6094,c_4398,c_4388,c_208,c_205,c_202,c_199,c_196,c_193,c_190,c_150,c_45,c_46,c_49,c_50,c_51,c_52,c_53,c_54,c_55,c_56,c_57,c_58,c_59,c_60])).


%------------------------------------------------------------------------------
