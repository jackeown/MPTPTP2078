%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:28:38 EST 2020

% Result     : Theorem 1.17s
% Output     : CNFRefutation 1.17s
% Verified   : 
% Statistics : Number of formulae       :  110 ( 292 expanded)
%              Number of clauses        :   60 (  76 expanded)
%              Number of leaves         :   14 (  77 expanded)
%              Depth                    :   21
%              Number of atoms          :  469 (1408 expanded)
%              Number of equality atoms :   35 (  35 expanded)
%              Maximal formula depth    :   14 (   6 average)
%              Maximal clause size      :   14 (   4 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f4,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( l1_waybel_0(X1,X0)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( r1_waybel_0(X0,X1,X2)
            <=> ? [X3] :
                  ( ! [X4] :
                      ( m1_subset_1(X4,u1_struct_0(X1))
                     => ( r1_orders_2(X1,X3,X4)
                       => r2_hidden(k2_waybel_0(X0,X1,X4),X2) ) )
                  & m1_subset_1(X3,u1_struct_0(X1)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_waybel_0(X0,X1,X2)
            <=> ? [X3] :
                  ( ! [X4] :
                      ( r2_hidden(k2_waybel_0(X0,X1,X4),X2)
                      | ~ r1_orders_2(X1,X3,X4)
                      | ~ m1_subset_1(X4,u1_struct_0(X1)) )
                  & m1_subset_1(X3,u1_struct_0(X1)) ) )
          | ~ l1_waybel_0(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_waybel_0(X0,X1,X2)
            <=> ? [X3] :
                  ( ! [X4] :
                      ( r2_hidden(k2_waybel_0(X0,X1,X4),X2)
                      | ~ r1_orders_2(X1,X3,X4)
                      | ~ m1_subset_1(X4,u1_struct_0(X1)) )
                  & m1_subset_1(X3,u1_struct_0(X1)) ) )
          | ~ l1_waybel_0(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f14])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r1_waybel_0(X0,X1,X2)
                | ! [X3] :
                    ( ? [X4] :
                        ( ~ r2_hidden(k2_waybel_0(X0,X1,X4),X2)
                        & r1_orders_2(X1,X3,X4)
                        & m1_subset_1(X4,u1_struct_0(X1)) )
                    | ~ m1_subset_1(X3,u1_struct_0(X1)) ) )
              & ( ? [X3] :
                    ( ! [X4] :
                        ( r2_hidden(k2_waybel_0(X0,X1,X4),X2)
                        | ~ r1_orders_2(X1,X3,X4)
                        | ~ m1_subset_1(X4,u1_struct_0(X1)) )
                    & m1_subset_1(X3,u1_struct_0(X1)) )
                | ~ r1_waybel_0(X0,X1,X2) ) )
          | ~ l1_waybel_0(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f15])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r1_waybel_0(X0,X1,X2)
                | ! [X3] :
                    ( ? [X4] :
                        ( ~ r2_hidden(k2_waybel_0(X0,X1,X4),X2)
                        & r1_orders_2(X1,X3,X4)
                        & m1_subset_1(X4,u1_struct_0(X1)) )
                    | ~ m1_subset_1(X3,u1_struct_0(X1)) ) )
              & ( ? [X5] :
                    ( ! [X6] :
                        ( r2_hidden(k2_waybel_0(X0,X1,X6),X2)
                        | ~ r1_orders_2(X1,X5,X6)
                        | ~ m1_subset_1(X6,u1_struct_0(X1)) )
                    & m1_subset_1(X5,u1_struct_0(X1)) )
                | ~ r1_waybel_0(X0,X1,X2) ) )
          | ~ l1_waybel_0(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(rectify,[],[f26])).

fof(f29,plain,(
    ! [X2,X1,X0] :
      ( ? [X5] :
          ( ! [X6] :
              ( r2_hidden(k2_waybel_0(X0,X1,X6),X2)
              | ~ r1_orders_2(X1,X5,X6)
              | ~ m1_subset_1(X6,u1_struct_0(X1)) )
          & m1_subset_1(X5,u1_struct_0(X1)) )
     => ( ! [X6] :
            ( r2_hidden(k2_waybel_0(X0,X1,X6),X2)
            | ~ r1_orders_2(X1,sK2(X0,X1,X2),X6)
            | ~ m1_subset_1(X6,u1_struct_0(X1)) )
        & m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,(
    ! [X3,X2,X1,X0] :
      ( ? [X4] :
          ( ~ r2_hidden(k2_waybel_0(X0,X1,X4),X2)
          & r1_orders_2(X1,X3,X4)
          & m1_subset_1(X4,u1_struct_0(X1)) )
     => ( ~ r2_hidden(k2_waybel_0(X0,X1,sK1(X0,X1,X2,X3)),X2)
        & r1_orders_2(X1,X3,sK1(X0,X1,X2,X3))
        & m1_subset_1(sK1(X0,X1,X2,X3),u1_struct_0(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r1_waybel_0(X0,X1,X2)
                | ! [X3] :
                    ( ( ~ r2_hidden(k2_waybel_0(X0,X1,sK1(X0,X1,X2,X3)),X2)
                      & r1_orders_2(X1,X3,sK1(X0,X1,X2,X3))
                      & m1_subset_1(sK1(X0,X1,X2,X3),u1_struct_0(X1)) )
                    | ~ m1_subset_1(X3,u1_struct_0(X1)) ) )
              & ( ( ! [X6] :
                      ( r2_hidden(k2_waybel_0(X0,X1,X6),X2)
                      | ~ r1_orders_2(X1,sK2(X0,X1,X2),X6)
                      | ~ m1_subset_1(X6,u1_struct_0(X1)) )
                  & m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X1)) )
                | ~ r1_waybel_0(X0,X1,X2) ) )
          | ~ l1_waybel_0(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f27,f29,f28])).

fof(f42,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_waybel_0(X0,X1,X2)
      | ~ r2_hidden(k2_waybel_0(X0,X1,sK1(X0,X1,X2,X3)),X2)
      | ~ m1_subset_1(X3,u1_struct_0(X1))
      | ~ l1_waybel_0(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f9,conjecture,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( l1_waybel_0(X1,X0)
            & ~ v2_struct_0(X1) )
         => r1_waybel_0(X0,X1,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f10,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_struct_0(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( l1_waybel_0(X1,X0)
              & ~ v2_struct_0(X1) )
           => r1_waybel_0(X0,X1,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1))) ) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f22,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ r1_waybel_0(X0,X1,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)))
          & l1_waybel_0(X1,X0)
          & ~ v2_struct_0(X1) )
      & l1_struct_0(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f23,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ r1_waybel_0(X0,X1,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)))
          & l1_waybel_0(X1,X0)
          & ~ v2_struct_0(X1) )
      & l1_struct_0(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f22])).

fof(f33,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ r1_waybel_0(X0,X1,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)))
          & l1_waybel_0(X1,X0)
          & ~ v2_struct_0(X1) )
     => ( ~ r1_waybel_0(X0,sK4,k2_relset_1(u1_struct_0(sK4),u1_struct_0(X0),u1_waybel_0(X0,sK4)))
        & l1_waybel_0(sK4,X0)
        & ~ v2_struct_0(sK4) ) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ~ r1_waybel_0(X0,X1,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)))
            & l1_waybel_0(X1,X0)
            & ~ v2_struct_0(X1) )
        & l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ~ r1_waybel_0(sK3,X1,k2_relset_1(u1_struct_0(X1),u1_struct_0(sK3),u1_waybel_0(sK3,X1)))
          & l1_waybel_0(X1,sK3)
          & ~ v2_struct_0(X1) )
      & l1_struct_0(sK3)
      & ~ v2_struct_0(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,
    ( ~ r1_waybel_0(sK3,sK4,k2_relset_1(u1_struct_0(sK4),u1_struct_0(sK3),u1_waybel_0(sK3,sK4)))
    & l1_waybel_0(sK4,sK3)
    & ~ v2_struct_0(sK4)
    & l1_struct_0(sK3)
    & ~ v2_struct_0(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f23,f33,f32])).

fof(f53,plain,(
    l1_waybel_0(sK4,sK3) ),
    inference(cnf_transformation,[],[f34])).

fof(f50,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f34])).

fof(f51,plain,(
    l1_struct_0(sK3) ),
    inference(cnf_transformation,[],[f34])).

fof(f52,plain,(
    ~ v2_struct_0(sK4) ),
    inference(cnf_transformation,[],[f34])).

fof(f8,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => ( v2_struct_0(X0)
      <=> v1_xboole_0(u1_struct_0(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0] :
      ( ( v2_struct_0(X0)
      <=> v1_xboole_0(u1_struct_0(X0)) )
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f31,plain,(
    ! [X0] :
      ( ( ( v2_struct_0(X0)
          | ~ v1_xboole_0(u1_struct_0(X0)) )
        & ( v1_xboole_0(u1_struct_0(X0))
          | ~ v2_struct_0(X0) ) )
      | ~ l1_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f21])).

fof(f49,plain,(
    ! [X0] :
      ( v2_struct_0(X0)
      | ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => ! [X1] :
          ( l1_waybel_0(X1,X0)
         => l1_orders_2(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_orders_2(X1)
          | ~ l1_waybel_0(X1,X0) )
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f44,plain,(
    ! [X0,X1] :
      ( l1_orders_2(X1)
      | ~ l1_waybel_0(X1,X0)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f3,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f37,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f2,axiom,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( ~ v1_xboole_0(X1)
         => ! [X2] :
              ( m1_subset_1(X2,X0)
             => ! [X3] :
                  ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
                    & v1_funct_2(X3,X0,X1)
                    & v1_funct_1(X3) )
                 => r2_hidden(k3_funct_2(X0,X1,X3,X2),k2_relset_1(X0,X1,X3)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f11,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( r2_hidden(k3_funct_2(X0,X1,X3,X2),k2_relset_1(X0,X1,X3))
                  | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
                  | ~ v1_funct_2(X3,X0,X1)
                  | ~ v1_funct_1(X3) )
              | ~ m1_subset_1(X2,X0) )
          | v1_xboole_0(X1) )
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f12,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( r2_hidden(k3_funct_2(X0,X1,X3,X2),k2_relset_1(X0,X1,X3))
                  | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
                  | ~ v1_funct_2(X3,X0,X1)
                  | ~ v1_funct_1(X3) )
              | ~ m1_subset_1(X2,X0) )
          | v1_xboole_0(X1) )
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f11])).

fof(f36,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(k3_funct_2(X0,X1,X3,X2),k2_relset_1(X0,X1,X3))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,X0)
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( ( l1_waybel_0(X1,X0)
        & l1_struct_0(X0) )
     => ( m1_subset_1(u1_waybel_0(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
        & v1_funct_2(u1_waybel_0(X0,X1),u1_struct_0(X1),u1_struct_0(X0))
        & v1_funct_1(u1_waybel_0(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(u1_waybel_0(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
        & v1_funct_2(u1_waybel_0(X0,X1),u1_struct_0(X1),u1_struct_0(X0))
        & v1_funct_1(u1_waybel_0(X0,X1)) )
      | ~ l1_waybel_0(X1,X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(u1_waybel_0(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
        & v1_funct_2(u1_waybel_0(X0,X1),u1_struct_0(X1),u1_struct_0(X0))
        & v1_funct_1(u1_waybel_0(X0,X1)) )
      | ~ l1_waybel_0(X1,X0)
      | ~ l1_struct_0(X0) ) ),
    inference(flattening,[],[f19])).

fof(f46,plain,(
    ! [X0,X1] :
      ( v1_funct_2(u1_waybel_0(X0,X1),u1_struct_0(X1),u1_struct_0(X0))
      | ~ l1_waybel_0(X1,X0)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f45,plain,(
    ! [X0,X1] :
      ( v1_funct_1(u1_waybel_0(X0,X1))
      | ~ l1_waybel_0(X1,X0)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f47,plain,(
    ! [X0,X1] :
      ( m1_subset_1(u1_waybel_0(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
      | ~ l1_waybel_0(X1,X0)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f54,plain,(
    ~ r1_waybel_0(sK3,sK4,k2_relset_1(u1_struct_0(sK4),u1_struct_0(sK3),u1_waybel_0(sK3,sK4))) ),
    inference(cnf_transformation,[],[f34])).

fof(f5,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( l1_waybel_0(X1,X0)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X1))
             => k3_funct_2(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1),X2) = k2_waybel_0(X0,X1,X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k3_funct_2(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1),X2) = k2_waybel_0(X0,X1,X2)
              | ~ m1_subset_1(X2,u1_struct_0(X1)) )
          | ~ l1_waybel_0(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k3_funct_2(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1),X2) = k2_waybel_0(X0,X1,X2)
              | ~ m1_subset_1(X2,u1_struct_0(X1)) )
          | ~ l1_waybel_0(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f16])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( k3_funct_2(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1),X2) = k2_waybel_0(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l1_waybel_0(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f40,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_waybel_0(X0,X1,X2)
      | m1_subset_1(sK1(X0,X1,X2,X3),u1_struct_0(X1))
      | ~ m1_subset_1(X3,u1_struct_0(X1))
      | ~ l1_waybel_0(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f1,axiom,(
    ! [X0] :
    ? [X1] : m1_subset_1(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0] :
      ( ? [X1] : m1_subset_1(X1,X0)
     => m1_subset_1(sK0(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,(
    ! [X0] : m1_subset_1(sK0(X0),X0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f1,f24])).

fof(f35,plain,(
    ! [X0] : m1_subset_1(sK0(X0),X0) ),
    inference(cnf_transformation,[],[f25])).

cnf(c_3,plain,
    ( r1_waybel_0(X0,X1,X2)
    | ~ l1_waybel_0(X1,X0)
    | ~ r2_hidden(k2_waybel_0(X0,X1,sK1(X0,X1,X2,X3)),X2)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | ~ l1_struct_0(X0) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_16,negated_conjecture,
    ( l1_waybel_0(sK4,sK3) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_448,plain,
    ( r1_waybel_0(X0,X1,X2)
    | ~ r2_hidden(k2_waybel_0(X0,X1,sK1(X0,X1,X2,X3)),X2)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | ~ l1_struct_0(X0)
    | sK4 != X1
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_3,c_16])).

cnf(c_449,plain,
    ( r1_waybel_0(sK3,sK4,X0)
    | ~ r2_hidden(k2_waybel_0(sK3,sK4,sK1(sK3,sK4,X0,X1)),X0)
    | ~ m1_subset_1(X1,u1_struct_0(sK4))
    | v2_struct_0(sK4)
    | v2_struct_0(sK3)
    | ~ l1_struct_0(sK3) ),
    inference(unflattening,[status(thm)],[c_448])).

cnf(c_19,negated_conjecture,
    ( ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_18,negated_conjecture,
    ( l1_struct_0(sK3) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_17,negated_conjecture,
    ( ~ v2_struct_0(sK4) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_453,plain,
    ( ~ m1_subset_1(X1,u1_struct_0(sK4))
    | ~ r2_hidden(k2_waybel_0(sK3,sK4,sK1(sK3,sK4,X0,X1)),X0)
    | r1_waybel_0(sK3,sK4,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_449,c_19,c_18,c_17])).

cnf(c_454,plain,
    ( r1_waybel_0(sK3,sK4,X0)
    | ~ r2_hidden(k2_waybel_0(sK3,sK4,sK1(sK3,sK4,X0,X1)),X0)
    | ~ m1_subset_1(X1,u1_struct_0(sK4)) ),
    inference(renaming,[status(thm)],[c_453])).

cnf(c_13,plain,
    ( v2_struct_0(X0)
    | ~ l1_struct_0(X0)
    | ~ v1_xboole_0(u1_struct_0(X0)) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_9,plain,
    ( ~ l1_waybel_0(X0,X1)
    | l1_orders_2(X0)
    | ~ l1_struct_0(X1) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_2,plain,
    ( ~ l1_orders_2(X0)
    | l1_struct_0(X0) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_227,plain,
    ( ~ l1_waybel_0(X0,X1)
    | ~ l1_struct_0(X1)
    | l1_struct_0(X0) ),
    inference(resolution,[status(thm)],[c_9,c_2])).

cnf(c_511,plain,
    ( ~ l1_struct_0(X0)
    | l1_struct_0(X1)
    | sK4 != X1
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_227,c_16])).

cnf(c_512,plain,
    ( l1_struct_0(sK4)
    | ~ l1_struct_0(sK3) ),
    inference(unflattening,[status(thm)],[c_511])).

cnf(c_514,plain,
    ( l1_struct_0(sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_512,c_18])).

cnf(c_672,plain,
    ( v2_struct_0(X0)
    | ~ v1_xboole_0(u1_struct_0(X0))
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_13,c_514])).

cnf(c_673,plain,
    ( v2_struct_0(sK4)
    | ~ v1_xboole_0(u1_struct_0(sK4)) ),
    inference(unflattening,[status(thm)],[c_672])).

cnf(c_675,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK4)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_673,c_17])).

cnf(c_1,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | r2_hidden(k3_funct_2(X1,X2,X0,X3),k2_relset_1(X1,X2,X0))
    | ~ m1_subset_1(X3,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_xboole_0(X1)
    | v1_xboole_0(X2)
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_11,plain,
    ( v1_funct_2(u1_waybel_0(X0,X1),u1_struct_0(X1),u1_struct_0(X0))
    | ~ l1_waybel_0(X1,X0)
    | ~ l1_struct_0(X0) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_243,plain,
    ( ~ l1_waybel_0(X0,X1)
    | r2_hidden(k3_funct_2(X2,X3,X4,X5),k2_relset_1(X2,X3,X4))
    | ~ m1_subset_1(X5,X2)
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ l1_struct_0(X1)
    | v1_xboole_0(X2)
    | v1_xboole_0(X3)
    | ~ v1_funct_1(X4)
    | u1_waybel_0(X1,X0) != X4
    | u1_struct_0(X1) != X3
    | u1_struct_0(X0) != X2 ),
    inference(resolution_lifted,[status(thm)],[c_1,c_11])).

cnf(c_244,plain,
    ( ~ l1_waybel_0(X0,X1)
    | r2_hidden(k3_funct_2(u1_struct_0(X0),u1_struct_0(X1),u1_waybel_0(X1,X0),X2),k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),u1_waybel_0(X1,X0)))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(u1_waybel_0(X1,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | ~ l1_struct_0(X1)
    | v1_xboole_0(u1_struct_0(X0))
    | v1_xboole_0(u1_struct_0(X1))
    | ~ v1_funct_1(u1_waybel_0(X1,X0)) ),
    inference(unflattening,[status(thm)],[c_243])).

cnf(c_12,plain,
    ( ~ l1_waybel_0(X0,X1)
    | ~ l1_struct_0(X1)
    | v1_funct_1(u1_waybel_0(X1,X0)) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_10,plain,
    ( ~ l1_waybel_0(X0,X1)
    | m1_subset_1(u1_waybel_0(X1,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | ~ l1_struct_0(X1) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_248,plain,
    ( v1_xboole_0(u1_struct_0(X1))
    | v1_xboole_0(u1_struct_0(X0))
    | ~ l1_struct_0(X1)
    | ~ l1_waybel_0(X0,X1)
    | r2_hidden(k3_funct_2(u1_struct_0(X0),u1_struct_0(X1),u1_waybel_0(X1,X0),X2),k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),u1_waybel_0(X1,X0)))
    | ~ m1_subset_1(X2,u1_struct_0(X0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_244,c_12,c_10])).

cnf(c_249,plain,
    ( ~ l1_waybel_0(X0,X1)
    | r2_hidden(k3_funct_2(u1_struct_0(X0),u1_struct_0(X1),u1_waybel_0(X1,X0),X2),k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),u1_waybel_0(X1,X0)))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ l1_struct_0(X1)
    | v1_xboole_0(u1_struct_0(X0))
    | v1_xboole_0(u1_struct_0(X1)) ),
    inference(renaming,[status(thm)],[c_248])).

cnf(c_490,plain,
    ( r2_hidden(k3_funct_2(u1_struct_0(X0),u1_struct_0(X1),u1_waybel_0(X1,X0),X2),k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),u1_waybel_0(X1,X0)))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ l1_struct_0(X1)
    | v1_xboole_0(u1_struct_0(X0))
    | v1_xboole_0(u1_struct_0(X1))
    | sK4 != X0
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_249,c_16])).

cnf(c_491,plain,
    ( r2_hidden(k3_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),u1_waybel_0(sK3,sK4),X0),k2_relset_1(u1_struct_0(sK4),u1_struct_0(sK3),u1_waybel_0(sK3,sK4)))
    | ~ m1_subset_1(X0,u1_struct_0(sK4))
    | ~ l1_struct_0(sK3)
    | v1_xboole_0(u1_struct_0(sK4))
    | v1_xboole_0(u1_struct_0(sK3)) ),
    inference(unflattening,[status(thm)],[c_490])).

cnf(c_27,plain,
    ( v2_struct_0(sK3)
    | ~ l1_struct_0(sK3)
    | ~ v1_xboole_0(u1_struct_0(sK3)) ),
    inference(instantiation,[status(thm)],[c_13])).

cnf(c_495,plain,
    ( v1_xboole_0(u1_struct_0(sK4))
    | r2_hidden(k3_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),u1_waybel_0(sK3,sK4),X0),k2_relset_1(u1_struct_0(sK4),u1_struct_0(sK3),u1_waybel_0(sK3,sK4)))
    | ~ m1_subset_1(X0,u1_struct_0(sK4)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_491,c_19,c_18,c_27])).

cnf(c_496,plain,
    ( r2_hidden(k3_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),u1_waybel_0(sK3,sK4),X0),k2_relset_1(u1_struct_0(sK4),u1_struct_0(sK3),u1_waybel_0(sK3,sK4)))
    | ~ m1_subset_1(X0,u1_struct_0(sK4))
    | v1_xboole_0(u1_struct_0(sK4)) ),
    inference(renaming,[status(thm)],[c_495])).

cnf(c_686,plain,
    ( r2_hidden(k3_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),u1_waybel_0(sK3,sK4),X0),k2_relset_1(u1_struct_0(sK4),u1_struct_0(sK3),u1_waybel_0(sK3,sK4)))
    | ~ m1_subset_1(X0,u1_struct_0(sK4)) ),
    inference(backward_subsumption_resolution,[status(thm)],[c_675,c_496])).

cnf(c_691,plain,
    ( r1_waybel_0(sK3,sK4,X0)
    | ~ m1_subset_1(X1,u1_struct_0(sK4))
    | ~ m1_subset_1(X2,u1_struct_0(sK4))
    | k3_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),u1_waybel_0(sK3,sK4),X2) != k2_waybel_0(sK3,sK4,sK1(sK3,sK4,X0,X1))
    | k2_relset_1(u1_struct_0(sK4),u1_struct_0(sK3),u1_waybel_0(sK3,sK4)) != X0 ),
    inference(resolution_lifted,[status(thm)],[c_454,c_686])).

cnf(c_692,plain,
    ( r1_waybel_0(sK3,sK4,k2_relset_1(u1_struct_0(sK4),u1_struct_0(sK3),u1_waybel_0(sK3,sK4)))
    | ~ m1_subset_1(X0,u1_struct_0(sK4))
    | ~ m1_subset_1(X1,u1_struct_0(sK4))
    | k3_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),u1_waybel_0(sK3,sK4),X1) != k2_waybel_0(sK3,sK4,sK1(sK3,sK4,k2_relset_1(u1_struct_0(sK4),u1_struct_0(sK3),u1_waybel_0(sK3,sK4)),X0)) ),
    inference(unflattening,[status(thm)],[c_691])).

cnf(c_15,negated_conjecture,
    ( ~ r1_waybel_0(sK3,sK4,k2_relset_1(u1_struct_0(sK4),u1_struct_0(sK3),u1_waybel_0(sK3,sK4))) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_696,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK4))
    | ~ m1_subset_1(X1,u1_struct_0(sK4))
    | k3_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),u1_waybel_0(sK3,sK4),X1) != k2_waybel_0(sK3,sK4,sK1(sK3,sK4,k2_relset_1(u1_struct_0(sK4),u1_struct_0(sK3),u1_waybel_0(sK3,sK4)),X0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_692,c_15])).

cnf(c_697,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK4))
    | ~ m1_subset_1(X1,u1_struct_0(sK4))
    | k3_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),u1_waybel_0(sK3,sK4),X0) != k2_waybel_0(sK3,sK4,sK1(sK3,sK4,k2_relset_1(u1_struct_0(sK4),u1_struct_0(sK3),u1_waybel_0(sK3,sK4)),X1)) ),
    inference(renaming,[status(thm)],[c_696])).

cnf(c_804,plain,
    ( ~ m1_subset_1(X0_51,u1_struct_0(sK4))
    | ~ m1_subset_1(X1_51,u1_struct_0(sK4))
    | k3_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),u1_waybel_0(sK3,sK4),X0_51) != k2_waybel_0(sK3,sK4,sK1(sK3,sK4,k2_relset_1(u1_struct_0(sK4),u1_struct_0(sK3),u1_waybel_0(sK3,sK4)),X1_51)) ),
    inference(subtyping,[status(esa)],[c_697])).

cnf(c_968,plain,
    ( ~ m1_subset_1(X0_51,u1_struct_0(sK4))
    | ~ m1_subset_1(sK1(sK3,sK4,k2_relset_1(u1_struct_0(sK4),u1_struct_0(sK3),u1_waybel_0(sK3,sK4)),sK0(u1_struct_0(sK4))),u1_struct_0(sK4))
    | k3_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),u1_waybel_0(sK3,sK4),sK1(sK3,sK4,k2_relset_1(u1_struct_0(sK4),u1_struct_0(sK3),u1_waybel_0(sK3,sK4)),sK0(u1_struct_0(sK4)))) != k2_waybel_0(sK3,sK4,sK1(sK3,sK4,k2_relset_1(u1_struct_0(sK4),u1_struct_0(sK3),u1_waybel_0(sK3,sK4)),X0_51)) ),
    inference(instantiation,[status(thm)],[c_804])).

cnf(c_1053,plain,
    ( ~ m1_subset_1(sK1(sK3,sK4,k2_relset_1(u1_struct_0(sK4),u1_struct_0(sK3),u1_waybel_0(sK3,sK4)),sK0(u1_struct_0(sK4))),u1_struct_0(sK4))
    | ~ m1_subset_1(sK0(u1_struct_0(sK4)),u1_struct_0(sK4))
    | k3_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),u1_waybel_0(sK3,sK4),sK1(sK3,sK4,k2_relset_1(u1_struct_0(sK4),u1_struct_0(sK3),u1_waybel_0(sK3,sK4)),sK0(u1_struct_0(sK4)))) != k2_waybel_0(sK3,sK4,sK1(sK3,sK4,k2_relset_1(u1_struct_0(sK4),u1_struct_0(sK3),u1_waybel_0(sK3,sK4)),sK0(u1_struct_0(sK4)))) ),
    inference(instantiation,[status(thm)],[c_968])).

cnf(c_8,plain,
    ( ~ l1_waybel_0(X0,X1)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | ~ l1_struct_0(X1)
    | k3_funct_2(u1_struct_0(X0),u1_struct_0(X1),u1_waybel_0(X1,X0),X2) = k2_waybel_0(X1,X0,X2) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_533,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ l1_struct_0(X2)
    | k3_funct_2(u1_struct_0(X1),u1_struct_0(X2),u1_waybel_0(X2,X1),X0) = k2_waybel_0(X2,X1,X0)
    | sK4 != X1
    | sK3 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_8,c_16])).

cnf(c_534,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK4))
    | v2_struct_0(sK4)
    | v2_struct_0(sK3)
    | ~ l1_struct_0(sK3)
    | k3_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),u1_waybel_0(sK3,sK4),X0) = k2_waybel_0(sK3,sK4,X0) ),
    inference(unflattening,[status(thm)],[c_533])).

cnf(c_538,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK4))
    | k3_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),u1_waybel_0(sK3,sK4),X0) = k2_waybel_0(sK3,sK4,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_534,c_19,c_18,c_17])).

cnf(c_805,plain,
    ( ~ m1_subset_1(X0_51,u1_struct_0(sK4))
    | k3_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),u1_waybel_0(sK3,sK4),X0_51) = k2_waybel_0(sK3,sK4,X0_51) ),
    inference(subtyping,[status(esa)],[c_538])).

cnf(c_970,plain,
    ( ~ m1_subset_1(sK1(sK3,sK4,k2_relset_1(u1_struct_0(sK4),u1_struct_0(sK3),u1_waybel_0(sK3,sK4)),sK0(u1_struct_0(sK4))),u1_struct_0(sK4))
    | k3_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),u1_waybel_0(sK3,sK4),sK1(sK3,sK4,k2_relset_1(u1_struct_0(sK4),u1_struct_0(sK3),u1_waybel_0(sK3,sK4)),sK0(u1_struct_0(sK4)))) = k2_waybel_0(sK3,sK4,sK1(sK3,sK4,k2_relset_1(u1_struct_0(sK4),u1_struct_0(sK3),u1_waybel_0(sK3,sK4)),sK0(u1_struct_0(sK4)))) ),
    inference(instantiation,[status(thm)],[c_805])).

cnf(c_5,plain,
    ( r1_waybel_0(X0,X1,X2)
    | ~ l1_waybel_0(X1,X0)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | m1_subset_1(sK1(X0,X1,X2,X3),u1_struct_0(X1))
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | ~ l1_struct_0(X0) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_427,plain,
    ( r1_waybel_0(X0,X1,X2)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | m1_subset_1(sK1(X0,X1,X2,X3),u1_struct_0(X1))
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | ~ l1_struct_0(X0)
    | sK4 != X1
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_5,c_16])).

cnf(c_428,plain,
    ( r1_waybel_0(sK3,sK4,X0)
    | ~ m1_subset_1(X1,u1_struct_0(sK4))
    | m1_subset_1(sK1(sK3,sK4,X0,X1),u1_struct_0(sK4))
    | v2_struct_0(sK4)
    | v2_struct_0(sK3)
    | ~ l1_struct_0(sK3) ),
    inference(unflattening,[status(thm)],[c_427])).

cnf(c_432,plain,
    ( m1_subset_1(sK1(sK3,sK4,X0,X1),u1_struct_0(sK4))
    | ~ m1_subset_1(X1,u1_struct_0(sK4))
    | r1_waybel_0(sK3,sK4,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_428,c_19,c_18,c_17])).

cnf(c_433,plain,
    ( r1_waybel_0(sK3,sK4,X0)
    | ~ m1_subset_1(X1,u1_struct_0(sK4))
    | m1_subset_1(sK1(sK3,sK4,X0,X1),u1_struct_0(sK4)) ),
    inference(renaming,[status(thm)],[c_432])).

cnf(c_732,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK4))
    | m1_subset_1(sK1(sK3,sK4,X1,X0),u1_struct_0(sK4))
    | k2_relset_1(u1_struct_0(sK4),u1_struct_0(sK3),u1_waybel_0(sK3,sK4)) != X1
    | sK4 != sK4
    | sK3 != sK3 ),
    inference(resolution_lifted,[status(thm)],[c_15,c_433])).

cnf(c_733,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK4))
    | m1_subset_1(sK1(sK3,sK4,k2_relset_1(u1_struct_0(sK4),u1_struct_0(sK3),u1_waybel_0(sK3,sK4)),X0),u1_struct_0(sK4)) ),
    inference(unflattening,[status(thm)],[c_732])).

cnf(c_802,plain,
    ( ~ m1_subset_1(X0_51,u1_struct_0(sK4))
    | m1_subset_1(sK1(sK3,sK4,k2_relset_1(u1_struct_0(sK4),u1_struct_0(sK3),u1_waybel_0(sK3,sK4)),X0_51),u1_struct_0(sK4)) ),
    inference(subtyping,[status(esa)],[c_733])).

cnf(c_943,plain,
    ( m1_subset_1(sK1(sK3,sK4,k2_relset_1(u1_struct_0(sK4),u1_struct_0(sK3),u1_waybel_0(sK3,sK4)),sK0(u1_struct_0(sK4))),u1_struct_0(sK4))
    | ~ m1_subset_1(sK0(u1_struct_0(sK4)),u1_struct_0(sK4)) ),
    inference(instantiation,[status(thm)],[c_802])).

cnf(c_0,plain,
    ( m1_subset_1(sK0(X0),X0) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_807,plain,
    ( m1_subset_1(sK0(X0_52),X0_52) ),
    inference(subtyping,[status(esa)],[c_0])).

cnf(c_942,plain,
    ( m1_subset_1(sK0(u1_struct_0(sK4)),u1_struct_0(sK4)) ),
    inference(instantiation,[status(thm)],[c_807])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_1053,c_970,c_943,c_942])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 20:46:37 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running in FOF mode
% 1.17/1.01  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.17/1.01  
% 1.17/1.01  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 1.17/1.01  
% 1.17/1.01  ------  iProver source info
% 1.17/1.01  
% 1.17/1.01  git: date: 2020-06-30 10:37:57 +0100
% 1.17/1.01  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 1.17/1.01  git: non_committed_changes: false
% 1.17/1.01  git: last_make_outside_of_git: false
% 1.17/1.01  
% 1.17/1.01  ------ 
% 1.17/1.01  
% 1.17/1.01  ------ Input Options
% 1.17/1.01  
% 1.17/1.01  --out_options                           all
% 1.17/1.01  --tptp_safe_out                         true
% 1.17/1.01  --problem_path                          ""
% 1.17/1.01  --include_path                          ""
% 1.17/1.01  --clausifier                            res/vclausify_rel
% 1.17/1.01  --clausifier_options                    --mode clausify
% 1.17/1.01  --stdin                                 false
% 1.17/1.01  --stats_out                             all
% 1.17/1.01  
% 1.17/1.01  ------ General Options
% 1.17/1.01  
% 1.17/1.01  --fof                                   false
% 1.17/1.01  --time_out_real                         305.
% 1.17/1.01  --time_out_virtual                      -1.
% 1.17/1.01  --symbol_type_check                     false
% 1.17/1.01  --clausify_out                          false
% 1.17/1.01  --sig_cnt_out                           false
% 1.17/1.01  --trig_cnt_out                          false
% 1.17/1.01  --trig_cnt_out_tolerance                1.
% 1.17/1.01  --trig_cnt_out_sk_spl                   false
% 1.17/1.01  --abstr_cl_out                          false
% 1.17/1.01  
% 1.17/1.01  ------ Global Options
% 1.17/1.01  
% 1.17/1.01  --schedule                              default
% 1.17/1.01  --add_important_lit                     false
% 1.17/1.01  --prop_solver_per_cl                    1000
% 1.17/1.01  --min_unsat_core                        false
% 1.17/1.01  --soft_assumptions                      false
% 1.17/1.01  --soft_lemma_size                       3
% 1.17/1.01  --prop_impl_unit_size                   0
% 1.17/1.01  --prop_impl_unit                        []
% 1.17/1.01  --share_sel_clauses                     true
% 1.17/1.01  --reset_solvers                         false
% 1.17/1.01  --bc_imp_inh                            [conj_cone]
% 1.17/1.01  --conj_cone_tolerance                   3.
% 1.17/1.01  --extra_neg_conj                        none
% 1.17/1.01  --large_theory_mode                     true
% 1.17/1.01  --prolific_symb_bound                   200
% 1.17/1.01  --lt_threshold                          2000
% 1.17/1.01  --clause_weak_htbl                      true
% 1.17/1.01  --gc_record_bc_elim                     false
% 1.17/1.01  
% 1.17/1.01  ------ Preprocessing Options
% 1.17/1.01  
% 1.17/1.01  --preprocessing_flag                    true
% 1.17/1.01  --time_out_prep_mult                    0.1
% 1.17/1.01  --splitting_mode                        input
% 1.17/1.01  --splitting_grd                         true
% 1.17/1.01  --splitting_cvd                         false
% 1.17/1.01  --splitting_cvd_svl                     false
% 1.17/1.01  --splitting_nvd                         32
% 1.17/1.01  --sub_typing                            true
% 1.17/1.01  --prep_gs_sim                           true
% 1.17/1.01  --prep_unflatten                        true
% 1.17/1.01  --prep_res_sim                          true
% 1.17/1.01  --prep_upred                            true
% 1.17/1.01  --prep_sem_filter                       exhaustive
% 1.17/1.01  --prep_sem_filter_out                   false
% 1.17/1.01  --pred_elim                             true
% 1.17/1.01  --res_sim_input                         true
% 1.17/1.01  --eq_ax_congr_red                       true
% 1.17/1.01  --pure_diseq_elim                       true
% 1.17/1.01  --brand_transform                       false
% 1.17/1.01  --non_eq_to_eq                          false
% 1.17/1.01  --prep_def_merge                        true
% 1.17/1.01  --prep_def_merge_prop_impl              false
% 1.17/1.01  --prep_def_merge_mbd                    true
% 1.17/1.01  --prep_def_merge_tr_red                 false
% 1.17/1.01  --prep_def_merge_tr_cl                  false
% 1.17/1.01  --smt_preprocessing                     true
% 1.17/1.01  --smt_ac_axioms                         fast
% 1.17/1.01  --preprocessed_out                      false
% 1.17/1.01  --preprocessed_stats                    false
% 1.17/1.01  
% 1.17/1.01  ------ Abstraction refinement Options
% 1.17/1.01  
% 1.17/1.01  --abstr_ref                             []
% 1.17/1.01  --abstr_ref_prep                        false
% 1.17/1.01  --abstr_ref_until_sat                   false
% 1.17/1.01  --abstr_ref_sig_restrict                funpre
% 1.17/1.01  --abstr_ref_af_restrict_to_split_sk     false
% 1.17/1.01  --abstr_ref_under                       []
% 1.17/1.01  
% 1.17/1.01  ------ SAT Options
% 1.17/1.01  
% 1.17/1.01  --sat_mode                              false
% 1.17/1.01  --sat_fm_restart_options                ""
% 1.17/1.01  --sat_gr_def                            false
% 1.17/1.01  --sat_epr_types                         true
% 1.17/1.01  --sat_non_cyclic_types                  false
% 1.17/1.01  --sat_finite_models                     false
% 1.17/1.01  --sat_fm_lemmas                         false
% 1.17/1.01  --sat_fm_prep                           false
% 1.17/1.01  --sat_fm_uc_incr                        true
% 1.17/1.01  --sat_out_model                         small
% 1.17/1.01  --sat_out_clauses                       false
% 1.17/1.01  
% 1.17/1.01  ------ QBF Options
% 1.17/1.01  
% 1.17/1.01  --qbf_mode                              false
% 1.17/1.01  --qbf_elim_univ                         false
% 1.17/1.01  --qbf_dom_inst                          none
% 1.17/1.01  --qbf_dom_pre_inst                      false
% 1.17/1.01  --qbf_sk_in                             false
% 1.17/1.01  --qbf_pred_elim                         true
% 1.17/1.01  --qbf_split                             512
% 1.17/1.01  
% 1.17/1.01  ------ BMC1 Options
% 1.17/1.01  
% 1.17/1.01  --bmc1_incremental                      false
% 1.17/1.01  --bmc1_axioms                           reachable_all
% 1.17/1.01  --bmc1_min_bound                        0
% 1.17/1.01  --bmc1_max_bound                        -1
% 1.17/1.01  --bmc1_max_bound_default                -1
% 1.17/1.01  --bmc1_symbol_reachability              true
% 1.17/1.01  --bmc1_property_lemmas                  false
% 1.17/1.01  --bmc1_k_induction                      false
% 1.17/1.01  --bmc1_non_equiv_states                 false
% 1.17/1.01  --bmc1_deadlock                         false
% 1.17/1.01  --bmc1_ucm                              false
% 1.17/1.01  --bmc1_add_unsat_core                   none
% 1.17/1.01  --bmc1_unsat_core_children              false
% 1.17/1.01  --bmc1_unsat_core_extrapolate_axioms    false
% 1.17/1.01  --bmc1_out_stat                         full
% 1.17/1.01  --bmc1_ground_init                      false
% 1.17/1.01  --bmc1_pre_inst_next_state              false
% 1.17/1.01  --bmc1_pre_inst_state                   false
% 1.17/1.01  --bmc1_pre_inst_reach_state             false
% 1.17/1.01  --bmc1_out_unsat_core                   false
% 1.17/1.01  --bmc1_aig_witness_out                  false
% 1.17/1.01  --bmc1_verbose                          false
% 1.17/1.01  --bmc1_dump_clauses_tptp                false
% 1.17/1.01  --bmc1_dump_unsat_core_tptp             false
% 1.17/1.01  --bmc1_dump_file                        -
% 1.17/1.01  --bmc1_ucm_expand_uc_limit              128
% 1.17/1.01  --bmc1_ucm_n_expand_iterations          6
% 1.17/1.01  --bmc1_ucm_extend_mode                  1
% 1.17/1.01  --bmc1_ucm_init_mode                    2
% 1.17/1.01  --bmc1_ucm_cone_mode                    none
% 1.17/1.01  --bmc1_ucm_reduced_relation_type        0
% 1.17/1.01  --bmc1_ucm_relax_model                  4
% 1.17/1.01  --bmc1_ucm_full_tr_after_sat            true
% 1.17/1.01  --bmc1_ucm_expand_neg_assumptions       false
% 1.17/1.01  --bmc1_ucm_layered_model                none
% 1.17/1.01  --bmc1_ucm_max_lemma_size               10
% 1.17/1.01  
% 1.17/1.01  ------ AIG Options
% 1.17/1.01  
% 1.17/1.01  --aig_mode                              false
% 1.17/1.01  
% 1.17/1.01  ------ Instantiation Options
% 1.17/1.01  
% 1.17/1.01  --instantiation_flag                    true
% 1.17/1.01  --inst_sos_flag                         false
% 1.17/1.01  --inst_sos_phase                        true
% 1.17/1.01  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.17/1.01  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.17/1.01  --inst_lit_sel_side                     num_symb
% 1.17/1.01  --inst_solver_per_active                1400
% 1.17/1.01  --inst_solver_calls_frac                1.
% 1.17/1.01  --inst_passive_queue_type               priority_queues
% 1.17/1.01  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.17/1.01  --inst_passive_queues_freq              [25;2]
% 1.17/1.01  --inst_dismatching                      true
% 1.17/1.01  --inst_eager_unprocessed_to_passive     true
% 1.17/1.01  --inst_prop_sim_given                   true
% 1.17/1.01  --inst_prop_sim_new                     false
% 1.17/1.01  --inst_subs_new                         false
% 1.17/1.01  --inst_eq_res_simp                      false
% 1.17/1.01  --inst_subs_given                       false
% 1.17/1.01  --inst_orphan_elimination               true
% 1.17/1.01  --inst_learning_loop_flag               true
% 1.17/1.01  --inst_learning_start                   3000
% 1.17/1.01  --inst_learning_factor                  2
% 1.17/1.01  --inst_start_prop_sim_after_learn       3
% 1.17/1.01  --inst_sel_renew                        solver
% 1.17/1.01  --inst_lit_activity_flag                true
% 1.17/1.01  --inst_restr_to_given                   false
% 1.17/1.01  --inst_activity_threshold               500
% 1.17/1.01  --inst_out_proof                        true
% 1.17/1.01  
% 1.17/1.01  ------ Resolution Options
% 1.17/1.01  
% 1.17/1.01  --resolution_flag                       true
% 1.17/1.01  --res_lit_sel                           adaptive
% 1.17/1.01  --res_lit_sel_side                      none
% 1.17/1.01  --res_ordering                          kbo
% 1.17/1.01  --res_to_prop_solver                    active
% 1.17/1.01  --res_prop_simpl_new                    false
% 1.17/1.01  --res_prop_simpl_given                  true
% 1.17/1.01  --res_passive_queue_type                priority_queues
% 1.17/1.01  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.17/1.01  --res_passive_queues_freq               [15;5]
% 1.17/1.01  --res_forward_subs                      full
% 1.17/1.01  --res_backward_subs                     full
% 1.17/1.01  --res_forward_subs_resolution           true
% 1.17/1.01  --res_backward_subs_resolution          true
% 1.17/1.01  --res_orphan_elimination                true
% 1.17/1.01  --res_time_limit                        2.
% 1.17/1.01  --res_out_proof                         true
% 1.17/1.01  
% 1.17/1.01  ------ Superposition Options
% 1.17/1.01  
% 1.17/1.01  --superposition_flag                    true
% 1.17/1.01  --sup_passive_queue_type                priority_queues
% 1.17/1.01  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.17/1.01  --sup_passive_queues_freq               [8;1;4]
% 1.17/1.01  --demod_completeness_check              fast
% 1.17/1.01  --demod_use_ground                      true
% 1.17/1.01  --sup_to_prop_solver                    passive
% 1.17/1.01  --sup_prop_simpl_new                    true
% 1.17/1.01  --sup_prop_simpl_given                  true
% 1.17/1.01  --sup_fun_splitting                     false
% 1.17/1.01  --sup_smt_interval                      50000
% 1.17/1.01  
% 1.17/1.01  ------ Superposition Simplification Setup
% 1.17/1.01  
% 1.17/1.01  --sup_indices_passive                   []
% 1.17/1.01  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.17/1.01  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.17/1.01  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.17/1.01  --sup_full_triv                         [TrivRules;PropSubs]
% 1.17/1.01  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.17/1.01  --sup_full_bw                           [BwDemod]
% 1.17/1.01  --sup_immed_triv                        [TrivRules]
% 1.17/1.01  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.17/1.01  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.17/1.01  --sup_immed_bw_main                     []
% 1.17/1.01  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.17/1.01  --sup_input_triv                        [Unflattening;TrivRules]
% 1.17/1.01  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.17/1.01  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.17/1.01  
% 1.17/1.01  ------ Combination Options
% 1.17/1.01  
% 1.17/1.01  --comb_res_mult                         3
% 1.17/1.01  --comb_sup_mult                         2
% 1.17/1.01  --comb_inst_mult                        10
% 1.17/1.01  
% 1.17/1.01  ------ Debug Options
% 1.17/1.01  
% 1.17/1.01  --dbg_backtrace                         false
% 1.17/1.01  --dbg_dump_prop_clauses                 false
% 1.17/1.01  --dbg_dump_prop_clauses_file            -
% 1.17/1.01  --dbg_out_stat                          false
% 1.17/1.01  ------ Parsing...
% 1.17/1.01  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 1.17/1.01  
% 1.17/1.01  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe:8:0s pe_e  sf_s  rm: 10 0s  sf_e  pe_s  pe_e 
% 1.17/1.01  
% 1.17/1.01  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 1.17/1.01  
% 1.17/1.01  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 1.17/1.01  ------ Proving...
% 1.17/1.01  ------ Problem Properties 
% 1.17/1.01  
% 1.17/1.01  
% 1.17/1.01  clauses                                 6
% 1.17/1.01  conjectures                             0
% 1.17/1.01  EPR                                     0
% 1.17/1.01  Horn                                    5
% 1.17/1.01  unary                                   2
% 1.17/1.01  binary                                  2
% 1.17/1.01  lits                                    12
% 1.17/1.01  lits eq                                 2
% 1.17/1.01  fd_pure                                 0
% 1.17/1.01  fd_pseudo                               0
% 1.17/1.01  fd_cond                                 0
% 1.17/1.01  fd_pseudo_cond                          0
% 1.17/1.01  AC symbols                              0
% 1.17/1.01  
% 1.17/1.01  ------ Schedule dynamic 5 is on 
% 1.17/1.01  
% 1.17/1.01  ------ no conjectures: strip conj schedule 
% 1.17/1.01  
% 1.17/1.01  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" stripped conjectures Time Limit: 10.
% 1.17/1.01  
% 1.17/1.01  
% 1.17/1.01  ------ 
% 1.17/1.01  Current options:
% 1.17/1.01  ------ 
% 1.17/1.01  
% 1.17/1.01  ------ Input Options
% 1.17/1.01  
% 1.17/1.01  --out_options                           all
% 1.17/1.01  --tptp_safe_out                         true
% 1.17/1.01  --problem_path                          ""
% 1.17/1.01  --include_path                          ""
% 1.17/1.01  --clausifier                            res/vclausify_rel
% 1.17/1.01  --clausifier_options                    --mode clausify
% 1.17/1.01  --stdin                                 false
% 1.17/1.01  --stats_out                             all
% 1.17/1.01  
% 1.17/1.01  ------ General Options
% 1.17/1.01  
% 1.17/1.01  --fof                                   false
% 1.17/1.01  --time_out_real                         305.
% 1.17/1.01  --time_out_virtual                      -1.
% 1.17/1.01  --symbol_type_check                     false
% 1.17/1.01  --clausify_out                          false
% 1.17/1.01  --sig_cnt_out                           false
% 1.17/1.01  --trig_cnt_out                          false
% 1.17/1.01  --trig_cnt_out_tolerance                1.
% 1.17/1.01  --trig_cnt_out_sk_spl                   false
% 1.17/1.01  --abstr_cl_out                          false
% 1.17/1.01  
% 1.17/1.01  ------ Global Options
% 1.17/1.01  
% 1.17/1.01  --schedule                              default
% 1.17/1.01  --add_important_lit                     false
% 1.17/1.01  --prop_solver_per_cl                    1000
% 1.17/1.01  --min_unsat_core                        false
% 1.17/1.01  --soft_assumptions                      false
% 1.17/1.01  --soft_lemma_size                       3
% 1.17/1.01  --prop_impl_unit_size                   0
% 1.17/1.01  --prop_impl_unit                        []
% 1.17/1.01  --share_sel_clauses                     true
% 1.17/1.01  --reset_solvers                         false
% 1.17/1.01  --bc_imp_inh                            [conj_cone]
% 1.17/1.01  --conj_cone_tolerance                   3.
% 1.17/1.01  --extra_neg_conj                        none
% 1.17/1.01  --large_theory_mode                     true
% 1.17/1.01  --prolific_symb_bound                   200
% 1.17/1.01  --lt_threshold                          2000
% 1.17/1.01  --clause_weak_htbl                      true
% 1.17/1.01  --gc_record_bc_elim                     false
% 1.17/1.01  
% 1.17/1.01  ------ Preprocessing Options
% 1.17/1.01  
% 1.17/1.01  --preprocessing_flag                    true
% 1.17/1.01  --time_out_prep_mult                    0.1
% 1.17/1.01  --splitting_mode                        input
% 1.17/1.01  --splitting_grd                         true
% 1.17/1.01  --splitting_cvd                         false
% 1.17/1.01  --splitting_cvd_svl                     false
% 1.17/1.01  --splitting_nvd                         32
% 1.17/1.01  --sub_typing                            true
% 1.17/1.01  --prep_gs_sim                           true
% 1.17/1.01  --prep_unflatten                        true
% 1.17/1.01  --prep_res_sim                          true
% 1.17/1.01  --prep_upred                            true
% 1.17/1.01  --prep_sem_filter                       exhaustive
% 1.17/1.01  --prep_sem_filter_out                   false
% 1.17/1.01  --pred_elim                             true
% 1.17/1.01  --res_sim_input                         true
% 1.17/1.01  --eq_ax_congr_red                       true
% 1.17/1.01  --pure_diseq_elim                       true
% 1.17/1.01  --brand_transform                       false
% 1.17/1.01  --non_eq_to_eq                          false
% 1.17/1.01  --prep_def_merge                        true
% 1.17/1.01  --prep_def_merge_prop_impl              false
% 1.17/1.01  --prep_def_merge_mbd                    true
% 1.17/1.01  --prep_def_merge_tr_red                 false
% 1.17/1.01  --prep_def_merge_tr_cl                  false
% 1.17/1.01  --smt_preprocessing                     true
% 1.17/1.01  --smt_ac_axioms                         fast
% 1.17/1.01  --preprocessed_out                      false
% 1.17/1.01  --preprocessed_stats                    false
% 1.17/1.01  
% 1.17/1.01  ------ Abstraction refinement Options
% 1.17/1.01  
% 1.17/1.01  --abstr_ref                             []
% 1.17/1.01  --abstr_ref_prep                        false
% 1.17/1.01  --abstr_ref_until_sat                   false
% 1.17/1.01  --abstr_ref_sig_restrict                funpre
% 1.17/1.01  --abstr_ref_af_restrict_to_split_sk     false
% 1.17/1.01  --abstr_ref_under                       []
% 1.17/1.01  
% 1.17/1.01  ------ SAT Options
% 1.17/1.01  
% 1.17/1.01  --sat_mode                              false
% 1.17/1.01  --sat_fm_restart_options                ""
% 1.17/1.01  --sat_gr_def                            false
% 1.17/1.01  --sat_epr_types                         true
% 1.17/1.01  --sat_non_cyclic_types                  false
% 1.17/1.01  --sat_finite_models                     false
% 1.17/1.01  --sat_fm_lemmas                         false
% 1.17/1.01  --sat_fm_prep                           false
% 1.17/1.01  --sat_fm_uc_incr                        true
% 1.17/1.01  --sat_out_model                         small
% 1.17/1.01  --sat_out_clauses                       false
% 1.17/1.01  
% 1.17/1.01  ------ QBF Options
% 1.17/1.01  
% 1.17/1.01  --qbf_mode                              false
% 1.17/1.01  --qbf_elim_univ                         false
% 1.17/1.01  --qbf_dom_inst                          none
% 1.17/1.01  --qbf_dom_pre_inst                      false
% 1.17/1.01  --qbf_sk_in                             false
% 1.17/1.01  --qbf_pred_elim                         true
% 1.17/1.01  --qbf_split                             512
% 1.17/1.01  
% 1.17/1.01  ------ BMC1 Options
% 1.17/1.01  
% 1.17/1.01  --bmc1_incremental                      false
% 1.17/1.01  --bmc1_axioms                           reachable_all
% 1.17/1.01  --bmc1_min_bound                        0
% 1.17/1.01  --bmc1_max_bound                        -1
% 1.17/1.01  --bmc1_max_bound_default                -1
% 1.17/1.01  --bmc1_symbol_reachability              true
% 1.17/1.01  --bmc1_property_lemmas                  false
% 1.17/1.01  --bmc1_k_induction                      false
% 1.17/1.01  --bmc1_non_equiv_states                 false
% 1.17/1.01  --bmc1_deadlock                         false
% 1.17/1.01  --bmc1_ucm                              false
% 1.17/1.01  --bmc1_add_unsat_core                   none
% 1.17/1.01  --bmc1_unsat_core_children              false
% 1.17/1.01  --bmc1_unsat_core_extrapolate_axioms    false
% 1.17/1.01  --bmc1_out_stat                         full
% 1.17/1.01  --bmc1_ground_init                      false
% 1.17/1.01  --bmc1_pre_inst_next_state              false
% 1.17/1.01  --bmc1_pre_inst_state                   false
% 1.17/1.01  --bmc1_pre_inst_reach_state             false
% 1.17/1.01  --bmc1_out_unsat_core                   false
% 1.17/1.01  --bmc1_aig_witness_out                  false
% 1.17/1.01  --bmc1_verbose                          false
% 1.17/1.01  --bmc1_dump_clauses_tptp                false
% 1.17/1.01  --bmc1_dump_unsat_core_tptp             false
% 1.17/1.01  --bmc1_dump_file                        -
% 1.17/1.01  --bmc1_ucm_expand_uc_limit              128
% 1.17/1.01  --bmc1_ucm_n_expand_iterations          6
% 1.17/1.01  --bmc1_ucm_extend_mode                  1
% 1.17/1.01  --bmc1_ucm_init_mode                    2
% 1.17/1.01  --bmc1_ucm_cone_mode                    none
% 1.17/1.01  --bmc1_ucm_reduced_relation_type        0
% 1.17/1.01  --bmc1_ucm_relax_model                  4
% 1.17/1.01  --bmc1_ucm_full_tr_after_sat            true
% 1.17/1.01  --bmc1_ucm_expand_neg_assumptions       false
% 1.17/1.01  --bmc1_ucm_layered_model                none
% 1.17/1.01  --bmc1_ucm_max_lemma_size               10
% 1.17/1.01  
% 1.17/1.01  ------ AIG Options
% 1.17/1.01  
% 1.17/1.01  --aig_mode                              false
% 1.17/1.01  
% 1.17/1.01  ------ Instantiation Options
% 1.17/1.01  
% 1.17/1.01  --instantiation_flag                    true
% 1.17/1.01  --inst_sos_flag                         false
% 1.17/1.01  --inst_sos_phase                        true
% 1.17/1.01  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.17/1.01  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.17/1.01  --inst_lit_sel_side                     none
% 1.17/1.01  --inst_solver_per_active                1400
% 1.17/1.01  --inst_solver_calls_frac                1.
% 1.17/1.01  --inst_passive_queue_type               priority_queues
% 1.17/1.01  --inst_passive_queues                   [[-num_var];[+age;-num_symb]]
% 1.17/1.01  --inst_passive_queues_freq              [25;2]
% 1.17/1.01  --inst_dismatching                      true
% 1.17/1.01  --inst_eager_unprocessed_to_passive     true
% 1.17/1.01  --inst_prop_sim_given                   true
% 1.17/1.01  --inst_prop_sim_new                     false
% 1.17/1.01  --inst_subs_new                         false
% 1.17/1.01  --inst_eq_res_simp                      false
% 1.17/1.01  --inst_subs_given                       false
% 1.17/1.01  --inst_orphan_elimination               true
% 1.17/1.01  --inst_learning_loop_flag               true
% 1.17/1.01  --inst_learning_start                   3000
% 1.17/1.01  --inst_learning_factor                  2
% 1.17/1.01  --inst_start_prop_sim_after_learn       3
% 1.17/1.01  --inst_sel_renew                        solver
% 1.17/1.01  --inst_lit_activity_flag                true
% 1.17/1.01  --inst_restr_to_given                   false
% 1.17/1.01  --inst_activity_threshold               500
% 1.17/1.01  --inst_out_proof                        true
% 1.17/1.01  
% 1.17/1.01  ------ Resolution Options
% 1.17/1.01  
% 1.17/1.01  --resolution_flag                       false
% 1.17/1.01  --res_lit_sel                           adaptive
% 1.17/1.01  --res_lit_sel_side                      none
% 1.17/1.01  --res_ordering                          kbo
% 1.17/1.01  --res_to_prop_solver                    active
% 1.17/1.01  --res_prop_simpl_new                    false
% 1.17/1.01  --res_prop_simpl_given                  true
% 1.17/1.01  --res_passive_queue_type                priority_queues
% 1.17/1.01  --res_passive_queues                    [[-num_symb];[+age;-num_symb]]
% 1.17/1.01  --res_passive_queues_freq               [15;5]
% 1.17/1.01  --res_forward_subs                      full
% 1.17/1.01  --res_backward_subs                     full
% 1.17/1.01  --res_forward_subs_resolution           true
% 1.17/1.01  --res_backward_subs_resolution          true
% 1.17/1.01  --res_orphan_elimination                true
% 1.17/1.01  --res_time_limit                        2.
% 1.17/1.01  --res_out_proof                         true
% 1.17/1.01  
% 1.17/1.01  ------ Superposition Options
% 1.17/1.01  
% 1.17/1.01  --superposition_flag                    true
% 1.17/1.01  --sup_passive_queue_type                priority_queues
% 1.17/1.01  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.17/1.01  --sup_passive_queues_freq               [8;1;4]
% 1.17/1.01  --demod_completeness_check              fast
% 1.17/1.01  --demod_use_ground                      true
% 1.17/1.01  --sup_to_prop_solver                    passive
% 1.17/1.01  --sup_prop_simpl_new                    true
% 1.17/1.01  --sup_prop_simpl_given                  true
% 1.17/1.01  --sup_fun_splitting                     false
% 1.17/1.01  --sup_smt_interval                      50000
% 1.17/1.01  
% 1.17/1.01  ------ Superposition Simplification Setup
% 1.17/1.01  
% 1.17/1.01  --sup_indices_passive                   []
% 1.17/1.01  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.17/1.01  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.17/1.01  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.17/1.01  --sup_full_triv                         [TrivRules;PropSubs]
% 1.17/1.01  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.17/1.01  --sup_full_bw                           [BwDemod]
% 1.17/1.01  --sup_immed_triv                        [TrivRules]
% 1.17/1.01  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.17/1.01  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.17/1.01  --sup_immed_bw_main                     []
% 1.17/1.01  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.17/1.01  --sup_input_triv                        [Unflattening;TrivRules]
% 1.17/1.01  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.17/1.01  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.17/1.01  
% 1.17/1.01  ------ Combination Options
% 1.17/1.01  
% 1.17/1.01  --comb_res_mult                         3
% 1.17/1.01  --comb_sup_mult                         2
% 1.17/1.01  --comb_inst_mult                        10
% 1.17/1.01  
% 1.17/1.01  ------ Debug Options
% 1.17/1.01  
% 1.17/1.01  --dbg_backtrace                         false
% 1.17/1.01  --dbg_dump_prop_clauses                 false
% 1.17/1.01  --dbg_dump_prop_clauses_file            -
% 1.17/1.01  --dbg_out_stat                          false
% 1.17/1.01  
% 1.17/1.01  
% 1.17/1.01  
% 1.17/1.01  
% 1.17/1.01  ------ Proving...
% 1.17/1.01  
% 1.17/1.01  
% 1.17/1.01  % SZS status Theorem for theBenchmark.p
% 1.17/1.01  
% 1.17/1.01  % SZS output start CNFRefutation for theBenchmark.p
% 1.17/1.01  
% 1.17/1.01  fof(f4,axiom,(
% 1.17/1.01    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_waybel_0(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : (r1_waybel_0(X0,X1,X2) <=> ? [X3] : (! [X4] : (m1_subset_1(X4,u1_struct_0(X1)) => (r1_orders_2(X1,X3,X4) => r2_hidden(k2_waybel_0(X0,X1,X4),X2))) & m1_subset_1(X3,u1_struct_0(X1))))))),
% 1.17/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.17/1.01  
% 1.17/1.01  fof(f14,plain,(
% 1.17/1.01    ! [X0] : (! [X1] : (! [X2] : (r1_waybel_0(X0,X1,X2) <=> ? [X3] : (! [X4] : ((r2_hidden(k2_waybel_0(X0,X1,X4),X2) | ~r1_orders_2(X1,X3,X4)) | ~m1_subset_1(X4,u1_struct_0(X1))) & m1_subset_1(X3,u1_struct_0(X1)))) | (~l1_waybel_0(X1,X0) | v2_struct_0(X1))) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 1.17/1.01    inference(ennf_transformation,[],[f4])).
% 1.17/1.01  
% 1.17/1.01  fof(f15,plain,(
% 1.17/1.01    ! [X0] : (! [X1] : (! [X2] : (r1_waybel_0(X0,X1,X2) <=> ? [X3] : (! [X4] : (r2_hidden(k2_waybel_0(X0,X1,X4),X2) | ~r1_orders_2(X1,X3,X4) | ~m1_subset_1(X4,u1_struct_0(X1))) & m1_subset_1(X3,u1_struct_0(X1)))) | ~l1_waybel_0(X1,X0) | v2_struct_0(X1)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 1.17/1.01    inference(flattening,[],[f14])).
% 1.17/1.01  
% 1.17/1.01  fof(f26,plain,(
% 1.17/1.01    ! [X0] : (! [X1] : (! [X2] : ((r1_waybel_0(X0,X1,X2) | ! [X3] : (? [X4] : (~r2_hidden(k2_waybel_0(X0,X1,X4),X2) & r1_orders_2(X1,X3,X4) & m1_subset_1(X4,u1_struct_0(X1))) | ~m1_subset_1(X3,u1_struct_0(X1)))) & (? [X3] : (! [X4] : (r2_hidden(k2_waybel_0(X0,X1,X4),X2) | ~r1_orders_2(X1,X3,X4) | ~m1_subset_1(X4,u1_struct_0(X1))) & m1_subset_1(X3,u1_struct_0(X1))) | ~r1_waybel_0(X0,X1,X2))) | ~l1_waybel_0(X1,X0) | v2_struct_0(X1)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 1.17/1.01    inference(nnf_transformation,[],[f15])).
% 1.17/1.01  
% 1.17/1.01  fof(f27,plain,(
% 1.17/1.01    ! [X0] : (! [X1] : (! [X2] : ((r1_waybel_0(X0,X1,X2) | ! [X3] : (? [X4] : (~r2_hidden(k2_waybel_0(X0,X1,X4),X2) & r1_orders_2(X1,X3,X4) & m1_subset_1(X4,u1_struct_0(X1))) | ~m1_subset_1(X3,u1_struct_0(X1)))) & (? [X5] : (! [X6] : (r2_hidden(k2_waybel_0(X0,X1,X6),X2) | ~r1_orders_2(X1,X5,X6) | ~m1_subset_1(X6,u1_struct_0(X1))) & m1_subset_1(X5,u1_struct_0(X1))) | ~r1_waybel_0(X0,X1,X2))) | ~l1_waybel_0(X1,X0) | v2_struct_0(X1)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 1.17/1.01    inference(rectify,[],[f26])).
% 1.17/1.01  
% 1.17/1.01  fof(f29,plain,(
% 1.17/1.01    ! [X2,X1,X0] : (? [X5] : (! [X6] : (r2_hidden(k2_waybel_0(X0,X1,X6),X2) | ~r1_orders_2(X1,X5,X6) | ~m1_subset_1(X6,u1_struct_0(X1))) & m1_subset_1(X5,u1_struct_0(X1))) => (! [X6] : (r2_hidden(k2_waybel_0(X0,X1,X6),X2) | ~r1_orders_2(X1,sK2(X0,X1,X2),X6) | ~m1_subset_1(X6,u1_struct_0(X1))) & m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X1))))),
% 1.17/1.01    introduced(choice_axiom,[])).
% 1.17/1.01  
% 1.17/1.01  fof(f28,plain,(
% 1.17/1.01    ! [X3,X2,X1,X0] : (? [X4] : (~r2_hidden(k2_waybel_0(X0,X1,X4),X2) & r1_orders_2(X1,X3,X4) & m1_subset_1(X4,u1_struct_0(X1))) => (~r2_hidden(k2_waybel_0(X0,X1,sK1(X0,X1,X2,X3)),X2) & r1_orders_2(X1,X3,sK1(X0,X1,X2,X3)) & m1_subset_1(sK1(X0,X1,X2,X3),u1_struct_0(X1))))),
% 1.17/1.01    introduced(choice_axiom,[])).
% 1.17/1.01  
% 1.17/1.01  fof(f30,plain,(
% 1.17/1.01    ! [X0] : (! [X1] : (! [X2] : ((r1_waybel_0(X0,X1,X2) | ! [X3] : ((~r2_hidden(k2_waybel_0(X0,X1,sK1(X0,X1,X2,X3)),X2) & r1_orders_2(X1,X3,sK1(X0,X1,X2,X3)) & m1_subset_1(sK1(X0,X1,X2,X3),u1_struct_0(X1))) | ~m1_subset_1(X3,u1_struct_0(X1)))) & ((! [X6] : (r2_hidden(k2_waybel_0(X0,X1,X6),X2) | ~r1_orders_2(X1,sK2(X0,X1,X2),X6) | ~m1_subset_1(X6,u1_struct_0(X1))) & m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X1))) | ~r1_waybel_0(X0,X1,X2))) | ~l1_waybel_0(X1,X0) | v2_struct_0(X1)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 1.17/1.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f27,f29,f28])).
% 1.17/1.01  
% 1.17/1.01  fof(f42,plain,(
% 1.17/1.01    ( ! [X2,X0,X3,X1] : (r1_waybel_0(X0,X1,X2) | ~r2_hidden(k2_waybel_0(X0,X1,sK1(X0,X1,X2,X3)),X2) | ~m1_subset_1(X3,u1_struct_0(X1)) | ~l1_waybel_0(X1,X0) | v2_struct_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 1.17/1.01    inference(cnf_transformation,[],[f30])).
% 1.17/1.01  
% 1.17/1.01  fof(f9,conjecture,(
% 1.17/1.01    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_waybel_0(X1,X0) & ~v2_struct_0(X1)) => r1_waybel_0(X0,X1,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)))))),
% 1.17/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.17/1.01  
% 1.17/1.01  fof(f10,negated_conjecture,(
% 1.17/1.01    ~! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_waybel_0(X1,X0) & ~v2_struct_0(X1)) => r1_waybel_0(X0,X1,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)))))),
% 1.17/1.01    inference(negated_conjecture,[],[f9])).
% 1.17/1.01  
% 1.17/1.01  fof(f22,plain,(
% 1.17/1.01    ? [X0] : (? [X1] : (~r1_waybel_0(X0,X1,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1))) & (l1_waybel_0(X1,X0) & ~v2_struct_0(X1))) & (l1_struct_0(X0) & ~v2_struct_0(X0)))),
% 1.17/1.01    inference(ennf_transformation,[],[f10])).
% 1.17/1.01  
% 1.17/1.01  fof(f23,plain,(
% 1.17/1.01    ? [X0] : (? [X1] : (~r1_waybel_0(X0,X1,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1))) & l1_waybel_0(X1,X0) & ~v2_struct_0(X1)) & l1_struct_0(X0) & ~v2_struct_0(X0))),
% 1.17/1.01    inference(flattening,[],[f22])).
% 1.17/1.01  
% 1.17/1.01  fof(f33,plain,(
% 1.17/1.01    ( ! [X0] : (? [X1] : (~r1_waybel_0(X0,X1,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1))) & l1_waybel_0(X1,X0) & ~v2_struct_0(X1)) => (~r1_waybel_0(X0,sK4,k2_relset_1(u1_struct_0(sK4),u1_struct_0(X0),u1_waybel_0(X0,sK4))) & l1_waybel_0(sK4,X0) & ~v2_struct_0(sK4))) )),
% 1.17/1.01    introduced(choice_axiom,[])).
% 1.17/1.01  
% 1.17/1.01  fof(f32,plain,(
% 1.17/1.01    ? [X0] : (? [X1] : (~r1_waybel_0(X0,X1,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1))) & l1_waybel_0(X1,X0) & ~v2_struct_0(X1)) & l1_struct_0(X0) & ~v2_struct_0(X0)) => (? [X1] : (~r1_waybel_0(sK3,X1,k2_relset_1(u1_struct_0(X1),u1_struct_0(sK3),u1_waybel_0(sK3,X1))) & l1_waybel_0(X1,sK3) & ~v2_struct_0(X1)) & l1_struct_0(sK3) & ~v2_struct_0(sK3))),
% 1.17/1.01    introduced(choice_axiom,[])).
% 1.17/1.01  
% 1.17/1.01  fof(f34,plain,(
% 1.17/1.01    (~r1_waybel_0(sK3,sK4,k2_relset_1(u1_struct_0(sK4),u1_struct_0(sK3),u1_waybel_0(sK3,sK4))) & l1_waybel_0(sK4,sK3) & ~v2_struct_0(sK4)) & l1_struct_0(sK3) & ~v2_struct_0(sK3)),
% 1.17/1.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f23,f33,f32])).
% 1.17/1.01  
% 1.17/1.01  fof(f53,plain,(
% 1.17/1.01    l1_waybel_0(sK4,sK3)),
% 1.17/1.01    inference(cnf_transformation,[],[f34])).
% 1.17/1.01  
% 1.17/1.01  fof(f50,plain,(
% 1.17/1.01    ~v2_struct_0(sK3)),
% 1.17/1.01    inference(cnf_transformation,[],[f34])).
% 1.17/1.01  
% 1.17/1.01  fof(f51,plain,(
% 1.17/1.01    l1_struct_0(sK3)),
% 1.17/1.01    inference(cnf_transformation,[],[f34])).
% 1.17/1.01  
% 1.17/1.01  fof(f52,plain,(
% 1.17/1.01    ~v2_struct_0(sK4)),
% 1.17/1.01    inference(cnf_transformation,[],[f34])).
% 1.17/1.01  
% 1.17/1.01  fof(f8,axiom,(
% 1.17/1.01    ! [X0] : (l1_struct_0(X0) => (v2_struct_0(X0) <=> v1_xboole_0(u1_struct_0(X0))))),
% 1.17/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.17/1.01  
% 1.17/1.01  fof(f21,plain,(
% 1.17/1.01    ! [X0] : ((v2_struct_0(X0) <=> v1_xboole_0(u1_struct_0(X0))) | ~l1_struct_0(X0))),
% 1.17/1.01    inference(ennf_transformation,[],[f8])).
% 1.17/1.01  
% 1.17/1.01  fof(f31,plain,(
% 1.17/1.01    ! [X0] : (((v2_struct_0(X0) | ~v1_xboole_0(u1_struct_0(X0))) & (v1_xboole_0(u1_struct_0(X0)) | ~v2_struct_0(X0))) | ~l1_struct_0(X0))),
% 1.17/1.01    inference(nnf_transformation,[],[f21])).
% 1.17/1.01  
% 1.17/1.01  fof(f49,plain,(
% 1.17/1.01    ( ! [X0] : (v2_struct_0(X0) | ~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0)) )),
% 1.17/1.01    inference(cnf_transformation,[],[f31])).
% 1.17/1.01  
% 1.17/1.01  fof(f6,axiom,(
% 1.17/1.01    ! [X0] : (l1_struct_0(X0) => ! [X1] : (l1_waybel_0(X1,X0) => l1_orders_2(X1)))),
% 1.17/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.17/1.01  
% 1.17/1.01  fof(f18,plain,(
% 1.17/1.01    ! [X0] : (! [X1] : (l1_orders_2(X1) | ~l1_waybel_0(X1,X0)) | ~l1_struct_0(X0))),
% 1.17/1.01    inference(ennf_transformation,[],[f6])).
% 1.17/1.01  
% 1.17/1.01  fof(f44,plain,(
% 1.17/1.01    ( ! [X0,X1] : (l1_orders_2(X1) | ~l1_waybel_0(X1,X0) | ~l1_struct_0(X0)) )),
% 1.17/1.01    inference(cnf_transformation,[],[f18])).
% 1.17/1.01  
% 1.17/1.01  fof(f3,axiom,(
% 1.17/1.01    ! [X0] : (l1_orders_2(X0) => l1_struct_0(X0))),
% 1.17/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.17/1.01  
% 1.17/1.01  fof(f13,plain,(
% 1.17/1.01    ! [X0] : (l1_struct_0(X0) | ~l1_orders_2(X0))),
% 1.17/1.01    inference(ennf_transformation,[],[f3])).
% 1.17/1.01  
% 1.17/1.01  fof(f37,plain,(
% 1.17/1.01    ( ! [X0] : (l1_struct_0(X0) | ~l1_orders_2(X0)) )),
% 1.17/1.01    inference(cnf_transformation,[],[f13])).
% 1.17/1.01  
% 1.17/1.01  fof(f2,axiom,(
% 1.17/1.01    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : (m1_subset_1(X2,X0) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => r2_hidden(k3_funct_2(X0,X1,X3,X2),k2_relset_1(X0,X1,X3))))))),
% 1.17/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.17/1.01  
% 1.17/1.01  fof(f11,plain,(
% 1.17/1.01    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (r2_hidden(k3_funct_2(X0,X1,X3,X2),k2_relset_1(X0,X1,X3)) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3))) | ~m1_subset_1(X2,X0)) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 1.17/1.01    inference(ennf_transformation,[],[f2])).
% 1.17/1.01  
% 1.17/1.01  fof(f12,plain,(
% 1.17/1.01    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (r2_hidden(k3_funct_2(X0,X1,X3,X2),k2_relset_1(X0,X1,X3)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,X0)) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 1.17/1.01    inference(flattening,[],[f11])).
% 1.17/1.01  
% 1.17/1.01  fof(f36,plain,(
% 1.17/1.01    ( ! [X2,X0,X3,X1] : (r2_hidden(k3_funct_2(X0,X1,X3,X2),k2_relset_1(X0,X1,X3)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,X0) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 1.17/1.01    inference(cnf_transformation,[],[f12])).
% 1.17/1.01  
% 1.17/1.01  fof(f7,axiom,(
% 1.17/1.01    ! [X0,X1] : ((l1_waybel_0(X1,X0) & l1_struct_0(X0)) => (m1_subset_1(u1_waybel_0(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(u1_waybel_0(X0,X1),u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(u1_waybel_0(X0,X1))))),
% 1.17/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.17/1.01  
% 1.17/1.01  fof(f19,plain,(
% 1.17/1.01    ! [X0,X1] : ((m1_subset_1(u1_waybel_0(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(u1_waybel_0(X0,X1),u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(u1_waybel_0(X0,X1))) | (~l1_waybel_0(X1,X0) | ~l1_struct_0(X0)))),
% 1.17/1.01    inference(ennf_transformation,[],[f7])).
% 1.17/1.01  
% 1.17/1.01  fof(f20,plain,(
% 1.17/1.01    ! [X0,X1] : ((m1_subset_1(u1_waybel_0(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(u1_waybel_0(X0,X1),u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(u1_waybel_0(X0,X1))) | ~l1_waybel_0(X1,X0) | ~l1_struct_0(X0))),
% 1.17/1.01    inference(flattening,[],[f19])).
% 1.17/1.01  
% 1.17/1.01  fof(f46,plain,(
% 1.17/1.01    ( ! [X0,X1] : (v1_funct_2(u1_waybel_0(X0,X1),u1_struct_0(X1),u1_struct_0(X0)) | ~l1_waybel_0(X1,X0) | ~l1_struct_0(X0)) )),
% 1.17/1.01    inference(cnf_transformation,[],[f20])).
% 1.17/1.01  
% 1.17/1.01  fof(f45,plain,(
% 1.17/1.01    ( ! [X0,X1] : (v1_funct_1(u1_waybel_0(X0,X1)) | ~l1_waybel_0(X1,X0) | ~l1_struct_0(X0)) )),
% 1.17/1.01    inference(cnf_transformation,[],[f20])).
% 1.17/1.01  
% 1.17/1.01  fof(f47,plain,(
% 1.17/1.01    ( ! [X0,X1] : (m1_subset_1(u1_waybel_0(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~l1_waybel_0(X1,X0) | ~l1_struct_0(X0)) )),
% 1.17/1.01    inference(cnf_transformation,[],[f20])).
% 1.17/1.01  
% 1.17/1.01  fof(f54,plain,(
% 1.17/1.01    ~r1_waybel_0(sK3,sK4,k2_relset_1(u1_struct_0(sK4),u1_struct_0(sK3),u1_waybel_0(sK3,sK4)))),
% 1.17/1.01    inference(cnf_transformation,[],[f34])).
% 1.17/1.01  
% 1.17/1.01  fof(f5,axiom,(
% 1.17/1.01    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_waybel_0(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X1)) => k3_funct_2(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1),X2) = k2_waybel_0(X0,X1,X2))))),
% 1.17/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.17/1.01  
% 1.17/1.01  fof(f16,plain,(
% 1.17/1.01    ! [X0] : (! [X1] : (! [X2] : (k3_funct_2(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1),X2) = k2_waybel_0(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X1))) | (~l1_waybel_0(X1,X0) | v2_struct_0(X1))) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 1.17/1.01    inference(ennf_transformation,[],[f5])).
% 1.17/1.01  
% 1.17/1.01  fof(f17,plain,(
% 1.17/1.01    ! [X0] : (! [X1] : (! [X2] : (k3_funct_2(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1),X2) = k2_waybel_0(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X1))) | ~l1_waybel_0(X1,X0) | v2_struct_0(X1)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 1.17/1.01    inference(flattening,[],[f16])).
% 1.17/1.01  
% 1.17/1.01  fof(f43,plain,(
% 1.17/1.01    ( ! [X2,X0,X1] : (k3_funct_2(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1),X2) = k2_waybel_0(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X1)) | ~l1_waybel_0(X1,X0) | v2_struct_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 1.17/1.01    inference(cnf_transformation,[],[f17])).
% 1.17/1.01  
% 1.17/1.01  fof(f40,plain,(
% 1.17/1.01    ( ! [X2,X0,X3,X1] : (r1_waybel_0(X0,X1,X2) | m1_subset_1(sK1(X0,X1,X2,X3),u1_struct_0(X1)) | ~m1_subset_1(X3,u1_struct_0(X1)) | ~l1_waybel_0(X1,X0) | v2_struct_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 1.17/1.01    inference(cnf_transformation,[],[f30])).
% 1.17/1.01  
% 1.17/1.01  fof(f1,axiom,(
% 1.17/1.01    ! [X0] : ? [X1] : m1_subset_1(X1,X0)),
% 1.17/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.17/1.01  
% 1.17/1.01  fof(f24,plain,(
% 1.17/1.01    ! [X0] : (? [X1] : m1_subset_1(X1,X0) => m1_subset_1(sK0(X0),X0))),
% 1.17/1.01    introduced(choice_axiom,[])).
% 1.17/1.01  
% 1.17/1.01  fof(f25,plain,(
% 1.17/1.01    ! [X0] : m1_subset_1(sK0(X0),X0)),
% 1.17/1.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f1,f24])).
% 1.17/1.01  
% 1.17/1.01  fof(f35,plain,(
% 1.17/1.01    ( ! [X0] : (m1_subset_1(sK0(X0),X0)) )),
% 1.17/1.01    inference(cnf_transformation,[],[f25])).
% 1.17/1.01  
% 1.17/1.01  cnf(c_3,plain,
% 1.17/1.01      ( r1_waybel_0(X0,X1,X2)
% 1.17/1.01      | ~ l1_waybel_0(X1,X0)
% 1.17/1.01      | ~ r2_hidden(k2_waybel_0(X0,X1,sK1(X0,X1,X2,X3)),X2)
% 1.17/1.01      | ~ m1_subset_1(X3,u1_struct_0(X1))
% 1.17/1.01      | v2_struct_0(X0)
% 1.17/1.01      | v2_struct_0(X1)
% 1.17/1.01      | ~ l1_struct_0(X0) ),
% 1.17/1.01      inference(cnf_transformation,[],[f42]) ).
% 1.17/1.01  
% 1.17/1.01  cnf(c_16,negated_conjecture,
% 1.17/1.01      ( l1_waybel_0(sK4,sK3) ),
% 1.17/1.01      inference(cnf_transformation,[],[f53]) ).
% 1.17/1.01  
% 1.17/1.01  cnf(c_448,plain,
% 1.17/1.01      ( r1_waybel_0(X0,X1,X2)
% 1.17/1.01      | ~ r2_hidden(k2_waybel_0(X0,X1,sK1(X0,X1,X2,X3)),X2)
% 1.17/1.01      | ~ m1_subset_1(X3,u1_struct_0(X1))
% 1.17/1.01      | v2_struct_0(X0)
% 1.17/1.01      | v2_struct_0(X1)
% 1.17/1.01      | ~ l1_struct_0(X0)
% 1.17/1.01      | sK4 != X1
% 1.17/1.01      | sK3 != X0 ),
% 1.17/1.01      inference(resolution_lifted,[status(thm)],[c_3,c_16]) ).
% 1.17/1.01  
% 1.17/1.01  cnf(c_449,plain,
% 1.17/1.01      ( r1_waybel_0(sK3,sK4,X0)
% 1.17/1.01      | ~ r2_hidden(k2_waybel_0(sK3,sK4,sK1(sK3,sK4,X0,X1)),X0)
% 1.17/1.01      | ~ m1_subset_1(X1,u1_struct_0(sK4))
% 1.17/1.01      | v2_struct_0(sK4)
% 1.17/1.01      | v2_struct_0(sK3)
% 1.17/1.01      | ~ l1_struct_0(sK3) ),
% 1.17/1.01      inference(unflattening,[status(thm)],[c_448]) ).
% 1.17/1.01  
% 1.17/1.01  cnf(c_19,negated_conjecture,
% 1.17/1.01      ( ~ v2_struct_0(sK3) ),
% 1.17/1.01      inference(cnf_transformation,[],[f50]) ).
% 1.17/1.01  
% 1.17/1.01  cnf(c_18,negated_conjecture,
% 1.17/1.01      ( l1_struct_0(sK3) ),
% 1.17/1.01      inference(cnf_transformation,[],[f51]) ).
% 1.17/1.01  
% 1.17/1.01  cnf(c_17,negated_conjecture,
% 1.17/1.01      ( ~ v2_struct_0(sK4) ),
% 1.17/1.01      inference(cnf_transformation,[],[f52]) ).
% 1.17/1.01  
% 1.17/1.01  cnf(c_453,plain,
% 1.17/1.01      ( ~ m1_subset_1(X1,u1_struct_0(sK4))
% 1.17/1.01      | ~ r2_hidden(k2_waybel_0(sK3,sK4,sK1(sK3,sK4,X0,X1)),X0)
% 1.17/1.01      | r1_waybel_0(sK3,sK4,X0) ),
% 1.17/1.01      inference(global_propositional_subsumption,
% 1.17/1.01                [status(thm)],
% 1.17/1.01                [c_449,c_19,c_18,c_17]) ).
% 1.17/1.01  
% 1.17/1.01  cnf(c_454,plain,
% 1.17/1.01      ( r1_waybel_0(sK3,sK4,X0)
% 1.17/1.01      | ~ r2_hidden(k2_waybel_0(sK3,sK4,sK1(sK3,sK4,X0,X1)),X0)
% 1.17/1.01      | ~ m1_subset_1(X1,u1_struct_0(sK4)) ),
% 1.17/1.01      inference(renaming,[status(thm)],[c_453]) ).
% 1.17/1.01  
% 1.17/1.01  cnf(c_13,plain,
% 1.17/1.01      ( v2_struct_0(X0)
% 1.17/1.01      | ~ l1_struct_0(X0)
% 1.17/1.01      | ~ v1_xboole_0(u1_struct_0(X0)) ),
% 1.17/1.01      inference(cnf_transformation,[],[f49]) ).
% 1.17/1.01  
% 1.17/1.01  cnf(c_9,plain,
% 1.17/1.01      ( ~ l1_waybel_0(X0,X1) | l1_orders_2(X0) | ~ l1_struct_0(X1) ),
% 1.17/1.01      inference(cnf_transformation,[],[f44]) ).
% 1.17/1.01  
% 1.17/1.01  cnf(c_2,plain,
% 1.17/1.01      ( ~ l1_orders_2(X0) | l1_struct_0(X0) ),
% 1.17/1.01      inference(cnf_transformation,[],[f37]) ).
% 1.17/1.01  
% 1.17/1.01  cnf(c_227,plain,
% 1.17/1.01      ( ~ l1_waybel_0(X0,X1) | ~ l1_struct_0(X1) | l1_struct_0(X0) ),
% 1.17/1.01      inference(resolution,[status(thm)],[c_9,c_2]) ).
% 1.17/1.01  
% 1.17/1.01  cnf(c_511,plain,
% 1.17/1.01      ( ~ l1_struct_0(X0) | l1_struct_0(X1) | sK4 != X1 | sK3 != X0 ),
% 1.17/1.01      inference(resolution_lifted,[status(thm)],[c_227,c_16]) ).
% 1.17/1.01  
% 1.17/1.01  cnf(c_512,plain,
% 1.17/1.01      ( l1_struct_0(sK4) | ~ l1_struct_0(sK3) ),
% 1.17/1.01      inference(unflattening,[status(thm)],[c_511]) ).
% 1.17/1.01  
% 1.17/1.01  cnf(c_514,plain,
% 1.17/1.01      ( l1_struct_0(sK4) ),
% 1.17/1.01      inference(global_propositional_subsumption,
% 1.17/1.01                [status(thm)],
% 1.17/1.01                [c_512,c_18]) ).
% 1.17/1.01  
% 1.17/1.01  cnf(c_672,plain,
% 1.17/1.01      ( v2_struct_0(X0) | ~ v1_xboole_0(u1_struct_0(X0)) | sK4 != X0 ),
% 1.17/1.01      inference(resolution_lifted,[status(thm)],[c_13,c_514]) ).
% 1.17/1.01  
% 1.17/1.01  cnf(c_673,plain,
% 1.17/1.01      ( v2_struct_0(sK4) | ~ v1_xboole_0(u1_struct_0(sK4)) ),
% 1.17/1.01      inference(unflattening,[status(thm)],[c_672]) ).
% 1.17/1.01  
% 1.17/1.01  cnf(c_675,plain,
% 1.17/1.01      ( ~ v1_xboole_0(u1_struct_0(sK4)) ),
% 1.17/1.01      inference(global_propositional_subsumption,
% 1.17/1.01                [status(thm)],
% 1.17/1.01                [c_673,c_17]) ).
% 1.17/1.01  
% 1.17/1.01  cnf(c_1,plain,
% 1.17/1.01      ( ~ v1_funct_2(X0,X1,X2)
% 1.17/1.01      | r2_hidden(k3_funct_2(X1,X2,X0,X3),k2_relset_1(X1,X2,X0))
% 1.17/1.01      | ~ m1_subset_1(X3,X1)
% 1.17/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 1.17/1.01      | v1_xboole_0(X1)
% 1.17/1.01      | v1_xboole_0(X2)
% 1.17/1.01      | ~ v1_funct_1(X0) ),
% 1.17/1.01      inference(cnf_transformation,[],[f36]) ).
% 1.17/1.01  
% 1.17/1.01  cnf(c_11,plain,
% 1.17/1.01      ( v1_funct_2(u1_waybel_0(X0,X1),u1_struct_0(X1),u1_struct_0(X0))
% 1.17/1.01      | ~ l1_waybel_0(X1,X0)
% 1.17/1.01      | ~ l1_struct_0(X0) ),
% 1.17/1.01      inference(cnf_transformation,[],[f46]) ).
% 1.17/1.01  
% 1.17/1.01  cnf(c_243,plain,
% 1.17/1.01      ( ~ l1_waybel_0(X0,X1)
% 1.17/1.01      | r2_hidden(k3_funct_2(X2,X3,X4,X5),k2_relset_1(X2,X3,X4))
% 1.17/1.01      | ~ m1_subset_1(X5,X2)
% 1.17/1.01      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
% 1.17/1.01      | ~ l1_struct_0(X1)
% 1.17/1.01      | v1_xboole_0(X2)
% 1.17/1.01      | v1_xboole_0(X3)
% 1.17/1.01      | ~ v1_funct_1(X4)
% 1.17/1.01      | u1_waybel_0(X1,X0) != X4
% 1.17/1.01      | u1_struct_0(X1) != X3
% 1.17/1.01      | u1_struct_0(X0) != X2 ),
% 1.17/1.01      inference(resolution_lifted,[status(thm)],[c_1,c_11]) ).
% 1.17/1.01  
% 1.17/1.01  cnf(c_244,plain,
% 1.17/1.01      ( ~ l1_waybel_0(X0,X1)
% 1.17/1.01      | r2_hidden(k3_funct_2(u1_struct_0(X0),u1_struct_0(X1),u1_waybel_0(X1,X0),X2),k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),u1_waybel_0(X1,X0)))
% 1.17/1.01      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 1.17/1.01      | ~ m1_subset_1(u1_waybel_0(X1,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 1.17/1.01      | ~ l1_struct_0(X1)
% 1.17/1.01      | v1_xboole_0(u1_struct_0(X0))
% 1.17/1.01      | v1_xboole_0(u1_struct_0(X1))
% 1.17/1.01      | ~ v1_funct_1(u1_waybel_0(X1,X0)) ),
% 1.17/1.01      inference(unflattening,[status(thm)],[c_243]) ).
% 1.17/1.01  
% 1.17/1.01  cnf(c_12,plain,
% 1.17/1.01      ( ~ l1_waybel_0(X0,X1)
% 1.17/1.01      | ~ l1_struct_0(X1)
% 1.17/1.01      | v1_funct_1(u1_waybel_0(X1,X0)) ),
% 1.17/1.01      inference(cnf_transformation,[],[f45]) ).
% 1.17/1.01  
% 1.17/1.01  cnf(c_10,plain,
% 1.17/1.01      ( ~ l1_waybel_0(X0,X1)
% 1.17/1.01      | m1_subset_1(u1_waybel_0(X1,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 1.17/1.01      | ~ l1_struct_0(X1) ),
% 1.17/1.01      inference(cnf_transformation,[],[f47]) ).
% 1.17/1.01  
% 1.17/1.01  cnf(c_248,plain,
% 1.17/1.01      ( v1_xboole_0(u1_struct_0(X1))
% 1.17/1.01      | v1_xboole_0(u1_struct_0(X0))
% 1.17/1.01      | ~ l1_struct_0(X1)
% 1.17/1.01      | ~ l1_waybel_0(X0,X1)
% 1.17/1.01      | r2_hidden(k3_funct_2(u1_struct_0(X0),u1_struct_0(X1),u1_waybel_0(X1,X0),X2),k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),u1_waybel_0(X1,X0)))
% 1.17/1.01      | ~ m1_subset_1(X2,u1_struct_0(X0)) ),
% 1.17/1.01      inference(global_propositional_subsumption,
% 1.17/1.01                [status(thm)],
% 1.17/1.01                [c_244,c_12,c_10]) ).
% 1.17/1.01  
% 1.17/1.01  cnf(c_249,plain,
% 1.17/1.01      ( ~ l1_waybel_0(X0,X1)
% 1.17/1.01      | r2_hidden(k3_funct_2(u1_struct_0(X0),u1_struct_0(X1),u1_waybel_0(X1,X0),X2),k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),u1_waybel_0(X1,X0)))
% 1.17/1.01      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 1.17/1.01      | ~ l1_struct_0(X1)
% 1.17/1.01      | v1_xboole_0(u1_struct_0(X0))
% 1.17/1.01      | v1_xboole_0(u1_struct_0(X1)) ),
% 1.17/1.01      inference(renaming,[status(thm)],[c_248]) ).
% 1.17/1.01  
% 1.17/1.01  cnf(c_490,plain,
% 1.17/1.01      ( r2_hidden(k3_funct_2(u1_struct_0(X0),u1_struct_0(X1),u1_waybel_0(X1,X0),X2),k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),u1_waybel_0(X1,X0)))
% 1.17/1.01      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 1.17/1.01      | ~ l1_struct_0(X1)
% 1.17/1.01      | v1_xboole_0(u1_struct_0(X0))
% 1.17/1.01      | v1_xboole_0(u1_struct_0(X1))
% 1.17/1.01      | sK4 != X0
% 1.17/1.01      | sK3 != X1 ),
% 1.17/1.01      inference(resolution_lifted,[status(thm)],[c_249,c_16]) ).
% 1.17/1.01  
% 1.17/1.01  cnf(c_491,plain,
% 1.17/1.01      ( r2_hidden(k3_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),u1_waybel_0(sK3,sK4),X0),k2_relset_1(u1_struct_0(sK4),u1_struct_0(sK3),u1_waybel_0(sK3,sK4)))
% 1.17/1.01      | ~ m1_subset_1(X0,u1_struct_0(sK4))
% 1.17/1.01      | ~ l1_struct_0(sK3)
% 1.17/1.01      | v1_xboole_0(u1_struct_0(sK4))
% 1.17/1.01      | v1_xboole_0(u1_struct_0(sK3)) ),
% 1.17/1.01      inference(unflattening,[status(thm)],[c_490]) ).
% 1.17/1.01  
% 1.17/1.01  cnf(c_27,plain,
% 1.17/1.01      ( v2_struct_0(sK3)
% 1.17/1.01      | ~ l1_struct_0(sK3)
% 1.17/1.01      | ~ v1_xboole_0(u1_struct_0(sK3)) ),
% 1.17/1.01      inference(instantiation,[status(thm)],[c_13]) ).
% 1.17/1.01  
% 1.17/1.01  cnf(c_495,plain,
% 1.17/1.01      ( v1_xboole_0(u1_struct_0(sK4))
% 1.17/1.01      | r2_hidden(k3_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),u1_waybel_0(sK3,sK4),X0),k2_relset_1(u1_struct_0(sK4),u1_struct_0(sK3),u1_waybel_0(sK3,sK4)))
% 1.17/1.01      | ~ m1_subset_1(X0,u1_struct_0(sK4)) ),
% 1.17/1.01      inference(global_propositional_subsumption,
% 1.17/1.01                [status(thm)],
% 1.17/1.01                [c_491,c_19,c_18,c_27]) ).
% 1.17/1.01  
% 1.17/1.01  cnf(c_496,plain,
% 1.17/1.01      ( r2_hidden(k3_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),u1_waybel_0(sK3,sK4),X0),k2_relset_1(u1_struct_0(sK4),u1_struct_0(sK3),u1_waybel_0(sK3,sK4)))
% 1.17/1.01      | ~ m1_subset_1(X0,u1_struct_0(sK4))
% 1.17/1.01      | v1_xboole_0(u1_struct_0(sK4)) ),
% 1.17/1.01      inference(renaming,[status(thm)],[c_495]) ).
% 1.17/1.01  
% 1.17/1.01  cnf(c_686,plain,
% 1.17/1.01      ( r2_hidden(k3_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),u1_waybel_0(sK3,sK4),X0),k2_relset_1(u1_struct_0(sK4),u1_struct_0(sK3),u1_waybel_0(sK3,sK4)))
% 1.17/1.01      | ~ m1_subset_1(X0,u1_struct_0(sK4)) ),
% 1.17/1.01      inference(backward_subsumption_resolution,
% 1.17/1.01                [status(thm)],
% 1.17/1.01                [c_675,c_496]) ).
% 1.17/1.01  
% 1.17/1.01  cnf(c_691,plain,
% 1.17/1.01      ( r1_waybel_0(sK3,sK4,X0)
% 1.17/1.01      | ~ m1_subset_1(X1,u1_struct_0(sK4))
% 1.17/1.01      | ~ m1_subset_1(X2,u1_struct_0(sK4))
% 1.17/1.01      | k3_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),u1_waybel_0(sK3,sK4),X2) != k2_waybel_0(sK3,sK4,sK1(sK3,sK4,X0,X1))
% 1.17/1.01      | k2_relset_1(u1_struct_0(sK4),u1_struct_0(sK3),u1_waybel_0(sK3,sK4)) != X0 ),
% 1.17/1.01      inference(resolution_lifted,[status(thm)],[c_454,c_686]) ).
% 1.17/1.01  
% 1.17/1.01  cnf(c_692,plain,
% 1.17/1.01      ( r1_waybel_0(sK3,sK4,k2_relset_1(u1_struct_0(sK4),u1_struct_0(sK3),u1_waybel_0(sK3,sK4)))
% 1.17/1.01      | ~ m1_subset_1(X0,u1_struct_0(sK4))
% 1.17/1.01      | ~ m1_subset_1(X1,u1_struct_0(sK4))
% 1.17/1.01      | k3_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),u1_waybel_0(sK3,sK4),X1) != k2_waybel_0(sK3,sK4,sK1(sK3,sK4,k2_relset_1(u1_struct_0(sK4),u1_struct_0(sK3),u1_waybel_0(sK3,sK4)),X0)) ),
% 1.17/1.01      inference(unflattening,[status(thm)],[c_691]) ).
% 1.17/1.01  
% 1.17/1.01  cnf(c_15,negated_conjecture,
% 1.17/1.01      ( ~ r1_waybel_0(sK3,sK4,k2_relset_1(u1_struct_0(sK4),u1_struct_0(sK3),u1_waybel_0(sK3,sK4))) ),
% 1.17/1.01      inference(cnf_transformation,[],[f54]) ).
% 1.17/1.01  
% 1.17/1.01  cnf(c_696,plain,
% 1.17/1.01      ( ~ m1_subset_1(X0,u1_struct_0(sK4))
% 1.17/1.01      | ~ m1_subset_1(X1,u1_struct_0(sK4))
% 1.17/1.01      | k3_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),u1_waybel_0(sK3,sK4),X1) != k2_waybel_0(sK3,sK4,sK1(sK3,sK4,k2_relset_1(u1_struct_0(sK4),u1_struct_0(sK3),u1_waybel_0(sK3,sK4)),X0)) ),
% 1.17/1.01      inference(global_propositional_subsumption,
% 1.17/1.01                [status(thm)],
% 1.17/1.01                [c_692,c_15]) ).
% 1.17/1.01  
% 1.17/1.01  cnf(c_697,plain,
% 1.17/1.01      ( ~ m1_subset_1(X0,u1_struct_0(sK4))
% 1.17/1.01      | ~ m1_subset_1(X1,u1_struct_0(sK4))
% 1.17/1.01      | k3_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),u1_waybel_0(sK3,sK4),X0) != k2_waybel_0(sK3,sK4,sK1(sK3,sK4,k2_relset_1(u1_struct_0(sK4),u1_struct_0(sK3),u1_waybel_0(sK3,sK4)),X1)) ),
% 1.17/1.01      inference(renaming,[status(thm)],[c_696]) ).
% 1.17/1.01  
% 1.17/1.01  cnf(c_804,plain,
% 1.17/1.01      ( ~ m1_subset_1(X0_51,u1_struct_0(sK4))
% 1.17/1.01      | ~ m1_subset_1(X1_51,u1_struct_0(sK4))
% 1.17/1.01      | k3_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),u1_waybel_0(sK3,sK4),X0_51) != k2_waybel_0(sK3,sK4,sK1(sK3,sK4,k2_relset_1(u1_struct_0(sK4),u1_struct_0(sK3),u1_waybel_0(sK3,sK4)),X1_51)) ),
% 1.17/1.01      inference(subtyping,[status(esa)],[c_697]) ).
% 1.17/1.01  
% 1.17/1.01  cnf(c_968,plain,
% 1.17/1.01      ( ~ m1_subset_1(X0_51,u1_struct_0(sK4))
% 1.17/1.01      | ~ m1_subset_1(sK1(sK3,sK4,k2_relset_1(u1_struct_0(sK4),u1_struct_0(sK3),u1_waybel_0(sK3,sK4)),sK0(u1_struct_0(sK4))),u1_struct_0(sK4))
% 1.17/1.01      | k3_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),u1_waybel_0(sK3,sK4),sK1(sK3,sK4,k2_relset_1(u1_struct_0(sK4),u1_struct_0(sK3),u1_waybel_0(sK3,sK4)),sK0(u1_struct_0(sK4)))) != k2_waybel_0(sK3,sK4,sK1(sK3,sK4,k2_relset_1(u1_struct_0(sK4),u1_struct_0(sK3),u1_waybel_0(sK3,sK4)),X0_51)) ),
% 1.17/1.01      inference(instantiation,[status(thm)],[c_804]) ).
% 1.17/1.01  
% 1.17/1.01  cnf(c_1053,plain,
% 1.17/1.01      ( ~ m1_subset_1(sK1(sK3,sK4,k2_relset_1(u1_struct_0(sK4),u1_struct_0(sK3),u1_waybel_0(sK3,sK4)),sK0(u1_struct_0(sK4))),u1_struct_0(sK4))
% 1.17/1.01      | ~ m1_subset_1(sK0(u1_struct_0(sK4)),u1_struct_0(sK4))
% 1.17/1.01      | k3_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),u1_waybel_0(sK3,sK4),sK1(sK3,sK4,k2_relset_1(u1_struct_0(sK4),u1_struct_0(sK3),u1_waybel_0(sK3,sK4)),sK0(u1_struct_0(sK4)))) != k2_waybel_0(sK3,sK4,sK1(sK3,sK4,k2_relset_1(u1_struct_0(sK4),u1_struct_0(sK3),u1_waybel_0(sK3,sK4)),sK0(u1_struct_0(sK4)))) ),
% 1.17/1.01      inference(instantiation,[status(thm)],[c_968]) ).
% 1.17/1.01  
% 1.17/1.01  cnf(c_8,plain,
% 1.17/1.01      ( ~ l1_waybel_0(X0,X1)
% 1.17/1.01      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 1.17/1.01      | v2_struct_0(X1)
% 1.17/1.01      | v2_struct_0(X0)
% 1.17/1.02      | ~ l1_struct_0(X1)
% 1.17/1.02      | k3_funct_2(u1_struct_0(X0),u1_struct_0(X1),u1_waybel_0(X1,X0),X2) = k2_waybel_0(X1,X0,X2) ),
% 1.17/1.02      inference(cnf_transformation,[],[f43]) ).
% 1.17/1.02  
% 1.17/1.02  cnf(c_533,plain,
% 1.17/1.02      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 1.17/1.02      | v2_struct_0(X1)
% 1.17/1.02      | v2_struct_0(X2)
% 1.17/1.02      | ~ l1_struct_0(X2)
% 1.17/1.02      | k3_funct_2(u1_struct_0(X1),u1_struct_0(X2),u1_waybel_0(X2,X1),X0) = k2_waybel_0(X2,X1,X0)
% 1.17/1.02      | sK4 != X1
% 1.17/1.02      | sK3 != X2 ),
% 1.17/1.02      inference(resolution_lifted,[status(thm)],[c_8,c_16]) ).
% 1.17/1.02  
% 1.17/1.02  cnf(c_534,plain,
% 1.17/1.02      ( ~ m1_subset_1(X0,u1_struct_0(sK4))
% 1.17/1.02      | v2_struct_0(sK4)
% 1.17/1.02      | v2_struct_0(sK3)
% 1.17/1.02      | ~ l1_struct_0(sK3)
% 1.17/1.02      | k3_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),u1_waybel_0(sK3,sK4),X0) = k2_waybel_0(sK3,sK4,X0) ),
% 1.17/1.02      inference(unflattening,[status(thm)],[c_533]) ).
% 1.17/1.02  
% 1.17/1.02  cnf(c_538,plain,
% 1.17/1.02      ( ~ m1_subset_1(X0,u1_struct_0(sK4))
% 1.17/1.02      | k3_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),u1_waybel_0(sK3,sK4),X0) = k2_waybel_0(sK3,sK4,X0) ),
% 1.17/1.02      inference(global_propositional_subsumption,
% 1.17/1.02                [status(thm)],
% 1.17/1.02                [c_534,c_19,c_18,c_17]) ).
% 1.17/1.02  
% 1.17/1.02  cnf(c_805,plain,
% 1.17/1.02      ( ~ m1_subset_1(X0_51,u1_struct_0(sK4))
% 1.17/1.02      | k3_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),u1_waybel_0(sK3,sK4),X0_51) = k2_waybel_0(sK3,sK4,X0_51) ),
% 1.17/1.02      inference(subtyping,[status(esa)],[c_538]) ).
% 1.17/1.02  
% 1.17/1.02  cnf(c_970,plain,
% 1.17/1.02      ( ~ m1_subset_1(sK1(sK3,sK4,k2_relset_1(u1_struct_0(sK4),u1_struct_0(sK3),u1_waybel_0(sK3,sK4)),sK0(u1_struct_0(sK4))),u1_struct_0(sK4))
% 1.17/1.02      | k3_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),u1_waybel_0(sK3,sK4),sK1(sK3,sK4,k2_relset_1(u1_struct_0(sK4),u1_struct_0(sK3),u1_waybel_0(sK3,sK4)),sK0(u1_struct_0(sK4)))) = k2_waybel_0(sK3,sK4,sK1(sK3,sK4,k2_relset_1(u1_struct_0(sK4),u1_struct_0(sK3),u1_waybel_0(sK3,sK4)),sK0(u1_struct_0(sK4)))) ),
% 1.17/1.02      inference(instantiation,[status(thm)],[c_805]) ).
% 1.17/1.02  
% 1.17/1.02  cnf(c_5,plain,
% 1.17/1.02      ( r1_waybel_0(X0,X1,X2)
% 1.17/1.02      | ~ l1_waybel_0(X1,X0)
% 1.17/1.02      | ~ m1_subset_1(X3,u1_struct_0(X1))
% 1.17/1.02      | m1_subset_1(sK1(X0,X1,X2,X3),u1_struct_0(X1))
% 1.17/1.02      | v2_struct_0(X0)
% 1.17/1.02      | v2_struct_0(X1)
% 1.17/1.02      | ~ l1_struct_0(X0) ),
% 1.17/1.02      inference(cnf_transformation,[],[f40]) ).
% 1.17/1.02  
% 1.17/1.02  cnf(c_427,plain,
% 1.17/1.02      ( r1_waybel_0(X0,X1,X2)
% 1.17/1.02      | ~ m1_subset_1(X3,u1_struct_0(X1))
% 1.17/1.02      | m1_subset_1(sK1(X0,X1,X2,X3),u1_struct_0(X1))
% 1.17/1.02      | v2_struct_0(X0)
% 1.17/1.02      | v2_struct_0(X1)
% 1.17/1.02      | ~ l1_struct_0(X0)
% 1.17/1.02      | sK4 != X1
% 1.17/1.02      | sK3 != X0 ),
% 1.17/1.02      inference(resolution_lifted,[status(thm)],[c_5,c_16]) ).
% 1.17/1.02  
% 1.17/1.02  cnf(c_428,plain,
% 1.17/1.02      ( r1_waybel_0(sK3,sK4,X0)
% 1.17/1.02      | ~ m1_subset_1(X1,u1_struct_0(sK4))
% 1.17/1.02      | m1_subset_1(sK1(sK3,sK4,X0,X1),u1_struct_0(sK4))
% 1.17/1.02      | v2_struct_0(sK4)
% 1.17/1.02      | v2_struct_0(sK3)
% 1.17/1.02      | ~ l1_struct_0(sK3) ),
% 1.17/1.02      inference(unflattening,[status(thm)],[c_427]) ).
% 1.17/1.02  
% 1.17/1.02  cnf(c_432,plain,
% 1.17/1.02      ( m1_subset_1(sK1(sK3,sK4,X0,X1),u1_struct_0(sK4))
% 1.17/1.02      | ~ m1_subset_1(X1,u1_struct_0(sK4))
% 1.17/1.02      | r1_waybel_0(sK3,sK4,X0) ),
% 1.17/1.02      inference(global_propositional_subsumption,
% 1.17/1.02                [status(thm)],
% 1.17/1.02                [c_428,c_19,c_18,c_17]) ).
% 1.17/1.02  
% 1.17/1.02  cnf(c_433,plain,
% 1.17/1.02      ( r1_waybel_0(sK3,sK4,X0)
% 1.17/1.02      | ~ m1_subset_1(X1,u1_struct_0(sK4))
% 1.17/1.02      | m1_subset_1(sK1(sK3,sK4,X0,X1),u1_struct_0(sK4)) ),
% 1.17/1.02      inference(renaming,[status(thm)],[c_432]) ).
% 1.17/1.02  
% 1.17/1.02  cnf(c_732,plain,
% 1.17/1.02      ( ~ m1_subset_1(X0,u1_struct_0(sK4))
% 1.17/1.02      | m1_subset_1(sK1(sK3,sK4,X1,X0),u1_struct_0(sK4))
% 1.17/1.02      | k2_relset_1(u1_struct_0(sK4),u1_struct_0(sK3),u1_waybel_0(sK3,sK4)) != X1
% 1.17/1.02      | sK4 != sK4
% 1.17/1.02      | sK3 != sK3 ),
% 1.17/1.02      inference(resolution_lifted,[status(thm)],[c_15,c_433]) ).
% 1.17/1.02  
% 1.17/1.02  cnf(c_733,plain,
% 1.17/1.02      ( ~ m1_subset_1(X0,u1_struct_0(sK4))
% 1.17/1.02      | m1_subset_1(sK1(sK3,sK4,k2_relset_1(u1_struct_0(sK4),u1_struct_0(sK3),u1_waybel_0(sK3,sK4)),X0),u1_struct_0(sK4)) ),
% 1.17/1.02      inference(unflattening,[status(thm)],[c_732]) ).
% 1.17/1.02  
% 1.17/1.02  cnf(c_802,plain,
% 1.17/1.02      ( ~ m1_subset_1(X0_51,u1_struct_0(sK4))
% 1.17/1.02      | m1_subset_1(sK1(sK3,sK4,k2_relset_1(u1_struct_0(sK4),u1_struct_0(sK3),u1_waybel_0(sK3,sK4)),X0_51),u1_struct_0(sK4)) ),
% 1.17/1.02      inference(subtyping,[status(esa)],[c_733]) ).
% 1.17/1.02  
% 1.17/1.02  cnf(c_943,plain,
% 1.17/1.02      ( m1_subset_1(sK1(sK3,sK4,k2_relset_1(u1_struct_0(sK4),u1_struct_0(sK3),u1_waybel_0(sK3,sK4)),sK0(u1_struct_0(sK4))),u1_struct_0(sK4))
% 1.17/1.02      | ~ m1_subset_1(sK0(u1_struct_0(sK4)),u1_struct_0(sK4)) ),
% 1.17/1.02      inference(instantiation,[status(thm)],[c_802]) ).
% 1.17/1.02  
% 1.17/1.02  cnf(c_0,plain,
% 1.17/1.02      ( m1_subset_1(sK0(X0),X0) ),
% 1.17/1.02      inference(cnf_transformation,[],[f35]) ).
% 1.17/1.02  
% 1.17/1.02  cnf(c_807,plain,
% 1.17/1.02      ( m1_subset_1(sK0(X0_52),X0_52) ),
% 1.17/1.02      inference(subtyping,[status(esa)],[c_0]) ).
% 1.17/1.02  
% 1.17/1.02  cnf(c_942,plain,
% 1.17/1.02      ( m1_subset_1(sK0(u1_struct_0(sK4)),u1_struct_0(sK4)) ),
% 1.17/1.02      inference(instantiation,[status(thm)],[c_807]) ).
% 1.17/1.02  
% 1.17/1.02  cnf(contradiction,plain,
% 1.17/1.02      ( $false ),
% 1.17/1.02      inference(minisat,[status(thm)],[c_1053,c_970,c_943,c_942]) ).
% 1.17/1.02  
% 1.17/1.02  
% 1.17/1.02  % SZS output end CNFRefutation for theBenchmark.p
% 1.17/1.02  
% 1.17/1.02  ------                               Statistics
% 1.17/1.02  
% 1.17/1.02  ------ General
% 1.17/1.02  
% 1.17/1.02  abstr_ref_over_cycles:                  0
% 1.17/1.02  abstr_ref_under_cycles:                 0
% 1.17/1.02  gc_basic_clause_elim:                   0
% 1.17/1.02  forced_gc_time:                         0
% 1.17/1.02  parsing_time:                           0.008
% 1.17/1.02  unif_index_cands_time:                  0.
% 1.17/1.02  unif_index_add_time:                    0.
% 1.17/1.02  orderings_time:                         0.
% 1.17/1.02  out_proof_time:                         0.009
% 1.17/1.02  total_time:                             0.051
% 1.17/1.02  num_of_symbols:                         57
% 1.17/1.02  num_of_terms:                           1509
% 1.17/1.02  
% 1.17/1.02  ------ Preprocessing
% 1.17/1.02  
% 1.17/1.02  num_of_splits:                          0
% 1.17/1.02  num_of_split_atoms:                     0
% 1.17/1.02  num_of_reused_defs:                     0
% 1.17/1.02  num_eq_ax_congr_red:                    43
% 1.17/1.02  num_of_sem_filtered_clauses:            1
% 1.17/1.02  num_of_subtypes:                        6
% 1.17/1.02  monotx_restored_types:                  0
% 1.17/1.02  sat_num_of_epr_types:                   0
% 1.17/1.02  sat_num_of_non_cyclic_types:            0
% 1.17/1.02  sat_guarded_non_collapsed_types:        0
% 1.17/1.02  num_pure_diseq_elim:                    0
% 1.17/1.02  simp_replaced_by:                       0
% 1.17/1.02  res_preprocessed:                       41
% 1.17/1.02  prep_upred:                             0
% 1.17/1.02  prep_unflattend:                        35
% 1.17/1.02  smt_new_axioms:                         0
% 1.17/1.02  pred_elim_cands:                        1
% 1.17/1.02  pred_elim:                              10
% 1.17/1.02  pred_elim_cl:                           14
% 1.17/1.02  pred_elim_cycles:                       15
% 1.17/1.02  merged_defs:                            0
% 1.17/1.02  merged_defs_ncl:                        0
% 1.17/1.02  bin_hyper_res:                          0
% 1.17/1.02  prep_cycles:                            4
% 1.17/1.02  pred_elim_time:                         0.008
% 1.17/1.02  splitting_time:                         0.
% 1.17/1.02  sem_filter_time:                        0.
% 1.17/1.02  monotx_time:                            0.
% 1.17/1.02  subtype_inf_time:                       0.
% 1.17/1.02  
% 1.17/1.02  ------ Problem properties
% 1.17/1.02  
% 1.17/1.02  clauses:                                6
% 1.17/1.02  conjectures:                            0
% 1.17/1.02  epr:                                    0
% 1.17/1.02  horn:                                   5
% 1.17/1.02  ground:                                 1
% 1.17/1.02  unary:                                  2
% 1.17/1.02  binary:                                 2
% 1.17/1.02  lits:                                   12
% 1.17/1.02  lits_eq:                                2
% 1.17/1.02  fd_pure:                                0
% 1.17/1.02  fd_pseudo:                              0
% 1.17/1.02  fd_cond:                                0
% 1.17/1.02  fd_pseudo_cond:                         0
% 1.17/1.02  ac_symbols:                             0
% 1.17/1.02  
% 1.17/1.02  ------ Propositional Solver
% 1.17/1.02  
% 1.17/1.02  prop_solver_calls:                      23
% 1.17/1.02  prop_fast_solver_calls:                 401
% 1.17/1.02  smt_solver_calls:                       0
% 1.17/1.02  smt_fast_solver_calls:                  0
% 1.17/1.02  prop_num_of_clauses:                    275
% 1.17/1.02  prop_preprocess_simplified:             1323
% 1.17/1.02  prop_fo_subsumed:                       29
% 1.17/1.02  prop_solver_time:                       0.
% 1.17/1.02  smt_solver_time:                        0.
% 1.17/1.02  smt_fast_solver_time:                   0.
% 1.17/1.02  prop_fast_solver_time:                  0.
% 1.17/1.02  prop_unsat_core_time:                   0.
% 1.17/1.02  
% 1.17/1.02  ------ QBF
% 1.17/1.02  
% 1.17/1.02  qbf_q_res:                              0
% 1.17/1.02  qbf_num_tautologies:                    0
% 1.17/1.02  qbf_prep_cycles:                        0
% 1.17/1.02  
% 1.17/1.02  ------ BMC1
% 1.17/1.02  
% 1.17/1.02  bmc1_current_bound:                     -1
% 1.17/1.02  bmc1_last_solved_bound:                 -1
% 1.17/1.02  bmc1_unsat_core_size:                   -1
% 1.17/1.02  bmc1_unsat_core_parents_size:           -1
% 1.17/1.02  bmc1_merge_next_fun:                    0
% 1.17/1.02  bmc1_unsat_core_clauses_time:           0.
% 1.17/1.02  
% 1.17/1.02  ------ Instantiation
% 1.17/1.02  
% 1.17/1.02  inst_num_of_clauses:                    29
% 1.17/1.02  inst_num_in_passive:                    1
% 1.17/1.02  inst_num_in_active:                     14
% 1.17/1.02  inst_num_in_unprocessed:                13
% 1.17/1.02  inst_num_of_loops:                      16
% 1.17/1.02  inst_num_of_learning_restarts:          0
% 1.17/1.02  inst_num_moves_active_passive:          0
% 1.17/1.02  inst_lit_activity:                      0
% 1.17/1.02  inst_lit_activity_moves:                0
% 1.17/1.02  inst_num_tautologies:                   0
% 1.17/1.02  inst_num_prop_implied:                  0
% 1.17/1.02  inst_num_existing_simplified:           0
% 1.17/1.02  inst_num_eq_res_simplified:             0
% 1.17/1.02  inst_num_child_elim:                    0
% 1.17/1.02  inst_num_of_dismatching_blockings:      0
% 1.17/1.02  inst_num_of_non_proper_insts:           9
% 1.17/1.02  inst_num_of_duplicates:                 0
% 1.17/1.02  inst_inst_num_from_inst_to_res:         0
% 1.17/1.02  inst_dismatching_checking_time:         0.
% 1.17/1.02  
% 1.17/1.02  ------ Resolution
% 1.17/1.02  
% 1.17/1.02  res_num_of_clauses:                     0
% 1.17/1.02  res_num_in_passive:                     0
% 1.17/1.02  res_num_in_active:                      0
% 1.17/1.02  res_num_of_loops:                       45
% 1.17/1.02  res_forward_subset_subsumed:            2
% 1.17/1.02  res_backward_subset_subsumed:           0
% 1.17/1.02  res_forward_subsumed:                   0
% 1.17/1.02  res_backward_subsumed:                  0
% 1.17/1.02  res_forward_subsumption_resolution:     0
% 1.17/1.02  res_backward_subsumption_resolution:    1
% 1.17/1.02  res_clause_to_clause_subsumption:       22
% 1.17/1.02  res_orphan_elimination:                 0
% 1.17/1.02  res_tautology_del:                      2
% 1.17/1.02  res_num_eq_res_simplified:              0
% 1.17/1.02  res_num_sel_changes:                    0
% 1.17/1.02  res_moves_from_active_to_pass:          0
% 1.17/1.02  
% 1.17/1.02  ------ Superposition
% 1.17/1.02  
% 1.17/1.02  sup_time_total:                         0.
% 1.17/1.02  sup_time_generating:                    0.
% 1.17/1.02  sup_time_sim_full:                      0.
% 1.17/1.02  sup_time_sim_immed:                     0.
% 1.17/1.02  
% 1.17/1.02  sup_num_of_clauses:                     6
% 1.17/1.02  sup_num_in_active:                      2
% 1.17/1.02  sup_num_in_passive:                     4
% 1.17/1.02  sup_num_of_loops:                       2
% 1.17/1.02  sup_fw_superposition:                   0
% 1.17/1.02  sup_bw_superposition:                   0
% 1.17/1.02  sup_immediate_simplified:               0
% 1.17/1.02  sup_given_eliminated:                   0
% 1.17/1.02  comparisons_done:                       0
% 1.17/1.02  comparisons_avoided:                    0
% 1.17/1.02  
% 1.17/1.02  ------ Simplifications
% 1.17/1.02  
% 1.17/1.02  
% 1.17/1.02  sim_fw_subset_subsumed:                 0
% 1.17/1.02  sim_bw_subset_subsumed:                 0
% 1.17/1.02  sim_fw_subsumed:                        0
% 1.17/1.02  sim_bw_subsumed:                        0
% 1.17/1.02  sim_fw_subsumption_res:                 0
% 1.17/1.02  sim_bw_subsumption_res:                 0
% 1.17/1.02  sim_tautology_del:                      0
% 1.17/1.02  sim_eq_tautology_del:                   0
% 1.17/1.02  sim_eq_res_simp:                        0
% 1.17/1.02  sim_fw_demodulated:                     0
% 1.17/1.02  sim_bw_demodulated:                     0
% 1.17/1.02  sim_light_normalised:                   0
% 1.17/1.02  sim_joinable_taut:                      0
% 1.17/1.02  sim_joinable_simp:                      0
% 1.17/1.02  sim_ac_normalised:                      0
% 1.17/1.02  sim_smt_subsumption:                    0
% 1.17/1.02  
%------------------------------------------------------------------------------
