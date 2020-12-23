%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT1913+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n026.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:46:52 EST 2020

% Result     : Theorem 1.39s
% Output     : CNFRefutation 1.39s
% Verified   : 
% Statistics : Number of formulae       :  119 ( 604 expanded)
%              Number of clauses        :   76 ( 135 expanded)
%              Number of leaves         :   13 ( 202 expanded)
%              Depth                    :   19
%              Number of atoms          :  686 (4487 expanded)
%              Number of equality atoms :  138 ( 676 expanded)
%              Maximal formula depth    :   17 (   7 average)
%              Maximal clause size      :   19 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2,axiom,(
    ! [X0,X1] :
      ( ( v2_pralg_1(X1)
        & v1_partfun1(X1,X0)
        & v1_funct_1(X1)
        & v4_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ( v1_partfun1(k12_pralg_1(X0,X1),X0)
        & v1_funct_1(k12_pralg_1(X0,X1))
        & v4_relat_1(k12_pralg_1(X0,X1),X0)
        & v1_relat_1(k12_pralg_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f9,plain,(
    ! [X0,X1] :
      ( ( v1_partfun1(k12_pralg_1(X0,X1),X0)
        & v1_funct_1(k12_pralg_1(X0,X1))
        & v4_relat_1(k12_pralg_1(X0,X1),X0)
        & v1_relat_1(k12_pralg_1(X0,X1)) )
      | ~ v2_pralg_1(X1)
      | ~ v1_partfun1(X1,X0)
      | ~ v1_funct_1(X1)
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f10,plain,(
    ! [X0,X1] :
      ( ( v1_partfun1(k12_pralg_1(X0,X1),X0)
        & v1_funct_1(k12_pralg_1(X0,X1))
        & v4_relat_1(k12_pralg_1(X0,X1),X0)
        & v1_relat_1(k12_pralg_1(X0,X1)) )
      | ~ v2_pralg_1(X1)
      | ~ v1_partfun1(X1,X0)
      | ~ v1_funct_1(X1)
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f9])).

fof(f34,plain,(
    ! [X0,X1] :
      ( v1_partfun1(k12_pralg_1(X0,X1),X0)
      | ~ v2_pralg_1(X1)
      | ~ v1_partfun1(X1,X0)
      | ~ v1_funct_1(X1)
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f5,conjecture,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( ( v2_pralg_1(X1)
            & v1_partfun1(X1,X0)
            & v1_funct_1(X1)
            & v4_relat_1(X1,X0)
            & v1_relat_1(X1) )
         => ! [X2] :
              ( m1_subset_1(X2,X0)
             => k1_funct_1(k12_pralg_1(X0,X1),X2) = u1_struct_0(k10_pralg_1(X0,X1,X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f6,negated_conjecture,(
    ~ ! [X0] :
        ( ~ v1_xboole_0(X0)
       => ! [X1] :
            ( ( v2_pralg_1(X1)
              & v1_partfun1(X1,X0)
              & v1_funct_1(X1)
              & v4_relat_1(X1,X0)
              & v1_relat_1(X1) )
           => ! [X2] :
                ( m1_subset_1(X2,X0)
               => k1_funct_1(k12_pralg_1(X0,X1),X2) = u1_struct_0(k10_pralg_1(X0,X1,X2)) ) ) ) ),
    inference(negated_conjecture,[],[f5])).

fof(f15,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( k1_funct_1(k12_pralg_1(X0,X1),X2) != u1_struct_0(k10_pralg_1(X0,X1,X2))
              & m1_subset_1(X2,X0) )
          & v2_pralg_1(X1)
          & v1_partfun1(X1,X0)
          & v1_funct_1(X1)
          & v4_relat_1(X1,X0)
          & v1_relat_1(X1) )
      & ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f16,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( k1_funct_1(k12_pralg_1(X0,X1),X2) != u1_struct_0(k10_pralg_1(X0,X1,X2))
              & m1_subset_1(X2,X0) )
          & v2_pralg_1(X1)
          & v1_partfun1(X1,X0)
          & v1_funct_1(X1)
          & v4_relat_1(X1,X0)
          & v1_relat_1(X1) )
      & ~ v1_xboole_0(X0) ) ),
    inference(flattening,[],[f15])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( k1_funct_1(k12_pralg_1(X0,X1),X2) != u1_struct_0(k10_pralg_1(X0,X1,X2))
          & m1_subset_1(X2,X0) )
     => ( k1_funct_1(k12_pralg_1(X0,X1),sK4) != u1_struct_0(k10_pralg_1(X0,X1,sK4))
        & m1_subset_1(sK4,X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( k1_funct_1(k12_pralg_1(X0,X1),X2) != u1_struct_0(k10_pralg_1(X0,X1,X2))
              & m1_subset_1(X2,X0) )
          & v2_pralg_1(X1)
          & v1_partfun1(X1,X0)
          & v1_funct_1(X1)
          & v4_relat_1(X1,X0)
          & v1_relat_1(X1) )
     => ( ? [X2] :
            ( k1_funct_1(k12_pralg_1(X0,sK3),X2) != u1_struct_0(k10_pralg_1(X0,sK3,X2))
            & m1_subset_1(X2,X0) )
        & v2_pralg_1(sK3)
        & v1_partfun1(sK3,X0)
        & v1_funct_1(sK3)
        & v4_relat_1(sK3,X0)
        & v1_relat_1(sK3) ) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( k1_funct_1(k12_pralg_1(X0,X1),X2) != u1_struct_0(k10_pralg_1(X0,X1,X2))
                & m1_subset_1(X2,X0) )
            & v2_pralg_1(X1)
            & v1_partfun1(X1,X0)
            & v1_funct_1(X1)
            & v4_relat_1(X1,X0)
            & v1_relat_1(X1) )
        & ~ v1_xboole_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( k1_funct_1(k12_pralg_1(sK2,X1),X2) != u1_struct_0(k10_pralg_1(sK2,X1,X2))
              & m1_subset_1(X2,sK2) )
          & v2_pralg_1(X1)
          & v1_partfun1(X1,sK2)
          & v1_funct_1(X1)
          & v4_relat_1(X1,sK2)
          & v1_relat_1(X1) )
      & ~ v1_xboole_0(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,
    ( k1_funct_1(k12_pralg_1(sK2,sK3),sK4) != u1_struct_0(k10_pralg_1(sK2,sK3,sK4))
    & m1_subset_1(sK4,sK2)
    & v2_pralg_1(sK3)
    & v1_partfun1(sK3,sK2)
    & v1_funct_1(sK3)
    & v4_relat_1(sK3,sK2)
    & v1_relat_1(sK3)
    & ~ v1_xboole_0(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f16,f24,f23,f22])).

fof(f42,plain,(
    v2_pralg_1(sK3) ),
    inference(cnf_transformation,[],[f25])).

fof(f38,plain,(
    v1_relat_1(sK3) ),
    inference(cnf_transformation,[],[f25])).

fof(f40,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f25])).

fof(f33,plain,(
    ! [X0,X1] :
      ( v1_funct_1(k12_pralg_1(X0,X1))
      | ~ v2_pralg_1(X1)
      | ~ v1_partfun1(X1,X0)
      | ~ v1_funct_1(X1)
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f32,plain,(
    ! [X0,X1] :
      ( v4_relat_1(k12_pralg_1(X0,X1),X0)
      | ~ v2_pralg_1(X1)
      | ~ v1_partfun1(X1,X0)
      | ~ v1_funct_1(X1)
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f31,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k12_pralg_1(X0,X1))
      | ~ v2_pralg_1(X1)
      | ~ v1_partfun1(X1,X0)
      | ~ v1_funct_1(X1)
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( ( v2_pralg_1(X1)
        & v1_partfun1(X1,X0)
        & v1_funct_1(X1)
        & v4_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ! [X2] :
          ( ( v1_partfun1(X2,X0)
            & v1_funct_1(X2)
            & v4_relat_1(X2,X0)
            & v1_relat_1(X2) )
         => ( k12_pralg_1(X0,X1) = X2
          <=> ! [X3] :
                ~ ( ! [X4] :
                      ( l1_struct_0(X4)
                     => ~ ( k1_funct_1(X2,X3) = u1_struct_0(X4)
                          & k1_funct_1(X1,X3) = X4 ) )
                  & r2_hidden(X3,X0) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f7,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( k12_pralg_1(X0,X1) = X2
          <=> ! [X3] :
                ( ? [X4] :
                    ( k1_funct_1(X2,X3) = u1_struct_0(X4)
                    & k1_funct_1(X1,X3) = X4
                    & l1_struct_0(X4) )
                | ~ r2_hidden(X3,X0) ) )
          | ~ v1_partfun1(X2,X0)
          | ~ v1_funct_1(X2)
          | ~ v4_relat_1(X2,X0)
          | ~ v1_relat_1(X2) )
      | ~ v2_pralg_1(X1)
      | ~ v1_partfun1(X1,X0)
      | ~ v1_funct_1(X1)
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f8,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( k12_pralg_1(X0,X1) = X2
          <=> ! [X3] :
                ( ? [X4] :
                    ( k1_funct_1(X2,X3) = u1_struct_0(X4)
                    & k1_funct_1(X1,X3) = X4
                    & l1_struct_0(X4) )
                | ~ r2_hidden(X3,X0) ) )
          | ~ v1_partfun1(X2,X0)
          | ~ v1_funct_1(X2)
          | ~ v4_relat_1(X2,X0)
          | ~ v1_relat_1(X2) )
      | ~ v2_pralg_1(X1)
      | ~ v1_partfun1(X1,X0)
      | ~ v1_funct_1(X1)
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f7])).

fof(f17,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( ( k12_pralg_1(X0,X1) = X2
              | ? [X3] :
                  ( ! [X4] :
                      ( k1_funct_1(X2,X3) != u1_struct_0(X4)
                      | k1_funct_1(X1,X3) != X4
                      | ~ l1_struct_0(X4) )
                  & r2_hidden(X3,X0) ) )
            & ( ! [X3] :
                  ( ? [X4] :
                      ( k1_funct_1(X2,X3) = u1_struct_0(X4)
                      & k1_funct_1(X1,X3) = X4
                      & l1_struct_0(X4) )
                  | ~ r2_hidden(X3,X0) )
              | k12_pralg_1(X0,X1) != X2 ) )
          | ~ v1_partfun1(X2,X0)
          | ~ v1_funct_1(X2)
          | ~ v4_relat_1(X2,X0)
          | ~ v1_relat_1(X2) )
      | ~ v2_pralg_1(X1)
      | ~ v1_partfun1(X1,X0)
      | ~ v1_funct_1(X1)
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f8])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( ( k12_pralg_1(X0,X1) = X2
              | ? [X3] :
                  ( ! [X4] :
                      ( k1_funct_1(X2,X3) != u1_struct_0(X4)
                      | k1_funct_1(X1,X3) != X4
                      | ~ l1_struct_0(X4) )
                  & r2_hidden(X3,X0) ) )
            & ( ! [X5] :
                  ( ? [X6] :
                      ( k1_funct_1(X2,X5) = u1_struct_0(X6)
                      & k1_funct_1(X1,X5) = X6
                      & l1_struct_0(X6) )
                  | ~ r2_hidden(X5,X0) )
              | k12_pralg_1(X0,X1) != X2 ) )
          | ~ v1_partfun1(X2,X0)
          | ~ v1_funct_1(X2)
          | ~ v4_relat_1(X2,X0)
          | ~ v1_relat_1(X2) )
      | ~ v2_pralg_1(X1)
      | ~ v1_partfun1(X1,X0)
      | ~ v1_funct_1(X1)
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(rectify,[],[f17])).

fof(f20,plain,(
    ! [X5,X2,X1] :
      ( ? [X6] :
          ( k1_funct_1(X2,X5) = u1_struct_0(X6)
          & k1_funct_1(X1,X5) = X6
          & l1_struct_0(X6) )
     => ( k1_funct_1(X2,X5) = u1_struct_0(sK1(X1,X2,X5))
        & k1_funct_1(X1,X5) = sK1(X1,X2,X5)
        & l1_struct_0(sK1(X1,X2,X5)) ) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ! [X4] :
              ( k1_funct_1(X2,X3) != u1_struct_0(X4)
              | k1_funct_1(X1,X3) != X4
              | ~ l1_struct_0(X4) )
          & r2_hidden(X3,X0) )
     => ( ! [X4] :
            ( k1_funct_1(X2,sK0(X0,X1,X2)) != u1_struct_0(X4)
            | k1_funct_1(X1,sK0(X0,X1,X2)) != X4
            | ~ l1_struct_0(X4) )
        & r2_hidden(sK0(X0,X1,X2),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( ( k12_pralg_1(X0,X1) = X2
              | ( ! [X4] :
                    ( k1_funct_1(X2,sK0(X0,X1,X2)) != u1_struct_0(X4)
                    | k1_funct_1(X1,sK0(X0,X1,X2)) != X4
                    | ~ l1_struct_0(X4) )
                & r2_hidden(sK0(X0,X1,X2),X0) ) )
            & ( ! [X5] :
                  ( ( k1_funct_1(X2,X5) = u1_struct_0(sK1(X1,X2,X5))
                    & k1_funct_1(X1,X5) = sK1(X1,X2,X5)
                    & l1_struct_0(sK1(X1,X2,X5)) )
                  | ~ r2_hidden(X5,X0) )
              | k12_pralg_1(X0,X1) != X2 ) )
          | ~ v1_partfun1(X2,X0)
          | ~ v1_funct_1(X2)
          | ~ v4_relat_1(X2,X0)
          | ~ v1_relat_1(X2) )
      | ~ v2_pralg_1(X1)
      | ~ v1_partfun1(X1,X0)
      | ~ v1_funct_1(X1)
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f18,f20,f19])).

fof(f27,plain,(
    ! [X2,X0,X5,X1] :
      ( k1_funct_1(X1,X5) = sK1(X1,X2,X5)
      | ~ r2_hidden(X5,X0)
      | k12_pralg_1(X0,X1) != X2
      | ~ v1_partfun1(X2,X0)
      | ~ v1_funct_1(X2)
      | ~ v4_relat_1(X2,X0)
      | ~ v1_relat_1(X2)
      | ~ v2_pralg_1(X1)
      | ~ v1_partfun1(X1,X0)
      | ~ v1_funct_1(X1)
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f47,plain,(
    ! [X0,X5,X1] :
      ( k1_funct_1(X1,X5) = sK1(X1,k12_pralg_1(X0,X1),X5)
      | ~ r2_hidden(X5,X0)
      | ~ v1_partfun1(k12_pralg_1(X0,X1),X0)
      | ~ v1_funct_1(k12_pralg_1(X0,X1))
      | ~ v4_relat_1(k12_pralg_1(X0,X1),X0)
      | ~ v1_relat_1(k12_pralg_1(X0,X1))
      | ~ v2_pralg_1(X1)
      | ~ v1_partfun1(X1,X0)
      | ~ v1_funct_1(X1)
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(equality_resolution,[],[f27])).

fof(f28,plain,(
    ! [X2,X0,X5,X1] :
      ( k1_funct_1(X2,X5) = u1_struct_0(sK1(X1,X2,X5))
      | ~ r2_hidden(X5,X0)
      | k12_pralg_1(X0,X1) != X2
      | ~ v1_partfun1(X2,X0)
      | ~ v1_funct_1(X2)
      | ~ v4_relat_1(X2,X0)
      | ~ v1_relat_1(X2)
      | ~ v2_pralg_1(X1)
      | ~ v1_partfun1(X1,X0)
      | ~ v1_funct_1(X1)
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f46,plain,(
    ! [X0,X5,X1] :
      ( k1_funct_1(k12_pralg_1(X0,X1),X5) = u1_struct_0(sK1(X1,k12_pralg_1(X0,X1),X5))
      | ~ r2_hidden(X5,X0)
      | ~ v1_partfun1(k12_pralg_1(X0,X1),X0)
      | ~ v1_funct_1(k12_pralg_1(X0,X1))
      | ~ v4_relat_1(k12_pralg_1(X0,X1),X0)
      | ~ v1_relat_1(k12_pralg_1(X0,X1))
      | ~ v2_pralg_1(X1)
      | ~ v1_partfun1(X1,X0)
      | ~ v1_funct_1(X1)
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(equality_resolution,[],[f28])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,X0)
        & v2_pralg_1(X1)
        & v1_partfun1(X1,X0)
        & v1_funct_1(X1)
        & v4_relat_1(X1,X0)
        & v1_relat_1(X1)
        & ~ v1_xboole_0(X0) )
     => k1_funct_1(X1,X2) = k10_pralg_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f11,plain,(
    ! [X0,X1,X2] :
      ( k1_funct_1(X1,X2) = k10_pralg_1(X0,X1,X2)
      | ~ m1_subset_1(X2,X0)
      | ~ v2_pralg_1(X1)
      | ~ v1_partfun1(X1,X0)
      | ~ v1_funct_1(X1)
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f12,plain,(
    ! [X0,X1,X2] :
      ( k1_funct_1(X1,X2) = k10_pralg_1(X0,X1,X2)
      | ~ m1_subset_1(X2,X0)
      | ~ v2_pralg_1(X1)
      | ~ v1_partfun1(X1,X0)
      | ~ v1_funct_1(X1)
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f11])).

fof(f35,plain,(
    ! [X2,X0,X1] :
      ( k1_funct_1(X1,X2) = k10_pralg_1(X0,X1,X2)
      | ~ m1_subset_1(X2,X0)
      | ~ v2_pralg_1(X1)
      | ~ v1_partfun1(X1,X0)
      | ~ v1_funct_1(X1)
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f43,plain,(
    m1_subset_1(sK4,sK2) ),
    inference(cnf_transformation,[],[f25])).

fof(f37,plain,(
    ~ v1_xboole_0(sK2) ),
    inference(cnf_transformation,[],[f25])).

fof(f39,plain,(
    v4_relat_1(sK3,sK2) ),
    inference(cnf_transformation,[],[f25])).

fof(f41,plain,(
    v1_partfun1(sK3,sK2) ),
    inference(cnf_transformation,[],[f25])).

fof(f44,plain,(
    k1_funct_1(k12_pralg_1(sK2,sK3),sK4) != u1_struct_0(k10_pralg_1(sK2,sK3,sK4)) ),
    inference(cnf_transformation,[],[f25])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f14,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f13])).

fof(f36,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f14])).

cnf(c_1741,plain,
    ( X0_49 != X1_49
    | u1_struct_0(X0_49) = u1_struct_0(X1_49) ),
    theory(equality)).

cnf(c_2478,plain,
    ( k10_pralg_1(sK2,sK3,sK4) != sK1(sK3,k12_pralg_1(sK2,sK3),sK4)
    | u1_struct_0(k10_pralg_1(sK2,sK3,sK4)) = u1_struct_0(sK1(sK3,k12_pralg_1(sK2,sK3),sK4)) ),
    inference(instantiation,[status(thm)],[c_1741])).

cnf(c_1737,plain,
    ( X0_49 != X1_49
    | X2_49 != X1_49
    | X2_49 = X0_49 ),
    theory(equality)).

cnf(c_2226,plain,
    ( X0_49 != X1_49
    | X0_49 = sK1(sK3,k12_pralg_1(X0_47,sK3),X0_46)
    | sK1(sK3,k12_pralg_1(X0_47,sK3),X0_46) != X1_49 ),
    inference(instantiation,[status(thm)],[c_1737])).

cnf(c_2260,plain,
    ( X0_49 = sK1(sK3,k12_pralg_1(X0_47,sK3),X0_46)
    | X0_49 != k1_funct_1(sK3,X0_46)
    | sK1(sK3,k12_pralg_1(X0_47,sK3),X0_46) != k1_funct_1(sK3,X0_46) ),
    inference(instantiation,[status(thm)],[c_2226])).

cnf(c_2368,plain,
    ( k10_pralg_1(sK2,sK3,sK4) = sK1(sK3,k12_pralg_1(X0_47,sK3),sK4)
    | k10_pralg_1(sK2,sK3,sK4) != k1_funct_1(sK3,sK4)
    | sK1(sK3,k12_pralg_1(X0_47,sK3),sK4) != k1_funct_1(sK3,sK4) ),
    inference(instantiation,[status(thm)],[c_2260])).

cnf(c_2369,plain,
    ( k10_pralg_1(sK2,sK3,sK4) = sK1(sK3,k12_pralg_1(sK2,sK3),sK4)
    | k10_pralg_1(sK2,sK3,sK4) != k1_funct_1(sK3,sK4)
    | sK1(sK3,k12_pralg_1(sK2,sK3),sK4) != k1_funct_1(sK3,sK4) ),
    inference(instantiation,[status(thm)],[c_2368])).

cnf(c_2214,plain,
    ( k1_funct_1(k12_pralg_1(sK2,sK3),sK4) != X0_49
    | k1_funct_1(k12_pralg_1(sK2,sK3),sK4) = u1_struct_0(k10_pralg_1(sK2,sK3,sK4))
    | u1_struct_0(k10_pralg_1(sK2,sK3,sK4)) != X0_49 ),
    inference(instantiation,[status(thm)],[c_1737])).

cnf(c_2327,plain,
    ( k1_funct_1(k12_pralg_1(sK2,sK3),sK4) = u1_struct_0(k10_pralg_1(sK2,sK3,sK4))
    | k1_funct_1(k12_pralg_1(sK2,sK3),sK4) != u1_struct_0(sK1(sK3,k12_pralg_1(sK2,sK3),sK4))
    | u1_struct_0(k10_pralg_1(sK2,sK3,sK4)) != u1_struct_0(sK1(sK3,k12_pralg_1(sK2,sK3),sK4)) ),
    inference(instantiation,[status(thm)],[c_2214])).

cnf(c_2220,plain,
    ( X0_49 != X1_49
    | k1_funct_1(k12_pralg_1(sK2,sK3),sK4) != X1_49
    | k1_funct_1(k12_pralg_1(sK2,sK3),sK4) = X0_49 ),
    inference(instantiation,[status(thm)],[c_1737])).

cnf(c_2243,plain,
    ( X0_49 != k1_funct_1(k12_pralg_1(sK2,sK3),sK4)
    | k1_funct_1(k12_pralg_1(sK2,sK3),sK4) = X0_49
    | k1_funct_1(k12_pralg_1(sK2,sK3),sK4) != k1_funct_1(k12_pralg_1(sK2,sK3),sK4) ),
    inference(instantiation,[status(thm)],[c_2220])).

cnf(c_2298,plain,
    ( k1_funct_1(k12_pralg_1(sK2,sK3),sK4) != k1_funct_1(k12_pralg_1(sK2,sK3),sK4)
    | k1_funct_1(k12_pralg_1(sK2,sK3),sK4) = u1_struct_0(sK1(sK3,k12_pralg_1(sK2,sK3),sK4))
    | u1_struct_0(sK1(sK3,k12_pralg_1(sK2,sK3),sK4)) != k1_funct_1(k12_pralg_1(sK2,sK3),sK4) ),
    inference(instantiation,[status(thm)],[c_2243])).

cnf(c_1735,plain,
    ( X0_49 = X0_49 ),
    theory(equality)).

cnf(c_2219,plain,
    ( k1_funct_1(k12_pralg_1(sK2,sK3),sK4) = k1_funct_1(k12_pralg_1(sK2,sK3),sK4) ),
    inference(instantiation,[status(thm)],[c_1735])).

cnf(c_5,plain,
    ( ~ v4_relat_1(X0,X1)
    | ~ v1_partfun1(X0,X1)
    | v1_partfun1(k12_pralg_1(X1,X0),X1)
    | ~ v2_pralg_1(X0)
    | ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_13,negated_conjecture,
    ( v2_pralg_1(sK3) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_608,plain,
    ( ~ v4_relat_1(X0,X1)
    | ~ v1_partfun1(X0,X1)
    | v1_partfun1(k12_pralg_1(X1,X0),X1)
    | ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0)
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_5,c_13])).

cnf(c_609,plain,
    ( ~ v4_relat_1(sK3,X0)
    | v1_partfun1(k12_pralg_1(X0,sK3),X0)
    | ~ v1_partfun1(sK3,X0)
    | ~ v1_relat_1(sK3)
    | ~ v1_funct_1(sK3) ),
    inference(unflattening,[status(thm)],[c_608])).

cnf(c_17,negated_conjecture,
    ( v1_relat_1(sK3) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_15,negated_conjecture,
    ( v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_613,plain,
    ( ~ v4_relat_1(sK3,X0)
    | v1_partfun1(k12_pralg_1(X0,sK3),X0)
    | ~ v1_partfun1(sK3,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_609,c_17,c_15])).

cnf(c_6,plain,
    ( ~ v4_relat_1(X0,X1)
    | ~ v1_partfun1(X0,X1)
    | ~ v2_pralg_1(X0)
    | ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0)
    | v1_funct_1(k12_pralg_1(X1,X0)) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_575,plain,
    ( ~ v4_relat_1(X0,X1)
    | ~ v1_partfun1(X0,X1)
    | ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0)
    | v1_funct_1(k12_pralg_1(X1,X0))
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_6,c_13])).

cnf(c_576,plain,
    ( ~ v4_relat_1(sK3,X0)
    | ~ v1_partfun1(sK3,X0)
    | ~ v1_relat_1(sK3)
    | v1_funct_1(k12_pralg_1(X0,sK3))
    | ~ v1_funct_1(sK3) ),
    inference(unflattening,[status(thm)],[c_575])).

cnf(c_580,plain,
    ( v1_funct_1(k12_pralg_1(X0,sK3))
    | ~ v4_relat_1(sK3,X0)
    | ~ v1_partfun1(sK3,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_576,c_17,c_15])).

cnf(c_581,plain,
    ( ~ v4_relat_1(sK3,X0)
    | ~ v1_partfun1(sK3,X0)
    | v1_funct_1(k12_pralg_1(X0,sK3)) ),
    inference(renaming,[status(thm)],[c_580])).

cnf(c_7,plain,
    ( ~ v4_relat_1(X0,X1)
    | v4_relat_1(k12_pralg_1(X1,X0),X1)
    | ~ v1_partfun1(X0,X1)
    | ~ v2_pralg_1(X0)
    | ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f32])).

cnf(c_542,plain,
    ( ~ v4_relat_1(X0,X1)
    | v4_relat_1(k12_pralg_1(X1,X0),X1)
    | ~ v1_partfun1(X0,X1)
    | ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0)
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_7,c_13])).

cnf(c_543,plain,
    ( v4_relat_1(k12_pralg_1(X0,sK3),X0)
    | ~ v4_relat_1(sK3,X0)
    | ~ v1_partfun1(sK3,X0)
    | ~ v1_relat_1(sK3)
    | ~ v1_funct_1(sK3) ),
    inference(unflattening,[status(thm)],[c_542])).

cnf(c_547,plain,
    ( v4_relat_1(k12_pralg_1(X0,sK3),X0)
    | ~ v4_relat_1(sK3,X0)
    | ~ v1_partfun1(sK3,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_543,c_17,c_15])).

cnf(c_8,plain,
    ( ~ v4_relat_1(X0,X1)
    | ~ v1_partfun1(X0,X1)
    | ~ v2_pralg_1(X0)
    | ~ v1_relat_1(X0)
    | v1_relat_1(k12_pralg_1(X1,X0))
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f31])).

cnf(c_509,plain,
    ( ~ v4_relat_1(X0,X1)
    | ~ v1_partfun1(X0,X1)
    | ~ v1_relat_1(X0)
    | v1_relat_1(k12_pralg_1(X1,X0))
    | ~ v1_funct_1(X0)
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_8,c_13])).

cnf(c_510,plain,
    ( ~ v4_relat_1(sK3,X0)
    | ~ v1_partfun1(sK3,X0)
    | v1_relat_1(k12_pralg_1(X0,sK3))
    | ~ v1_relat_1(sK3)
    | ~ v1_funct_1(sK3) ),
    inference(unflattening,[status(thm)],[c_509])).

cnf(c_514,plain,
    ( ~ v4_relat_1(sK3,X0)
    | ~ v1_partfun1(sK3,X0)
    | v1_relat_1(k12_pralg_1(X0,sK3)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_510,c_17,c_15])).

cnf(c_3,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ v4_relat_1(X2,X1)
    | ~ v4_relat_1(k12_pralg_1(X1,X2),X1)
    | ~ v1_partfun1(X2,X1)
    | ~ v1_partfun1(k12_pralg_1(X1,X2),X1)
    | ~ v2_pralg_1(X2)
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(k12_pralg_1(X1,X2))
    | ~ v1_funct_1(X2)
    | ~ v1_funct_1(k12_pralg_1(X1,X2))
    | sK1(X2,k12_pralg_1(X1,X2),X0) = k1_funct_1(X2,X0) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_392,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ v4_relat_1(X2,X1)
    | ~ v4_relat_1(k12_pralg_1(X1,X2),X1)
    | ~ v1_partfun1(X2,X1)
    | ~ v1_partfun1(k12_pralg_1(X1,X2),X1)
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(k12_pralg_1(X1,X2))
    | ~ v1_funct_1(X2)
    | ~ v1_funct_1(k12_pralg_1(X1,X2))
    | sK1(X2,k12_pralg_1(X1,X2),X0) = k1_funct_1(X2,X0)
    | sK3 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_3,c_13])).

cnf(c_393,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ v4_relat_1(k12_pralg_1(X1,sK3),X1)
    | ~ v4_relat_1(sK3,X1)
    | ~ v1_partfun1(k12_pralg_1(X1,sK3),X1)
    | ~ v1_partfun1(sK3,X1)
    | ~ v1_relat_1(k12_pralg_1(X1,sK3))
    | ~ v1_relat_1(sK3)
    | ~ v1_funct_1(k12_pralg_1(X1,sK3))
    | ~ v1_funct_1(sK3)
    | sK1(sK3,k12_pralg_1(X1,sK3),X0) = k1_funct_1(sK3,X0) ),
    inference(unflattening,[status(thm)],[c_392])).

cnf(c_397,plain,
    ( ~ v1_funct_1(k12_pralg_1(X1,sK3))
    | ~ r2_hidden(X0,X1)
    | ~ v4_relat_1(k12_pralg_1(X1,sK3),X1)
    | ~ v4_relat_1(sK3,X1)
    | ~ v1_partfun1(k12_pralg_1(X1,sK3),X1)
    | ~ v1_partfun1(sK3,X1)
    | ~ v1_relat_1(k12_pralg_1(X1,sK3))
    | sK1(sK3,k12_pralg_1(X1,sK3),X0) = k1_funct_1(sK3,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_393,c_17,c_15])).

cnf(c_398,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ v4_relat_1(k12_pralg_1(X1,sK3),X1)
    | ~ v4_relat_1(sK3,X1)
    | ~ v1_partfun1(k12_pralg_1(X1,sK3),X1)
    | ~ v1_partfun1(sK3,X1)
    | ~ v1_relat_1(k12_pralg_1(X1,sK3))
    | ~ v1_funct_1(k12_pralg_1(X1,sK3))
    | sK1(sK3,k12_pralg_1(X1,sK3),X0) = k1_funct_1(sK3,X0) ),
    inference(renaming,[status(thm)],[c_397])).

cnf(c_529,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ v4_relat_1(k12_pralg_1(X1,sK3),X1)
    | ~ v4_relat_1(sK3,X1)
    | ~ v1_partfun1(k12_pralg_1(X1,sK3),X1)
    | ~ v1_partfun1(sK3,X1)
    | ~ v1_funct_1(k12_pralg_1(X1,sK3))
    | sK1(sK3,k12_pralg_1(X1,sK3),X0) = k1_funct_1(sK3,X0) ),
    inference(backward_subsumption_resolution,[status(thm)],[c_514,c_398])).

cnf(c_561,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ v4_relat_1(sK3,X1)
    | ~ v1_partfun1(k12_pralg_1(X1,sK3),X1)
    | ~ v1_partfun1(sK3,X1)
    | ~ v1_funct_1(k12_pralg_1(X1,sK3))
    | sK1(sK3,k12_pralg_1(X1,sK3),X0) = k1_funct_1(sK3,X0) ),
    inference(backward_subsumption_resolution,[status(thm)],[c_547,c_529])).

cnf(c_595,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ v4_relat_1(sK3,X1)
    | ~ v1_partfun1(k12_pralg_1(X1,sK3),X1)
    | ~ v1_partfun1(sK3,X1)
    | sK1(sK3,k12_pralg_1(X1,sK3),X0) = k1_funct_1(sK3,X0) ),
    inference(backward_subsumption_resolution,[status(thm)],[c_581,c_561])).

cnf(c_628,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ v4_relat_1(sK3,X1)
    | ~ v1_partfun1(sK3,X1)
    | sK1(sK3,k12_pralg_1(X1,sK3),X0) = k1_funct_1(sK3,X0) ),
    inference(backward_subsumption_resolution,[status(thm)],[c_613,c_595])).

cnf(c_1717,plain,
    ( ~ r2_hidden(X0_46,X0_47)
    | ~ v4_relat_1(sK3,X0_47)
    | ~ v1_partfun1(sK3,X0_47)
    | sK1(sK3,k12_pralg_1(X0_47,sK3),X0_46) = k1_funct_1(sK3,X0_46) ),
    inference(subtyping,[status(esa)],[c_628])).

cnf(c_1793,plain,
    ( ~ r2_hidden(sK4,sK2)
    | ~ v4_relat_1(sK3,sK2)
    | ~ v1_partfun1(sK3,sK2)
    | sK1(sK3,k12_pralg_1(sK2,sK3),sK4) = k1_funct_1(sK3,sK4) ),
    inference(instantiation,[status(thm)],[c_1717])).

cnf(c_2,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ v4_relat_1(X2,X1)
    | ~ v4_relat_1(k12_pralg_1(X1,X2),X1)
    | ~ v1_partfun1(X2,X1)
    | ~ v1_partfun1(k12_pralg_1(X1,X2),X1)
    | ~ v2_pralg_1(X2)
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(k12_pralg_1(X1,X2))
    | ~ v1_funct_1(X2)
    | ~ v1_funct_1(k12_pralg_1(X1,X2))
    | u1_struct_0(sK1(X2,k12_pralg_1(X1,X2),X0)) = k1_funct_1(k12_pralg_1(X1,X2),X0) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_428,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ v4_relat_1(X2,X1)
    | ~ v4_relat_1(k12_pralg_1(X1,X2),X1)
    | ~ v1_partfun1(X2,X1)
    | ~ v1_partfun1(k12_pralg_1(X1,X2),X1)
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(k12_pralg_1(X1,X2))
    | ~ v1_funct_1(X2)
    | ~ v1_funct_1(k12_pralg_1(X1,X2))
    | u1_struct_0(sK1(X2,k12_pralg_1(X1,X2),X0)) = k1_funct_1(k12_pralg_1(X1,X2),X0)
    | sK3 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_2,c_13])).

cnf(c_429,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ v4_relat_1(k12_pralg_1(X1,sK3),X1)
    | ~ v4_relat_1(sK3,X1)
    | ~ v1_partfun1(k12_pralg_1(X1,sK3),X1)
    | ~ v1_partfun1(sK3,X1)
    | ~ v1_relat_1(k12_pralg_1(X1,sK3))
    | ~ v1_relat_1(sK3)
    | ~ v1_funct_1(k12_pralg_1(X1,sK3))
    | ~ v1_funct_1(sK3)
    | u1_struct_0(sK1(sK3,k12_pralg_1(X1,sK3),X0)) = k1_funct_1(k12_pralg_1(X1,sK3),X0) ),
    inference(unflattening,[status(thm)],[c_428])).

cnf(c_433,plain,
    ( ~ v1_funct_1(k12_pralg_1(X1,sK3))
    | ~ r2_hidden(X0,X1)
    | ~ v4_relat_1(k12_pralg_1(X1,sK3),X1)
    | ~ v4_relat_1(sK3,X1)
    | ~ v1_partfun1(k12_pralg_1(X1,sK3),X1)
    | ~ v1_partfun1(sK3,X1)
    | ~ v1_relat_1(k12_pralg_1(X1,sK3))
    | u1_struct_0(sK1(sK3,k12_pralg_1(X1,sK3),X0)) = k1_funct_1(k12_pralg_1(X1,sK3),X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_429,c_17,c_15])).

cnf(c_434,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ v4_relat_1(k12_pralg_1(X1,sK3),X1)
    | ~ v4_relat_1(sK3,X1)
    | ~ v1_partfun1(k12_pralg_1(X1,sK3),X1)
    | ~ v1_partfun1(sK3,X1)
    | ~ v1_relat_1(k12_pralg_1(X1,sK3))
    | ~ v1_funct_1(k12_pralg_1(X1,sK3))
    | u1_struct_0(sK1(sK3,k12_pralg_1(X1,sK3),X0)) = k1_funct_1(k12_pralg_1(X1,sK3),X0) ),
    inference(renaming,[status(thm)],[c_433])).

cnf(c_530,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ v4_relat_1(k12_pralg_1(X1,sK3),X1)
    | ~ v4_relat_1(sK3,X1)
    | ~ v1_partfun1(k12_pralg_1(X1,sK3),X1)
    | ~ v1_partfun1(sK3,X1)
    | ~ v1_funct_1(k12_pralg_1(X1,sK3))
    | u1_struct_0(sK1(sK3,k12_pralg_1(X1,sK3),X0)) = k1_funct_1(k12_pralg_1(X1,sK3),X0) ),
    inference(backward_subsumption_resolution,[status(thm)],[c_514,c_434])).

cnf(c_560,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ v4_relat_1(sK3,X1)
    | ~ v1_partfun1(k12_pralg_1(X1,sK3),X1)
    | ~ v1_partfun1(sK3,X1)
    | ~ v1_funct_1(k12_pralg_1(X1,sK3))
    | u1_struct_0(sK1(sK3,k12_pralg_1(X1,sK3),X0)) = k1_funct_1(k12_pralg_1(X1,sK3),X0) ),
    inference(backward_subsumption_resolution,[status(thm)],[c_547,c_530])).

cnf(c_596,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ v4_relat_1(sK3,X1)
    | ~ v1_partfun1(k12_pralg_1(X1,sK3),X1)
    | ~ v1_partfun1(sK3,X1)
    | u1_struct_0(sK1(sK3,k12_pralg_1(X1,sK3),X0)) = k1_funct_1(k12_pralg_1(X1,sK3),X0) ),
    inference(backward_subsumption_resolution,[status(thm)],[c_581,c_560])).

cnf(c_627,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ v4_relat_1(sK3,X1)
    | ~ v1_partfun1(sK3,X1)
    | u1_struct_0(sK1(sK3,k12_pralg_1(X1,sK3),X0)) = k1_funct_1(k12_pralg_1(X1,sK3),X0) ),
    inference(backward_subsumption_resolution,[status(thm)],[c_613,c_596])).

cnf(c_1718,plain,
    ( ~ r2_hidden(X0_46,X0_47)
    | ~ v4_relat_1(sK3,X0_47)
    | ~ v1_partfun1(sK3,X0_47)
    | u1_struct_0(sK1(sK3,k12_pralg_1(X0_47,sK3),X0_46)) = k1_funct_1(k12_pralg_1(X0_47,sK3),X0_46) ),
    inference(subtyping,[status(esa)],[c_627])).

cnf(c_1790,plain,
    ( ~ r2_hidden(sK4,sK2)
    | ~ v4_relat_1(sK3,sK2)
    | ~ v1_partfun1(sK3,sK2)
    | u1_struct_0(sK1(sK3,k12_pralg_1(sK2,sK3),sK4)) = k1_funct_1(k12_pralg_1(sK2,sK3),sK4) ),
    inference(instantiation,[status(thm)],[c_1718])).

cnf(c_9,plain,
    ( ~ m1_subset_1(X0,X1)
    | ~ v4_relat_1(X2,X1)
    | ~ v1_partfun1(X2,X1)
    | v1_xboole_0(X1)
    | ~ v2_pralg_1(X2)
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2)
    | k10_pralg_1(X1,X2,X0) = k1_funct_1(X2,X0) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_12,negated_conjecture,
    ( m1_subset_1(sK4,sK2) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_213,plain,
    ( ~ v4_relat_1(X0,X1)
    | ~ v1_partfun1(X0,X1)
    | v1_xboole_0(X1)
    | ~ v2_pralg_1(X0)
    | ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0)
    | k10_pralg_1(X1,X0,X2) = k1_funct_1(X0,X2)
    | sK4 != X2
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_9,c_12])).

cnf(c_214,plain,
    ( ~ v4_relat_1(X0,sK2)
    | ~ v1_partfun1(X0,sK2)
    | v1_xboole_0(sK2)
    | ~ v2_pralg_1(X0)
    | ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0)
    | k10_pralg_1(sK2,X0,sK4) = k1_funct_1(X0,sK4) ),
    inference(unflattening,[status(thm)],[c_213])).

cnf(c_18,negated_conjecture,
    ( ~ v1_xboole_0(sK2) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_218,plain,
    ( ~ v1_partfun1(X0,sK2)
    | ~ v4_relat_1(X0,sK2)
    | ~ v2_pralg_1(X0)
    | ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0)
    | k10_pralg_1(sK2,X0,sK4) = k1_funct_1(X0,sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_214,c_18])).

cnf(c_219,plain,
    ( ~ v4_relat_1(X0,sK2)
    | ~ v1_partfun1(X0,sK2)
    | ~ v2_pralg_1(X0)
    | ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0)
    | k10_pralg_1(sK2,X0,sK4) = k1_funct_1(X0,sK4) ),
    inference(renaming,[status(thm)],[c_218])).

cnf(c_501,plain,
    ( ~ v4_relat_1(X0,sK2)
    | ~ v1_partfun1(X0,sK2)
    | ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0)
    | k10_pralg_1(sK2,X0,sK4) = k1_funct_1(X0,sK4)
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_219,c_13])).

cnf(c_502,plain,
    ( ~ v4_relat_1(sK3,sK2)
    | ~ v1_partfun1(sK3,sK2)
    | ~ v1_relat_1(sK3)
    | ~ v1_funct_1(sK3)
    | k10_pralg_1(sK2,sK3,sK4) = k1_funct_1(sK3,sK4) ),
    inference(unflattening,[status(thm)],[c_501])).

cnf(c_16,negated_conjecture,
    ( v4_relat_1(sK3,sK2) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_14,negated_conjecture,
    ( v1_partfun1(sK3,sK2) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_216,plain,
    ( ~ v4_relat_1(sK3,sK2)
    | ~ v1_partfun1(sK3,sK2)
    | v1_xboole_0(sK2)
    | ~ v2_pralg_1(sK3)
    | ~ v1_relat_1(sK3)
    | ~ v1_funct_1(sK3)
    | k10_pralg_1(sK2,sK3,sK4) = k1_funct_1(sK3,sK4) ),
    inference(instantiation,[status(thm)],[c_214])).

cnf(c_504,plain,
    ( k10_pralg_1(sK2,sK3,sK4) = k1_funct_1(sK3,sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_502,c_18,c_17,c_16,c_15,c_14,c_13,c_216])).

cnf(c_1723,plain,
    ( k10_pralg_1(sK2,sK3,sK4) = k1_funct_1(sK3,sK4) ),
    inference(subtyping,[status(esa)],[c_504])).

cnf(c_11,negated_conjecture,
    ( k1_funct_1(k12_pralg_1(sK2,sK3),sK4) != u1_struct_0(k10_pralg_1(sK2,sK3,sK4)) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_1731,negated_conjecture,
    ( k1_funct_1(k12_pralg_1(sK2,sK3),sK4) != u1_struct_0(k10_pralg_1(sK2,sK3,sK4)) ),
    inference(subtyping,[status(esa)],[c_11])).

cnf(c_10,plain,
    ( ~ m1_subset_1(X0,X1)
    | r2_hidden(X0,X1)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_202,plain,
    ( r2_hidden(X0,X1)
    | v1_xboole_0(X1)
    | sK4 != X0
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_10,c_12])).

cnf(c_203,plain,
    ( r2_hidden(sK4,sK2)
    | v1_xboole_0(sK2) ),
    inference(unflattening,[status(thm)],[c_202])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_2478,c_2369,c_2327,c_2298,c_2219,c_1793,c_1790,c_1723,c_1731,c_203,c_14,c_16,c_18])).


%------------------------------------------------------------------------------
