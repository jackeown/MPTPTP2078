%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:28:02 EST 2020

% Result     : Theorem 1.45s
% Output     : CNFRefutation 1.45s
% Verified   : 
% Statistics : Number of formulae       :  102 ( 336 expanded)
%              Number of clauses        :   59 (  83 expanded)
%              Number of leaves         :   13 ( 106 expanded)
%              Depth                    :   16
%              Number of atoms          :  574 (2505 expanded)
%              Number of equality atoms :  130 ( 403 expanded)
%              Maximal formula depth    :   17 (   6 average)
%              Maximal clause size      :   19 (   4 average)
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

fof(f9,plain,(
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
    inference(ennf_transformation,[],[f2])).

fof(f10,plain,(
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
    inference(flattening,[],[f9])).

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
    inference(nnf_transformation,[],[f10])).

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

fof(f28,plain,(
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
    inference(equality_resolution,[],[f28])).

fof(f3,axiom,(
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

fof(f11,plain,(
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
    inference(ennf_transformation,[],[f3])).

fof(f12,plain,(
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
    inference(flattening,[],[f11])).

fof(f32,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k12_pralg_1(X0,X1))
      | ~ v2_pralg_1(X1)
      | ~ v1_partfun1(X1,X0)
      | ~ v1_funct_1(X1)
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f33,plain,(
    ! [X0,X1] :
      ( v4_relat_1(k12_pralg_1(X0,X1),X0)
      | ~ v2_pralg_1(X1)
      | ~ v1_partfun1(X1,X0)
      | ~ v1_funct_1(X1)
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f34,plain,(
    ! [X0,X1] :
      ( v1_funct_1(k12_pralg_1(X0,X1))
      | ~ v2_pralg_1(X1)
      | ~ v1_partfun1(X1,X0)
      | ~ v1_funct_1(X1)
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f35,plain,(
    ! [X0,X1] :
      ( v1_partfun1(k12_pralg_1(X0,X1),X0)
      | ~ v2_pralg_1(X1)
      | ~ v1_partfun1(X1,X0)
      | ~ v1_funct_1(X1)
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f12])).

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

fof(f29,plain,(
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
    inference(equality_resolution,[],[f29])).

fof(f43,plain,(
    m1_subset_1(sK4,sK2) ),
    inference(cnf_transformation,[],[f25])).

fof(f4,axiom,(
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

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( k1_funct_1(X1,X2) = k10_pralg_1(X0,X1,X2)
      | ~ m1_subset_1(X2,X0)
      | ~ v2_pralg_1(X1)
      | ~ v1_partfun1(X1,X0)
      | ~ v1_funct_1(X1)
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( k1_funct_1(X1,X2) = k10_pralg_1(X0,X1,X2)
      | ~ m1_subset_1(X2,X0)
      | ~ v2_pralg_1(X1)
      | ~ v1_partfun1(X1,X0)
      | ~ v1_funct_1(X1)
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f13])).

fof(f36,plain,(
    ! [X2,X0,X1] :
      ( k1_funct_1(X1,X2) = k10_pralg_1(X0,X1,X2)
      | ~ m1_subset_1(X2,X0)
      | ~ v2_pralg_1(X1)
      | ~ v1_partfun1(X1,X0)
      | ~ v1_funct_1(X1)
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f14])).

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

fof(f1,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f7,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f8,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f7])).

fof(f26,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f8])).

cnf(c_1706,plain,
    ( X0_49 != X1_49
    | u1_struct_0(X0_49) = u1_struct_0(X1_49) ),
    theory(equality)).

cnf(c_2465,plain,
    ( k10_pralg_1(sK2,sK3,sK4) != sK1(sK3,k12_pralg_1(sK2,sK3),sK4)
    | u1_struct_0(k10_pralg_1(sK2,sK3,sK4)) = u1_struct_0(sK1(sK3,k12_pralg_1(sK2,sK3),sK4)) ),
    inference(instantiation,[status(thm)],[c_1706])).

cnf(c_1701,plain,
    ( X0_49 != X1_49
    | X2_49 != X1_49
    | X2_49 = X0_49 ),
    theory(equality)).

cnf(c_2178,plain,
    ( k1_funct_1(k12_pralg_1(sK2,sK3),sK4) != X0_49
    | k1_funct_1(k12_pralg_1(sK2,sK3),sK4) = u1_struct_0(k10_pralg_1(sK2,sK3,sK4))
    | u1_struct_0(k10_pralg_1(sK2,sK3,sK4)) != X0_49 ),
    inference(instantiation,[status(thm)],[c_1701])).

cnf(c_2288,plain,
    ( k1_funct_1(k12_pralg_1(sK2,sK3),sK4) = u1_struct_0(k10_pralg_1(sK2,sK3,sK4))
    | k1_funct_1(k12_pralg_1(sK2,sK3),sK4) != u1_struct_0(sK1(sK3,k12_pralg_1(sK2,sK3),sK4))
    | u1_struct_0(k10_pralg_1(sK2,sK3,sK4)) != u1_struct_0(sK1(sK3,k12_pralg_1(sK2,sK3),sK4)) ),
    inference(instantiation,[status(thm)],[c_2178])).

cnf(c_2184,plain,
    ( X0_49 != X1_49
    | k1_funct_1(k12_pralg_1(sK2,sK3),sK4) != X1_49
    | k1_funct_1(k12_pralg_1(sK2,sK3),sK4) = X0_49 ),
    inference(instantiation,[status(thm)],[c_1701])).

cnf(c_2207,plain,
    ( X0_49 != k1_funct_1(k12_pralg_1(sK2,sK3),sK4)
    | k1_funct_1(k12_pralg_1(sK2,sK3),sK4) = X0_49
    | k1_funct_1(k12_pralg_1(sK2,sK3),sK4) != k1_funct_1(k12_pralg_1(sK2,sK3),sK4) ),
    inference(instantiation,[status(thm)],[c_2184])).

cnf(c_2274,plain,
    ( k1_funct_1(k12_pralg_1(sK2,sK3),sK4) != k1_funct_1(k12_pralg_1(sK2,sK3),sK4)
    | k1_funct_1(k12_pralg_1(sK2,sK3),sK4) = u1_struct_0(sK1(sK3,k12_pralg_1(sK2,sK3),sK4))
    | u1_struct_0(sK1(sK3,k12_pralg_1(sK2,sK3),sK4)) != k1_funct_1(k12_pralg_1(sK2,sK3),sK4) ),
    inference(instantiation,[status(thm)],[c_2207])).

cnf(c_2190,plain,
    ( X0_49 != X1_49
    | X0_49 = sK1(sK3,k12_pralg_1(X0_47,sK3),X0_48)
    | sK1(sK3,k12_pralg_1(X0_47,sK3),X0_48) != X1_49 ),
    inference(instantiation,[status(thm)],[c_1701])).

cnf(c_2224,plain,
    ( X0_49 = sK1(sK3,k12_pralg_1(X0_47,sK3),X0_48)
    | X0_49 != k1_funct_1(sK3,X0_48)
    | sK1(sK3,k12_pralg_1(X0_47,sK3),X0_48) != k1_funct_1(sK3,X0_48) ),
    inference(instantiation,[status(thm)],[c_2190])).

cnf(c_2244,plain,
    ( k10_pralg_1(sK2,sK3,sK4) = sK1(sK3,k12_pralg_1(X0_47,sK3),sK4)
    | k10_pralg_1(sK2,sK3,sK4) != k1_funct_1(sK3,sK4)
    | sK1(sK3,k12_pralg_1(X0_47,sK3),sK4) != k1_funct_1(sK3,sK4) ),
    inference(instantiation,[status(thm)],[c_2224])).

cnf(c_2245,plain,
    ( k10_pralg_1(sK2,sK3,sK4) = sK1(sK3,k12_pralg_1(sK2,sK3),sK4)
    | k10_pralg_1(sK2,sK3,sK4) != k1_funct_1(sK3,sK4)
    | sK1(sK3,k12_pralg_1(sK2,sK3),sK4) != k1_funct_1(sK3,sK4) ),
    inference(instantiation,[status(thm)],[c_2244])).

cnf(c_1699,plain,
    ( X0_49 = X0_49 ),
    theory(equality)).

cnf(c_2183,plain,
    ( k1_funct_1(k12_pralg_1(sK2,sK3),sK4) = k1_funct_1(k12_pralg_1(sK2,sK3),sK4) ),
    inference(instantiation,[status(thm)],[c_1699])).

cnf(c_4,plain,
    ( ~ v4_relat_1(X0,X1)
    | ~ v4_relat_1(k12_pralg_1(X1,X0),X1)
    | ~ v1_partfun1(X0,X1)
    | ~ v1_partfun1(k12_pralg_1(X1,X0),X1)
    | ~ r2_hidden(X2,X1)
    | ~ v2_pralg_1(X0)
    | ~ v1_relat_1(X0)
    | ~ v1_relat_1(k12_pralg_1(X1,X0))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(k12_pralg_1(X1,X0))
    | sK1(X0,k12_pralg_1(X1,X0),X2) = k1_funct_1(X0,X2) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_9,plain,
    ( ~ v4_relat_1(X0,X1)
    | ~ v1_partfun1(X0,X1)
    | ~ v2_pralg_1(X0)
    | ~ v1_relat_1(X0)
    | v1_relat_1(k12_pralg_1(X1,X0))
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f32])).

cnf(c_8,plain,
    ( ~ v4_relat_1(X0,X1)
    | v4_relat_1(k12_pralg_1(X1,X0),X1)
    | ~ v1_partfun1(X0,X1)
    | ~ v2_pralg_1(X0)
    | ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_7,plain,
    ( ~ v4_relat_1(X0,X1)
    | ~ v1_partfun1(X0,X1)
    | ~ v2_pralg_1(X0)
    | ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0)
    | v1_funct_1(k12_pralg_1(X1,X0)) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_6,plain,
    ( ~ v4_relat_1(X0,X1)
    | ~ v1_partfun1(X0,X1)
    | v1_partfun1(k12_pralg_1(X1,X0),X1)
    | ~ v2_pralg_1(X0)
    | ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_115,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_partfun1(X0,X1)
    | ~ v4_relat_1(X0,X1)
    | ~ r2_hidden(X2,X1)
    | ~ v2_pralg_1(X0)
    | ~ v1_relat_1(X0)
    | sK1(X0,k12_pralg_1(X1,X0),X2) = k1_funct_1(X0,X2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_4,c_9,c_8,c_7,c_6])).

cnf(c_116,plain,
    ( ~ v4_relat_1(X0,X1)
    | ~ v1_partfun1(X0,X1)
    | ~ r2_hidden(X2,X1)
    | ~ v2_pralg_1(X0)
    | ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0)
    | sK1(X0,k12_pralg_1(X1,X0),X2) = k1_funct_1(X0,X2) ),
    inference(renaming,[status(thm)],[c_115])).

cnf(c_13,negated_conjecture,
    ( v2_pralg_1(sK3) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_472,plain,
    ( ~ v4_relat_1(X0,X1)
    | ~ v1_partfun1(X0,X1)
    | ~ r2_hidden(X2,X1)
    | ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0)
    | sK1(X0,k12_pralg_1(X1,X0),X2) = k1_funct_1(X0,X2)
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_116,c_13])).

cnf(c_473,plain,
    ( ~ v4_relat_1(sK3,X0)
    | ~ v1_partfun1(sK3,X0)
    | ~ r2_hidden(X1,X0)
    | ~ v1_relat_1(sK3)
    | ~ v1_funct_1(sK3)
    | sK1(sK3,k12_pralg_1(X0,sK3),X1) = k1_funct_1(sK3,X1) ),
    inference(unflattening,[status(thm)],[c_472])).

cnf(c_17,negated_conjecture,
    ( v1_relat_1(sK3) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_15,negated_conjecture,
    ( v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_477,plain,
    ( ~ v4_relat_1(sK3,X0)
    | ~ v1_partfun1(sK3,X0)
    | ~ r2_hidden(X1,X0)
    | sK1(sK3,k12_pralg_1(X0,sK3),X1) = k1_funct_1(sK3,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_473,c_17,c_15])).

cnf(c_1685,plain,
    ( ~ v4_relat_1(sK3,X0_47)
    | ~ v1_partfun1(sK3,X0_47)
    | ~ r2_hidden(X0_48,X0_47)
    | sK1(sK3,k12_pralg_1(X0_47,sK3),X0_48) = k1_funct_1(sK3,X0_48) ),
    inference(subtyping,[status(esa)],[c_477])).

cnf(c_1745,plain,
    ( ~ v4_relat_1(sK3,sK2)
    | ~ v1_partfun1(sK3,sK2)
    | ~ r2_hidden(sK4,sK2)
    | sK1(sK3,k12_pralg_1(sK2,sK3),sK4) = k1_funct_1(sK3,sK4) ),
    inference(instantiation,[status(thm)],[c_1685])).

cnf(c_3,plain,
    ( ~ v4_relat_1(X0,X1)
    | ~ v4_relat_1(k12_pralg_1(X1,X0),X1)
    | ~ v1_partfun1(X0,X1)
    | ~ v1_partfun1(k12_pralg_1(X1,X0),X1)
    | ~ r2_hidden(X2,X1)
    | ~ v2_pralg_1(X0)
    | ~ v1_relat_1(X0)
    | ~ v1_relat_1(k12_pralg_1(X1,X0))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(k12_pralg_1(X1,X0))
    | u1_struct_0(sK1(X0,k12_pralg_1(X1,X0),X2)) = k1_funct_1(k12_pralg_1(X1,X0),X2) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_122,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_partfun1(X0,X1)
    | ~ v4_relat_1(X0,X1)
    | ~ r2_hidden(X2,X1)
    | ~ v2_pralg_1(X0)
    | ~ v1_relat_1(X0)
    | u1_struct_0(sK1(X0,k12_pralg_1(X1,X0),X2)) = k1_funct_1(k12_pralg_1(X1,X0),X2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3,c_9,c_8,c_7,c_6])).

cnf(c_123,plain,
    ( ~ v4_relat_1(X0,X1)
    | ~ v1_partfun1(X0,X1)
    | ~ r2_hidden(X2,X1)
    | ~ v2_pralg_1(X0)
    | ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0)
    | u1_struct_0(sK1(X0,k12_pralg_1(X1,X0),X2)) = k1_funct_1(k12_pralg_1(X1,X0),X2) ),
    inference(renaming,[status(thm)],[c_122])).

cnf(c_448,plain,
    ( ~ v4_relat_1(X0,X1)
    | ~ v1_partfun1(X0,X1)
    | ~ r2_hidden(X2,X1)
    | ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0)
    | u1_struct_0(sK1(X0,k12_pralg_1(X1,X0),X2)) = k1_funct_1(k12_pralg_1(X1,X0),X2)
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_123,c_13])).

cnf(c_449,plain,
    ( ~ v4_relat_1(sK3,X0)
    | ~ v1_partfun1(sK3,X0)
    | ~ r2_hidden(X1,X0)
    | ~ v1_relat_1(sK3)
    | ~ v1_funct_1(sK3)
    | u1_struct_0(sK1(sK3,k12_pralg_1(X0,sK3),X1)) = k1_funct_1(k12_pralg_1(X0,sK3),X1) ),
    inference(unflattening,[status(thm)],[c_448])).

cnf(c_453,plain,
    ( ~ v4_relat_1(sK3,X0)
    | ~ v1_partfun1(sK3,X0)
    | ~ r2_hidden(X1,X0)
    | u1_struct_0(sK1(sK3,k12_pralg_1(X0,sK3),X1)) = k1_funct_1(k12_pralg_1(X0,sK3),X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_449,c_17,c_15])).

cnf(c_1686,plain,
    ( ~ v4_relat_1(sK3,X0_47)
    | ~ v1_partfun1(sK3,X0_47)
    | ~ r2_hidden(X0_48,X0_47)
    | u1_struct_0(sK1(sK3,k12_pralg_1(X0_47,sK3),X0_48)) = k1_funct_1(k12_pralg_1(X0_47,sK3),X0_48) ),
    inference(subtyping,[status(esa)],[c_453])).

cnf(c_1742,plain,
    ( ~ v4_relat_1(sK3,sK2)
    | ~ v1_partfun1(sK3,sK2)
    | ~ r2_hidden(sK4,sK2)
    | u1_struct_0(sK1(sK3,k12_pralg_1(sK2,sK3),sK4)) = k1_funct_1(k12_pralg_1(sK2,sK3),sK4) ),
    inference(instantiation,[status(thm)],[c_1686])).

cnf(c_12,negated_conjecture,
    ( m1_subset_1(sK4,sK2) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_10,plain,
    ( ~ v4_relat_1(X0,X1)
    | ~ v1_partfun1(X0,X1)
    | ~ m1_subset_1(X2,X1)
    | ~ v2_pralg_1(X0)
    | ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0)
    | v1_xboole_0(X1)
    | k10_pralg_1(X1,X0,X2) = k1_funct_1(X0,X2) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_18,negated_conjecture,
    ( ~ v1_xboole_0(sK2) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_220,plain,
    ( ~ v4_relat_1(X0,X1)
    | ~ v1_partfun1(X0,X1)
    | ~ m1_subset_1(X2,X1)
    | ~ v2_pralg_1(X0)
    | ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0)
    | k10_pralg_1(X1,X0,X2) = k1_funct_1(X0,X2)
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_10,c_18])).

cnf(c_221,plain,
    ( ~ v4_relat_1(X0,sK2)
    | ~ v1_partfun1(X0,sK2)
    | ~ m1_subset_1(X1,sK2)
    | ~ v2_pralg_1(X0)
    | ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0)
    | k10_pralg_1(sK2,X0,X1) = k1_funct_1(X0,X1) ),
    inference(unflattening,[status(thm)],[c_220])).

cnf(c_270,plain,
    ( ~ v4_relat_1(X0,sK2)
    | ~ v1_partfun1(X0,sK2)
    | ~ v2_pralg_1(X0)
    | ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0)
    | k10_pralg_1(sK2,X0,X1) = k1_funct_1(X0,X1)
    | sK4 != X1
    | sK2 != sK2 ),
    inference(resolution_lifted,[status(thm)],[c_12,c_221])).

cnf(c_271,plain,
    ( ~ v4_relat_1(X0,sK2)
    | ~ v1_partfun1(X0,sK2)
    | ~ v2_pralg_1(X0)
    | ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0)
    | k10_pralg_1(sK2,X0,sK4) = k1_funct_1(X0,sK4) ),
    inference(unflattening,[status(thm)],[c_270])).

cnf(c_440,plain,
    ( ~ v4_relat_1(X0,sK2)
    | ~ v1_partfun1(X0,sK2)
    | ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0)
    | k10_pralg_1(sK2,X0,sK4) = k1_funct_1(X0,sK4)
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_271,c_13])).

cnf(c_441,plain,
    ( ~ v4_relat_1(sK3,sK2)
    | ~ v1_partfun1(sK3,sK2)
    | ~ v1_relat_1(sK3)
    | ~ v1_funct_1(sK3)
    | k10_pralg_1(sK2,sK3,sK4) = k1_funct_1(sK3,sK4) ),
    inference(unflattening,[status(thm)],[c_440])).

cnf(c_16,negated_conjecture,
    ( v4_relat_1(sK3,sK2) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_14,negated_conjecture,
    ( v1_partfun1(sK3,sK2) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_273,plain,
    ( ~ v4_relat_1(sK3,sK2)
    | ~ v1_partfun1(sK3,sK2)
    | ~ v2_pralg_1(sK3)
    | ~ v1_relat_1(sK3)
    | ~ v1_funct_1(sK3)
    | k10_pralg_1(sK2,sK3,sK4) = k1_funct_1(sK3,sK4) ),
    inference(instantiation,[status(thm)],[c_271])).

cnf(c_443,plain,
    ( k10_pralg_1(sK2,sK3,sK4) = k1_funct_1(sK3,sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_441,c_17,c_16,c_15,c_14,c_13,c_273])).

cnf(c_1687,plain,
    ( k10_pralg_1(sK2,sK3,sK4) = k1_funct_1(sK3,sK4) ),
    inference(subtyping,[status(esa)],[c_443])).

cnf(c_11,negated_conjecture,
    ( k1_funct_1(k12_pralg_1(sK2,sK3),sK4) != u1_struct_0(k10_pralg_1(sK2,sK3,sK4)) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_1695,negated_conjecture,
    ( k1_funct_1(k12_pralg_1(sK2,sK3),sK4) != u1_struct_0(k10_pralg_1(sK2,sK3,sK4)) ),
    inference(subtyping,[status(esa)],[c_11])).

cnf(c_0,plain,
    ( ~ m1_subset_1(X0,X1)
    | r2_hidden(X0,X1)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f26])).

cnf(c_247,plain,
    ( ~ m1_subset_1(X0,X1)
    | r2_hidden(X0,X1)
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_18])).

cnf(c_248,plain,
    ( ~ m1_subset_1(X0,sK2)
    | r2_hidden(X0,sK2) ),
    inference(unflattening,[status(thm)],[c_247])).

cnf(c_294,plain,
    ( r2_hidden(X0,sK2)
    | sK4 != X0
    | sK2 != sK2 ),
    inference(resolution_lifted,[status(thm)],[c_12,c_248])).

cnf(c_295,plain,
    ( r2_hidden(sK4,sK2) ),
    inference(unflattening,[status(thm)],[c_294])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_2465,c_2288,c_2274,c_2245,c_2183,c_1745,c_1742,c_1687,c_1695,c_295,c_14,c_16])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.34  % Computer   : n017.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 16:18:16 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 1.35/0.98  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.35/0.98  
% 1.35/0.98  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 1.35/0.98  
% 1.35/0.98  ------  iProver source info
% 1.35/0.98  
% 1.35/0.98  git: date: 2020-06-30 10:37:57 +0100
% 1.35/0.98  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 1.35/0.98  git: non_committed_changes: false
% 1.35/0.98  git: last_make_outside_of_git: false
% 1.35/0.98  
% 1.35/0.98  ------ 
% 1.35/0.98  
% 1.35/0.98  ------ Input Options
% 1.35/0.98  
% 1.35/0.98  --out_options                           all
% 1.35/0.98  --tptp_safe_out                         true
% 1.35/0.98  --problem_path                          ""
% 1.35/0.98  --include_path                          ""
% 1.35/0.98  --clausifier                            res/vclausify_rel
% 1.35/0.98  --clausifier_options                    --mode clausify
% 1.35/0.98  --stdin                                 false
% 1.35/0.98  --stats_out                             all
% 1.35/0.98  
% 1.35/0.98  ------ General Options
% 1.35/0.98  
% 1.35/0.98  --fof                                   false
% 1.35/0.98  --time_out_real                         305.
% 1.35/0.98  --time_out_virtual                      -1.
% 1.35/0.98  --symbol_type_check                     false
% 1.35/0.98  --clausify_out                          false
% 1.35/0.98  --sig_cnt_out                           false
% 1.35/0.98  --trig_cnt_out                          false
% 1.35/0.98  --trig_cnt_out_tolerance                1.
% 1.35/0.98  --trig_cnt_out_sk_spl                   false
% 1.35/0.98  --abstr_cl_out                          false
% 1.35/0.98  
% 1.35/0.98  ------ Global Options
% 1.35/0.98  
% 1.35/0.98  --schedule                              default
% 1.35/0.98  --add_important_lit                     false
% 1.35/0.98  --prop_solver_per_cl                    1000
% 1.35/0.98  --min_unsat_core                        false
% 1.35/0.98  --soft_assumptions                      false
% 1.35/0.98  --soft_lemma_size                       3
% 1.35/0.98  --prop_impl_unit_size                   0
% 1.35/0.98  --prop_impl_unit                        []
% 1.35/0.98  --share_sel_clauses                     true
% 1.35/0.98  --reset_solvers                         false
% 1.35/0.98  --bc_imp_inh                            [conj_cone]
% 1.35/0.98  --conj_cone_tolerance                   3.
% 1.35/0.98  --extra_neg_conj                        none
% 1.35/0.98  --large_theory_mode                     true
% 1.35/0.98  --prolific_symb_bound                   200
% 1.35/0.98  --lt_threshold                          2000
% 1.35/0.98  --clause_weak_htbl                      true
% 1.35/0.98  --gc_record_bc_elim                     false
% 1.35/0.98  
% 1.35/0.98  ------ Preprocessing Options
% 1.35/0.98  
% 1.35/0.98  --preprocessing_flag                    true
% 1.35/0.98  --time_out_prep_mult                    0.1
% 1.35/0.98  --splitting_mode                        input
% 1.35/0.98  --splitting_grd                         true
% 1.35/0.98  --splitting_cvd                         false
% 1.35/0.98  --splitting_cvd_svl                     false
% 1.35/0.98  --splitting_nvd                         32
% 1.35/0.98  --sub_typing                            true
% 1.35/0.98  --prep_gs_sim                           true
% 1.35/0.98  --prep_unflatten                        true
% 1.35/0.98  --prep_res_sim                          true
% 1.35/0.98  --prep_upred                            true
% 1.35/0.98  --prep_sem_filter                       exhaustive
% 1.35/0.98  --prep_sem_filter_out                   false
% 1.35/0.98  --pred_elim                             true
% 1.35/0.98  --res_sim_input                         true
% 1.35/0.98  --eq_ax_congr_red                       true
% 1.35/0.98  --pure_diseq_elim                       true
% 1.35/0.98  --brand_transform                       false
% 1.35/0.98  --non_eq_to_eq                          false
% 1.35/0.98  --prep_def_merge                        true
% 1.35/0.98  --prep_def_merge_prop_impl              false
% 1.35/0.98  --prep_def_merge_mbd                    true
% 1.35/0.98  --prep_def_merge_tr_red                 false
% 1.35/0.98  --prep_def_merge_tr_cl                  false
% 1.35/0.98  --smt_preprocessing                     true
% 1.35/0.98  --smt_ac_axioms                         fast
% 1.35/0.98  --preprocessed_out                      false
% 1.35/0.98  --preprocessed_stats                    false
% 1.35/0.98  
% 1.35/0.98  ------ Abstraction refinement Options
% 1.35/0.98  
% 1.35/0.98  --abstr_ref                             []
% 1.35/0.98  --abstr_ref_prep                        false
% 1.35/0.98  --abstr_ref_until_sat                   false
% 1.35/0.98  --abstr_ref_sig_restrict                funpre
% 1.35/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 1.35/0.98  --abstr_ref_under                       []
% 1.35/0.98  
% 1.35/0.98  ------ SAT Options
% 1.35/0.98  
% 1.35/0.98  --sat_mode                              false
% 1.35/0.98  --sat_fm_restart_options                ""
% 1.35/0.98  --sat_gr_def                            false
% 1.35/0.98  --sat_epr_types                         true
% 1.35/0.98  --sat_non_cyclic_types                  false
% 1.35/0.98  --sat_finite_models                     false
% 1.35/0.98  --sat_fm_lemmas                         false
% 1.35/0.98  --sat_fm_prep                           false
% 1.35/0.98  --sat_fm_uc_incr                        true
% 1.35/0.98  --sat_out_model                         small
% 1.35/0.98  --sat_out_clauses                       false
% 1.35/0.98  
% 1.35/0.98  ------ QBF Options
% 1.35/0.98  
% 1.35/0.98  --qbf_mode                              false
% 1.35/0.98  --qbf_elim_univ                         false
% 1.35/0.98  --qbf_dom_inst                          none
% 1.35/0.98  --qbf_dom_pre_inst                      false
% 1.35/0.98  --qbf_sk_in                             false
% 1.35/0.98  --qbf_pred_elim                         true
% 1.35/0.98  --qbf_split                             512
% 1.35/0.98  
% 1.35/0.98  ------ BMC1 Options
% 1.35/0.98  
% 1.35/0.98  --bmc1_incremental                      false
% 1.35/0.98  --bmc1_axioms                           reachable_all
% 1.35/0.98  --bmc1_min_bound                        0
% 1.35/0.98  --bmc1_max_bound                        -1
% 1.35/0.98  --bmc1_max_bound_default                -1
% 1.35/0.98  --bmc1_symbol_reachability              true
% 1.35/0.98  --bmc1_property_lemmas                  false
% 1.35/0.98  --bmc1_k_induction                      false
% 1.35/0.98  --bmc1_non_equiv_states                 false
% 1.35/0.98  --bmc1_deadlock                         false
% 1.35/0.98  --bmc1_ucm                              false
% 1.35/0.98  --bmc1_add_unsat_core                   none
% 1.35/0.98  --bmc1_unsat_core_children              false
% 1.35/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 1.35/0.98  --bmc1_out_stat                         full
% 1.35/0.98  --bmc1_ground_init                      false
% 1.35/0.98  --bmc1_pre_inst_next_state              false
% 1.35/0.98  --bmc1_pre_inst_state                   false
% 1.35/0.98  --bmc1_pre_inst_reach_state             false
% 1.35/0.98  --bmc1_out_unsat_core                   false
% 1.35/0.98  --bmc1_aig_witness_out                  false
% 1.35/0.98  --bmc1_verbose                          false
% 1.35/0.98  --bmc1_dump_clauses_tptp                false
% 1.35/0.98  --bmc1_dump_unsat_core_tptp             false
% 1.35/0.98  --bmc1_dump_file                        -
% 1.35/0.98  --bmc1_ucm_expand_uc_limit              128
% 1.35/0.98  --bmc1_ucm_n_expand_iterations          6
% 1.35/0.98  --bmc1_ucm_extend_mode                  1
% 1.35/0.98  --bmc1_ucm_init_mode                    2
% 1.35/0.98  --bmc1_ucm_cone_mode                    none
% 1.35/0.98  --bmc1_ucm_reduced_relation_type        0
% 1.35/0.98  --bmc1_ucm_relax_model                  4
% 1.35/0.98  --bmc1_ucm_full_tr_after_sat            true
% 1.35/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 1.35/0.98  --bmc1_ucm_layered_model                none
% 1.35/0.98  --bmc1_ucm_max_lemma_size               10
% 1.35/0.98  
% 1.35/0.98  ------ AIG Options
% 1.35/0.98  
% 1.35/0.98  --aig_mode                              false
% 1.35/0.98  
% 1.35/0.98  ------ Instantiation Options
% 1.35/0.98  
% 1.35/0.98  --instantiation_flag                    true
% 1.35/0.98  --inst_sos_flag                         false
% 1.35/0.98  --inst_sos_phase                        true
% 1.35/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.35/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.35/0.98  --inst_lit_sel_side                     num_symb
% 1.35/0.98  --inst_solver_per_active                1400
% 1.35/0.98  --inst_solver_calls_frac                1.
% 1.35/0.98  --inst_passive_queue_type               priority_queues
% 1.35/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.35/0.98  --inst_passive_queues_freq              [25;2]
% 1.35/0.98  --inst_dismatching                      true
% 1.35/0.98  --inst_eager_unprocessed_to_passive     true
% 1.35/0.98  --inst_prop_sim_given                   true
% 1.35/0.98  --inst_prop_sim_new                     false
% 1.35/0.98  --inst_subs_new                         false
% 1.35/0.98  --inst_eq_res_simp                      false
% 1.35/0.98  --inst_subs_given                       false
% 1.35/0.98  --inst_orphan_elimination               true
% 1.35/0.98  --inst_learning_loop_flag               true
% 1.35/0.98  --inst_learning_start                   3000
% 1.35/0.98  --inst_learning_factor                  2
% 1.35/0.98  --inst_start_prop_sim_after_learn       3
% 1.35/0.98  --inst_sel_renew                        solver
% 1.35/0.98  --inst_lit_activity_flag                true
% 1.35/0.98  --inst_restr_to_given                   false
% 1.35/0.98  --inst_activity_threshold               500
% 1.35/0.98  --inst_out_proof                        true
% 1.35/0.98  
% 1.35/0.98  ------ Resolution Options
% 1.35/0.98  
% 1.35/0.98  --resolution_flag                       true
% 1.35/0.98  --res_lit_sel                           adaptive
% 1.35/0.98  --res_lit_sel_side                      none
% 1.35/0.98  --res_ordering                          kbo
% 1.35/0.98  --res_to_prop_solver                    active
% 1.35/0.98  --res_prop_simpl_new                    false
% 1.35/0.98  --res_prop_simpl_given                  true
% 1.35/0.98  --res_passive_queue_type                priority_queues
% 1.35/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.35/0.98  --res_passive_queues_freq               [15;5]
% 1.35/0.98  --res_forward_subs                      full
% 1.35/0.98  --res_backward_subs                     full
% 1.35/0.98  --res_forward_subs_resolution           true
% 1.35/0.98  --res_backward_subs_resolution          true
% 1.35/0.98  --res_orphan_elimination                true
% 1.35/0.98  --res_time_limit                        2.
% 1.35/0.98  --res_out_proof                         true
% 1.35/0.98  
% 1.35/0.98  ------ Superposition Options
% 1.35/0.98  
% 1.35/0.98  --superposition_flag                    true
% 1.35/0.98  --sup_passive_queue_type                priority_queues
% 1.35/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.35/0.98  --sup_passive_queues_freq               [8;1;4]
% 1.35/0.98  --demod_completeness_check              fast
% 1.35/0.98  --demod_use_ground                      true
% 1.35/0.98  --sup_to_prop_solver                    passive
% 1.35/0.98  --sup_prop_simpl_new                    true
% 1.35/0.98  --sup_prop_simpl_given                  true
% 1.35/0.98  --sup_fun_splitting                     false
% 1.35/0.98  --sup_smt_interval                      50000
% 1.35/0.98  
% 1.35/0.98  ------ Superposition Simplification Setup
% 1.35/0.98  
% 1.35/0.98  --sup_indices_passive                   []
% 1.35/0.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.35/0.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.35/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.35/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 1.35/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.35/0.98  --sup_full_bw                           [BwDemod]
% 1.35/0.98  --sup_immed_triv                        [TrivRules]
% 1.35/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.35/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.35/0.98  --sup_immed_bw_main                     []
% 1.35/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.35/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 1.45/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.45/0.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.45/0.98  
% 1.45/0.98  ------ Combination Options
% 1.45/0.98  
% 1.45/0.98  --comb_res_mult                         3
% 1.45/0.98  --comb_sup_mult                         2
% 1.45/0.98  --comb_inst_mult                        10
% 1.45/0.98  
% 1.45/0.98  ------ Debug Options
% 1.45/0.98  
% 1.45/0.98  --dbg_backtrace                         false
% 1.45/0.98  --dbg_dump_prop_clauses                 false
% 1.45/0.98  --dbg_dump_prop_clauses_file            -
% 1.45/0.98  --dbg_out_stat                          false
% 1.45/0.98  ------ Parsing...
% 1.45/0.98  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 1.45/0.98  
% 1.45/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 4 0s  sf_e  pe_s  pe_e 
% 1.45/0.98  
% 1.45/0.98  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 1.45/0.98  
% 1.45/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 1.45/0.98  ------ Proving...
% 1.45/0.98  ------ Problem Properties 
% 1.45/0.98  
% 1.45/0.98  
% 1.45/0.98  clauses                                 16
% 1.45/0.98  conjectures                             5
% 1.45/0.98  EPR                                     5
% 1.45/0.98  Horn                                    15
% 1.45/0.98  unary                                   7
% 1.45/0.98  binary                                  0
% 1.45/0.98  lits                                    48
% 1.45/0.98  lits eq                                 7
% 1.45/0.98  fd_pure                                 0
% 1.45/0.98  fd_pseudo                               0
% 1.45/0.98  fd_cond                                 0
% 1.45/0.98  fd_pseudo_cond                          2
% 1.45/0.98  AC symbols                              0
% 1.45/0.98  
% 1.45/0.98  ------ Schedule dynamic 5 is on 
% 1.45/0.98  
% 1.45/0.98  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 1.45/0.98  
% 1.45/0.98  
% 1.45/0.98  ------ 
% 1.45/0.98  Current options:
% 1.45/0.98  ------ 
% 1.45/0.98  
% 1.45/0.98  ------ Input Options
% 1.45/0.98  
% 1.45/0.98  --out_options                           all
% 1.45/0.98  --tptp_safe_out                         true
% 1.45/0.98  --problem_path                          ""
% 1.45/0.98  --include_path                          ""
% 1.45/0.98  --clausifier                            res/vclausify_rel
% 1.45/0.98  --clausifier_options                    --mode clausify
% 1.45/0.98  --stdin                                 false
% 1.45/0.98  --stats_out                             all
% 1.45/0.98  
% 1.45/0.98  ------ General Options
% 1.45/0.98  
% 1.45/0.98  --fof                                   false
% 1.45/0.98  --time_out_real                         305.
% 1.45/0.98  --time_out_virtual                      -1.
% 1.45/0.98  --symbol_type_check                     false
% 1.45/0.98  --clausify_out                          false
% 1.45/0.98  --sig_cnt_out                           false
% 1.45/0.98  --trig_cnt_out                          false
% 1.45/0.98  --trig_cnt_out_tolerance                1.
% 1.45/0.98  --trig_cnt_out_sk_spl                   false
% 1.45/0.98  --abstr_cl_out                          false
% 1.45/0.98  
% 1.45/0.98  ------ Global Options
% 1.45/0.98  
% 1.45/0.98  --schedule                              default
% 1.45/0.98  --add_important_lit                     false
% 1.45/0.98  --prop_solver_per_cl                    1000
% 1.45/0.98  --min_unsat_core                        false
% 1.45/0.98  --soft_assumptions                      false
% 1.45/0.98  --soft_lemma_size                       3
% 1.45/0.98  --prop_impl_unit_size                   0
% 1.45/0.98  --prop_impl_unit                        []
% 1.45/0.98  --share_sel_clauses                     true
% 1.45/0.98  --reset_solvers                         false
% 1.45/0.98  --bc_imp_inh                            [conj_cone]
% 1.45/0.98  --conj_cone_tolerance                   3.
% 1.45/0.98  --extra_neg_conj                        none
% 1.45/0.98  --large_theory_mode                     true
% 1.45/0.98  --prolific_symb_bound                   200
% 1.45/0.98  --lt_threshold                          2000
% 1.45/0.98  --clause_weak_htbl                      true
% 1.45/0.98  --gc_record_bc_elim                     false
% 1.45/0.98  
% 1.45/0.98  ------ Preprocessing Options
% 1.45/0.98  
% 1.45/0.98  --preprocessing_flag                    true
% 1.45/0.98  --time_out_prep_mult                    0.1
% 1.45/0.98  --splitting_mode                        input
% 1.45/0.98  --splitting_grd                         true
% 1.45/0.98  --splitting_cvd                         false
% 1.45/0.98  --splitting_cvd_svl                     false
% 1.45/0.98  --splitting_nvd                         32
% 1.45/0.98  --sub_typing                            true
% 1.45/0.98  --prep_gs_sim                           true
% 1.45/0.98  --prep_unflatten                        true
% 1.45/0.98  --prep_res_sim                          true
% 1.45/0.98  --prep_upred                            true
% 1.45/0.98  --prep_sem_filter                       exhaustive
% 1.45/0.98  --prep_sem_filter_out                   false
% 1.45/0.98  --pred_elim                             true
% 1.45/0.98  --res_sim_input                         true
% 1.45/0.98  --eq_ax_congr_red                       true
% 1.45/0.98  --pure_diseq_elim                       true
% 1.45/0.98  --brand_transform                       false
% 1.45/0.98  --non_eq_to_eq                          false
% 1.45/0.98  --prep_def_merge                        true
% 1.45/0.98  --prep_def_merge_prop_impl              false
% 1.45/0.98  --prep_def_merge_mbd                    true
% 1.45/0.98  --prep_def_merge_tr_red                 false
% 1.45/0.98  --prep_def_merge_tr_cl                  false
% 1.45/0.98  --smt_preprocessing                     true
% 1.45/0.98  --smt_ac_axioms                         fast
% 1.45/0.98  --preprocessed_out                      false
% 1.45/0.98  --preprocessed_stats                    false
% 1.45/0.98  
% 1.45/0.98  ------ Abstraction refinement Options
% 1.45/0.98  
% 1.45/0.98  --abstr_ref                             []
% 1.45/0.98  --abstr_ref_prep                        false
% 1.45/0.98  --abstr_ref_until_sat                   false
% 1.45/0.98  --abstr_ref_sig_restrict                funpre
% 1.45/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 1.45/0.98  --abstr_ref_under                       []
% 1.45/0.98  
% 1.45/0.98  ------ SAT Options
% 1.45/0.98  
% 1.45/0.98  --sat_mode                              false
% 1.45/0.98  --sat_fm_restart_options                ""
% 1.45/0.98  --sat_gr_def                            false
% 1.45/0.98  --sat_epr_types                         true
% 1.45/0.98  --sat_non_cyclic_types                  false
% 1.45/0.98  --sat_finite_models                     false
% 1.45/0.98  --sat_fm_lemmas                         false
% 1.45/0.98  --sat_fm_prep                           false
% 1.45/0.98  --sat_fm_uc_incr                        true
% 1.45/0.98  --sat_out_model                         small
% 1.45/0.98  --sat_out_clauses                       false
% 1.45/0.98  
% 1.45/0.98  ------ QBF Options
% 1.45/0.98  
% 1.45/0.98  --qbf_mode                              false
% 1.45/0.98  --qbf_elim_univ                         false
% 1.45/0.98  --qbf_dom_inst                          none
% 1.45/0.98  --qbf_dom_pre_inst                      false
% 1.45/0.98  --qbf_sk_in                             false
% 1.45/0.98  --qbf_pred_elim                         true
% 1.45/0.98  --qbf_split                             512
% 1.45/0.98  
% 1.45/0.98  ------ BMC1 Options
% 1.45/0.98  
% 1.45/0.98  --bmc1_incremental                      false
% 1.45/0.98  --bmc1_axioms                           reachable_all
% 1.45/0.98  --bmc1_min_bound                        0
% 1.45/0.98  --bmc1_max_bound                        -1
% 1.45/0.98  --bmc1_max_bound_default                -1
% 1.45/0.98  --bmc1_symbol_reachability              true
% 1.45/0.98  --bmc1_property_lemmas                  false
% 1.45/0.98  --bmc1_k_induction                      false
% 1.45/0.98  --bmc1_non_equiv_states                 false
% 1.45/0.98  --bmc1_deadlock                         false
% 1.45/0.98  --bmc1_ucm                              false
% 1.45/0.98  --bmc1_add_unsat_core                   none
% 1.45/0.98  --bmc1_unsat_core_children              false
% 1.45/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 1.45/0.98  --bmc1_out_stat                         full
% 1.45/0.98  --bmc1_ground_init                      false
% 1.45/0.98  --bmc1_pre_inst_next_state              false
% 1.45/0.98  --bmc1_pre_inst_state                   false
% 1.45/0.98  --bmc1_pre_inst_reach_state             false
% 1.45/0.98  --bmc1_out_unsat_core                   false
% 1.45/0.98  --bmc1_aig_witness_out                  false
% 1.45/0.98  --bmc1_verbose                          false
% 1.45/0.98  --bmc1_dump_clauses_tptp                false
% 1.45/0.98  --bmc1_dump_unsat_core_tptp             false
% 1.45/0.98  --bmc1_dump_file                        -
% 1.45/0.98  --bmc1_ucm_expand_uc_limit              128
% 1.45/0.98  --bmc1_ucm_n_expand_iterations          6
% 1.45/0.98  --bmc1_ucm_extend_mode                  1
% 1.45/0.98  --bmc1_ucm_init_mode                    2
% 1.45/0.98  --bmc1_ucm_cone_mode                    none
% 1.45/0.98  --bmc1_ucm_reduced_relation_type        0
% 1.45/0.98  --bmc1_ucm_relax_model                  4
% 1.45/0.98  --bmc1_ucm_full_tr_after_sat            true
% 1.45/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 1.45/0.98  --bmc1_ucm_layered_model                none
% 1.45/0.98  --bmc1_ucm_max_lemma_size               10
% 1.45/0.98  
% 1.45/0.98  ------ AIG Options
% 1.45/0.98  
% 1.45/0.98  --aig_mode                              false
% 1.45/0.98  
% 1.45/0.98  ------ Instantiation Options
% 1.45/0.98  
% 1.45/0.98  --instantiation_flag                    true
% 1.45/0.98  --inst_sos_flag                         false
% 1.45/0.98  --inst_sos_phase                        true
% 1.45/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.45/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.45/0.98  --inst_lit_sel_side                     none
% 1.45/0.98  --inst_solver_per_active                1400
% 1.45/0.98  --inst_solver_calls_frac                1.
% 1.45/0.98  --inst_passive_queue_type               priority_queues
% 1.45/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.45/0.98  --inst_passive_queues_freq              [25;2]
% 1.45/0.98  --inst_dismatching                      true
% 1.45/0.98  --inst_eager_unprocessed_to_passive     true
% 1.45/0.98  --inst_prop_sim_given                   true
% 1.45/0.98  --inst_prop_sim_new                     false
% 1.45/0.98  --inst_subs_new                         false
% 1.45/0.98  --inst_eq_res_simp                      false
% 1.45/0.98  --inst_subs_given                       false
% 1.45/0.98  --inst_orphan_elimination               true
% 1.45/0.98  --inst_learning_loop_flag               true
% 1.45/0.98  --inst_learning_start                   3000
% 1.45/0.98  --inst_learning_factor                  2
% 1.45/0.98  --inst_start_prop_sim_after_learn       3
% 1.45/0.98  --inst_sel_renew                        solver
% 1.45/0.98  --inst_lit_activity_flag                true
% 1.45/0.98  --inst_restr_to_given                   false
% 1.45/0.98  --inst_activity_threshold               500
% 1.45/0.98  --inst_out_proof                        true
% 1.45/0.98  
% 1.45/0.98  ------ Resolution Options
% 1.45/0.98  
% 1.45/0.98  --resolution_flag                       false
% 1.45/0.98  --res_lit_sel                           adaptive
% 1.45/0.98  --res_lit_sel_side                      none
% 1.45/0.98  --res_ordering                          kbo
% 1.45/0.98  --res_to_prop_solver                    active
% 1.45/0.98  --res_prop_simpl_new                    false
% 1.45/0.98  --res_prop_simpl_given                  true
% 1.45/0.98  --res_passive_queue_type                priority_queues
% 1.45/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.45/0.98  --res_passive_queues_freq               [15;5]
% 1.45/0.98  --res_forward_subs                      full
% 1.45/0.98  --res_backward_subs                     full
% 1.45/0.98  --res_forward_subs_resolution           true
% 1.45/0.98  --res_backward_subs_resolution          true
% 1.45/0.98  --res_orphan_elimination                true
% 1.45/0.98  --res_time_limit                        2.
% 1.45/0.98  --res_out_proof                         true
% 1.45/0.98  
% 1.45/0.98  ------ Superposition Options
% 1.45/0.98  
% 1.45/0.98  --superposition_flag                    true
% 1.45/0.98  --sup_passive_queue_type                priority_queues
% 1.45/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.45/0.98  --sup_passive_queues_freq               [8;1;4]
% 1.45/0.98  --demod_completeness_check              fast
% 1.45/0.98  --demod_use_ground                      true
% 1.45/0.98  --sup_to_prop_solver                    passive
% 1.45/0.98  --sup_prop_simpl_new                    true
% 1.45/0.98  --sup_prop_simpl_given                  true
% 1.45/0.98  --sup_fun_splitting                     false
% 1.45/0.98  --sup_smt_interval                      50000
% 1.45/0.98  
% 1.45/0.98  ------ Superposition Simplification Setup
% 1.45/0.98  
% 1.45/0.98  --sup_indices_passive                   []
% 1.45/0.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.45/0.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.45/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.45/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 1.45/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.45/0.98  --sup_full_bw                           [BwDemod]
% 1.45/0.98  --sup_immed_triv                        [TrivRules]
% 1.45/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.45/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.45/0.98  --sup_immed_bw_main                     []
% 1.45/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.45/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 1.45/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.45/0.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.45/0.98  
% 1.45/0.98  ------ Combination Options
% 1.45/0.98  
% 1.45/0.98  --comb_res_mult                         3
% 1.45/0.98  --comb_sup_mult                         2
% 1.45/0.98  --comb_inst_mult                        10
% 1.45/0.98  
% 1.45/0.98  ------ Debug Options
% 1.45/0.98  
% 1.45/0.98  --dbg_backtrace                         false
% 1.45/0.98  --dbg_dump_prop_clauses                 false
% 1.45/0.98  --dbg_dump_prop_clauses_file            -
% 1.45/0.98  --dbg_out_stat                          false
% 1.45/0.98  
% 1.45/0.98  
% 1.45/0.98  
% 1.45/0.98  
% 1.45/0.98  ------ Proving...
% 1.45/0.98  
% 1.45/0.98  
% 1.45/0.98  % SZS status Theorem for theBenchmark.p
% 1.45/0.98  
% 1.45/0.98  % SZS output start CNFRefutation for theBenchmark.p
% 1.45/0.98  
% 1.45/0.98  fof(f2,axiom,(
% 1.45/0.98    ! [X0,X1] : ((v2_pralg_1(X1) & v1_partfun1(X1,X0) & v1_funct_1(X1) & v4_relat_1(X1,X0) & v1_relat_1(X1)) => ! [X2] : ((v1_partfun1(X2,X0) & v1_funct_1(X2) & v4_relat_1(X2,X0) & v1_relat_1(X2)) => (k12_pralg_1(X0,X1) = X2 <=> ! [X3] : ~(! [X4] : (l1_struct_0(X4) => ~(k1_funct_1(X2,X3) = u1_struct_0(X4) & k1_funct_1(X1,X3) = X4)) & r2_hidden(X3,X0)))))),
% 1.45/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.45/0.98  
% 1.45/0.98  fof(f9,plain,(
% 1.45/0.98    ! [X0,X1] : (! [X2] : ((k12_pralg_1(X0,X1) = X2 <=> ! [X3] : (? [X4] : ((k1_funct_1(X2,X3) = u1_struct_0(X4) & k1_funct_1(X1,X3) = X4) & l1_struct_0(X4)) | ~r2_hidden(X3,X0))) | (~v1_partfun1(X2,X0) | ~v1_funct_1(X2) | ~v4_relat_1(X2,X0) | ~v1_relat_1(X2))) | (~v2_pralg_1(X1) | ~v1_partfun1(X1,X0) | ~v1_funct_1(X1) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 1.45/0.98    inference(ennf_transformation,[],[f2])).
% 1.45/0.98  
% 1.45/0.98  fof(f10,plain,(
% 1.45/0.98    ! [X0,X1] : (! [X2] : ((k12_pralg_1(X0,X1) = X2 <=> ! [X3] : (? [X4] : (k1_funct_1(X2,X3) = u1_struct_0(X4) & k1_funct_1(X1,X3) = X4 & l1_struct_0(X4)) | ~r2_hidden(X3,X0))) | ~v1_partfun1(X2,X0) | ~v1_funct_1(X2) | ~v4_relat_1(X2,X0) | ~v1_relat_1(X2)) | ~v2_pralg_1(X1) | ~v1_partfun1(X1,X0) | ~v1_funct_1(X1) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 1.45/0.98    inference(flattening,[],[f9])).
% 1.45/0.98  
% 1.45/0.98  fof(f17,plain,(
% 1.45/0.98    ! [X0,X1] : (! [X2] : (((k12_pralg_1(X0,X1) = X2 | ? [X3] : (! [X4] : (k1_funct_1(X2,X3) != u1_struct_0(X4) | k1_funct_1(X1,X3) != X4 | ~l1_struct_0(X4)) & r2_hidden(X3,X0))) & (! [X3] : (? [X4] : (k1_funct_1(X2,X3) = u1_struct_0(X4) & k1_funct_1(X1,X3) = X4 & l1_struct_0(X4)) | ~r2_hidden(X3,X0)) | k12_pralg_1(X0,X1) != X2)) | ~v1_partfun1(X2,X0) | ~v1_funct_1(X2) | ~v4_relat_1(X2,X0) | ~v1_relat_1(X2)) | ~v2_pralg_1(X1) | ~v1_partfun1(X1,X0) | ~v1_funct_1(X1) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 1.45/0.98    inference(nnf_transformation,[],[f10])).
% 1.45/0.98  
% 1.45/0.98  fof(f18,plain,(
% 1.45/0.98    ! [X0,X1] : (! [X2] : (((k12_pralg_1(X0,X1) = X2 | ? [X3] : (! [X4] : (k1_funct_1(X2,X3) != u1_struct_0(X4) | k1_funct_1(X1,X3) != X4 | ~l1_struct_0(X4)) & r2_hidden(X3,X0))) & (! [X5] : (? [X6] : (k1_funct_1(X2,X5) = u1_struct_0(X6) & k1_funct_1(X1,X5) = X6 & l1_struct_0(X6)) | ~r2_hidden(X5,X0)) | k12_pralg_1(X0,X1) != X2)) | ~v1_partfun1(X2,X0) | ~v1_funct_1(X2) | ~v4_relat_1(X2,X0) | ~v1_relat_1(X2)) | ~v2_pralg_1(X1) | ~v1_partfun1(X1,X0) | ~v1_funct_1(X1) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 1.45/0.98    inference(rectify,[],[f17])).
% 1.45/0.98  
% 1.45/0.98  fof(f20,plain,(
% 1.45/0.98    ! [X5,X2,X1] : (? [X6] : (k1_funct_1(X2,X5) = u1_struct_0(X6) & k1_funct_1(X1,X5) = X6 & l1_struct_0(X6)) => (k1_funct_1(X2,X5) = u1_struct_0(sK1(X1,X2,X5)) & k1_funct_1(X1,X5) = sK1(X1,X2,X5) & l1_struct_0(sK1(X1,X2,X5))))),
% 1.45/0.98    introduced(choice_axiom,[])).
% 1.45/0.98  
% 1.45/0.98  fof(f19,plain,(
% 1.45/0.98    ! [X2,X1,X0] : (? [X3] : (! [X4] : (k1_funct_1(X2,X3) != u1_struct_0(X4) | k1_funct_1(X1,X3) != X4 | ~l1_struct_0(X4)) & r2_hidden(X3,X0)) => (! [X4] : (k1_funct_1(X2,sK0(X0,X1,X2)) != u1_struct_0(X4) | k1_funct_1(X1,sK0(X0,X1,X2)) != X4 | ~l1_struct_0(X4)) & r2_hidden(sK0(X0,X1,X2),X0)))),
% 1.45/0.98    introduced(choice_axiom,[])).
% 1.45/0.98  
% 1.45/0.98  fof(f21,plain,(
% 1.45/0.98    ! [X0,X1] : (! [X2] : (((k12_pralg_1(X0,X1) = X2 | (! [X4] : (k1_funct_1(X2,sK0(X0,X1,X2)) != u1_struct_0(X4) | k1_funct_1(X1,sK0(X0,X1,X2)) != X4 | ~l1_struct_0(X4)) & r2_hidden(sK0(X0,X1,X2),X0))) & (! [X5] : ((k1_funct_1(X2,X5) = u1_struct_0(sK1(X1,X2,X5)) & k1_funct_1(X1,X5) = sK1(X1,X2,X5) & l1_struct_0(sK1(X1,X2,X5))) | ~r2_hidden(X5,X0)) | k12_pralg_1(X0,X1) != X2)) | ~v1_partfun1(X2,X0) | ~v1_funct_1(X2) | ~v4_relat_1(X2,X0) | ~v1_relat_1(X2)) | ~v2_pralg_1(X1) | ~v1_partfun1(X1,X0) | ~v1_funct_1(X1) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 1.45/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f18,f20,f19])).
% 1.45/0.98  
% 1.45/0.98  fof(f28,plain,(
% 1.45/0.98    ( ! [X2,X0,X5,X1] : (k1_funct_1(X1,X5) = sK1(X1,X2,X5) | ~r2_hidden(X5,X0) | k12_pralg_1(X0,X1) != X2 | ~v1_partfun1(X2,X0) | ~v1_funct_1(X2) | ~v4_relat_1(X2,X0) | ~v1_relat_1(X2) | ~v2_pralg_1(X1) | ~v1_partfun1(X1,X0) | ~v1_funct_1(X1) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 1.45/0.98    inference(cnf_transformation,[],[f21])).
% 1.45/0.98  
% 1.45/0.98  fof(f47,plain,(
% 1.45/0.98    ( ! [X0,X5,X1] : (k1_funct_1(X1,X5) = sK1(X1,k12_pralg_1(X0,X1),X5) | ~r2_hidden(X5,X0) | ~v1_partfun1(k12_pralg_1(X0,X1),X0) | ~v1_funct_1(k12_pralg_1(X0,X1)) | ~v4_relat_1(k12_pralg_1(X0,X1),X0) | ~v1_relat_1(k12_pralg_1(X0,X1)) | ~v2_pralg_1(X1) | ~v1_partfun1(X1,X0) | ~v1_funct_1(X1) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 1.45/0.98    inference(equality_resolution,[],[f28])).
% 1.45/0.98  
% 1.45/0.98  fof(f3,axiom,(
% 1.45/0.98    ! [X0,X1] : ((v2_pralg_1(X1) & v1_partfun1(X1,X0) & v1_funct_1(X1) & v4_relat_1(X1,X0) & v1_relat_1(X1)) => (v1_partfun1(k12_pralg_1(X0,X1),X0) & v1_funct_1(k12_pralg_1(X0,X1)) & v4_relat_1(k12_pralg_1(X0,X1),X0) & v1_relat_1(k12_pralg_1(X0,X1))))),
% 1.45/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.45/0.98  
% 1.45/0.98  fof(f11,plain,(
% 1.45/0.98    ! [X0,X1] : ((v1_partfun1(k12_pralg_1(X0,X1),X0) & v1_funct_1(k12_pralg_1(X0,X1)) & v4_relat_1(k12_pralg_1(X0,X1),X0) & v1_relat_1(k12_pralg_1(X0,X1))) | (~v2_pralg_1(X1) | ~v1_partfun1(X1,X0) | ~v1_funct_1(X1) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 1.45/0.98    inference(ennf_transformation,[],[f3])).
% 1.45/0.98  
% 1.45/0.98  fof(f12,plain,(
% 1.45/0.98    ! [X0,X1] : ((v1_partfun1(k12_pralg_1(X0,X1),X0) & v1_funct_1(k12_pralg_1(X0,X1)) & v4_relat_1(k12_pralg_1(X0,X1),X0) & v1_relat_1(k12_pralg_1(X0,X1))) | ~v2_pralg_1(X1) | ~v1_partfun1(X1,X0) | ~v1_funct_1(X1) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 1.45/0.98    inference(flattening,[],[f11])).
% 1.45/0.98  
% 1.45/0.98  fof(f32,plain,(
% 1.45/0.98    ( ! [X0,X1] : (v1_relat_1(k12_pralg_1(X0,X1)) | ~v2_pralg_1(X1) | ~v1_partfun1(X1,X0) | ~v1_funct_1(X1) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 1.45/0.98    inference(cnf_transformation,[],[f12])).
% 1.45/0.98  
% 1.45/0.98  fof(f33,plain,(
% 1.45/0.98    ( ! [X0,X1] : (v4_relat_1(k12_pralg_1(X0,X1),X0) | ~v2_pralg_1(X1) | ~v1_partfun1(X1,X0) | ~v1_funct_1(X1) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 1.45/0.98    inference(cnf_transformation,[],[f12])).
% 1.45/0.98  
% 1.45/0.98  fof(f34,plain,(
% 1.45/0.98    ( ! [X0,X1] : (v1_funct_1(k12_pralg_1(X0,X1)) | ~v2_pralg_1(X1) | ~v1_partfun1(X1,X0) | ~v1_funct_1(X1) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 1.45/0.98    inference(cnf_transformation,[],[f12])).
% 1.45/0.98  
% 1.45/0.98  fof(f35,plain,(
% 1.45/0.98    ( ! [X0,X1] : (v1_partfun1(k12_pralg_1(X0,X1),X0) | ~v2_pralg_1(X1) | ~v1_partfun1(X1,X0) | ~v1_funct_1(X1) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 1.45/0.98    inference(cnf_transformation,[],[f12])).
% 1.45/0.98  
% 1.45/0.98  fof(f5,conjecture,(
% 1.45/0.98    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : ((v2_pralg_1(X1) & v1_partfun1(X1,X0) & v1_funct_1(X1) & v4_relat_1(X1,X0) & v1_relat_1(X1)) => ! [X2] : (m1_subset_1(X2,X0) => k1_funct_1(k12_pralg_1(X0,X1),X2) = u1_struct_0(k10_pralg_1(X0,X1,X2)))))),
% 1.45/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.45/0.98  
% 1.45/0.98  fof(f6,negated_conjecture,(
% 1.45/0.98    ~! [X0] : (~v1_xboole_0(X0) => ! [X1] : ((v2_pralg_1(X1) & v1_partfun1(X1,X0) & v1_funct_1(X1) & v4_relat_1(X1,X0) & v1_relat_1(X1)) => ! [X2] : (m1_subset_1(X2,X0) => k1_funct_1(k12_pralg_1(X0,X1),X2) = u1_struct_0(k10_pralg_1(X0,X1,X2)))))),
% 1.45/0.98    inference(negated_conjecture,[],[f5])).
% 1.45/0.98  
% 1.45/0.98  fof(f15,plain,(
% 1.45/0.98    ? [X0] : (? [X1] : (? [X2] : (k1_funct_1(k12_pralg_1(X0,X1),X2) != u1_struct_0(k10_pralg_1(X0,X1,X2)) & m1_subset_1(X2,X0)) & (v2_pralg_1(X1) & v1_partfun1(X1,X0) & v1_funct_1(X1) & v4_relat_1(X1,X0) & v1_relat_1(X1))) & ~v1_xboole_0(X0))),
% 1.45/0.98    inference(ennf_transformation,[],[f6])).
% 1.45/0.98  
% 1.45/0.98  fof(f16,plain,(
% 1.45/0.98    ? [X0] : (? [X1] : (? [X2] : (k1_funct_1(k12_pralg_1(X0,X1),X2) != u1_struct_0(k10_pralg_1(X0,X1,X2)) & m1_subset_1(X2,X0)) & v2_pralg_1(X1) & v1_partfun1(X1,X0) & v1_funct_1(X1) & v4_relat_1(X1,X0) & v1_relat_1(X1)) & ~v1_xboole_0(X0))),
% 1.45/0.98    inference(flattening,[],[f15])).
% 1.45/0.98  
% 1.45/0.98  fof(f24,plain,(
% 1.45/0.98    ( ! [X0,X1] : (? [X2] : (k1_funct_1(k12_pralg_1(X0,X1),X2) != u1_struct_0(k10_pralg_1(X0,X1,X2)) & m1_subset_1(X2,X0)) => (k1_funct_1(k12_pralg_1(X0,X1),sK4) != u1_struct_0(k10_pralg_1(X0,X1,sK4)) & m1_subset_1(sK4,X0))) )),
% 1.45/0.98    introduced(choice_axiom,[])).
% 1.45/0.98  
% 1.45/0.98  fof(f23,plain,(
% 1.45/0.98    ( ! [X0] : (? [X1] : (? [X2] : (k1_funct_1(k12_pralg_1(X0,X1),X2) != u1_struct_0(k10_pralg_1(X0,X1,X2)) & m1_subset_1(X2,X0)) & v2_pralg_1(X1) & v1_partfun1(X1,X0) & v1_funct_1(X1) & v4_relat_1(X1,X0) & v1_relat_1(X1)) => (? [X2] : (k1_funct_1(k12_pralg_1(X0,sK3),X2) != u1_struct_0(k10_pralg_1(X0,sK3,X2)) & m1_subset_1(X2,X0)) & v2_pralg_1(sK3) & v1_partfun1(sK3,X0) & v1_funct_1(sK3) & v4_relat_1(sK3,X0) & v1_relat_1(sK3))) )),
% 1.45/0.98    introduced(choice_axiom,[])).
% 1.45/0.98  
% 1.45/0.98  fof(f22,plain,(
% 1.45/0.98    ? [X0] : (? [X1] : (? [X2] : (k1_funct_1(k12_pralg_1(X0,X1),X2) != u1_struct_0(k10_pralg_1(X0,X1,X2)) & m1_subset_1(X2,X0)) & v2_pralg_1(X1) & v1_partfun1(X1,X0) & v1_funct_1(X1) & v4_relat_1(X1,X0) & v1_relat_1(X1)) & ~v1_xboole_0(X0)) => (? [X1] : (? [X2] : (k1_funct_1(k12_pralg_1(sK2,X1),X2) != u1_struct_0(k10_pralg_1(sK2,X1,X2)) & m1_subset_1(X2,sK2)) & v2_pralg_1(X1) & v1_partfun1(X1,sK2) & v1_funct_1(X1) & v4_relat_1(X1,sK2) & v1_relat_1(X1)) & ~v1_xboole_0(sK2))),
% 1.45/0.98    introduced(choice_axiom,[])).
% 1.45/0.98  
% 1.45/0.98  fof(f25,plain,(
% 1.45/0.98    ((k1_funct_1(k12_pralg_1(sK2,sK3),sK4) != u1_struct_0(k10_pralg_1(sK2,sK3,sK4)) & m1_subset_1(sK4,sK2)) & v2_pralg_1(sK3) & v1_partfun1(sK3,sK2) & v1_funct_1(sK3) & v4_relat_1(sK3,sK2) & v1_relat_1(sK3)) & ~v1_xboole_0(sK2)),
% 1.45/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f16,f24,f23,f22])).
% 1.45/0.98  
% 1.45/0.98  fof(f42,plain,(
% 1.45/0.98    v2_pralg_1(sK3)),
% 1.45/0.98    inference(cnf_transformation,[],[f25])).
% 1.45/0.98  
% 1.45/0.98  fof(f38,plain,(
% 1.45/0.98    v1_relat_1(sK3)),
% 1.45/0.98    inference(cnf_transformation,[],[f25])).
% 1.45/0.98  
% 1.45/0.98  fof(f40,plain,(
% 1.45/0.98    v1_funct_1(sK3)),
% 1.45/0.98    inference(cnf_transformation,[],[f25])).
% 1.45/0.98  
% 1.45/0.98  fof(f29,plain,(
% 1.45/0.98    ( ! [X2,X0,X5,X1] : (k1_funct_1(X2,X5) = u1_struct_0(sK1(X1,X2,X5)) | ~r2_hidden(X5,X0) | k12_pralg_1(X0,X1) != X2 | ~v1_partfun1(X2,X0) | ~v1_funct_1(X2) | ~v4_relat_1(X2,X0) | ~v1_relat_1(X2) | ~v2_pralg_1(X1) | ~v1_partfun1(X1,X0) | ~v1_funct_1(X1) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 1.45/0.98    inference(cnf_transformation,[],[f21])).
% 1.45/0.98  
% 1.45/0.98  fof(f46,plain,(
% 1.45/0.98    ( ! [X0,X5,X1] : (k1_funct_1(k12_pralg_1(X0,X1),X5) = u1_struct_0(sK1(X1,k12_pralg_1(X0,X1),X5)) | ~r2_hidden(X5,X0) | ~v1_partfun1(k12_pralg_1(X0,X1),X0) | ~v1_funct_1(k12_pralg_1(X0,X1)) | ~v4_relat_1(k12_pralg_1(X0,X1),X0) | ~v1_relat_1(k12_pralg_1(X0,X1)) | ~v2_pralg_1(X1) | ~v1_partfun1(X1,X0) | ~v1_funct_1(X1) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 1.45/0.98    inference(equality_resolution,[],[f29])).
% 1.45/0.98  
% 1.45/0.98  fof(f43,plain,(
% 1.45/0.98    m1_subset_1(sK4,sK2)),
% 1.45/0.98    inference(cnf_transformation,[],[f25])).
% 1.45/0.98  
% 1.45/0.98  fof(f4,axiom,(
% 1.45/0.98    ! [X0,X1,X2] : ((m1_subset_1(X2,X0) & v2_pralg_1(X1) & v1_partfun1(X1,X0) & v1_funct_1(X1) & v4_relat_1(X1,X0) & v1_relat_1(X1) & ~v1_xboole_0(X0)) => k1_funct_1(X1,X2) = k10_pralg_1(X0,X1,X2))),
% 1.45/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.45/0.98  
% 1.45/0.98  fof(f13,plain,(
% 1.45/0.98    ! [X0,X1,X2] : (k1_funct_1(X1,X2) = k10_pralg_1(X0,X1,X2) | (~m1_subset_1(X2,X0) | ~v2_pralg_1(X1) | ~v1_partfun1(X1,X0) | ~v1_funct_1(X1) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1) | v1_xboole_0(X0)))),
% 1.45/0.98    inference(ennf_transformation,[],[f4])).
% 1.45/0.98  
% 1.45/0.98  fof(f14,plain,(
% 1.45/0.98    ! [X0,X1,X2] : (k1_funct_1(X1,X2) = k10_pralg_1(X0,X1,X2) | ~m1_subset_1(X2,X0) | ~v2_pralg_1(X1) | ~v1_partfun1(X1,X0) | ~v1_funct_1(X1) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1) | v1_xboole_0(X0))),
% 1.45/0.98    inference(flattening,[],[f13])).
% 1.45/0.98  
% 1.45/0.98  fof(f36,plain,(
% 1.45/0.98    ( ! [X2,X0,X1] : (k1_funct_1(X1,X2) = k10_pralg_1(X0,X1,X2) | ~m1_subset_1(X2,X0) | ~v2_pralg_1(X1) | ~v1_partfun1(X1,X0) | ~v1_funct_1(X1) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1) | v1_xboole_0(X0)) )),
% 1.45/0.98    inference(cnf_transformation,[],[f14])).
% 1.45/0.98  
% 1.45/0.98  fof(f37,plain,(
% 1.45/0.98    ~v1_xboole_0(sK2)),
% 1.45/0.98    inference(cnf_transformation,[],[f25])).
% 1.45/0.98  
% 1.45/0.98  fof(f39,plain,(
% 1.45/0.98    v4_relat_1(sK3,sK2)),
% 1.45/0.98    inference(cnf_transformation,[],[f25])).
% 1.45/0.98  
% 1.45/0.98  fof(f41,plain,(
% 1.45/0.98    v1_partfun1(sK3,sK2)),
% 1.45/0.98    inference(cnf_transformation,[],[f25])).
% 1.45/0.98  
% 1.45/0.98  fof(f44,plain,(
% 1.45/0.98    k1_funct_1(k12_pralg_1(sK2,sK3),sK4) != u1_struct_0(k10_pralg_1(sK2,sK3,sK4))),
% 1.45/0.98    inference(cnf_transformation,[],[f25])).
% 1.45/0.98  
% 1.45/0.98  fof(f1,axiom,(
% 1.45/0.98    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 1.45/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.45/0.98  
% 1.45/0.98  fof(f7,plain,(
% 1.45/0.98    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 1.45/0.98    inference(ennf_transformation,[],[f1])).
% 1.45/0.98  
% 1.45/0.98  fof(f8,plain,(
% 1.45/0.98    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 1.45/0.98    inference(flattening,[],[f7])).
% 1.45/0.98  
% 1.45/0.98  fof(f26,plain,(
% 1.45/0.98    ( ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1)) )),
% 1.45/0.98    inference(cnf_transformation,[],[f8])).
% 1.45/0.98  
% 1.45/0.98  cnf(c_1706,plain,
% 1.45/0.98      ( X0_49 != X1_49 | u1_struct_0(X0_49) = u1_struct_0(X1_49) ),
% 1.45/0.98      theory(equality) ).
% 1.45/0.98  
% 1.45/0.98  cnf(c_2465,plain,
% 1.45/0.98      ( k10_pralg_1(sK2,sK3,sK4) != sK1(sK3,k12_pralg_1(sK2,sK3),sK4)
% 1.45/0.98      | u1_struct_0(k10_pralg_1(sK2,sK3,sK4)) = u1_struct_0(sK1(sK3,k12_pralg_1(sK2,sK3),sK4)) ),
% 1.45/0.98      inference(instantiation,[status(thm)],[c_1706]) ).
% 1.45/0.98  
% 1.45/0.98  cnf(c_1701,plain,
% 1.45/0.98      ( X0_49 != X1_49 | X2_49 != X1_49 | X2_49 = X0_49 ),
% 1.45/0.98      theory(equality) ).
% 1.45/0.98  
% 1.45/0.98  cnf(c_2178,plain,
% 1.45/0.98      ( k1_funct_1(k12_pralg_1(sK2,sK3),sK4) != X0_49
% 1.45/0.98      | k1_funct_1(k12_pralg_1(sK2,sK3),sK4) = u1_struct_0(k10_pralg_1(sK2,sK3,sK4))
% 1.45/0.98      | u1_struct_0(k10_pralg_1(sK2,sK3,sK4)) != X0_49 ),
% 1.45/0.98      inference(instantiation,[status(thm)],[c_1701]) ).
% 1.45/0.98  
% 1.45/0.98  cnf(c_2288,plain,
% 1.45/0.98      ( k1_funct_1(k12_pralg_1(sK2,sK3),sK4) = u1_struct_0(k10_pralg_1(sK2,sK3,sK4))
% 1.45/0.98      | k1_funct_1(k12_pralg_1(sK2,sK3),sK4) != u1_struct_0(sK1(sK3,k12_pralg_1(sK2,sK3),sK4))
% 1.45/0.98      | u1_struct_0(k10_pralg_1(sK2,sK3,sK4)) != u1_struct_0(sK1(sK3,k12_pralg_1(sK2,sK3),sK4)) ),
% 1.45/0.98      inference(instantiation,[status(thm)],[c_2178]) ).
% 1.45/0.98  
% 1.45/0.98  cnf(c_2184,plain,
% 1.45/0.98      ( X0_49 != X1_49
% 1.45/0.98      | k1_funct_1(k12_pralg_1(sK2,sK3),sK4) != X1_49
% 1.45/0.98      | k1_funct_1(k12_pralg_1(sK2,sK3),sK4) = X0_49 ),
% 1.45/0.98      inference(instantiation,[status(thm)],[c_1701]) ).
% 1.45/0.98  
% 1.45/0.98  cnf(c_2207,plain,
% 1.45/0.98      ( X0_49 != k1_funct_1(k12_pralg_1(sK2,sK3),sK4)
% 1.45/0.98      | k1_funct_1(k12_pralg_1(sK2,sK3),sK4) = X0_49
% 1.45/0.98      | k1_funct_1(k12_pralg_1(sK2,sK3),sK4) != k1_funct_1(k12_pralg_1(sK2,sK3),sK4) ),
% 1.45/0.98      inference(instantiation,[status(thm)],[c_2184]) ).
% 1.45/0.98  
% 1.45/0.98  cnf(c_2274,plain,
% 1.45/0.98      ( k1_funct_1(k12_pralg_1(sK2,sK3),sK4) != k1_funct_1(k12_pralg_1(sK2,sK3),sK4)
% 1.45/0.98      | k1_funct_1(k12_pralg_1(sK2,sK3),sK4) = u1_struct_0(sK1(sK3,k12_pralg_1(sK2,sK3),sK4))
% 1.45/0.98      | u1_struct_0(sK1(sK3,k12_pralg_1(sK2,sK3),sK4)) != k1_funct_1(k12_pralg_1(sK2,sK3),sK4) ),
% 1.45/0.98      inference(instantiation,[status(thm)],[c_2207]) ).
% 1.45/0.98  
% 1.45/0.98  cnf(c_2190,plain,
% 1.45/0.98      ( X0_49 != X1_49
% 1.45/0.98      | X0_49 = sK1(sK3,k12_pralg_1(X0_47,sK3),X0_48)
% 1.45/0.98      | sK1(sK3,k12_pralg_1(X0_47,sK3),X0_48) != X1_49 ),
% 1.45/0.98      inference(instantiation,[status(thm)],[c_1701]) ).
% 1.45/0.98  
% 1.45/0.98  cnf(c_2224,plain,
% 1.45/0.98      ( X0_49 = sK1(sK3,k12_pralg_1(X0_47,sK3),X0_48)
% 1.45/0.98      | X0_49 != k1_funct_1(sK3,X0_48)
% 1.45/0.98      | sK1(sK3,k12_pralg_1(X0_47,sK3),X0_48) != k1_funct_1(sK3,X0_48) ),
% 1.45/0.98      inference(instantiation,[status(thm)],[c_2190]) ).
% 1.45/0.98  
% 1.45/0.98  cnf(c_2244,plain,
% 1.45/0.98      ( k10_pralg_1(sK2,sK3,sK4) = sK1(sK3,k12_pralg_1(X0_47,sK3),sK4)
% 1.45/0.98      | k10_pralg_1(sK2,sK3,sK4) != k1_funct_1(sK3,sK4)
% 1.45/0.98      | sK1(sK3,k12_pralg_1(X0_47,sK3),sK4) != k1_funct_1(sK3,sK4) ),
% 1.45/0.98      inference(instantiation,[status(thm)],[c_2224]) ).
% 1.45/0.98  
% 1.45/0.98  cnf(c_2245,plain,
% 1.45/0.98      ( k10_pralg_1(sK2,sK3,sK4) = sK1(sK3,k12_pralg_1(sK2,sK3),sK4)
% 1.45/0.98      | k10_pralg_1(sK2,sK3,sK4) != k1_funct_1(sK3,sK4)
% 1.45/0.98      | sK1(sK3,k12_pralg_1(sK2,sK3),sK4) != k1_funct_1(sK3,sK4) ),
% 1.45/0.98      inference(instantiation,[status(thm)],[c_2244]) ).
% 1.45/0.98  
% 1.45/0.98  cnf(c_1699,plain,( X0_49 = X0_49 ),theory(equality) ).
% 1.45/0.98  
% 1.45/0.98  cnf(c_2183,plain,
% 1.45/0.98      ( k1_funct_1(k12_pralg_1(sK2,sK3),sK4) = k1_funct_1(k12_pralg_1(sK2,sK3),sK4) ),
% 1.45/0.98      inference(instantiation,[status(thm)],[c_1699]) ).
% 1.45/0.98  
% 1.45/0.98  cnf(c_4,plain,
% 1.45/0.98      ( ~ v4_relat_1(X0,X1)
% 1.45/0.98      | ~ v4_relat_1(k12_pralg_1(X1,X0),X1)
% 1.45/0.98      | ~ v1_partfun1(X0,X1)
% 1.45/0.98      | ~ v1_partfun1(k12_pralg_1(X1,X0),X1)
% 1.45/0.98      | ~ r2_hidden(X2,X1)
% 1.45/0.98      | ~ v2_pralg_1(X0)
% 1.45/0.98      | ~ v1_relat_1(X0)
% 1.45/0.98      | ~ v1_relat_1(k12_pralg_1(X1,X0))
% 1.45/0.98      | ~ v1_funct_1(X0)
% 1.45/0.98      | ~ v1_funct_1(k12_pralg_1(X1,X0))
% 1.45/0.98      | sK1(X0,k12_pralg_1(X1,X0),X2) = k1_funct_1(X0,X2) ),
% 1.45/0.98      inference(cnf_transformation,[],[f47]) ).
% 1.45/0.98  
% 1.45/0.98  cnf(c_9,plain,
% 1.45/0.98      ( ~ v4_relat_1(X0,X1)
% 1.45/0.98      | ~ v1_partfun1(X0,X1)
% 1.45/0.98      | ~ v2_pralg_1(X0)
% 1.45/0.98      | ~ v1_relat_1(X0)
% 1.45/0.98      | v1_relat_1(k12_pralg_1(X1,X0))
% 1.45/0.98      | ~ v1_funct_1(X0) ),
% 1.45/0.98      inference(cnf_transformation,[],[f32]) ).
% 1.45/0.98  
% 1.45/0.98  cnf(c_8,plain,
% 1.45/0.98      ( ~ v4_relat_1(X0,X1)
% 1.45/0.98      | v4_relat_1(k12_pralg_1(X1,X0),X1)
% 1.45/0.98      | ~ v1_partfun1(X0,X1)
% 1.45/0.98      | ~ v2_pralg_1(X0)
% 1.45/0.98      | ~ v1_relat_1(X0)
% 1.45/0.98      | ~ v1_funct_1(X0) ),
% 1.45/0.98      inference(cnf_transformation,[],[f33]) ).
% 1.45/0.98  
% 1.45/0.98  cnf(c_7,plain,
% 1.45/0.98      ( ~ v4_relat_1(X0,X1)
% 1.45/0.98      | ~ v1_partfun1(X0,X1)
% 1.45/0.98      | ~ v2_pralg_1(X0)
% 1.45/0.98      | ~ v1_relat_1(X0)
% 1.45/0.98      | ~ v1_funct_1(X0)
% 1.45/0.98      | v1_funct_1(k12_pralg_1(X1,X0)) ),
% 1.45/0.98      inference(cnf_transformation,[],[f34]) ).
% 1.45/0.98  
% 1.45/0.98  cnf(c_6,plain,
% 1.45/0.98      ( ~ v4_relat_1(X0,X1)
% 1.45/0.98      | ~ v1_partfun1(X0,X1)
% 1.45/0.98      | v1_partfun1(k12_pralg_1(X1,X0),X1)
% 1.45/0.98      | ~ v2_pralg_1(X0)
% 1.45/0.98      | ~ v1_relat_1(X0)
% 1.45/0.98      | ~ v1_funct_1(X0) ),
% 1.45/0.98      inference(cnf_transformation,[],[f35]) ).
% 1.45/0.98  
% 1.45/0.98  cnf(c_115,plain,
% 1.45/0.98      ( ~ v1_funct_1(X0)
% 1.45/0.98      | ~ v1_partfun1(X0,X1)
% 1.45/0.98      | ~ v4_relat_1(X0,X1)
% 1.45/0.98      | ~ r2_hidden(X2,X1)
% 1.45/0.98      | ~ v2_pralg_1(X0)
% 1.45/0.98      | ~ v1_relat_1(X0)
% 1.45/0.98      | sK1(X0,k12_pralg_1(X1,X0),X2) = k1_funct_1(X0,X2) ),
% 1.45/0.98      inference(global_propositional_subsumption,
% 1.45/0.98                [status(thm)],
% 1.45/0.98                [c_4,c_9,c_8,c_7,c_6]) ).
% 1.45/0.98  
% 1.45/0.98  cnf(c_116,plain,
% 1.45/0.98      ( ~ v4_relat_1(X0,X1)
% 1.45/0.98      | ~ v1_partfun1(X0,X1)
% 1.45/0.98      | ~ r2_hidden(X2,X1)
% 1.45/0.98      | ~ v2_pralg_1(X0)
% 1.45/0.98      | ~ v1_relat_1(X0)
% 1.45/0.98      | ~ v1_funct_1(X0)
% 1.45/0.98      | sK1(X0,k12_pralg_1(X1,X0),X2) = k1_funct_1(X0,X2) ),
% 1.45/0.98      inference(renaming,[status(thm)],[c_115]) ).
% 1.45/0.98  
% 1.45/0.98  cnf(c_13,negated_conjecture,
% 1.45/0.98      ( v2_pralg_1(sK3) ),
% 1.45/0.98      inference(cnf_transformation,[],[f42]) ).
% 1.45/0.98  
% 1.45/0.98  cnf(c_472,plain,
% 1.45/0.98      ( ~ v4_relat_1(X0,X1)
% 1.45/0.98      | ~ v1_partfun1(X0,X1)
% 1.45/0.98      | ~ r2_hidden(X2,X1)
% 1.45/0.98      | ~ v1_relat_1(X0)
% 1.45/0.98      | ~ v1_funct_1(X0)
% 1.45/0.98      | sK1(X0,k12_pralg_1(X1,X0),X2) = k1_funct_1(X0,X2)
% 1.45/0.98      | sK3 != X0 ),
% 1.45/0.98      inference(resolution_lifted,[status(thm)],[c_116,c_13]) ).
% 1.45/0.98  
% 1.45/0.98  cnf(c_473,plain,
% 1.45/0.98      ( ~ v4_relat_1(sK3,X0)
% 1.45/0.98      | ~ v1_partfun1(sK3,X0)
% 1.45/0.98      | ~ r2_hidden(X1,X0)
% 1.45/0.98      | ~ v1_relat_1(sK3)
% 1.45/0.98      | ~ v1_funct_1(sK3)
% 1.45/0.98      | sK1(sK3,k12_pralg_1(X0,sK3),X1) = k1_funct_1(sK3,X1) ),
% 1.45/0.98      inference(unflattening,[status(thm)],[c_472]) ).
% 1.45/0.98  
% 1.45/0.98  cnf(c_17,negated_conjecture,
% 1.45/0.98      ( v1_relat_1(sK3) ),
% 1.45/0.98      inference(cnf_transformation,[],[f38]) ).
% 1.45/0.98  
% 1.45/0.98  cnf(c_15,negated_conjecture,
% 1.45/0.98      ( v1_funct_1(sK3) ),
% 1.45/0.98      inference(cnf_transformation,[],[f40]) ).
% 1.45/0.98  
% 1.45/0.98  cnf(c_477,plain,
% 1.45/0.98      ( ~ v4_relat_1(sK3,X0)
% 1.45/0.98      | ~ v1_partfun1(sK3,X0)
% 1.45/0.98      | ~ r2_hidden(X1,X0)
% 1.45/0.98      | sK1(sK3,k12_pralg_1(X0,sK3),X1) = k1_funct_1(sK3,X1) ),
% 1.45/0.98      inference(global_propositional_subsumption,
% 1.45/0.98                [status(thm)],
% 1.45/0.98                [c_473,c_17,c_15]) ).
% 1.45/0.98  
% 1.45/0.98  cnf(c_1685,plain,
% 1.45/0.98      ( ~ v4_relat_1(sK3,X0_47)
% 1.45/0.98      | ~ v1_partfun1(sK3,X0_47)
% 1.45/0.98      | ~ r2_hidden(X0_48,X0_47)
% 1.45/0.98      | sK1(sK3,k12_pralg_1(X0_47,sK3),X0_48) = k1_funct_1(sK3,X0_48) ),
% 1.45/0.98      inference(subtyping,[status(esa)],[c_477]) ).
% 1.45/0.98  
% 1.45/0.98  cnf(c_1745,plain,
% 1.45/0.98      ( ~ v4_relat_1(sK3,sK2)
% 1.45/0.98      | ~ v1_partfun1(sK3,sK2)
% 1.45/0.98      | ~ r2_hidden(sK4,sK2)
% 1.45/0.98      | sK1(sK3,k12_pralg_1(sK2,sK3),sK4) = k1_funct_1(sK3,sK4) ),
% 1.45/0.98      inference(instantiation,[status(thm)],[c_1685]) ).
% 1.45/0.98  
% 1.45/0.98  cnf(c_3,plain,
% 1.45/0.98      ( ~ v4_relat_1(X0,X1)
% 1.45/0.98      | ~ v4_relat_1(k12_pralg_1(X1,X0),X1)
% 1.45/0.98      | ~ v1_partfun1(X0,X1)
% 1.45/0.98      | ~ v1_partfun1(k12_pralg_1(X1,X0),X1)
% 1.45/0.98      | ~ r2_hidden(X2,X1)
% 1.45/0.98      | ~ v2_pralg_1(X0)
% 1.45/0.98      | ~ v1_relat_1(X0)
% 1.45/0.98      | ~ v1_relat_1(k12_pralg_1(X1,X0))
% 1.45/0.98      | ~ v1_funct_1(X0)
% 1.45/0.98      | ~ v1_funct_1(k12_pralg_1(X1,X0))
% 1.45/0.98      | u1_struct_0(sK1(X0,k12_pralg_1(X1,X0),X2)) = k1_funct_1(k12_pralg_1(X1,X0),X2) ),
% 1.45/0.98      inference(cnf_transformation,[],[f46]) ).
% 1.45/0.98  
% 1.45/0.98  cnf(c_122,plain,
% 1.45/0.98      ( ~ v1_funct_1(X0)
% 1.45/0.98      | ~ v1_partfun1(X0,X1)
% 1.45/0.98      | ~ v4_relat_1(X0,X1)
% 1.45/0.98      | ~ r2_hidden(X2,X1)
% 1.45/0.98      | ~ v2_pralg_1(X0)
% 1.45/0.98      | ~ v1_relat_1(X0)
% 1.45/0.98      | u1_struct_0(sK1(X0,k12_pralg_1(X1,X0),X2)) = k1_funct_1(k12_pralg_1(X1,X0),X2) ),
% 1.45/0.98      inference(global_propositional_subsumption,
% 1.45/0.98                [status(thm)],
% 1.45/0.98                [c_3,c_9,c_8,c_7,c_6]) ).
% 1.45/0.98  
% 1.45/0.98  cnf(c_123,plain,
% 1.45/0.98      ( ~ v4_relat_1(X0,X1)
% 1.45/0.98      | ~ v1_partfun1(X0,X1)
% 1.45/0.98      | ~ r2_hidden(X2,X1)
% 1.45/0.98      | ~ v2_pralg_1(X0)
% 1.45/0.98      | ~ v1_relat_1(X0)
% 1.45/0.98      | ~ v1_funct_1(X0)
% 1.45/0.98      | u1_struct_0(sK1(X0,k12_pralg_1(X1,X0),X2)) = k1_funct_1(k12_pralg_1(X1,X0),X2) ),
% 1.45/0.98      inference(renaming,[status(thm)],[c_122]) ).
% 1.45/0.98  
% 1.45/0.98  cnf(c_448,plain,
% 1.45/0.98      ( ~ v4_relat_1(X0,X1)
% 1.45/0.98      | ~ v1_partfun1(X0,X1)
% 1.45/0.98      | ~ r2_hidden(X2,X1)
% 1.45/0.98      | ~ v1_relat_1(X0)
% 1.45/0.98      | ~ v1_funct_1(X0)
% 1.45/0.98      | u1_struct_0(sK1(X0,k12_pralg_1(X1,X0),X2)) = k1_funct_1(k12_pralg_1(X1,X0),X2)
% 1.45/0.98      | sK3 != X0 ),
% 1.45/0.98      inference(resolution_lifted,[status(thm)],[c_123,c_13]) ).
% 1.45/0.98  
% 1.45/0.98  cnf(c_449,plain,
% 1.45/0.98      ( ~ v4_relat_1(sK3,X0)
% 1.45/0.98      | ~ v1_partfun1(sK3,X0)
% 1.45/0.98      | ~ r2_hidden(X1,X0)
% 1.45/0.98      | ~ v1_relat_1(sK3)
% 1.45/0.98      | ~ v1_funct_1(sK3)
% 1.45/0.98      | u1_struct_0(sK1(sK3,k12_pralg_1(X0,sK3),X1)) = k1_funct_1(k12_pralg_1(X0,sK3),X1) ),
% 1.45/0.98      inference(unflattening,[status(thm)],[c_448]) ).
% 1.45/0.98  
% 1.45/0.98  cnf(c_453,plain,
% 1.45/0.98      ( ~ v4_relat_1(sK3,X0)
% 1.45/0.98      | ~ v1_partfun1(sK3,X0)
% 1.45/0.98      | ~ r2_hidden(X1,X0)
% 1.45/0.98      | u1_struct_0(sK1(sK3,k12_pralg_1(X0,sK3),X1)) = k1_funct_1(k12_pralg_1(X0,sK3),X1) ),
% 1.45/0.98      inference(global_propositional_subsumption,
% 1.45/0.98                [status(thm)],
% 1.45/0.98                [c_449,c_17,c_15]) ).
% 1.45/0.98  
% 1.45/0.98  cnf(c_1686,plain,
% 1.45/0.98      ( ~ v4_relat_1(sK3,X0_47)
% 1.45/0.98      | ~ v1_partfun1(sK3,X0_47)
% 1.45/0.98      | ~ r2_hidden(X0_48,X0_47)
% 1.45/0.98      | u1_struct_0(sK1(sK3,k12_pralg_1(X0_47,sK3),X0_48)) = k1_funct_1(k12_pralg_1(X0_47,sK3),X0_48) ),
% 1.45/0.98      inference(subtyping,[status(esa)],[c_453]) ).
% 1.45/0.98  
% 1.45/0.98  cnf(c_1742,plain,
% 1.45/0.98      ( ~ v4_relat_1(sK3,sK2)
% 1.45/0.98      | ~ v1_partfun1(sK3,sK2)
% 1.45/0.98      | ~ r2_hidden(sK4,sK2)
% 1.45/0.98      | u1_struct_0(sK1(sK3,k12_pralg_1(sK2,sK3),sK4)) = k1_funct_1(k12_pralg_1(sK2,sK3),sK4) ),
% 1.45/0.98      inference(instantiation,[status(thm)],[c_1686]) ).
% 1.45/0.98  
% 1.45/0.98  cnf(c_12,negated_conjecture,
% 1.45/0.98      ( m1_subset_1(sK4,sK2) ),
% 1.45/0.98      inference(cnf_transformation,[],[f43]) ).
% 1.45/0.98  
% 1.45/0.98  cnf(c_10,plain,
% 1.45/0.98      ( ~ v4_relat_1(X0,X1)
% 1.45/0.98      | ~ v1_partfun1(X0,X1)
% 1.45/0.98      | ~ m1_subset_1(X2,X1)
% 1.45/0.98      | ~ v2_pralg_1(X0)
% 1.45/0.98      | ~ v1_relat_1(X0)
% 1.45/0.98      | ~ v1_funct_1(X0)
% 1.45/0.98      | v1_xboole_0(X1)
% 1.45/0.98      | k10_pralg_1(X1,X0,X2) = k1_funct_1(X0,X2) ),
% 1.45/0.98      inference(cnf_transformation,[],[f36]) ).
% 1.45/0.98  
% 1.45/0.98  cnf(c_18,negated_conjecture,
% 1.45/0.98      ( ~ v1_xboole_0(sK2) ),
% 1.45/0.98      inference(cnf_transformation,[],[f37]) ).
% 1.45/0.98  
% 1.45/0.98  cnf(c_220,plain,
% 1.45/0.98      ( ~ v4_relat_1(X0,X1)
% 1.45/0.98      | ~ v1_partfun1(X0,X1)
% 1.45/0.98      | ~ m1_subset_1(X2,X1)
% 1.45/0.98      | ~ v2_pralg_1(X0)
% 1.45/0.98      | ~ v1_relat_1(X0)
% 1.45/0.98      | ~ v1_funct_1(X0)
% 1.45/0.98      | k10_pralg_1(X1,X0,X2) = k1_funct_1(X0,X2)
% 1.45/0.98      | sK2 != X1 ),
% 1.45/0.98      inference(resolution_lifted,[status(thm)],[c_10,c_18]) ).
% 1.45/0.98  
% 1.45/0.98  cnf(c_221,plain,
% 1.45/0.98      ( ~ v4_relat_1(X0,sK2)
% 1.45/0.98      | ~ v1_partfun1(X0,sK2)
% 1.45/0.98      | ~ m1_subset_1(X1,sK2)
% 1.45/0.98      | ~ v2_pralg_1(X0)
% 1.45/0.98      | ~ v1_relat_1(X0)
% 1.45/0.98      | ~ v1_funct_1(X0)
% 1.45/0.98      | k10_pralg_1(sK2,X0,X1) = k1_funct_1(X0,X1) ),
% 1.45/0.98      inference(unflattening,[status(thm)],[c_220]) ).
% 1.45/0.98  
% 1.45/0.98  cnf(c_270,plain,
% 1.45/0.98      ( ~ v4_relat_1(X0,sK2)
% 1.45/0.98      | ~ v1_partfun1(X0,sK2)
% 1.45/0.98      | ~ v2_pralg_1(X0)
% 1.45/0.98      | ~ v1_relat_1(X0)
% 1.45/0.98      | ~ v1_funct_1(X0)
% 1.45/0.98      | k10_pralg_1(sK2,X0,X1) = k1_funct_1(X0,X1)
% 1.45/0.98      | sK4 != X1
% 1.45/0.98      | sK2 != sK2 ),
% 1.45/0.98      inference(resolution_lifted,[status(thm)],[c_12,c_221]) ).
% 1.45/0.98  
% 1.45/0.98  cnf(c_271,plain,
% 1.45/0.98      ( ~ v4_relat_1(X0,sK2)
% 1.45/0.98      | ~ v1_partfun1(X0,sK2)
% 1.45/0.98      | ~ v2_pralg_1(X0)
% 1.45/0.98      | ~ v1_relat_1(X0)
% 1.45/0.98      | ~ v1_funct_1(X0)
% 1.45/0.98      | k10_pralg_1(sK2,X0,sK4) = k1_funct_1(X0,sK4) ),
% 1.45/0.98      inference(unflattening,[status(thm)],[c_270]) ).
% 1.45/0.98  
% 1.45/0.98  cnf(c_440,plain,
% 1.45/0.98      ( ~ v4_relat_1(X0,sK2)
% 1.45/0.98      | ~ v1_partfun1(X0,sK2)
% 1.45/0.98      | ~ v1_relat_1(X0)
% 1.45/0.98      | ~ v1_funct_1(X0)
% 1.45/0.98      | k10_pralg_1(sK2,X0,sK4) = k1_funct_1(X0,sK4)
% 1.45/0.98      | sK3 != X0 ),
% 1.45/0.98      inference(resolution_lifted,[status(thm)],[c_271,c_13]) ).
% 1.45/0.98  
% 1.45/0.98  cnf(c_441,plain,
% 1.45/0.98      ( ~ v4_relat_1(sK3,sK2)
% 1.45/0.98      | ~ v1_partfun1(sK3,sK2)
% 1.45/0.98      | ~ v1_relat_1(sK3)
% 1.45/0.98      | ~ v1_funct_1(sK3)
% 1.45/0.98      | k10_pralg_1(sK2,sK3,sK4) = k1_funct_1(sK3,sK4) ),
% 1.45/0.98      inference(unflattening,[status(thm)],[c_440]) ).
% 1.45/0.98  
% 1.45/0.98  cnf(c_16,negated_conjecture,
% 1.45/0.98      ( v4_relat_1(sK3,sK2) ),
% 1.45/0.98      inference(cnf_transformation,[],[f39]) ).
% 1.45/0.98  
% 1.45/0.98  cnf(c_14,negated_conjecture,
% 1.45/0.98      ( v1_partfun1(sK3,sK2) ),
% 1.45/0.98      inference(cnf_transformation,[],[f41]) ).
% 1.45/0.98  
% 1.45/0.98  cnf(c_273,plain,
% 1.45/0.98      ( ~ v4_relat_1(sK3,sK2)
% 1.45/0.98      | ~ v1_partfun1(sK3,sK2)
% 1.45/0.98      | ~ v2_pralg_1(sK3)
% 1.45/0.98      | ~ v1_relat_1(sK3)
% 1.45/0.98      | ~ v1_funct_1(sK3)
% 1.45/0.98      | k10_pralg_1(sK2,sK3,sK4) = k1_funct_1(sK3,sK4) ),
% 1.45/0.98      inference(instantiation,[status(thm)],[c_271]) ).
% 1.45/0.98  
% 1.45/0.98  cnf(c_443,plain,
% 1.45/0.98      ( k10_pralg_1(sK2,sK3,sK4) = k1_funct_1(sK3,sK4) ),
% 1.45/0.98      inference(global_propositional_subsumption,
% 1.45/0.98                [status(thm)],
% 1.45/0.98                [c_441,c_17,c_16,c_15,c_14,c_13,c_273]) ).
% 1.45/0.98  
% 1.45/0.98  cnf(c_1687,plain,
% 1.45/0.98      ( k10_pralg_1(sK2,sK3,sK4) = k1_funct_1(sK3,sK4) ),
% 1.45/0.98      inference(subtyping,[status(esa)],[c_443]) ).
% 1.45/0.98  
% 1.45/0.98  cnf(c_11,negated_conjecture,
% 1.45/0.98      ( k1_funct_1(k12_pralg_1(sK2,sK3),sK4) != u1_struct_0(k10_pralg_1(sK2,sK3,sK4)) ),
% 1.45/0.98      inference(cnf_transformation,[],[f44]) ).
% 1.45/0.98  
% 1.45/0.98  cnf(c_1695,negated_conjecture,
% 1.45/0.98      ( k1_funct_1(k12_pralg_1(sK2,sK3),sK4) != u1_struct_0(k10_pralg_1(sK2,sK3,sK4)) ),
% 1.45/0.98      inference(subtyping,[status(esa)],[c_11]) ).
% 1.45/0.98  
% 1.45/0.98  cnf(c_0,plain,
% 1.45/0.98      ( ~ m1_subset_1(X0,X1) | r2_hidden(X0,X1) | v1_xboole_0(X1) ),
% 1.45/0.98      inference(cnf_transformation,[],[f26]) ).
% 1.45/0.98  
% 1.45/0.98  cnf(c_247,plain,
% 1.45/0.98      ( ~ m1_subset_1(X0,X1) | r2_hidden(X0,X1) | sK2 != X1 ),
% 1.45/0.98      inference(resolution_lifted,[status(thm)],[c_0,c_18]) ).
% 1.45/0.98  
% 1.45/0.98  cnf(c_248,plain,
% 1.45/0.98      ( ~ m1_subset_1(X0,sK2) | r2_hidden(X0,sK2) ),
% 1.45/0.98      inference(unflattening,[status(thm)],[c_247]) ).
% 1.45/0.98  
% 1.45/0.98  cnf(c_294,plain,
% 1.45/0.98      ( r2_hidden(X0,sK2) | sK4 != X0 | sK2 != sK2 ),
% 1.45/0.98      inference(resolution_lifted,[status(thm)],[c_12,c_248]) ).
% 1.45/0.98  
% 1.45/0.98  cnf(c_295,plain,
% 1.45/0.98      ( r2_hidden(sK4,sK2) ),
% 1.45/0.98      inference(unflattening,[status(thm)],[c_294]) ).
% 1.45/0.98  
% 1.45/0.98  cnf(contradiction,plain,
% 1.45/0.98      ( $false ),
% 1.45/0.98      inference(minisat,
% 1.45/0.98                [status(thm)],
% 1.45/0.98                [c_2465,c_2288,c_2274,c_2245,c_2183,c_1745,c_1742,c_1687,
% 1.45/0.98                 c_1695,c_295,c_14,c_16]) ).
% 1.45/0.98  
% 1.45/0.98  
% 1.45/0.98  % SZS output end CNFRefutation for theBenchmark.p
% 1.45/0.98  
% 1.45/0.98  ------                               Statistics
% 1.45/0.98  
% 1.45/0.98  ------ General
% 1.45/0.98  
% 1.45/0.98  abstr_ref_over_cycles:                  0
% 1.45/0.98  abstr_ref_under_cycles:                 0
% 1.45/0.98  gc_basic_clause_elim:                   0
% 1.45/0.98  forced_gc_time:                         0
% 1.45/0.98  parsing_time:                           0.011
% 1.45/0.98  unif_index_cands_time:                  0.
% 1.45/0.98  unif_index_add_time:                    0.
% 1.45/0.98  orderings_time:                         0.
% 1.45/0.98  out_proof_time:                         0.009
% 1.45/0.98  total_time:                             0.11
% 1.45/0.98  num_of_symbols:                         50
% 1.45/0.98  num_of_terms:                           1705
% 1.45/0.98  
% 1.45/0.98  ------ Preprocessing
% 1.45/0.98  
% 1.45/0.98  num_of_splits:                          0
% 1.45/0.98  num_of_split_atoms:                     0
% 1.45/0.98  num_of_reused_defs:                     0
% 1.45/0.98  num_eq_ax_congr_red:                    17
% 1.45/0.98  num_of_sem_filtered_clauses:            1
% 1.45/0.98  num_of_subtypes:                        4
% 1.45/0.98  monotx_restored_types:                  0
% 1.45/0.98  sat_num_of_epr_types:                   0
% 1.45/0.98  sat_num_of_non_cyclic_types:            0
% 1.45/0.98  sat_guarded_non_collapsed_types:        1
% 1.45/0.98  num_pure_diseq_elim:                    0
% 1.45/0.98  simp_replaced_by:                       0
% 1.45/0.98  res_preprocessed:                       102
% 1.45/0.98  prep_upred:                             0
% 1.45/0.98  prep_unflattend:                        54
% 1.45/0.98  smt_new_axioms:                         0
% 1.45/0.98  pred_elim_cands:                        6
% 1.45/0.98  pred_elim:                              3
% 1.45/0.98  pred_elim_cl:                           3
% 1.45/0.98  pred_elim_cycles:                       12
% 1.45/0.98  merged_defs:                            0
% 1.45/0.98  merged_defs_ncl:                        0
% 1.45/0.98  bin_hyper_res:                          0
% 1.45/0.98  prep_cycles:                            4
% 1.45/0.98  pred_elim_time:                         0.028
% 1.45/0.98  splitting_time:                         0.
% 1.45/0.98  sem_filter_time:                        0.
% 1.45/0.98  monotx_time:                            0.
% 1.45/0.98  subtype_inf_time:                       0.
% 1.45/0.98  
% 1.45/0.98  ------ Problem properties
% 1.45/0.98  
% 1.45/0.98  clauses:                                16
% 1.45/0.98  conjectures:                            5
% 1.45/0.98  epr:                                    5
% 1.45/0.98  horn:                                   15
% 1.45/0.98  ground:                                 7
% 1.45/0.98  unary:                                  7
% 1.45/0.98  binary:                                 0
% 1.45/0.98  lits:                                   48
% 1.45/0.98  lits_eq:                                7
% 1.45/0.98  fd_pure:                                0
% 1.45/0.98  fd_pseudo:                              0
% 1.45/0.98  fd_cond:                                0
% 1.45/0.98  fd_pseudo_cond:                         2
% 1.45/0.98  ac_symbols:                             0
% 1.45/0.98  
% 1.45/0.98  ------ Propositional Solver
% 1.45/0.98  
% 1.45/0.98  prop_solver_calls:                      27
% 1.45/0.98  prop_fast_solver_calls:                 1160
% 1.45/0.98  smt_solver_calls:                       0
% 1.45/0.98  smt_fast_solver_calls:                  0
% 1.45/0.98  prop_num_of_clauses:                    439
% 1.45/0.98  prop_preprocess_simplified:             2866
% 1.45/0.98  prop_fo_subsumed:                       62
% 1.45/0.98  prop_solver_time:                       0.
% 1.45/0.98  smt_solver_time:                        0.
% 1.45/0.98  smt_fast_solver_time:                   0.
% 1.45/0.98  prop_fast_solver_time:                  0.
% 1.45/0.98  prop_unsat_core_time:                   0.
% 1.45/0.98  
% 1.45/0.98  ------ QBF
% 1.45/0.98  
% 1.45/0.98  qbf_q_res:                              0
% 1.45/0.98  qbf_num_tautologies:                    0
% 1.45/0.98  qbf_prep_cycles:                        0
% 1.45/0.98  
% 1.45/0.98  ------ BMC1
% 1.45/0.98  
% 1.45/0.98  bmc1_current_bound:                     -1
% 1.45/0.98  bmc1_last_solved_bound:                 -1
% 1.45/0.98  bmc1_unsat_core_size:                   -1
% 1.45/0.98  bmc1_unsat_core_parents_size:           -1
% 1.45/0.98  bmc1_merge_next_fun:                    0
% 1.45/0.98  bmc1_unsat_core_clauses_time:           0.
% 1.45/0.98  
% 1.45/0.98  ------ Instantiation
% 1.45/0.98  
% 1.45/0.98  inst_num_of_clauses:                    123
% 1.45/0.98  inst_num_in_passive:                    50
% 1.45/0.98  inst_num_in_active:                     71
% 1.45/0.98  inst_num_in_unprocessed:                1
% 1.45/0.98  inst_num_of_loops:                      78
% 1.45/0.98  inst_num_of_learning_restarts:          0
% 1.45/0.98  inst_num_moves_active_passive:          2
% 1.45/0.98  inst_lit_activity:                      0
% 1.45/0.98  inst_lit_activity_moves:                0
% 1.45/0.98  inst_num_tautologies:                   0
% 1.45/0.98  inst_num_prop_implied:                  0
% 1.45/0.98  inst_num_existing_simplified:           0
% 1.45/0.98  inst_num_eq_res_simplified:             0
% 1.45/0.98  inst_num_child_elim:                    0
% 1.45/0.98  inst_num_of_dismatching_blockings:      18
% 1.45/0.98  inst_num_of_non_proper_insts:           75
% 1.45/0.98  inst_num_of_duplicates:                 0
% 1.45/0.98  inst_inst_num_from_inst_to_res:         0
% 1.45/0.98  inst_dismatching_checking_time:         0.
% 1.45/0.98  
% 1.45/0.98  ------ Resolution
% 1.45/0.98  
% 1.45/0.98  res_num_of_clauses:                     0
% 1.45/0.98  res_num_in_passive:                     0
% 1.45/0.98  res_num_in_active:                      0
% 1.45/0.98  res_num_of_loops:                       106
% 1.45/0.98  res_forward_subset_subsumed:            13
% 1.45/0.98  res_backward_subset_subsumed:           0
% 1.45/0.98  res_forward_subsumed:                   0
% 1.45/0.98  res_backward_subsumed:                  0
% 1.45/0.98  res_forward_subsumption_resolution:     0
% 1.45/0.98  res_backward_subsumption_resolution:    0
% 1.45/0.98  res_clause_to_clause_subsumption:       153
% 1.45/0.98  res_orphan_elimination:                 0
% 1.45/0.98  res_tautology_del:                      13
% 1.45/0.98  res_num_eq_res_simplified:              0
% 1.45/0.98  res_num_sel_changes:                    0
% 1.45/0.98  res_moves_from_active_to_pass:          0
% 1.45/0.98  
% 1.45/0.98  ------ Superposition
% 1.45/0.98  
% 1.45/0.98  sup_time_total:                         0.
% 1.45/0.98  sup_time_generating:                    0.
% 1.45/0.98  sup_time_sim_full:                      0.
% 1.45/0.98  sup_time_sim_immed:                     0.
% 1.45/0.98  
% 1.45/0.98  sup_num_of_clauses:                     17
% 1.45/0.98  sup_num_in_active:                      14
% 1.45/0.98  sup_num_in_passive:                     3
% 1.45/0.98  sup_num_of_loops:                       14
% 1.45/0.98  sup_fw_superposition:                   1
% 1.45/0.98  sup_bw_superposition:                   0
% 1.45/0.98  sup_immediate_simplified:               0
% 1.45/0.98  sup_given_eliminated:                   0
% 1.45/0.98  comparisons_done:                       0
% 1.45/0.98  comparisons_avoided:                    0
% 1.45/0.98  
% 1.45/0.98  ------ Simplifications
% 1.45/0.98  
% 1.45/0.98  
% 1.45/0.98  sim_fw_subset_subsumed:                 0
% 1.45/0.98  sim_bw_subset_subsumed:                 0
% 1.45/0.98  sim_fw_subsumed:                        0
% 1.45/0.98  sim_bw_subsumed:                        0
% 1.45/0.98  sim_fw_subsumption_res:                 0
% 1.45/0.98  sim_bw_subsumption_res:                 0
% 1.45/0.98  sim_tautology_del:                      0
% 1.45/0.98  sim_eq_tautology_del:                   0
% 1.45/0.98  sim_eq_res_simp:                        0
% 1.45/0.98  sim_fw_demodulated:                     0
% 1.45/0.98  sim_bw_demodulated:                     0
% 1.45/0.98  sim_light_normalised:                   1
% 1.45/0.98  sim_joinable_taut:                      0
% 1.45/0.98  sim_joinable_simp:                      0
% 1.45/0.98  sim_ac_normalised:                      0
% 1.45/0.98  sim_smt_subsumption:                    0
% 1.45/0.98  
%------------------------------------------------------------------------------
