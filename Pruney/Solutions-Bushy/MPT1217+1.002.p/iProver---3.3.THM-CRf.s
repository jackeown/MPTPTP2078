%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT1217+1.002 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n028.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:45:10 EST 2020

% Result     : Theorem 11.48s
% Output     : CNFRefutation 11.48s
% Verified   : 
% Statistics : Number of formulae       :  276 (3035 expanded)
%              Number of clauses        :  193 ( 857 expanded)
%              Number of leaves         :   21 ( 885 expanded)
%              Depth                    :   28
%              Number of atoms          : 1257 (19170 expanded)
%              Number of equality atoms :  287 ( 744 expanded)
%              Maximal formula depth    :   15 (   6 average)
%              Maximal clause size      :   16 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f16,conjecture,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & v17_lattices(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( r3_lattices(X0,X1,X2)
               => r3_lattices(X0,k7_lattices(X0,X2),k7_lattices(X0,X1)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,negated_conjecture,(
    ~ ! [X0] :
        ( ( l3_lattices(X0)
          & v17_lattices(X0)
          & v10_lattices(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => ( r3_lattices(X0,X1,X2)
                 => r3_lattices(X0,k7_lattices(X0,X2),k7_lattices(X0,X1)) ) ) ) ) ),
    inference(negated_conjecture,[],[f16])).

fof(f51,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ r3_lattices(X0,k7_lattices(X0,X2),k7_lattices(X0,X1))
              & r3_lattices(X0,X1,X2)
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l3_lattices(X0)
      & v17_lattices(X0)
      & v10_lattices(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f52,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ r3_lattices(X0,k7_lattices(X0,X2),k7_lattices(X0,X1))
              & r3_lattices(X0,X1,X2)
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l3_lattices(X0)
      & v17_lattices(X0)
      & v10_lattices(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f51])).

fof(f57,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ~ r3_lattices(X0,k7_lattices(X0,X2),k7_lattices(X0,X1))
          & r3_lattices(X0,X1,X2)
          & m1_subset_1(X2,u1_struct_0(X0)) )
     => ( ~ r3_lattices(X0,k7_lattices(X0,sK2),k7_lattices(X0,X1))
        & r3_lattices(X0,X1,sK2)
        & m1_subset_1(sK2,u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f56,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ r3_lattices(X0,k7_lattices(X0,X2),k7_lattices(X0,X1))
              & r3_lattices(X0,X1,X2)
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
     => ( ? [X2] :
            ( ~ r3_lattices(X0,k7_lattices(X0,X2),k7_lattices(X0,sK1))
            & r3_lattices(X0,sK1,X2)
            & m1_subset_1(X2,u1_struct_0(X0)) )
        & m1_subset_1(sK1,u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f55,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ~ r3_lattices(X0,k7_lattices(X0,X2),k7_lattices(X0,X1))
                & r3_lattices(X0,X1,X2)
                & m1_subset_1(X2,u1_struct_0(X0)) )
            & m1_subset_1(X1,u1_struct_0(X0)) )
        & l3_lattices(X0)
        & v17_lattices(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ~ r3_lattices(sK0,k7_lattices(sK0,X2),k7_lattices(sK0,X1))
              & r3_lattices(sK0,X1,X2)
              & m1_subset_1(X2,u1_struct_0(sK0)) )
          & m1_subset_1(X1,u1_struct_0(sK0)) )
      & l3_lattices(sK0)
      & v17_lattices(sK0)
      & v10_lattices(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f58,plain,
    ( ~ r3_lattices(sK0,k7_lattices(sK0,sK2),k7_lattices(sK0,sK1))
    & r3_lattices(sK0,sK1,sK2)
    & m1_subset_1(sK2,u1_struct_0(sK0))
    & m1_subset_1(sK1,u1_struct_0(sK0))
    & l3_lattices(sK0)
    & v17_lattices(sK0)
    & v10_lattices(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f52,f57,f56,f55])).

fof(f89,plain,(
    m1_subset_1(sK2,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f58])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,u1_struct_0(X0))
        & l3_lattices(X0)
        & ~ v2_struct_0(X0) )
     => m1_subset_1(k7_lattices(X0,X1),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k7_lattices(X0,X1),u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f35,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k7_lattices(X0,X1),u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f34])).

fof(f72,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k7_lattices(X0,X1),u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f84,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f58])).

fof(f87,plain,(
    l3_lattices(sK0) ),
    inference(cnf_transformation,[],[f58])).

fof(f88,plain,(
    m1_subset_1(sK1,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f58])).

fof(f1,axiom,(
    ! [X0] :
      ( l3_lattices(X0)
     => ( ( v10_lattices(X0)
          & ~ v2_struct_0(X0) )
       => ( v9_lattices(X0)
          & v8_lattices(X0)
          & v7_lattices(X0)
          & v6_lattices(X0)
          & v5_lattices(X0)
          & v4_lattices(X0)
          & ~ v2_struct_0(X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0] :
      ( l3_lattices(X0)
     => ( ( v10_lattices(X0)
          & ~ v2_struct_0(X0) )
       => ( v9_lattices(X0)
          & v8_lattices(X0)
          & v7_lattices(X0)
          & v6_lattices(X0)
          & v4_lattices(X0)
          & ~ v2_struct_0(X0) ) ) ) ),
    inference(pure_predicate_removal,[],[f1])).

fof(f22,plain,(
    ! [X0] :
      ( ( v9_lattices(X0)
        & v8_lattices(X0)
        & v7_lattices(X0)
        & v6_lattices(X0)
        & v4_lattices(X0)
        & ~ v2_struct_0(X0) )
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f23,plain,(
    ! [X0] :
      ( ( v9_lattices(X0)
        & v8_lattices(X0)
        & v7_lattices(X0)
        & v6_lattices(X0)
        & v4_lattices(X0)
        & ~ v2_struct_0(X0) )
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(flattening,[],[f22])).

fof(f61,plain,(
    ! [X0] :
      ( v6_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f8,axiom,(
    ! [X0] :
      ( l3_lattices(X0)
     => ( l2_lattices(X0)
        & l1_lattices(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0] :
      ( ( l2_lattices(X0)
        & l1_lattices(X0) )
      | ~ l3_lattices(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f73,plain,(
    ! [X0] :
      ( l1_lattices(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l1_lattices(X0)
        & v6_lattices(X0)
        & ~ v2_struct_0(X0) )
     => k4_lattices(X0,X1,X2) = k2_lattices(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( k4_lattices(X0,X1,X2) = k2_lattices(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f38,plain,(
    ! [X0,X1,X2] :
      ( k4_lattices(X0,X1,X2) = k2_lattices(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f37])).

fof(f75,plain,(
    ! [X2,X0,X1] :
      ( k4_lattices(X0,X1,X2) = k2_lattices(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f85,plain,(
    v10_lattices(sK0) ),
    inference(cnf_transformation,[],[f58])).

fof(f62,plain,(
    ! [X0] :
      ( v7_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f12,axiom,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & v9_lattices(X0)
        & v8_lattices(X0)
        & v7_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ! [X3] :
                  ( m1_subset_1(X3,u1_struct_0(X0))
                 => ( r1_lattices(X0,X1,X2)
                   => r1_lattices(X0,k2_lattices(X0,X1,X3),k2_lattices(X0,X2,X3)) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f43,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( r1_lattices(X0,k2_lattices(X0,X1,X3),k2_lattices(X0,X2,X3))
                  | ~ r1_lattices(X0,X1,X2)
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v9_lattices(X0)
      | ~ v8_lattices(X0)
      | ~ v7_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f44,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( r1_lattices(X0,k2_lattices(X0,X1,X3),k2_lattices(X0,X2,X3))
                  | ~ r1_lattices(X0,X1,X2)
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v9_lattices(X0)
      | ~ v8_lattices(X0)
      | ~ v7_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f43])).

fof(f79,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_lattices(X0,k2_lattices(X0,X1,X3),k2_lattices(X0,X2,X3))
      | ~ r1_lattices(X0,X1,X2)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v9_lattices(X0)
      | ~ v8_lattices(X0)
      | ~ v7_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f63,plain,(
    ! [X0] :
      ( v8_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f64,plain,(
    ! [X0] :
      ( v9_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l1_lattices(X0)
        & v6_lattices(X0)
        & ~ v2_struct_0(X0) )
     => k4_lattices(X0,X1,X2) = k4_lattices(X0,X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( k4_lattices(X0,X1,X2) = k4_lattices(X0,X2,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( k4_lattices(X0,X1,X2) = k4_lattices(X0,X2,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f28])).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( k4_lattices(X0,X1,X2) = k4_lattices(X0,X2,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f14,axiom,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & v17_lattices(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => k4_lattices(X0,k7_lattices(X0,X1),X1) = k5_lattices(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f47,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k4_lattices(X0,k7_lattices(X0,X1),X1) = k5_lattices(X0)
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v17_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f48,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k4_lattices(X0,k7_lattices(X0,X1),X1) = k5_lattices(X0)
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v17_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f47])).

fof(f81,plain,(
    ! [X0,X1] :
      ( k4_lattices(X0,k7_lattices(X0,X1),X1) = k5_lattices(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v17_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f86,plain,(
    v17_lattices(sK0) ),
    inference(cnf_transformation,[],[f58])).

fof(f3,axiom,(
    ! [X0] :
      ( l3_lattices(X0)
     => ( ( v17_lattices(X0)
          & ~ v2_struct_0(X0) )
       => ( v16_lattices(X0)
          & v15_lattices(X0)
          & v11_lattices(X0)
          & ~ v2_struct_0(X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0] :
      ( l3_lattices(X0)
     => ( ( v17_lattices(X0)
          & ~ v2_struct_0(X0) )
       => ( v15_lattices(X0)
          & v11_lattices(X0)
          & ~ v2_struct_0(X0) ) ) ) ),
    inference(pure_predicate_removal,[],[f3])).

fof(f19,plain,(
    ! [X0] :
      ( l3_lattices(X0)
     => ( ( v17_lattices(X0)
          & ~ v2_struct_0(X0) )
       => ( v15_lattices(X0)
          & ~ v2_struct_0(X0) ) ) ) ),
    inference(pure_predicate_removal,[],[f18])).

fof(f26,plain,(
    ! [X0] :
      ( ( v15_lattices(X0)
        & ~ v2_struct_0(X0) )
      | ~ v17_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f27,plain,(
    ! [X0] :
      ( ( v15_lattices(X0)
        & ~ v2_struct_0(X0) )
      | ~ v17_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(flattening,[],[f26])).

fof(f68,plain,(
    ! [X0] :
      ( v15_lattices(X0)
      | ~ v17_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f2,axiom,(
    ! [X0] :
      ( l3_lattices(X0)
     => ( ( v15_lattices(X0)
          & ~ v2_struct_0(X0) )
       => ( v14_lattices(X0)
          & v13_lattices(X0)
          & ~ v2_struct_0(X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0] :
      ( l3_lattices(X0)
     => ( ( v15_lattices(X0)
          & ~ v2_struct_0(X0) )
       => ( v13_lattices(X0)
          & ~ v2_struct_0(X0) ) ) ) ),
    inference(pure_predicate_removal,[],[f2])).

fof(f24,plain,(
    ! [X0] :
      ( ( v13_lattices(X0)
        & ~ v2_struct_0(X0) )
      | ~ v15_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f25,plain,(
    ! [X0] :
      ( ( v13_lattices(X0)
        & ~ v2_struct_0(X0) )
      | ~ v15_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(flattening,[],[f24])).

fof(f66,plain,(
    ! [X0] :
      ( v13_lattices(X0)
      | ~ v15_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f13,axiom,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & v13_lattices(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => r3_lattices(X0,k5_lattices(X0),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f45,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r3_lattices(X0,k5_lattices(X0),X1)
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v13_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f46,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r3_lattices(X0,k5_lattices(X0),X1)
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v13_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f45])).

fof(f80,plain,(
    ! [X0,X1] :
      ( r3_lattices(X0,k5_lattices(X0),X1)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v13_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l3_lattices(X0)
        & v9_lattices(X0)
        & v8_lattices(X0)
        & v6_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ( r3_lattices(X0,X1,X2)
      <=> r1_lattices(X0,X1,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X0,X1,X2] :
      ( ( r3_lattices(X0,X1,X2)
      <=> r1_lattices(X0,X1,X2) )
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v9_lattices(X0)
      | ~ v8_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f40,plain,(
    ! [X0,X1,X2] :
      ( ( r3_lattices(X0,X1,X2)
      <=> r1_lattices(X0,X1,X2) )
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v9_lattices(X0)
      | ~ v8_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f39])).

fof(f53,plain,(
    ! [X0,X1,X2] :
      ( ( ( r3_lattices(X0,X1,X2)
          | ~ r1_lattices(X0,X1,X2) )
        & ( r1_lattices(X0,X1,X2)
          | ~ r3_lattices(X0,X1,X2) ) )
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v9_lattices(X0)
      | ~ v8_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f40])).

fof(f76,plain,(
    ! [X2,X0,X1] :
      ( r1_lattices(X0,X1,X2)
      | ~ r3_lattices(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v9_lattices(X0)
      | ~ v8_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l1_lattices(X0)
        & v6_lattices(X0)
        & ~ v2_struct_0(X0) )
     => m1_subset_1(k4_lattices(X0,X1,X2),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k4_lattices(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k4_lattices(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f32])).

fof(f71,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k4_lattices(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f15,axiom,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & v17_lattices(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( k4_lattices(X0,X1,X2) = k5_lattices(X0)
              <=> r3_lattices(X0,X1,k7_lattices(X0,X2)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f49,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( k4_lattices(X0,X1,X2) = k5_lattices(X0)
              <=> r3_lattices(X0,X1,k7_lattices(X0,X2)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v17_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f50,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( k4_lattices(X0,X1,X2) = k5_lattices(X0)
              <=> r3_lattices(X0,X1,k7_lattices(X0,X2)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v17_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f49])).

fof(f54,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( k4_lattices(X0,X1,X2) = k5_lattices(X0)
                  | ~ r3_lattices(X0,X1,k7_lattices(X0,X2)) )
                & ( r3_lattices(X0,X1,k7_lattices(X0,X2))
                  | k4_lattices(X0,X1,X2) != k5_lattices(X0) ) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v17_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f50])).

fof(f83,plain,(
    ! [X2,X0,X1] :
      ( k4_lattices(X0,X1,X2) = k5_lattices(X0)
      | ~ r3_lattices(X0,X1,k7_lattices(X0,X2))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v17_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f60,plain,(
    ! [X0] :
      ( v4_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f74,plain,(
    ! [X0] :
      ( l2_lattices(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f11,axiom,(
    ! [X0] :
      ( ( l2_lattices(X0)
        & v4_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( ( r1_lattices(X0,X2,X1)
                  & r1_lattices(X0,X1,X2) )
               => X1 = X2 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( X1 = X2
              | ~ r1_lattices(X0,X2,X1)
              | ~ r1_lattices(X0,X1,X2)
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l2_lattices(X0)
      | ~ v4_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f42,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( X1 = X2
              | ~ r1_lattices(X0,X2,X1)
              | ~ r1_lattices(X0,X1,X2)
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l2_lattices(X0)
      | ~ v4_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f41])).

fof(f78,plain,(
    ! [X2,X0,X1] :
      ( X1 = X2
      | ~ r1_lattices(X0,X2,X1)
      | ~ r1_lattices(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l2_lattices(X0)
      | ~ v4_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f91,plain,(
    ~ r3_lattices(sK0,k7_lattices(sK0,sK2),k7_lattices(sK0,sK1)) ),
    inference(cnf_transformation,[],[f58])).

fof(f82,plain,(
    ! [X2,X0,X1] :
      ( r3_lattices(X0,X1,k7_lattices(X0,X2))
      | k4_lattices(X0,X1,X2) != k5_lattices(X0)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v17_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f90,plain,(
    r3_lattices(sK0,sK1,sK2) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_27,negated_conjecture,
    ( m1_subset_1(sK2,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_1504,negated_conjecture,
    ( m1_subset_1(sK2,u1_struct_0(sK0)) ),
    inference(subtyping,[status(esa)],[c_27])).

cnf(c_1835,plain,
    ( m1_subset_1(sK2,u1_struct_0(sK0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1504])).

cnf(c_13,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | m1_subset_1(k7_lattices(X1,X0),u1_struct_0(X1))
    | ~ l3_lattices(X1)
    | v2_struct_0(X1) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_32,negated_conjecture,
    ( ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_1126,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | m1_subset_1(k7_lattices(X1,X0),u1_struct_0(X1))
    | ~ l3_lattices(X1)
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_13,c_32])).

cnf(c_1127,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK0))
    | m1_subset_1(k7_lattices(sK0,X0),u1_struct_0(sK0))
    | ~ l3_lattices(sK0) ),
    inference(unflattening,[status(thm)],[c_1126])).

cnf(c_29,negated_conjecture,
    ( l3_lattices(sK0) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_1131,plain,
    ( m1_subset_1(k7_lattices(sK0,X0),u1_struct_0(sK0))
    | ~ m1_subset_1(X0,u1_struct_0(sK0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1127,c_29])).

cnf(c_1132,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK0))
    | m1_subset_1(k7_lattices(sK0,X0),u1_struct_0(sK0)) ),
    inference(renaming,[status(thm)],[c_1131])).

cnf(c_1495,plain,
    ( ~ m1_subset_1(X0_52,u1_struct_0(sK0))
    | m1_subset_1(k7_lattices(sK0,X0_52),u1_struct_0(sK0)) ),
    inference(subtyping,[status(esa)],[c_1132])).

cnf(c_1844,plain,
    ( m1_subset_1(X0_52,u1_struct_0(sK0)) != iProver_top
    | m1_subset_1(k7_lattices(sK0,X0_52),u1_struct_0(sK0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1495])).

cnf(c_28,negated_conjecture,
    ( m1_subset_1(sK1,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_1503,negated_conjecture,
    ( m1_subset_1(sK1,u1_struct_0(sK0)) ),
    inference(subtyping,[status(esa)],[c_28])).

cnf(c_1836,plain,
    ( m1_subset_1(sK1,u1_struct_0(sK0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1503])).

cnf(c_3,plain,
    ( v6_lattices(X0)
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | ~ v10_lattices(X0) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_15,plain,
    ( l1_lattices(X0)
    | ~ l3_lattices(X0) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_16,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l1_lattices(X1)
    | ~ v6_lattices(X1)
    | v2_struct_0(X1)
    | k2_lattices(X1,X2,X0) = k4_lattices(X1,X2,X0) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_593,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v6_lattices(X1)
    | ~ l3_lattices(X3)
    | v2_struct_0(X1)
    | X1 != X3
    | k2_lattices(X1,X2,X0) = k4_lattices(X1,X2,X0) ),
    inference(resolution_lifted,[status(thm)],[c_15,c_16])).

cnf(c_594,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v6_lattices(X1)
    | ~ l3_lattices(X1)
    | v2_struct_0(X1)
    | k2_lattices(X1,X2,X0) = k4_lattices(X1,X2,X0) ),
    inference(unflattening,[status(thm)],[c_593])).

cnf(c_761,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l3_lattices(X3)
    | ~ l3_lattices(X1)
    | v2_struct_0(X3)
    | v2_struct_0(X1)
    | ~ v10_lattices(X3)
    | X1 != X3
    | k2_lattices(X1,X2,X0) = k4_lattices(X1,X2,X0) ),
    inference(resolution_lifted,[status(thm)],[c_3,c_594])).

cnf(c_762,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l3_lattices(X1)
    | v2_struct_0(X1)
    | ~ v10_lattices(X1)
    | k2_lattices(X1,X2,X0) = k4_lattices(X1,X2,X0) ),
    inference(unflattening,[status(thm)],[c_761])).

cnf(c_31,negated_conjecture,
    ( v10_lattices(sK0) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_1008,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l3_lattices(X1)
    | v2_struct_0(X1)
    | k2_lattices(X1,X2,X0) = k4_lattices(X1,X2,X0)
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_762,c_31])).

cnf(c_1009,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK0))
    | ~ m1_subset_1(X1,u1_struct_0(sK0))
    | ~ l3_lattices(sK0)
    | v2_struct_0(sK0)
    | k2_lattices(sK0,X1,X0) = k4_lattices(sK0,X1,X0) ),
    inference(unflattening,[status(thm)],[c_1008])).

cnf(c_1013,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK0))
    | ~ m1_subset_1(X1,u1_struct_0(sK0))
    | k2_lattices(sK0,X1,X0) = k4_lattices(sK0,X1,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1009,c_32,c_29])).

cnf(c_1014,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK0))
    | ~ m1_subset_1(X1,u1_struct_0(sK0))
    | k2_lattices(sK0,X0,X1) = k4_lattices(sK0,X0,X1) ),
    inference(renaming,[status(thm)],[c_1013])).

cnf(c_1499,plain,
    ( ~ m1_subset_1(X0_52,u1_struct_0(sK0))
    | ~ m1_subset_1(X1_52,u1_struct_0(sK0))
    | k2_lattices(sK0,X0_52,X1_52) = k4_lattices(sK0,X0_52,X1_52) ),
    inference(subtyping,[status(esa)],[c_1014])).

cnf(c_1840,plain,
    ( k2_lattices(sK0,X0_52,X1_52) = k4_lattices(sK0,X0_52,X1_52)
    | m1_subset_1(X0_52,u1_struct_0(sK0)) != iProver_top
    | m1_subset_1(X1_52,u1_struct_0(sK0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1499])).

cnf(c_2329,plain,
    ( k2_lattices(sK0,sK1,X0_52) = k4_lattices(sK0,sK1,X0_52)
    | m1_subset_1(X0_52,u1_struct_0(sK0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1836,c_1840])).

cnf(c_2517,plain,
    ( k2_lattices(sK0,sK1,k7_lattices(sK0,X0_52)) = k4_lattices(sK0,sK1,k7_lattices(sK0,X0_52))
    | m1_subset_1(X0_52,u1_struct_0(sK0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1844,c_2329])).

cnf(c_4419,plain,
    ( k2_lattices(sK0,sK1,k7_lattices(sK0,sK2)) = k4_lattices(sK0,sK1,k7_lattices(sK0,sK2)) ),
    inference(superposition,[status(thm)],[c_1835,c_2517])).

cnf(c_2328,plain,
    ( k2_lattices(sK0,sK2,X0_52) = k4_lattices(sK0,sK2,X0_52)
    | m1_subset_1(X0_52,u1_struct_0(sK0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1835,c_1840])).

cnf(c_2341,plain,
    ( k2_lattices(sK0,sK2,k7_lattices(sK0,X0_52)) = k4_lattices(sK0,sK2,k7_lattices(sK0,X0_52))
    | m1_subset_1(X0_52,u1_struct_0(sK0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1844,c_2328])).

cnf(c_2791,plain,
    ( k2_lattices(sK0,sK2,k7_lattices(sK0,sK2)) = k4_lattices(sK0,sK2,k7_lattices(sK0,sK2)) ),
    inference(superposition,[status(thm)],[c_1835,c_2341])).

cnf(c_2,plain,
    ( v7_lattices(X0)
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | ~ v10_lattices(X0) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_20,plain,
    ( ~ r1_lattices(X0,X1,X2)
    | r1_lattices(X0,k2_lattices(X0,X1,X3),k2_lattices(X0,X2,X3))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ v7_lattices(X0)
    | ~ v8_lattices(X0)
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | ~ v9_lattices(X0) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_469,plain,
    ( ~ r1_lattices(X0,X1,X2)
    | r1_lattices(X0,k2_lattices(X0,X1,X3),k2_lattices(X0,X2,X3))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ v8_lattices(X0)
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | ~ v10_lattices(X0)
    | ~ v9_lattices(X0) ),
    inference(resolution,[status(thm)],[c_2,c_20])).

cnf(c_1,plain,
    ( v8_lattices(X0)
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | ~ v10_lattices(X0) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_0,plain,
    ( ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | ~ v10_lattices(X0)
    | v9_lattices(X0) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_473,plain,
    ( ~ v10_lattices(X0)
    | v2_struct_0(X0)
    | ~ l3_lattices(X0)
    | ~ r1_lattices(X0,X1,X2)
    | r1_lattices(X0,k2_lattices(X0,X1,X3),k2_lattices(X0,X2,X3))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(X0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_469,c_1,c_0])).

cnf(c_474,plain,
    ( ~ r1_lattices(X0,X1,X2)
    | r1_lattices(X0,k2_lattices(X0,X1,X3),k2_lattices(X0,X2,X3))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | ~ v10_lattices(X0) ),
    inference(renaming,[status(thm)],[c_473])).

cnf(c_954,plain,
    ( ~ r1_lattices(X0,X1,X2)
    | r1_lattices(X0,k2_lattices(X0,X1,X3),k2_lattices(X0,X2,X3))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | sK0 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_474,c_31])).

cnf(c_955,plain,
    ( ~ r1_lattices(sK0,X0,X1)
    | r1_lattices(sK0,k2_lattices(sK0,X0,X2),k2_lattices(sK0,X1,X2))
    | ~ m1_subset_1(X0,u1_struct_0(sK0))
    | ~ m1_subset_1(X1,u1_struct_0(sK0))
    | ~ m1_subset_1(X2,u1_struct_0(sK0))
    | ~ l3_lattices(sK0)
    | v2_struct_0(sK0) ),
    inference(unflattening,[status(thm)],[c_954])).

cnf(c_959,plain,
    ( ~ r1_lattices(sK0,X0,X1)
    | r1_lattices(sK0,k2_lattices(sK0,X0,X2),k2_lattices(sK0,X1,X2))
    | ~ m1_subset_1(X0,u1_struct_0(sK0))
    | ~ m1_subset_1(X1,u1_struct_0(sK0))
    | ~ m1_subset_1(X2,u1_struct_0(sK0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_955,c_32,c_29])).

cnf(c_960,plain,
    ( ~ r1_lattices(sK0,X0,X1)
    | r1_lattices(sK0,k2_lattices(sK0,X0,X2),k2_lattices(sK0,X1,X2))
    | ~ m1_subset_1(X1,u1_struct_0(sK0))
    | ~ m1_subset_1(X0,u1_struct_0(sK0))
    | ~ m1_subset_1(X2,u1_struct_0(sK0)) ),
    inference(renaming,[status(thm)],[c_959])).

cnf(c_1501,plain,
    ( ~ r1_lattices(sK0,X0_52,X1_52)
    | r1_lattices(sK0,k2_lattices(sK0,X0_52,X2_52),k2_lattices(sK0,X1_52,X2_52))
    | ~ m1_subset_1(X1_52,u1_struct_0(sK0))
    | ~ m1_subset_1(X0_52,u1_struct_0(sK0))
    | ~ m1_subset_1(X2_52,u1_struct_0(sK0)) ),
    inference(subtyping,[status(esa)],[c_960])).

cnf(c_1838,plain,
    ( r1_lattices(sK0,X0_52,X1_52) != iProver_top
    | r1_lattices(sK0,k2_lattices(sK0,X0_52,X2_52),k2_lattices(sK0,X1_52,X2_52)) = iProver_top
    | m1_subset_1(X0_52,u1_struct_0(sK0)) != iProver_top
    | m1_subset_1(X1_52,u1_struct_0(sK0)) != iProver_top
    | m1_subset_1(X2_52,u1_struct_0(sK0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1501])).

cnf(c_2874,plain,
    ( r1_lattices(sK0,k4_lattices(sK0,sK2,k7_lattices(sK0,sK2)),k2_lattices(sK0,X0_52,k7_lattices(sK0,sK2))) = iProver_top
    | r1_lattices(sK0,sK2,X0_52) != iProver_top
    | m1_subset_1(X0_52,u1_struct_0(sK0)) != iProver_top
    | m1_subset_1(k7_lattices(sK0,sK2),u1_struct_0(sK0)) != iProver_top
    | m1_subset_1(sK2,u1_struct_0(sK0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2791,c_1838])).

cnf(c_38,plain,
    ( m1_subset_1(sK2,u1_struct_0(sK0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_1898,plain,
    ( m1_subset_1(k7_lattices(sK0,sK2),u1_struct_0(sK0))
    | ~ m1_subset_1(sK2,u1_struct_0(sK0)) ),
    inference(instantiation,[status(thm)],[c_1495])).

cnf(c_1899,plain,
    ( m1_subset_1(k7_lattices(sK0,sK2),u1_struct_0(sK0)) = iProver_top
    | m1_subset_1(sK2,u1_struct_0(sK0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1898])).

cnf(c_29446,plain,
    ( r1_lattices(sK0,k4_lattices(sK0,sK2,k7_lattices(sK0,sK2)),k2_lattices(sK0,X0_52,k7_lattices(sK0,sK2))) = iProver_top
    | r1_lattices(sK0,sK2,X0_52) != iProver_top
    | m1_subset_1(X0_52,u1_struct_0(sK0)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2874,c_38,c_1899])).

cnf(c_10,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l1_lattices(X1)
    | ~ v6_lattices(X1)
    | v2_struct_0(X1)
    | k4_lattices(X1,X0,X2) = k4_lattices(X1,X2,X0) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_662,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v6_lattices(X1)
    | ~ l3_lattices(X3)
    | v2_struct_0(X1)
    | X1 != X3
    | k4_lattices(X1,X0,X2) = k4_lattices(X1,X2,X0) ),
    inference(resolution_lifted,[status(thm)],[c_15,c_10])).

cnf(c_663,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v6_lattices(X1)
    | ~ l3_lattices(X1)
    | v2_struct_0(X1)
    | k4_lattices(X1,X0,X2) = k4_lattices(X1,X2,X0) ),
    inference(unflattening,[status(thm)],[c_662])).

cnf(c_713,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l3_lattices(X3)
    | ~ l3_lattices(X1)
    | v2_struct_0(X3)
    | v2_struct_0(X1)
    | ~ v10_lattices(X3)
    | X1 != X3
    | k4_lattices(X1,X0,X2) = k4_lattices(X1,X2,X0) ),
    inference(resolution_lifted,[status(thm)],[c_3,c_663])).

cnf(c_714,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l3_lattices(X1)
    | v2_struct_0(X1)
    | ~ v10_lattices(X1)
    | k4_lattices(X1,X0,X2) = k4_lattices(X1,X2,X0) ),
    inference(unflattening,[status(thm)],[c_713])).

cnf(c_1050,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l3_lattices(X1)
    | v2_struct_0(X1)
    | k4_lattices(X1,X2,X0) = k4_lattices(X1,X0,X2)
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_714,c_31])).

cnf(c_1051,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK0))
    | ~ m1_subset_1(X1,u1_struct_0(sK0))
    | ~ l3_lattices(sK0)
    | v2_struct_0(sK0)
    | k4_lattices(sK0,X1,X0) = k4_lattices(sK0,X0,X1) ),
    inference(unflattening,[status(thm)],[c_1050])).

cnf(c_1055,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK0))
    | ~ m1_subset_1(X1,u1_struct_0(sK0))
    | k4_lattices(sK0,X1,X0) = k4_lattices(sK0,X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1051,c_32,c_29])).

cnf(c_1056,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK0))
    | ~ m1_subset_1(X1,u1_struct_0(sK0))
    | k4_lattices(sK0,X0,X1) = k4_lattices(sK0,X1,X0) ),
    inference(renaming,[status(thm)],[c_1055])).

cnf(c_1497,plain,
    ( ~ m1_subset_1(X0_52,u1_struct_0(sK0))
    | ~ m1_subset_1(X1_52,u1_struct_0(sK0))
    | k4_lattices(sK0,X0_52,X1_52) = k4_lattices(sK0,X1_52,X0_52) ),
    inference(subtyping,[status(esa)],[c_1056])).

cnf(c_1842,plain,
    ( k4_lattices(sK0,X0_52,X1_52) = k4_lattices(sK0,X1_52,X0_52)
    | m1_subset_1(X0_52,u1_struct_0(sK0)) != iProver_top
    | m1_subset_1(X1_52,u1_struct_0(sK0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1497])).

cnf(c_2989,plain,
    ( k4_lattices(sK0,X0_52,sK2) = k4_lattices(sK0,sK2,X0_52)
    | m1_subset_1(X0_52,u1_struct_0(sK0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1835,c_1842])).

cnf(c_3096,plain,
    ( k4_lattices(sK0,k7_lattices(sK0,X0_52),sK2) = k4_lattices(sK0,sK2,k7_lattices(sK0,X0_52))
    | m1_subset_1(X0_52,u1_struct_0(sK0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1844,c_2989])).

cnf(c_5393,plain,
    ( k4_lattices(sK0,sK2,k7_lattices(sK0,sK2)) = k4_lattices(sK0,k7_lattices(sK0,sK2),sK2) ),
    inference(superposition,[status(thm)],[c_1835,c_3096])).

cnf(c_22,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ v17_lattices(X1)
    | ~ l3_lattices(X1)
    | v2_struct_0(X1)
    | ~ v10_lattices(X1)
    | k4_lattices(X1,k7_lattices(X1,X0),X0) = k5_lattices(X1) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_30,negated_conjecture,
    ( v17_lattices(sK0) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_872,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ l3_lattices(X1)
    | v2_struct_0(X1)
    | ~ v10_lattices(X1)
    | k4_lattices(X1,k7_lattices(X1,X0),X0) = k5_lattices(X1)
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_22,c_30])).

cnf(c_873,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK0))
    | ~ l3_lattices(sK0)
    | v2_struct_0(sK0)
    | ~ v10_lattices(sK0)
    | k4_lattices(sK0,k7_lattices(sK0,X0),X0) = k5_lattices(sK0) ),
    inference(unflattening,[status(thm)],[c_872])).

cnf(c_877,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK0))
    | k4_lattices(sK0,k7_lattices(sK0,X0),X0) = k5_lattices(sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_873,c_32,c_31,c_29])).

cnf(c_1502,plain,
    ( ~ m1_subset_1(X0_52,u1_struct_0(sK0))
    | k4_lattices(sK0,k7_lattices(sK0,X0_52),X0_52) = k5_lattices(sK0) ),
    inference(subtyping,[status(esa)],[c_877])).

cnf(c_1837,plain,
    ( k4_lattices(sK0,k7_lattices(sK0,X0_52),X0_52) = k5_lattices(sK0)
    | m1_subset_1(X0_52,u1_struct_0(sK0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1502])).

cnf(c_1977,plain,
    ( k4_lattices(sK0,k7_lattices(sK0,sK2),sK2) = k5_lattices(sK0) ),
    inference(superposition,[status(thm)],[c_1835,c_1837])).

cnf(c_5400,plain,
    ( k4_lattices(sK0,sK2,k7_lattices(sK0,sK2)) = k5_lattices(sK0) ),
    inference(light_normalisation,[status(thm)],[c_5393,c_1977])).

cnf(c_29450,plain,
    ( r1_lattices(sK0,k5_lattices(sK0),k2_lattices(sK0,X0_52,k7_lattices(sK0,sK2))) = iProver_top
    | r1_lattices(sK0,sK2,X0_52) != iProver_top
    | m1_subset_1(X0_52,u1_struct_0(sK0)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_29446,c_5400])).

cnf(c_37,plain,
    ( m1_subset_1(sK1,u1_struct_0(sK0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_1521,plain,
    ( ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | k4_lattices(sK0,k7_lattices(sK0,sK1),sK1) = k5_lattices(sK0) ),
    inference(instantiation,[status(thm)],[c_1502])).

cnf(c_1539,plain,
    ( m1_subset_1(X0_52,u1_struct_0(sK0)) != iProver_top
    | m1_subset_1(k7_lattices(sK0,X0_52),u1_struct_0(sK0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1495])).

cnf(c_1541,plain,
    ( m1_subset_1(k7_lattices(sK0,sK1),u1_struct_0(sK0)) = iProver_top
    | m1_subset_1(sK1,u1_struct_0(sK0)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_1539])).

cnf(c_8,plain,
    ( ~ v17_lattices(X0)
    | v15_lattices(X0)
    | ~ l3_lattices(X0)
    | v2_struct_0(X0) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_6,plain,
    ( ~ v15_lattices(X0)
    | v13_lattices(X0)
    | ~ l3_lattices(X0)
    | v2_struct_0(X0) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_341,plain,
    ( ~ v17_lattices(X0)
    | v13_lattices(X0)
    | ~ l3_lattices(X0)
    | v2_struct_0(X0) ),
    inference(resolution,[status(thm)],[c_8,c_6])).

cnf(c_21,plain,
    ( r3_lattices(X0,k5_lattices(X0),X1)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ v13_lattices(X0)
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | ~ v10_lattices(X0) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_363,plain,
    ( r3_lattices(X0,k5_lattices(X0),X1)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ v17_lattices(X0)
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | ~ v10_lattices(X0) ),
    inference(resolution,[status(thm)],[c_341,c_21])).

cnf(c_806,plain,
    ( r3_lattices(X0,k5_lattices(X0),X1)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | ~ v10_lattices(X0)
    | sK0 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_363,c_30])).

cnf(c_807,plain,
    ( r3_lattices(sK0,k5_lattices(sK0),X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK0))
    | ~ l3_lattices(sK0)
    | v2_struct_0(sK0)
    | ~ v10_lattices(sK0) ),
    inference(unflattening,[status(thm)],[c_806])).

cnf(c_811,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK0))
    | r3_lattices(sK0,k5_lattices(sK0),X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_807,c_32,c_31,c_29])).

cnf(c_812,plain,
    ( r3_lattices(sK0,k5_lattices(sK0),X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK0)) ),
    inference(renaming,[status(thm)],[c_811])).

cnf(c_18,plain,
    ( r1_lattices(X0,X1,X2)
    | ~ r3_lattices(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ v6_lattices(X0)
    | ~ v8_lattices(X0)
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | ~ v9_lattices(X0) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_513,plain,
    ( r1_lattices(X0,X1,X2)
    | ~ r3_lattices(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ v6_lattices(X0)
    | ~ v8_lattices(X0)
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | ~ v10_lattices(X0) ),
    inference(resolution,[status(thm)],[c_0,c_18])).

cnf(c_517,plain,
    ( r1_lattices(X0,X1,X2)
    | ~ r3_lattices(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | ~ v10_lattices(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_513,c_3,c_1])).

cnf(c_930,plain,
    ( r1_lattices(X0,X1,X2)
    | ~ r3_lattices(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | sK0 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_517,c_31])).

cnf(c_931,plain,
    ( r1_lattices(sK0,X0,X1)
    | ~ r3_lattices(sK0,X0,X1)
    | ~ m1_subset_1(X0,u1_struct_0(sK0))
    | ~ m1_subset_1(X1,u1_struct_0(sK0))
    | ~ l3_lattices(sK0)
    | v2_struct_0(sK0) ),
    inference(unflattening,[status(thm)],[c_930])).

cnf(c_935,plain,
    ( r1_lattices(sK0,X0,X1)
    | ~ r3_lattices(sK0,X0,X1)
    | ~ m1_subset_1(X0,u1_struct_0(sK0))
    | ~ m1_subset_1(X1,u1_struct_0(sK0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_931,c_32,c_29])).

cnf(c_936,plain,
    ( r1_lattices(sK0,X0,X1)
    | ~ r3_lattices(sK0,X0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK0))
    | ~ m1_subset_1(X0,u1_struct_0(sK0)) ),
    inference(renaming,[status(thm)],[c_935])).

cnf(c_1257,plain,
    ( r1_lattices(sK0,X0,X1)
    | ~ m1_subset_1(X0,u1_struct_0(sK0))
    | ~ m1_subset_1(X2,u1_struct_0(sK0))
    | ~ m1_subset_1(X1,u1_struct_0(sK0))
    | X1 != X2
    | k5_lattices(sK0) != X0
    | sK0 != sK0 ),
    inference(resolution_lifted,[status(thm)],[c_812,c_936])).

cnf(c_1258,plain,
    ( r1_lattices(sK0,k5_lattices(sK0),X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK0))
    | ~ m1_subset_1(k5_lattices(sK0),u1_struct_0(sK0)) ),
    inference(unflattening,[status(thm)],[c_1257])).

cnf(c_1488,plain,
    ( r1_lattices(sK0,k5_lattices(sK0),X0_52)
    | ~ m1_subset_1(X0_52,u1_struct_0(sK0))
    | ~ m1_subset_1(k5_lattices(sK0),u1_struct_0(sK0)) ),
    inference(subtyping,[status(esa)],[c_1258])).

cnf(c_1554,plain,
    ( r1_lattices(sK0,k5_lattices(sK0),X0_52) = iProver_top
    | m1_subset_1(X0_52,u1_struct_0(sK0)) != iProver_top
    | m1_subset_1(k5_lattices(sK0),u1_struct_0(sK0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1488])).

cnf(c_1506,plain,
    ( X0_52 = X0_52 ),
    theory(equality)).

cnf(c_2128,plain,
    ( k5_lattices(sK0) = k5_lattices(sK0) ),
    inference(instantiation,[status(thm)],[c_1506])).

cnf(c_1507,plain,
    ( X0_52 != X1_52
    | X2_52 != X1_52
    | X2_52 = X0_52 ),
    theory(equality)).

cnf(c_1961,plain,
    ( X0_52 != X1_52
    | k5_lattices(sK0) != X1_52
    | k5_lattices(sK0) = X0_52 ),
    inference(instantiation,[status(thm)],[c_1507])).

cnf(c_2062,plain,
    ( X0_52 != k5_lattices(sK0)
    | k5_lattices(sK0) = X0_52
    | k5_lattices(sK0) != k5_lattices(sK0) ),
    inference(instantiation,[status(thm)],[c_1961])).

cnf(c_2438,plain,
    ( k4_lattices(sK0,k7_lattices(sK0,X0_52),X0_52) != k5_lattices(sK0)
    | k5_lattices(sK0) = k4_lattices(sK0,k7_lattices(sK0,X0_52),X0_52)
    | k5_lattices(sK0) != k5_lattices(sK0) ),
    inference(instantiation,[status(thm)],[c_2062])).

cnf(c_2439,plain,
    ( k4_lattices(sK0,k7_lattices(sK0,sK1),sK1) != k5_lattices(sK0)
    | k5_lattices(sK0) = k4_lattices(sK0,k7_lattices(sK0,sK1),sK1)
    | k5_lattices(sK0) != k5_lattices(sK0) ),
    inference(instantiation,[status(thm)],[c_2438])).

cnf(c_1509,plain,
    ( ~ m1_subset_1(X0_52,X0_54)
    | m1_subset_1(X1_52,X0_54)
    | X1_52 != X0_52 ),
    theory(equality)).

cnf(c_1925,plain,
    ( ~ m1_subset_1(X0_52,u1_struct_0(sK0))
    | m1_subset_1(k5_lattices(sK0),u1_struct_0(sK0))
    | k5_lattices(sK0) != X0_52 ),
    inference(instantiation,[status(thm)],[c_1509])).

cnf(c_2538,plain,
    ( ~ m1_subset_1(k4_lattices(sK0,k7_lattices(sK0,X0_52),X0_52),u1_struct_0(sK0))
    | m1_subset_1(k5_lattices(sK0),u1_struct_0(sK0))
    | k5_lattices(sK0) != k4_lattices(sK0,k7_lattices(sK0,X0_52),X0_52) ),
    inference(instantiation,[status(thm)],[c_1925])).

cnf(c_2541,plain,
    ( k5_lattices(sK0) != k4_lattices(sK0,k7_lattices(sK0,X0_52),X0_52)
    | m1_subset_1(k4_lattices(sK0,k7_lattices(sK0,X0_52),X0_52),u1_struct_0(sK0)) != iProver_top
    | m1_subset_1(k5_lattices(sK0),u1_struct_0(sK0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2538])).

cnf(c_2543,plain,
    ( k5_lattices(sK0) != k4_lattices(sK0,k7_lattices(sK0,sK1),sK1)
    | m1_subset_1(k4_lattices(sK0,k7_lattices(sK0,sK1),sK1),u1_struct_0(sK0)) != iProver_top
    | m1_subset_1(k5_lattices(sK0),u1_struct_0(sK0)) = iProver_top ),
    inference(instantiation,[status(thm)],[c_2541])).

cnf(c_12,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | m1_subset_1(k4_lattices(X1,X2,X0),u1_struct_0(X1))
    | ~ l1_lattices(X1)
    | ~ v6_lattices(X1)
    | v2_struct_0(X1) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_617,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | m1_subset_1(k4_lattices(X1,X2,X0),u1_struct_0(X1))
    | ~ v6_lattices(X1)
    | ~ l3_lattices(X3)
    | v2_struct_0(X1)
    | X1 != X3 ),
    inference(resolution_lifted,[status(thm)],[c_15,c_12])).

cnf(c_618,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | m1_subset_1(k4_lattices(X1,X2,X0),u1_struct_0(X1))
    | ~ v6_lattices(X1)
    | ~ l3_lattices(X1)
    | v2_struct_0(X1) ),
    inference(unflattening,[status(thm)],[c_617])).

cnf(c_737,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | m1_subset_1(k4_lattices(X1,X2,X0),u1_struct_0(X1))
    | ~ l3_lattices(X3)
    | ~ l3_lattices(X1)
    | v2_struct_0(X3)
    | v2_struct_0(X1)
    | ~ v10_lattices(X3)
    | X1 != X3 ),
    inference(resolution_lifted,[status(thm)],[c_3,c_618])).

cnf(c_738,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | m1_subset_1(k4_lattices(X1,X2,X0),u1_struct_0(X1))
    | ~ l3_lattices(X1)
    | v2_struct_0(X1)
    | ~ v10_lattices(X1) ),
    inference(unflattening,[status(thm)],[c_737])).

cnf(c_1029,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | m1_subset_1(k4_lattices(X1,X2,X0),u1_struct_0(X1))
    | ~ l3_lattices(X1)
    | v2_struct_0(X1)
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_738,c_31])).

cnf(c_1030,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK0))
    | ~ m1_subset_1(X1,u1_struct_0(sK0))
    | m1_subset_1(k4_lattices(sK0,X1,X0),u1_struct_0(sK0))
    | ~ l3_lattices(sK0)
    | v2_struct_0(sK0) ),
    inference(unflattening,[status(thm)],[c_1029])).

cnf(c_1034,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK0))
    | ~ m1_subset_1(X1,u1_struct_0(sK0))
    | m1_subset_1(k4_lattices(sK0,X1,X0),u1_struct_0(sK0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1030,c_32,c_29])).

cnf(c_1035,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK0))
    | ~ m1_subset_1(X1,u1_struct_0(sK0))
    | m1_subset_1(k4_lattices(sK0,X0,X1),u1_struct_0(sK0)) ),
    inference(renaming,[status(thm)],[c_1034])).

cnf(c_1498,plain,
    ( ~ m1_subset_1(X0_52,u1_struct_0(sK0))
    | ~ m1_subset_1(X1_52,u1_struct_0(sK0))
    | m1_subset_1(k4_lattices(sK0,X0_52,X1_52),u1_struct_0(sK0)) ),
    inference(subtyping,[status(esa)],[c_1035])).

cnf(c_2886,plain,
    ( ~ m1_subset_1(X0_52,u1_struct_0(sK0))
    | m1_subset_1(k4_lattices(sK0,k7_lattices(sK0,X1_52),X0_52),u1_struct_0(sK0))
    | ~ m1_subset_1(k7_lattices(sK0,X1_52),u1_struct_0(sK0)) ),
    inference(instantiation,[status(thm)],[c_1498])).

cnf(c_2887,plain,
    ( m1_subset_1(X0_52,u1_struct_0(sK0)) != iProver_top
    | m1_subset_1(k4_lattices(sK0,k7_lattices(sK0,X1_52),X0_52),u1_struct_0(sK0)) = iProver_top
    | m1_subset_1(k7_lattices(sK0,X1_52),u1_struct_0(sK0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2886])).

cnf(c_2889,plain,
    ( m1_subset_1(k4_lattices(sK0,k7_lattices(sK0,sK1),sK1),u1_struct_0(sK0)) = iProver_top
    | m1_subset_1(k7_lattices(sK0,sK1),u1_struct_0(sK0)) != iProver_top
    | m1_subset_1(sK1,u1_struct_0(sK0)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_2887])).

cnf(c_1978,plain,
    ( k4_lattices(sK0,k7_lattices(sK0,sK1),sK1) = k5_lattices(sK0) ),
    inference(superposition,[status(thm)],[c_1836,c_1837])).

cnf(c_1841,plain,
    ( m1_subset_1(X0_52,u1_struct_0(sK0)) != iProver_top
    | m1_subset_1(X1_52,u1_struct_0(sK0)) != iProver_top
    | m1_subset_1(k4_lattices(sK0,X0_52,X1_52),u1_struct_0(sK0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1498])).

cnf(c_2954,plain,
    ( m1_subset_1(k7_lattices(sK0,sK1),u1_struct_0(sK0)) != iProver_top
    | m1_subset_1(k5_lattices(sK0),u1_struct_0(sK0)) = iProver_top
    | m1_subset_1(sK1,u1_struct_0(sK0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1978,c_1841])).

cnf(c_9473,plain,
    ( m1_subset_1(k5_lattices(sK0),u1_struct_0(sK0)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2954,c_28,c_37,c_1521,c_1541,c_2128,c_2439,c_2543,c_2889])).

cnf(c_9502,plain,
    ( k2_lattices(sK0,k5_lattices(sK0),X0_52) = k4_lattices(sK0,k5_lattices(sK0),X0_52)
    | m1_subset_1(X0_52,u1_struct_0(sK0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_9473,c_1840])).

cnf(c_10443,plain,
    ( k2_lattices(sK0,k5_lattices(sK0),k7_lattices(sK0,X0_52)) = k4_lattices(sK0,k5_lattices(sK0),k7_lattices(sK0,X0_52))
    | m1_subset_1(X0_52,u1_struct_0(sK0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1844,c_9502])).

cnf(c_11280,plain,
    ( k2_lattices(sK0,k5_lattices(sK0),k7_lattices(sK0,sK2)) = k4_lattices(sK0,k5_lattices(sK0),k7_lattices(sK0,sK2)) ),
    inference(superposition,[status(thm)],[c_1835,c_10443])).

cnf(c_23,plain,
    ( ~ r3_lattices(X0,X1,k7_lattices(X0,X2))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ v17_lattices(X0)
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | ~ v10_lattices(X0)
    | k4_lattices(X0,X1,X2) = k5_lattices(X0) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_848,plain,
    ( ~ r3_lattices(X0,X1,k7_lattices(X0,X2))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | ~ v10_lattices(X0)
    | k4_lattices(X0,X1,X2) = k5_lattices(X0)
    | sK0 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_23,c_30])).

cnf(c_849,plain,
    ( ~ r3_lattices(sK0,X0,k7_lattices(sK0,X1))
    | ~ m1_subset_1(X0,u1_struct_0(sK0))
    | ~ m1_subset_1(X1,u1_struct_0(sK0))
    | ~ l3_lattices(sK0)
    | v2_struct_0(sK0)
    | ~ v10_lattices(sK0)
    | k4_lattices(sK0,X0,X1) = k5_lattices(sK0) ),
    inference(unflattening,[status(thm)],[c_848])).

cnf(c_853,plain,
    ( ~ m1_subset_1(X1,u1_struct_0(sK0))
    | ~ m1_subset_1(X0,u1_struct_0(sK0))
    | ~ r3_lattices(sK0,X0,k7_lattices(sK0,X1))
    | k4_lattices(sK0,X0,X1) = k5_lattices(sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_849,c_32,c_31,c_29])).

cnf(c_854,plain,
    ( ~ r3_lattices(sK0,X0,k7_lattices(sK0,X1))
    | ~ m1_subset_1(X1,u1_struct_0(sK0))
    | ~ m1_subset_1(X0,u1_struct_0(sK0))
    | k4_lattices(sK0,X0,X1) = k5_lattices(sK0) ),
    inference(renaming,[status(thm)],[c_853])).

cnf(c_1236,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK0))
    | ~ m1_subset_1(X1,u1_struct_0(sK0))
    | ~ m1_subset_1(X2,u1_struct_0(sK0))
    | k4_lattices(sK0,X0,X2) = k5_lattices(sK0)
    | k7_lattices(sK0,X2) != X1
    | k5_lattices(sK0) != X0
    | sK0 != sK0 ),
    inference(resolution_lifted,[status(thm)],[c_812,c_854])).

cnf(c_1237,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK0))
    | ~ m1_subset_1(k7_lattices(sK0,X0),u1_struct_0(sK0))
    | ~ m1_subset_1(k5_lattices(sK0),u1_struct_0(sK0))
    | k4_lattices(sK0,k5_lattices(sK0),X0) = k5_lattices(sK0) ),
    inference(unflattening,[status(thm)],[c_1236])).

cnf(c_1241,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK0))
    | ~ m1_subset_1(k5_lattices(sK0),u1_struct_0(sK0))
    | k4_lattices(sK0,k5_lattices(sK0),X0) = k5_lattices(sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1237,c_29,c_1127])).

cnf(c_1489,plain,
    ( ~ m1_subset_1(X0_52,u1_struct_0(sK0))
    | ~ m1_subset_1(k5_lattices(sK0),u1_struct_0(sK0))
    | k4_lattices(sK0,k5_lattices(sK0),X0_52) = k5_lattices(sK0) ),
    inference(subtyping,[status(esa)],[c_1241])).

cnf(c_1850,plain,
    ( k4_lattices(sK0,k5_lattices(sK0),X0_52) = k5_lattices(sK0)
    | m1_subset_1(X0_52,u1_struct_0(sK0)) != iProver_top
    | m1_subset_1(k5_lattices(sK0),u1_struct_0(sK0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1489])).

cnf(c_1551,plain,
    ( k4_lattices(sK0,k5_lattices(sK0),X0_52) = k5_lattices(sK0)
    | m1_subset_1(X0_52,u1_struct_0(sK0)) != iProver_top
    | m1_subset_1(k5_lattices(sK0),u1_struct_0(sK0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1489])).

cnf(c_3375,plain,
    ( m1_subset_1(X0_52,u1_struct_0(sK0)) != iProver_top
    | k4_lattices(sK0,k5_lattices(sK0),X0_52) = k5_lattices(sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1850,c_28,c_37,c_1521,c_1541,c_1551,c_2128,c_2439,c_2543,c_2889])).

cnf(c_3376,plain,
    ( k4_lattices(sK0,k5_lattices(sK0),X0_52) = k5_lattices(sK0)
    | m1_subset_1(X0_52,u1_struct_0(sK0)) != iProver_top ),
    inference(renaming,[status(thm)],[c_3375])).

cnf(c_3383,plain,
    ( k4_lattices(sK0,k5_lattices(sK0),k7_lattices(sK0,X0_52)) = k5_lattices(sK0)
    | m1_subset_1(X0_52,u1_struct_0(sK0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1844,c_3376])).

cnf(c_4777,plain,
    ( k4_lattices(sK0,k5_lattices(sK0),k7_lattices(sK0,sK2)) = k5_lattices(sK0) ),
    inference(superposition,[status(thm)],[c_1835,c_3383])).

cnf(c_11292,plain,
    ( k2_lattices(sK0,k5_lattices(sK0),k7_lattices(sK0,sK2)) = k5_lattices(sK0) ),
    inference(light_normalisation,[status(thm)],[c_11280,c_4777])).

cnf(c_11408,plain,
    ( r1_lattices(sK0,k5_lattices(sK0),X0_52) != iProver_top
    | r1_lattices(sK0,k5_lattices(sK0),k2_lattices(sK0,X0_52,k7_lattices(sK0,sK2))) = iProver_top
    | m1_subset_1(X0_52,u1_struct_0(sK0)) != iProver_top
    | m1_subset_1(k7_lattices(sK0,sK2),u1_struct_0(sK0)) != iProver_top
    | m1_subset_1(k5_lattices(sK0),u1_struct_0(sK0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_11292,c_1838])).

cnf(c_29452,plain,
    ( r1_lattices(sK0,k5_lattices(sK0),k2_lattices(sK0,X0_52,k7_lattices(sK0,sK2))) = iProver_top
    | m1_subset_1(X0_52,u1_struct_0(sK0)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_29450,c_28,c_37,c_38,c_1521,c_1541,c_1554,c_1899,c_2128,c_2439,c_2543,c_2889,c_11408])).

cnf(c_29459,plain,
    ( r1_lattices(sK0,k5_lattices(sK0),k4_lattices(sK0,sK1,k7_lattices(sK0,sK2))) = iProver_top
    | m1_subset_1(sK1,u1_struct_0(sK0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_4419,c_29452])).

cnf(c_29696,plain,
    ( r1_lattices(sK0,k5_lattices(sK0),k4_lattices(sK0,sK1,k7_lattices(sK0,sK2))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_29459,c_37])).

cnf(c_4,plain,
    ( v4_lattices(X0)
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | ~ v10_lattices(X0) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_14,plain,
    ( l2_lattices(X0)
    | ~ l3_lattices(X0) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_19,plain,
    ( ~ r1_lattices(X0,X1,X2)
    | ~ r1_lattices(X0,X2,X1)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ l2_lattices(X0)
    | ~ v4_lattices(X0)
    | v2_struct_0(X0)
    | X2 = X1 ),
    inference(cnf_transformation,[],[f78])).

cnf(c_393,plain,
    ( ~ r1_lattices(X0,X1,X2)
    | ~ r1_lattices(X0,X2,X1)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ v4_lattices(X0)
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | X2 = X1 ),
    inference(resolution,[status(thm)],[c_14,c_19])).

cnf(c_431,plain,
    ( ~ r1_lattices(X0,X1,X2)
    | ~ r1_lattices(X0,X2,X1)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | ~ v10_lattices(X0)
    | X2 = X1 ),
    inference(resolution,[status(thm)],[c_4,c_393])).

cnf(c_981,plain,
    ( ~ r1_lattices(X0,X1,X2)
    | ~ r1_lattices(X0,X2,X1)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | X2 = X1
    | sK0 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_431,c_31])).

cnf(c_982,plain,
    ( ~ r1_lattices(sK0,X0,X1)
    | ~ r1_lattices(sK0,X1,X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK0))
    | ~ m1_subset_1(X1,u1_struct_0(sK0))
    | ~ l3_lattices(sK0)
    | v2_struct_0(sK0)
    | X1 = X0 ),
    inference(unflattening,[status(thm)],[c_981])).

cnf(c_986,plain,
    ( ~ r1_lattices(sK0,X0,X1)
    | ~ r1_lattices(sK0,X1,X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK0))
    | ~ m1_subset_1(X1,u1_struct_0(sK0))
    | X1 = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_982,c_32,c_29])).

cnf(c_987,plain,
    ( ~ r1_lattices(sK0,X0,X1)
    | ~ r1_lattices(sK0,X1,X0)
    | ~ m1_subset_1(X1,u1_struct_0(sK0))
    | ~ m1_subset_1(X0,u1_struct_0(sK0))
    | X1 = X0 ),
    inference(renaming,[status(thm)],[c_986])).

cnf(c_1500,plain,
    ( ~ r1_lattices(sK0,X0_52,X1_52)
    | ~ r1_lattices(sK0,X1_52,X0_52)
    | ~ m1_subset_1(X1_52,u1_struct_0(sK0))
    | ~ m1_subset_1(X0_52,u1_struct_0(sK0))
    | X1_52 = X0_52 ),
    inference(subtyping,[status(esa)],[c_987])).

cnf(c_1839,plain,
    ( X0_52 = X1_52
    | r1_lattices(sK0,X1_52,X0_52) != iProver_top
    | r1_lattices(sK0,X0_52,X1_52) != iProver_top
    | m1_subset_1(X1_52,u1_struct_0(sK0)) != iProver_top
    | m1_subset_1(X0_52,u1_struct_0(sK0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1500])).

cnf(c_2959,plain,
    ( k4_lattices(sK0,X0_52,X1_52) = X2_52
    | r1_lattices(sK0,X2_52,k4_lattices(sK0,X0_52,X1_52)) != iProver_top
    | r1_lattices(sK0,k4_lattices(sK0,X0_52,X1_52),X2_52) != iProver_top
    | m1_subset_1(X0_52,u1_struct_0(sK0)) != iProver_top
    | m1_subset_1(X1_52,u1_struct_0(sK0)) != iProver_top
    | m1_subset_1(X2_52,u1_struct_0(sK0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1841,c_1839])).

cnf(c_44412,plain,
    ( k4_lattices(sK0,sK1,k7_lattices(sK0,sK2)) = k5_lattices(sK0)
    | r1_lattices(sK0,k4_lattices(sK0,sK1,k7_lattices(sK0,sK2)),k5_lattices(sK0)) != iProver_top
    | m1_subset_1(k7_lattices(sK0,sK2),u1_struct_0(sK0)) != iProver_top
    | m1_subset_1(k5_lattices(sK0),u1_struct_0(sK0)) != iProver_top
    | m1_subset_1(sK1,u1_struct_0(sK0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_29696,c_2959])).

cnf(c_2875,plain,
    ( r1_lattices(sK0,X0_52,sK2) != iProver_top
    | r1_lattices(sK0,k2_lattices(sK0,X0_52,k7_lattices(sK0,sK2)),k4_lattices(sK0,sK2,k7_lattices(sK0,sK2))) = iProver_top
    | m1_subset_1(X0_52,u1_struct_0(sK0)) != iProver_top
    | m1_subset_1(k7_lattices(sK0,sK2),u1_struct_0(sK0)) != iProver_top
    | m1_subset_1(sK2,u1_struct_0(sK0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2791,c_1838])).

cnf(c_31769,plain,
    ( r1_lattices(sK0,X0_52,sK2) != iProver_top
    | r1_lattices(sK0,k2_lattices(sK0,X0_52,k7_lattices(sK0,sK2)),k4_lattices(sK0,sK2,k7_lattices(sK0,sK2))) = iProver_top
    | m1_subset_1(X0_52,u1_struct_0(sK0)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2875,c_38,c_1899])).

cnf(c_31775,plain,
    ( r1_lattices(sK0,X0_52,sK2) != iProver_top
    | r1_lattices(sK0,k2_lattices(sK0,X0_52,k7_lattices(sK0,sK2)),k5_lattices(sK0)) = iProver_top
    | m1_subset_1(X0_52,u1_struct_0(sK0)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_31769,c_5400])).

cnf(c_31780,plain,
    ( r1_lattices(sK0,k4_lattices(sK0,sK1,k7_lattices(sK0,sK2)),k5_lattices(sK0)) = iProver_top
    | r1_lattices(sK0,sK1,sK2) != iProver_top
    | m1_subset_1(sK1,u1_struct_0(sK0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_4419,c_31775])).

cnf(c_2990,plain,
    ( k4_lattices(sK0,X0_52,sK1) = k4_lattices(sK0,sK1,X0_52)
    | m1_subset_1(X0_52,u1_struct_0(sK0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1836,c_1842])).

cnf(c_3218,plain,
    ( k4_lattices(sK0,k7_lattices(sK0,X0_52),sK1) = k4_lattices(sK0,sK1,k7_lattices(sK0,X0_52))
    | m1_subset_1(X0_52,u1_struct_0(sK0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1844,c_2990])).

cnf(c_6305,plain,
    ( k4_lattices(sK0,sK1,k7_lattices(sK0,sK2)) = k4_lattices(sK0,k7_lattices(sK0,sK2),sK1) ),
    inference(superposition,[status(thm)],[c_1835,c_3218])).

cnf(c_25,negated_conjecture,
    ( ~ r3_lattices(sK0,k7_lattices(sK0,sK2),k7_lattices(sK0,sK1)) ),
    inference(cnf_transformation,[],[f91])).

cnf(c_24,plain,
    ( r3_lattices(X0,X1,k7_lattices(X0,X2))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ v17_lattices(X0)
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | ~ v10_lattices(X0)
    | k4_lattices(X0,X1,X2) != k5_lattices(X0) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_824,plain,
    ( r3_lattices(X0,X1,k7_lattices(X0,X2))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | ~ v10_lattices(X0)
    | k4_lattices(X0,X1,X2) != k5_lattices(X0)
    | sK0 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_24,c_30])).

cnf(c_825,plain,
    ( r3_lattices(sK0,X0,k7_lattices(sK0,X1))
    | ~ m1_subset_1(X0,u1_struct_0(sK0))
    | ~ m1_subset_1(X1,u1_struct_0(sK0))
    | ~ l3_lattices(sK0)
    | v2_struct_0(sK0)
    | ~ v10_lattices(sK0)
    | k4_lattices(sK0,X0,X1) != k5_lattices(sK0) ),
    inference(unflattening,[status(thm)],[c_824])).

cnf(c_829,plain,
    ( ~ m1_subset_1(X1,u1_struct_0(sK0))
    | ~ m1_subset_1(X0,u1_struct_0(sK0))
    | r3_lattices(sK0,X0,k7_lattices(sK0,X1))
    | k4_lattices(sK0,X0,X1) != k5_lattices(sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_825,c_32,c_31,c_29])).

cnf(c_830,plain,
    ( r3_lattices(sK0,X0,k7_lattices(sK0,X1))
    | ~ m1_subset_1(X1,u1_struct_0(sK0))
    | ~ m1_subset_1(X0,u1_struct_0(sK0))
    | k4_lattices(sK0,X0,X1) != k5_lattices(sK0) ),
    inference(renaming,[status(thm)],[c_829])).

cnf(c_1173,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK0))
    | ~ m1_subset_1(X1,u1_struct_0(sK0))
    | k4_lattices(sK0,X1,X0) != k5_lattices(sK0)
    | k7_lattices(sK0,X0) != k7_lattices(sK0,sK1)
    | k7_lattices(sK0,sK2) != X1
    | sK0 != sK0 ),
    inference(resolution_lifted,[status(thm)],[c_25,c_830])).

cnf(c_1174,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK0))
    | ~ m1_subset_1(k7_lattices(sK0,sK2),u1_struct_0(sK0))
    | k4_lattices(sK0,k7_lattices(sK0,sK2),X0) != k5_lattices(sK0)
    | k7_lattices(sK0,X0) != k7_lattices(sK0,sK1) ),
    inference(unflattening,[status(thm)],[c_1173])).

cnf(c_1493,plain,
    ( ~ m1_subset_1(X0_52,u1_struct_0(sK0))
    | ~ m1_subset_1(k7_lattices(sK0,sK2),u1_struct_0(sK0))
    | k4_lattices(sK0,k7_lattices(sK0,sK2),X0_52) != k5_lattices(sK0)
    | k7_lattices(sK0,X0_52) != k7_lattices(sK0,sK1) ),
    inference(subtyping,[status(esa)],[c_1174])).

cnf(c_1846,plain,
    ( k4_lattices(sK0,k7_lattices(sK0,sK2),X0_52) != k5_lattices(sK0)
    | k7_lattices(sK0,X0_52) != k7_lattices(sK0,sK1)
    | m1_subset_1(X0_52,u1_struct_0(sK0)) != iProver_top
    | m1_subset_1(k7_lattices(sK0,sK2),u1_struct_0(sK0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1493])).

cnf(c_1543,plain,
    ( k4_lattices(sK0,k7_lattices(sK0,sK2),X0_52) != k5_lattices(sK0)
    | k7_lattices(sK0,X0_52) != k7_lattices(sK0,sK1)
    | m1_subset_1(X0_52,u1_struct_0(sK0)) != iProver_top
    | m1_subset_1(k7_lattices(sK0,sK2),u1_struct_0(sK0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1493])).

cnf(c_2170,plain,
    ( m1_subset_1(X0_52,u1_struct_0(sK0)) != iProver_top
    | k7_lattices(sK0,X0_52) != k7_lattices(sK0,sK1)
    | k4_lattices(sK0,k7_lattices(sK0,sK2),X0_52) != k5_lattices(sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1846,c_38,c_1543,c_1899])).

cnf(c_2171,plain,
    ( k4_lattices(sK0,k7_lattices(sK0,sK2),X0_52) != k5_lattices(sK0)
    | k7_lattices(sK0,X0_52) != k7_lattices(sK0,sK1)
    | m1_subset_1(X0_52,u1_struct_0(sK0)) != iProver_top ),
    inference(renaming,[status(thm)],[c_2170])).

cnf(c_6324,plain,
    ( k4_lattices(sK0,sK1,k7_lattices(sK0,sK2)) != k5_lattices(sK0)
    | k7_lattices(sK0,sK1) != k7_lattices(sK0,sK1)
    | m1_subset_1(sK1,u1_struct_0(sK0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_6305,c_2171])).

cnf(c_6325,plain,
    ( k4_lattices(sK0,sK1,k7_lattices(sK0,sK2)) != k5_lattices(sK0)
    | m1_subset_1(sK1,u1_struct_0(sK0)) != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_6324])).

cnf(c_26,negated_conjecture,
    ( r3_lattices(sK0,sK1,sK2) ),
    inference(cnf_transformation,[],[f90])).

cnf(c_1225,plain,
    ( r1_lattices(sK0,X0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK0))
    | ~ m1_subset_1(X0,u1_struct_0(sK0))
    | sK1 != X0
    | sK2 != X1
    | sK0 != sK0 ),
    inference(resolution_lifted,[status(thm)],[c_26,c_936])).

cnf(c_1226,plain,
    ( r1_lattices(sK0,sK1,sK2)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ m1_subset_1(sK2,u1_struct_0(sK0)) ),
    inference(unflattening,[status(thm)],[c_1225])).

cnf(c_1227,plain,
    ( r1_lattices(sK0,sK1,sK2) = iProver_top
    | m1_subset_1(sK1,u1_struct_0(sK0)) != iProver_top
    | m1_subset_1(sK2,u1_struct_0(sK0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1226])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_44412,c_31780,c_6325,c_2889,c_2543,c_2439,c_2128,c_1899,c_1541,c_1521,c_1227,c_38,c_37,c_28])).


%------------------------------------------------------------------------------
