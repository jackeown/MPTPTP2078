%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT1217+1.003 : TPTP v7.4.0. Released v7.4.0.
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

% Result     : Theorem 33.54s
% Output     : CNFRefutation 33.54s
% Verified   : 
% Statistics : Number of formulae       :  283 (3107 expanded)
%              Number of clauses        :  196 ( 855 expanded)
%              Number of leaves         :   19 ( 890 expanded)
%              Depth                    :   26
%              Number of atoms          : 1259 (19394 expanded)
%              Number of equality atoms :  269 ( 661 expanded)
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

fof(f6,axiom,(
    ! [X0] :
      ( ( l1_lattices(X0)
        & ~ v2_struct_0(X0) )
     => m1_subset_1(k5_lattices(X0),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0] :
      ( m1_subset_1(k5_lattices(X0),u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f33,plain,(
    ! [X0] :
      ( m1_subset_1(k5_lattices(X0),u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f32])).

fof(f71,plain,(
    ! [X0] :
      ( m1_subset_1(k5_lattices(X0),u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f33])).

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

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l1_lattices(X0)
        & v6_lattices(X0)
        & ~ v2_struct_0(X0) )
     => m1_subset_1(k4_lattices(X0,X1,X2),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k4_lattices(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k4_lattices(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f30])).

fof(f70,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k4_lattices(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f31])).

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

cnf(c_1483,negated_conjecture,
    ( m1_subset_1(sK2,u1_struct_0(sK0)) ),
    inference(subtyping,[status(esa)],[c_27])).

cnf(c_1816,plain,
    ( m1_subset_1(sK2,u1_struct_0(sK0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1483])).

cnf(c_13,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | m1_subset_1(k7_lattices(X1,X0),u1_struct_0(X1))
    | ~ l3_lattices(X1)
    | v2_struct_0(X1) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_32,negated_conjecture,
    ( ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_1107,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | m1_subset_1(k7_lattices(X1,X0),u1_struct_0(X1))
    | ~ l3_lattices(X1)
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_13,c_32])).

cnf(c_1108,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK0))
    | m1_subset_1(k7_lattices(sK0,X0),u1_struct_0(sK0))
    | ~ l3_lattices(sK0) ),
    inference(unflattening,[status(thm)],[c_1107])).

cnf(c_29,negated_conjecture,
    ( l3_lattices(sK0) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_1112,plain,
    ( m1_subset_1(k7_lattices(sK0,X0),u1_struct_0(sK0))
    | ~ m1_subset_1(X0,u1_struct_0(sK0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1108,c_29])).

cnf(c_1113,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK0))
    | m1_subset_1(k7_lattices(sK0,X0),u1_struct_0(sK0)) ),
    inference(renaming,[status(thm)],[c_1112])).

cnf(c_1474,plain,
    ( ~ m1_subset_1(X0_52,u1_struct_0(sK0))
    | m1_subset_1(k7_lattices(sK0,X0_52),u1_struct_0(sK0)) ),
    inference(subtyping,[status(esa)],[c_1113])).

cnf(c_1825,plain,
    ( m1_subset_1(X0_52,u1_struct_0(sK0)) != iProver_top
    | m1_subset_1(k7_lattices(sK0,X0_52),u1_struct_0(sK0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1474])).

cnf(c_28,negated_conjecture,
    ( m1_subset_1(sK1,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_1482,negated_conjecture,
    ( m1_subset_1(sK1,u1_struct_0(sK0)) ),
    inference(subtyping,[status(esa)],[c_28])).

cnf(c_1817,plain,
    ( m1_subset_1(sK1,u1_struct_0(sK0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1482])).

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

cnf(c_527,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v6_lattices(X1)
    | ~ l3_lattices(X3)
    | v2_struct_0(X1)
    | X1 != X3
    | k2_lattices(X1,X2,X0) = k4_lattices(X1,X2,X0) ),
    inference(resolution_lifted,[status(thm)],[c_15,c_16])).

cnf(c_528,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v6_lattices(X1)
    | ~ l3_lattices(X1)
    | v2_struct_0(X1)
    | k2_lattices(X1,X2,X0) = k4_lattices(X1,X2,X0) ),
    inference(unflattening,[status(thm)],[c_527])).

cnf(c_752,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l3_lattices(X3)
    | ~ l3_lattices(X1)
    | v2_struct_0(X3)
    | v2_struct_0(X1)
    | ~ v10_lattices(X3)
    | X1 != X3
    | k2_lattices(X1,X2,X0) = k4_lattices(X1,X2,X0) ),
    inference(resolution_lifted,[status(thm)],[c_3,c_528])).

cnf(c_753,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l3_lattices(X1)
    | v2_struct_0(X1)
    | ~ v10_lattices(X1)
    | k2_lattices(X1,X2,X0) = k4_lattices(X1,X2,X0) ),
    inference(unflattening,[status(thm)],[c_752])).

cnf(c_31,negated_conjecture,
    ( v10_lattices(sK0) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_999,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l3_lattices(X1)
    | v2_struct_0(X1)
    | k2_lattices(X1,X2,X0) = k4_lattices(X1,X2,X0)
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_753,c_31])).

cnf(c_1000,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK0))
    | ~ m1_subset_1(X1,u1_struct_0(sK0))
    | ~ l3_lattices(sK0)
    | v2_struct_0(sK0)
    | k2_lattices(sK0,X1,X0) = k4_lattices(sK0,X1,X0) ),
    inference(unflattening,[status(thm)],[c_999])).

cnf(c_1004,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK0))
    | ~ m1_subset_1(X1,u1_struct_0(sK0))
    | k2_lattices(sK0,X1,X0) = k4_lattices(sK0,X1,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1000,c_32,c_29])).

cnf(c_1005,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK0))
    | ~ m1_subset_1(X1,u1_struct_0(sK0))
    | k2_lattices(sK0,X0,X1) = k4_lattices(sK0,X0,X1) ),
    inference(renaming,[status(thm)],[c_1004])).

cnf(c_1478,plain,
    ( ~ m1_subset_1(X0_52,u1_struct_0(sK0))
    | ~ m1_subset_1(X1_52,u1_struct_0(sK0))
    | k2_lattices(sK0,X0_52,X1_52) = k4_lattices(sK0,X0_52,X1_52) ),
    inference(subtyping,[status(esa)],[c_1005])).

cnf(c_1821,plain,
    ( k2_lattices(sK0,X0_52,X1_52) = k4_lattices(sK0,X0_52,X1_52)
    | m1_subset_1(X0_52,u1_struct_0(sK0)) != iProver_top
    | m1_subset_1(X1_52,u1_struct_0(sK0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1478])).

cnf(c_2460,plain,
    ( k2_lattices(sK0,sK1,X0_52) = k4_lattices(sK0,sK1,X0_52)
    | m1_subset_1(X0_52,u1_struct_0(sK0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1817,c_1821])).

cnf(c_2627,plain,
    ( k2_lattices(sK0,sK1,k7_lattices(sK0,X0_52)) = k4_lattices(sK0,sK1,k7_lattices(sK0,X0_52))
    | m1_subset_1(X0_52,u1_struct_0(sK0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1825,c_2460])).

cnf(c_5773,plain,
    ( k2_lattices(sK0,sK1,k7_lattices(sK0,sK2)) = k4_lattices(sK0,sK1,k7_lattices(sK0,sK2)) ),
    inference(superposition,[status(thm)],[c_1816,c_2627])).

cnf(c_2459,plain,
    ( k2_lattices(sK0,sK2,X0_52) = k4_lattices(sK0,sK2,X0_52)
    | m1_subset_1(X0_52,u1_struct_0(sK0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1816,c_1821])).

cnf(c_2477,plain,
    ( k2_lattices(sK0,sK2,k7_lattices(sK0,X0_52)) = k4_lattices(sK0,sK2,k7_lattices(sK0,X0_52))
    | m1_subset_1(X0_52,u1_struct_0(sK0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1825,c_2459])).

cnf(c_4683,plain,
    ( k2_lattices(sK0,sK2,k7_lattices(sK0,sK2)) = k4_lattices(sK0,sK2,k7_lattices(sK0,sK2)) ),
    inference(superposition,[status(thm)],[c_1816,c_2477])).

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

cnf(c_945,plain,
    ( ~ r1_lattices(X0,X1,X2)
    | r1_lattices(X0,k2_lattices(X0,X1,X3),k2_lattices(X0,X2,X3))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | sK0 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_474,c_31])).

cnf(c_946,plain,
    ( ~ r1_lattices(sK0,X0,X1)
    | r1_lattices(sK0,k2_lattices(sK0,X0,X2),k2_lattices(sK0,X1,X2))
    | ~ m1_subset_1(X0,u1_struct_0(sK0))
    | ~ m1_subset_1(X1,u1_struct_0(sK0))
    | ~ m1_subset_1(X2,u1_struct_0(sK0))
    | ~ l3_lattices(sK0)
    | v2_struct_0(sK0) ),
    inference(unflattening,[status(thm)],[c_945])).

cnf(c_950,plain,
    ( ~ r1_lattices(sK0,X0,X1)
    | r1_lattices(sK0,k2_lattices(sK0,X0,X2),k2_lattices(sK0,X1,X2))
    | ~ m1_subset_1(X0,u1_struct_0(sK0))
    | ~ m1_subset_1(X1,u1_struct_0(sK0))
    | ~ m1_subset_1(X2,u1_struct_0(sK0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_946,c_32,c_29])).

cnf(c_951,plain,
    ( ~ r1_lattices(sK0,X0,X1)
    | r1_lattices(sK0,k2_lattices(sK0,X0,X2),k2_lattices(sK0,X1,X2))
    | ~ m1_subset_1(X1,u1_struct_0(sK0))
    | ~ m1_subset_1(X0,u1_struct_0(sK0))
    | ~ m1_subset_1(X2,u1_struct_0(sK0)) ),
    inference(renaming,[status(thm)],[c_950])).

cnf(c_1480,plain,
    ( ~ r1_lattices(sK0,X0_52,X1_52)
    | r1_lattices(sK0,k2_lattices(sK0,X0_52,X2_52),k2_lattices(sK0,X1_52,X2_52))
    | ~ m1_subset_1(X1_52,u1_struct_0(sK0))
    | ~ m1_subset_1(X0_52,u1_struct_0(sK0))
    | ~ m1_subset_1(X2_52,u1_struct_0(sK0)) ),
    inference(subtyping,[status(esa)],[c_951])).

cnf(c_1819,plain,
    ( r1_lattices(sK0,X0_52,X1_52) != iProver_top
    | r1_lattices(sK0,k2_lattices(sK0,X0_52,X2_52),k2_lattices(sK0,X1_52,X2_52)) = iProver_top
    | m1_subset_1(X0_52,u1_struct_0(sK0)) != iProver_top
    | m1_subset_1(X1_52,u1_struct_0(sK0)) != iProver_top
    | m1_subset_1(X2_52,u1_struct_0(sK0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1480])).

cnf(c_4695,plain,
    ( r1_lattices(sK0,X0_52,sK2) != iProver_top
    | r1_lattices(sK0,k2_lattices(sK0,X0_52,k7_lattices(sK0,sK2)),k4_lattices(sK0,sK2,k7_lattices(sK0,sK2))) = iProver_top
    | m1_subset_1(X0_52,u1_struct_0(sK0)) != iProver_top
    | m1_subset_1(k7_lattices(sK0,sK2),u1_struct_0(sK0)) != iProver_top
    | m1_subset_1(sK2,u1_struct_0(sK0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_4683,c_1819])).

cnf(c_38,plain,
    ( m1_subset_1(sK2,u1_struct_0(sK0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_1879,plain,
    ( m1_subset_1(k7_lattices(sK0,sK2),u1_struct_0(sK0))
    | ~ m1_subset_1(sK2,u1_struct_0(sK0)) ),
    inference(instantiation,[status(thm)],[c_1474])).

cnf(c_1880,plain,
    ( m1_subset_1(k7_lattices(sK0,sK2),u1_struct_0(sK0)) = iProver_top
    | m1_subset_1(sK2,u1_struct_0(sK0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1879])).

cnf(c_114954,plain,
    ( r1_lattices(sK0,X0_52,sK2) != iProver_top
    | r1_lattices(sK0,k2_lattices(sK0,X0_52,k7_lattices(sK0,sK2)),k4_lattices(sK0,sK2,k7_lattices(sK0,sK2))) = iProver_top
    | m1_subset_1(X0_52,u1_struct_0(sK0)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4695,c_38,c_1880])).

cnf(c_10,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l1_lattices(X1)
    | ~ v6_lattices(X1)
    | v2_struct_0(X1)
    | k4_lattices(X1,X0,X2) = k4_lattices(X1,X2,X0) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_575,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v6_lattices(X1)
    | ~ l3_lattices(X3)
    | v2_struct_0(X1)
    | X1 != X3
    | k4_lattices(X1,X0,X2) = k4_lattices(X1,X2,X0) ),
    inference(resolution_lifted,[status(thm)],[c_15,c_10])).

cnf(c_576,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v6_lattices(X1)
    | ~ l3_lattices(X1)
    | v2_struct_0(X1)
    | k4_lattices(X1,X0,X2) = k4_lattices(X1,X2,X0) ),
    inference(unflattening,[status(thm)],[c_575])).

cnf(c_704,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l3_lattices(X3)
    | ~ l3_lattices(X1)
    | v2_struct_0(X3)
    | v2_struct_0(X1)
    | ~ v10_lattices(X3)
    | X1 != X3
    | k4_lattices(X1,X0,X2) = k4_lattices(X1,X2,X0) ),
    inference(resolution_lifted,[status(thm)],[c_3,c_576])).

cnf(c_705,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l3_lattices(X1)
    | v2_struct_0(X1)
    | ~ v10_lattices(X1)
    | k4_lattices(X1,X0,X2) = k4_lattices(X1,X2,X0) ),
    inference(unflattening,[status(thm)],[c_704])).

cnf(c_1041,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l3_lattices(X1)
    | v2_struct_0(X1)
    | k4_lattices(X1,X2,X0) = k4_lattices(X1,X0,X2)
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_705,c_31])).

cnf(c_1042,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK0))
    | ~ m1_subset_1(X1,u1_struct_0(sK0))
    | ~ l3_lattices(sK0)
    | v2_struct_0(sK0)
    | k4_lattices(sK0,X1,X0) = k4_lattices(sK0,X0,X1) ),
    inference(unflattening,[status(thm)],[c_1041])).

cnf(c_1046,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK0))
    | ~ m1_subset_1(X1,u1_struct_0(sK0))
    | k4_lattices(sK0,X1,X0) = k4_lattices(sK0,X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1042,c_32,c_29])).

cnf(c_1047,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK0))
    | ~ m1_subset_1(X1,u1_struct_0(sK0))
    | k4_lattices(sK0,X0,X1) = k4_lattices(sK0,X1,X0) ),
    inference(renaming,[status(thm)],[c_1046])).

cnf(c_1476,plain,
    ( ~ m1_subset_1(X0_52,u1_struct_0(sK0))
    | ~ m1_subset_1(X1_52,u1_struct_0(sK0))
    | k4_lattices(sK0,X0_52,X1_52) = k4_lattices(sK0,X1_52,X0_52) ),
    inference(subtyping,[status(esa)],[c_1047])).

cnf(c_1823,plain,
    ( k4_lattices(sK0,X0_52,X1_52) = k4_lattices(sK0,X1_52,X0_52)
    | m1_subset_1(X0_52,u1_struct_0(sK0)) != iProver_top
    | m1_subset_1(X1_52,u1_struct_0(sK0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1476])).

cnf(c_3045,plain,
    ( k4_lattices(sK0,X0_52,sK2) = k4_lattices(sK0,sK2,X0_52)
    | m1_subset_1(X0_52,u1_struct_0(sK0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1816,c_1823])).

cnf(c_3203,plain,
    ( k4_lattices(sK0,k7_lattices(sK0,X0_52),sK2) = k4_lattices(sK0,sK2,k7_lattices(sK0,X0_52))
    | m1_subset_1(X0_52,u1_struct_0(sK0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1825,c_3045])).

cnf(c_6908,plain,
    ( k4_lattices(sK0,sK2,k7_lattices(sK0,sK2)) = k4_lattices(sK0,k7_lattices(sK0,sK2),sK2) ),
    inference(superposition,[status(thm)],[c_1816,c_3203])).

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

cnf(c_863,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ l3_lattices(X1)
    | v2_struct_0(X1)
    | ~ v10_lattices(X1)
    | k4_lattices(X1,k7_lattices(X1,X0),X0) = k5_lattices(X1)
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_22,c_30])).

cnf(c_864,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK0))
    | ~ l3_lattices(sK0)
    | v2_struct_0(sK0)
    | ~ v10_lattices(sK0)
    | k4_lattices(sK0,k7_lattices(sK0,X0),X0) = k5_lattices(sK0) ),
    inference(unflattening,[status(thm)],[c_863])).

cnf(c_868,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK0))
    | k4_lattices(sK0,k7_lattices(sK0,X0),X0) = k5_lattices(sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_864,c_32,c_31,c_29])).

cnf(c_1481,plain,
    ( ~ m1_subset_1(X0_52,u1_struct_0(sK0))
    | k4_lattices(sK0,k7_lattices(sK0,X0_52),X0_52) = k5_lattices(sK0) ),
    inference(subtyping,[status(esa)],[c_868])).

cnf(c_1818,plain,
    ( k4_lattices(sK0,k7_lattices(sK0,X0_52),X0_52) = k5_lattices(sK0)
    | m1_subset_1(X0_52,u1_struct_0(sK0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1481])).

cnf(c_2044,plain,
    ( k4_lattices(sK0,k7_lattices(sK0,sK2),sK2) = k5_lattices(sK0) ),
    inference(superposition,[status(thm)],[c_1816,c_1818])).

cnf(c_6913,plain,
    ( k4_lattices(sK0,sK2,k7_lattices(sK0,sK2)) = k5_lattices(sK0) ),
    inference(light_normalisation,[status(thm)],[c_6908,c_2044])).

cnf(c_114960,plain,
    ( r1_lattices(sK0,X0_52,sK2) != iProver_top
    | r1_lattices(sK0,k2_lattices(sK0,X0_52,k7_lattices(sK0,sK2)),k5_lattices(sK0)) = iProver_top
    | m1_subset_1(X0_52,u1_struct_0(sK0)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_114954,c_6913])).

cnf(c_114965,plain,
    ( r1_lattices(sK0,k4_lattices(sK0,sK1,k7_lattices(sK0,sK2)),k5_lattices(sK0)) = iProver_top
    | r1_lattices(sK0,sK1,sK2) != iProver_top
    | m1_subset_1(sK1,u1_struct_0(sK0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_5773,c_114960])).

cnf(c_4694,plain,
    ( r1_lattices(sK0,k4_lattices(sK0,sK2,k7_lattices(sK0,sK2)),k2_lattices(sK0,X0_52,k7_lattices(sK0,sK2))) = iProver_top
    | r1_lattices(sK0,sK2,X0_52) != iProver_top
    | m1_subset_1(X0_52,u1_struct_0(sK0)) != iProver_top
    | m1_subset_1(k7_lattices(sK0,sK2),u1_struct_0(sK0)) != iProver_top
    | m1_subset_1(sK2,u1_struct_0(sK0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_4683,c_1819])).

cnf(c_114386,plain,
    ( r1_lattices(sK0,k4_lattices(sK0,sK2,k7_lattices(sK0,sK2)),k2_lattices(sK0,X0_52,k7_lattices(sK0,sK2))) = iProver_top
    | r1_lattices(sK0,sK2,X0_52) != iProver_top
    | m1_subset_1(X0_52,u1_struct_0(sK0)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4694,c_38,c_1880])).

cnf(c_114390,plain,
    ( r1_lattices(sK0,k5_lattices(sK0),k2_lattices(sK0,X0_52,k7_lattices(sK0,sK2))) = iProver_top
    | r1_lattices(sK0,sK2,X0_52) != iProver_top
    | m1_subset_1(X0_52,u1_struct_0(sK0)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_114386,c_6913])).

cnf(c_33,plain,
    ( v2_struct_0(sK0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_36,plain,
    ( l3_lattices(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_68,plain,
    ( l1_lattices(X0) = iProver_top
    | l3_lattices(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_70,plain,
    ( l1_lattices(sK0) = iProver_top
    | l3_lattices(sK0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_68])).

cnf(c_12,plain,
    ( m1_subset_1(k5_lattices(X0),u1_struct_0(X0))
    | ~ l1_lattices(X0)
    | v2_struct_0(X0) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_77,plain,
    ( m1_subset_1(k5_lattices(X0),u1_struct_0(X0)) = iProver_top
    | l1_lattices(X0) != iProver_top
    | v2_struct_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_79,plain,
    ( m1_subset_1(k5_lattices(sK0),u1_struct_0(sK0)) = iProver_top
    | l1_lattices(sK0) != iProver_top
    | v2_struct_0(sK0) = iProver_top ),
    inference(instantiation,[status(thm)],[c_77])).

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

cnf(c_797,plain,
    ( r3_lattices(X0,k5_lattices(X0),X1)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | ~ v10_lattices(X0)
    | sK0 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_363,c_30])).

cnf(c_798,plain,
    ( r3_lattices(sK0,k5_lattices(sK0),X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK0))
    | ~ l3_lattices(sK0)
    | v2_struct_0(sK0)
    | ~ v10_lattices(sK0) ),
    inference(unflattening,[status(thm)],[c_797])).

cnf(c_802,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK0))
    | r3_lattices(sK0,k5_lattices(sK0),X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_798,c_32,c_31,c_29])).

cnf(c_803,plain,
    ( r3_lattices(sK0,k5_lattices(sK0),X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK0)) ),
    inference(renaming,[status(thm)],[c_802])).

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

cnf(c_624,plain,
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

cnf(c_628,plain,
    ( r1_lattices(X0,X1,X2)
    | ~ r3_lattices(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | ~ v10_lattices(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_624,c_3,c_1])).

cnf(c_921,plain,
    ( r1_lattices(X0,X1,X2)
    | ~ r3_lattices(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | sK0 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_628,c_31])).

cnf(c_922,plain,
    ( r1_lattices(sK0,X0,X1)
    | ~ r3_lattices(sK0,X0,X1)
    | ~ m1_subset_1(X0,u1_struct_0(sK0))
    | ~ m1_subset_1(X1,u1_struct_0(sK0))
    | ~ l3_lattices(sK0)
    | v2_struct_0(sK0) ),
    inference(unflattening,[status(thm)],[c_921])).

cnf(c_926,plain,
    ( r1_lattices(sK0,X0,X1)
    | ~ r3_lattices(sK0,X0,X1)
    | ~ m1_subset_1(X0,u1_struct_0(sK0))
    | ~ m1_subset_1(X1,u1_struct_0(sK0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_922,c_32,c_29])).

cnf(c_927,plain,
    ( r1_lattices(sK0,X0,X1)
    | ~ r3_lattices(sK0,X0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK0))
    | ~ m1_subset_1(X0,u1_struct_0(sK0)) ),
    inference(renaming,[status(thm)],[c_926])).

cnf(c_1233,plain,
    ( r1_lattices(sK0,X0,X1)
    | ~ m1_subset_1(X0,u1_struct_0(sK0))
    | ~ m1_subset_1(X2,u1_struct_0(sK0))
    | ~ m1_subset_1(X1,u1_struct_0(sK0))
    | X1 != X2
    | k5_lattices(sK0) != X0
    | sK0 != sK0 ),
    inference(resolution_lifted,[status(thm)],[c_803,c_927])).

cnf(c_1234,plain,
    ( r1_lattices(sK0,k5_lattices(sK0),X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK0))
    | ~ m1_subset_1(k5_lattices(sK0),u1_struct_0(sK0)) ),
    inference(unflattening,[status(thm)],[c_1233])).

cnf(c_69,plain,
    ( l1_lattices(sK0)
    | ~ l3_lattices(sK0) ),
    inference(instantiation,[status(thm)],[c_15])).

cnf(c_78,plain,
    ( m1_subset_1(k5_lattices(sK0),u1_struct_0(sK0))
    | ~ l1_lattices(sK0)
    | v2_struct_0(sK0) ),
    inference(instantiation,[status(thm)],[c_12])).

cnf(c_1238,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK0))
    | r1_lattices(sK0,k5_lattices(sK0),X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1234,c_32,c_29,c_69,c_78])).

cnf(c_1239,plain,
    ( r1_lattices(sK0,k5_lattices(sK0),X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK0)) ),
    inference(renaming,[status(thm)],[c_1238])).

cnf(c_1467,plain,
    ( r1_lattices(sK0,k5_lattices(sK0),X0_52)
    | ~ m1_subset_1(X0_52,u1_struct_0(sK0)) ),
    inference(subtyping,[status(esa)],[c_1239])).

cnf(c_1531,plain,
    ( r1_lattices(sK0,k5_lattices(sK0),X0_52) = iProver_top
    | m1_subset_1(X0_52,u1_struct_0(sK0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1467])).

cnf(c_513,plain,
    ( m1_subset_1(k5_lattices(X0),u1_struct_0(X0))
    | ~ l3_lattices(X0)
    | v2_struct_0(X0) ),
    inference(resolution,[status(thm)],[c_15,c_12])).

cnf(c_1096,plain,
    ( m1_subset_1(k5_lattices(X0),u1_struct_0(X0))
    | ~ l3_lattices(X0)
    | sK0 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_513,c_32])).

cnf(c_1097,plain,
    ( m1_subset_1(k5_lattices(sK0),u1_struct_0(sK0))
    | ~ l3_lattices(sK0) ),
    inference(unflattening,[status(thm)],[c_1096])).

cnf(c_1099,plain,
    ( m1_subset_1(k5_lattices(sK0),u1_struct_0(sK0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1097,c_32,c_29,c_69,c_78])).

cnf(c_1475,plain,
    ( m1_subset_1(k5_lattices(sK0),u1_struct_0(sK0)) ),
    inference(subtyping,[status(esa)],[c_1099])).

cnf(c_1824,plain,
    ( m1_subset_1(k5_lattices(sK0),u1_struct_0(sK0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1475])).

cnf(c_2461,plain,
    ( k2_lattices(sK0,k5_lattices(sK0),X0_52) = k4_lattices(sK0,k5_lattices(sK0),X0_52)
    | m1_subset_1(X0_52,u1_struct_0(sK0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1824,c_1821])).

cnf(c_4468,plain,
    ( k2_lattices(sK0,k5_lattices(sK0),k7_lattices(sK0,X0_52)) = k4_lattices(sK0,k5_lattices(sK0),k7_lattices(sK0,X0_52))
    | m1_subset_1(X0_52,u1_struct_0(sK0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1825,c_2461])).

cnf(c_11120,plain,
    ( k2_lattices(sK0,k5_lattices(sK0),k7_lattices(sK0,sK2)) = k4_lattices(sK0,k5_lattices(sK0),k7_lattices(sK0,sK2)) ),
    inference(superposition,[status(thm)],[c_1816,c_4468])).

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

cnf(c_839,plain,
    ( ~ r3_lattices(X0,X1,k7_lattices(X0,X2))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | ~ v10_lattices(X0)
    | k4_lattices(X0,X1,X2) = k5_lattices(X0)
    | sK0 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_23,c_30])).

cnf(c_840,plain,
    ( ~ r3_lattices(sK0,X0,k7_lattices(sK0,X1))
    | ~ m1_subset_1(X0,u1_struct_0(sK0))
    | ~ m1_subset_1(X1,u1_struct_0(sK0))
    | ~ l3_lattices(sK0)
    | v2_struct_0(sK0)
    | ~ v10_lattices(sK0)
    | k4_lattices(sK0,X0,X1) = k5_lattices(sK0) ),
    inference(unflattening,[status(thm)],[c_839])).

cnf(c_844,plain,
    ( ~ m1_subset_1(X1,u1_struct_0(sK0))
    | ~ m1_subset_1(X0,u1_struct_0(sK0))
    | ~ r3_lattices(sK0,X0,k7_lattices(sK0,X1))
    | k4_lattices(sK0,X0,X1) = k5_lattices(sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_840,c_32,c_31,c_29])).

cnf(c_845,plain,
    ( ~ r3_lattices(sK0,X0,k7_lattices(sK0,X1))
    | ~ m1_subset_1(X1,u1_struct_0(sK0))
    | ~ m1_subset_1(X0,u1_struct_0(sK0))
    | k4_lattices(sK0,X0,X1) = k5_lattices(sK0) ),
    inference(renaming,[status(thm)],[c_844])).

cnf(c_1215,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK0))
    | ~ m1_subset_1(X1,u1_struct_0(sK0))
    | ~ m1_subset_1(X2,u1_struct_0(sK0))
    | k4_lattices(sK0,X0,X2) = k5_lattices(sK0)
    | k7_lattices(sK0,X2) != X1
    | k5_lattices(sK0) != X0
    | sK0 != sK0 ),
    inference(resolution_lifted,[status(thm)],[c_803,c_845])).

cnf(c_1216,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK0))
    | ~ m1_subset_1(k7_lattices(sK0,X0),u1_struct_0(sK0))
    | ~ m1_subset_1(k5_lattices(sK0),u1_struct_0(sK0))
    | k4_lattices(sK0,k5_lattices(sK0),X0) = k5_lattices(sK0) ),
    inference(unflattening,[status(thm)],[c_1215])).

cnf(c_1220,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK0))
    | k4_lattices(sK0,k5_lattices(sK0),X0) = k5_lattices(sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1216,c_32,c_29,c_69,c_78,c_1108])).

cnf(c_1468,plain,
    ( ~ m1_subset_1(X0_52,u1_struct_0(sK0))
    | k4_lattices(sK0,k5_lattices(sK0),X0_52) = k5_lattices(sK0) ),
    inference(subtyping,[status(esa)],[c_1220])).

cnf(c_1831,plain,
    ( k4_lattices(sK0,k5_lattices(sK0),X0_52) = k5_lattices(sK0)
    | m1_subset_1(X0_52,u1_struct_0(sK0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1468])).

cnf(c_3516,plain,
    ( k4_lattices(sK0,k5_lattices(sK0),k7_lattices(sK0,X0_52)) = k5_lattices(sK0)
    | m1_subset_1(X0_52,u1_struct_0(sK0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1825,c_1831])).

cnf(c_4244,plain,
    ( k4_lattices(sK0,k5_lattices(sK0),k7_lattices(sK0,sK2)) = k5_lattices(sK0) ),
    inference(superposition,[status(thm)],[c_1816,c_3516])).

cnf(c_11127,plain,
    ( k2_lattices(sK0,k5_lattices(sK0),k7_lattices(sK0,sK2)) = k5_lattices(sK0) ),
    inference(light_normalisation,[status(thm)],[c_11120,c_4244])).

cnf(c_11253,plain,
    ( r1_lattices(sK0,k5_lattices(sK0),X0_52) != iProver_top
    | r1_lattices(sK0,k5_lattices(sK0),k2_lattices(sK0,X0_52,k7_lattices(sK0,sK2))) = iProver_top
    | m1_subset_1(X0_52,u1_struct_0(sK0)) != iProver_top
    | m1_subset_1(k7_lattices(sK0,sK2),u1_struct_0(sK0)) != iProver_top
    | m1_subset_1(k5_lattices(sK0),u1_struct_0(sK0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_11127,c_1819])).

cnf(c_114392,plain,
    ( r1_lattices(sK0,k5_lattices(sK0),k2_lattices(sK0,X0_52,k7_lattices(sK0,sK2))) = iProver_top
    | m1_subset_1(X0_52,u1_struct_0(sK0)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_114390,c_33,c_36,c_38,c_70,c_79,c_1531,c_1880,c_11253])).

cnf(c_114399,plain,
    ( r1_lattices(sK0,k5_lattices(sK0),k4_lattices(sK0,sK1,k7_lattices(sK0,sK2))) = iProver_top
    | m1_subset_1(sK1,u1_struct_0(sK0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_5773,c_114392])).

cnf(c_3046,plain,
    ( k4_lattices(sK0,X0_52,sK1) = k4_lattices(sK0,sK1,X0_52)
    | m1_subset_1(X0_52,u1_struct_0(sK0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1817,c_1823])).

cnf(c_3307,plain,
    ( k4_lattices(sK0,k7_lattices(sK0,X0_52),sK1) = k4_lattices(sK0,sK1,k7_lattices(sK0,X0_52))
    | m1_subset_1(X0_52,u1_struct_0(sK0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1825,c_3046])).

cnf(c_7850,plain,
    ( k4_lattices(sK0,sK1,k7_lattices(sK0,sK2)) = k4_lattices(sK0,k7_lattices(sK0,sK2),sK1) ),
    inference(superposition,[status(thm)],[c_1816,c_3307])).

cnf(c_2462,plain,
    ( k2_lattices(sK0,k7_lattices(sK0,X0_52),X1_52) = k4_lattices(sK0,k7_lattices(sK0,X0_52),X1_52)
    | m1_subset_1(X0_52,u1_struct_0(sK0)) != iProver_top
    | m1_subset_1(X1_52,u1_struct_0(sK0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1825,c_1821])).

cnf(c_7244,plain,
    ( k2_lattices(sK0,k7_lattices(sK0,sK2),X0_52) = k4_lattices(sK0,k7_lattices(sK0,sK2),X0_52)
    | m1_subset_1(X0_52,u1_struct_0(sK0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1816,c_2462])).

cnf(c_7309,plain,
    ( k2_lattices(sK0,k7_lattices(sK0,sK2),sK1) = k4_lattices(sK0,k7_lattices(sK0,sK2),sK1) ),
    inference(superposition,[status(thm)],[c_1817,c_7244])).

cnf(c_7862,plain,
    ( k2_lattices(sK0,k7_lattices(sK0,sK2),sK1) = k4_lattices(sK0,sK1,k7_lattices(sK0,sK2)) ),
    inference(demodulation,[status(thm)],[c_7850,c_7309])).

cnf(c_4466,plain,
    ( k2_lattices(sK0,k5_lattices(sK0),sK1) = k4_lattices(sK0,k5_lattices(sK0),sK1) ),
    inference(superposition,[status(thm)],[c_1817,c_2461])).

cnf(c_3514,plain,
    ( k4_lattices(sK0,k5_lattices(sK0),sK1) = k5_lattices(sK0) ),
    inference(superposition,[status(thm)],[c_1817,c_1831])).

cnf(c_4471,plain,
    ( k2_lattices(sK0,k5_lattices(sK0),sK1) = k5_lattices(sK0) ),
    inference(light_normalisation,[status(thm)],[c_4466,c_3514])).

cnf(c_4575,plain,
    ( r1_lattices(sK0,k5_lattices(sK0),X0_52) != iProver_top
    | r1_lattices(sK0,k5_lattices(sK0),k2_lattices(sK0,X0_52,sK1)) = iProver_top
    | m1_subset_1(X0_52,u1_struct_0(sK0)) != iProver_top
    | m1_subset_1(k5_lattices(sK0),u1_struct_0(sK0)) != iProver_top
    | m1_subset_1(sK1,u1_struct_0(sK0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_4471,c_1819])).

cnf(c_37,plain,
    ( m1_subset_1(sK1,u1_struct_0(sK0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_98017,plain,
    ( r1_lattices(sK0,k5_lattices(sK0),k2_lattices(sK0,X0_52,sK1)) = iProver_top
    | m1_subset_1(X0_52,u1_struct_0(sK0)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4575,c_33,c_36,c_37,c_70,c_79,c_1531])).

cnf(c_98028,plain,
    ( r1_lattices(sK0,k5_lattices(sK0),k4_lattices(sK0,sK1,k7_lattices(sK0,sK2))) = iProver_top
    | m1_subset_1(k7_lattices(sK0,sK2),u1_struct_0(sK0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_7862,c_98017])).

cnf(c_114537,plain,
    ( r1_lattices(sK0,k5_lattices(sK0),k4_lattices(sK0,sK1,k7_lattices(sK0,sK2))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_114399,c_38,c_1880,c_98028])).

cnf(c_11,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | m1_subset_1(k4_lattices(X1,X2,X0),u1_struct_0(X1))
    | ~ l1_lattices(X1)
    | ~ v6_lattices(X1)
    | v2_struct_0(X1) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_551,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | m1_subset_1(k4_lattices(X1,X2,X0),u1_struct_0(X1))
    | ~ v6_lattices(X1)
    | ~ l3_lattices(X3)
    | v2_struct_0(X1)
    | X1 != X3 ),
    inference(resolution_lifted,[status(thm)],[c_15,c_11])).

cnf(c_552,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | m1_subset_1(k4_lattices(X1,X2,X0),u1_struct_0(X1))
    | ~ v6_lattices(X1)
    | ~ l3_lattices(X1)
    | v2_struct_0(X1) ),
    inference(unflattening,[status(thm)],[c_551])).

cnf(c_728,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | m1_subset_1(k4_lattices(X1,X2,X0),u1_struct_0(X1))
    | ~ l3_lattices(X3)
    | ~ l3_lattices(X1)
    | v2_struct_0(X3)
    | v2_struct_0(X1)
    | ~ v10_lattices(X3)
    | X1 != X3 ),
    inference(resolution_lifted,[status(thm)],[c_3,c_552])).

cnf(c_729,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | m1_subset_1(k4_lattices(X1,X2,X0),u1_struct_0(X1))
    | ~ l3_lattices(X1)
    | v2_struct_0(X1)
    | ~ v10_lattices(X1) ),
    inference(unflattening,[status(thm)],[c_728])).

cnf(c_1020,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | m1_subset_1(k4_lattices(X1,X2,X0),u1_struct_0(X1))
    | ~ l3_lattices(X1)
    | v2_struct_0(X1)
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_729,c_31])).

cnf(c_1021,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK0))
    | ~ m1_subset_1(X1,u1_struct_0(sK0))
    | m1_subset_1(k4_lattices(sK0,X1,X0),u1_struct_0(sK0))
    | ~ l3_lattices(sK0)
    | v2_struct_0(sK0) ),
    inference(unflattening,[status(thm)],[c_1020])).

cnf(c_1025,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK0))
    | ~ m1_subset_1(X1,u1_struct_0(sK0))
    | m1_subset_1(k4_lattices(sK0,X1,X0),u1_struct_0(sK0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1021,c_32,c_29])).

cnf(c_1026,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK0))
    | ~ m1_subset_1(X1,u1_struct_0(sK0))
    | m1_subset_1(k4_lattices(sK0,X0,X1),u1_struct_0(sK0)) ),
    inference(renaming,[status(thm)],[c_1025])).

cnf(c_1477,plain,
    ( ~ m1_subset_1(X0_52,u1_struct_0(sK0))
    | ~ m1_subset_1(X1_52,u1_struct_0(sK0))
    | m1_subset_1(k4_lattices(sK0,X0_52,X1_52),u1_struct_0(sK0)) ),
    inference(subtyping,[status(esa)],[c_1026])).

cnf(c_1822,plain,
    ( m1_subset_1(X0_52,u1_struct_0(sK0)) != iProver_top
    | m1_subset_1(X1_52,u1_struct_0(sK0)) != iProver_top
    | m1_subset_1(k4_lattices(sK0,X0_52,X1_52),u1_struct_0(sK0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1477])).

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

cnf(c_972,plain,
    ( ~ r1_lattices(X0,X1,X2)
    | ~ r1_lattices(X0,X2,X1)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | X2 = X1
    | sK0 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_431,c_31])).

cnf(c_973,plain,
    ( ~ r1_lattices(sK0,X0,X1)
    | ~ r1_lattices(sK0,X1,X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK0))
    | ~ m1_subset_1(X1,u1_struct_0(sK0))
    | ~ l3_lattices(sK0)
    | v2_struct_0(sK0)
    | X1 = X0 ),
    inference(unflattening,[status(thm)],[c_972])).

cnf(c_977,plain,
    ( ~ r1_lattices(sK0,X0,X1)
    | ~ r1_lattices(sK0,X1,X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK0))
    | ~ m1_subset_1(X1,u1_struct_0(sK0))
    | X1 = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_973,c_32,c_29])).

cnf(c_978,plain,
    ( ~ r1_lattices(sK0,X0,X1)
    | ~ r1_lattices(sK0,X1,X0)
    | ~ m1_subset_1(X1,u1_struct_0(sK0))
    | ~ m1_subset_1(X0,u1_struct_0(sK0))
    | X1 = X0 ),
    inference(renaming,[status(thm)],[c_977])).

cnf(c_1479,plain,
    ( ~ r1_lattices(sK0,X0_52,X1_52)
    | ~ r1_lattices(sK0,X1_52,X0_52)
    | ~ m1_subset_1(X1_52,u1_struct_0(sK0))
    | ~ m1_subset_1(X0_52,u1_struct_0(sK0))
    | X1_52 = X0_52 ),
    inference(subtyping,[status(esa)],[c_978])).

cnf(c_1820,plain,
    ( X0_52 = X1_52
    | r1_lattices(sK0,X1_52,X0_52) != iProver_top
    | r1_lattices(sK0,X0_52,X1_52) != iProver_top
    | m1_subset_1(X1_52,u1_struct_0(sK0)) != iProver_top
    | m1_subset_1(X0_52,u1_struct_0(sK0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1479])).

cnf(c_3020,plain,
    ( k4_lattices(sK0,X0_52,X1_52) = X2_52
    | r1_lattices(sK0,X2_52,k4_lattices(sK0,X0_52,X1_52)) != iProver_top
    | r1_lattices(sK0,k4_lattices(sK0,X0_52,X1_52),X2_52) != iProver_top
    | m1_subset_1(X0_52,u1_struct_0(sK0)) != iProver_top
    | m1_subset_1(X1_52,u1_struct_0(sK0)) != iProver_top
    | m1_subset_1(X2_52,u1_struct_0(sK0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1822,c_1820])).

cnf(c_114541,plain,
    ( k4_lattices(sK0,sK1,k7_lattices(sK0,sK2)) = k5_lattices(sK0)
    | r1_lattices(sK0,k4_lattices(sK0,sK1,k7_lattices(sK0,sK2)),k5_lattices(sK0)) != iProver_top
    | m1_subset_1(k7_lattices(sK0,sK2),u1_struct_0(sK0)) != iProver_top
    | m1_subset_1(k5_lattices(sK0),u1_struct_0(sK0)) != iProver_top
    | m1_subset_1(sK1,u1_struct_0(sK0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_114537,c_3020])).

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

cnf(c_815,plain,
    ( r3_lattices(X0,X1,k7_lattices(X0,X2))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | ~ v10_lattices(X0)
    | k4_lattices(X0,X1,X2) != k5_lattices(X0)
    | sK0 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_24,c_30])).

cnf(c_816,plain,
    ( r3_lattices(sK0,X0,k7_lattices(sK0,X1))
    | ~ m1_subset_1(X0,u1_struct_0(sK0))
    | ~ m1_subset_1(X1,u1_struct_0(sK0))
    | ~ l3_lattices(sK0)
    | v2_struct_0(sK0)
    | ~ v10_lattices(sK0)
    | k4_lattices(sK0,X0,X1) != k5_lattices(sK0) ),
    inference(unflattening,[status(thm)],[c_815])).

cnf(c_820,plain,
    ( ~ m1_subset_1(X1,u1_struct_0(sK0))
    | ~ m1_subset_1(X0,u1_struct_0(sK0))
    | r3_lattices(sK0,X0,k7_lattices(sK0,X1))
    | k4_lattices(sK0,X0,X1) != k5_lattices(sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_816,c_32,c_31,c_29])).

cnf(c_821,plain,
    ( r3_lattices(sK0,X0,k7_lattices(sK0,X1))
    | ~ m1_subset_1(X1,u1_struct_0(sK0))
    | ~ m1_subset_1(X0,u1_struct_0(sK0))
    | k4_lattices(sK0,X0,X1) != k5_lattices(sK0) ),
    inference(renaming,[status(thm)],[c_820])).

cnf(c_1152,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK0))
    | ~ m1_subset_1(X1,u1_struct_0(sK0))
    | k4_lattices(sK0,X1,X0) != k5_lattices(sK0)
    | k7_lattices(sK0,X0) != k7_lattices(sK0,sK1)
    | k7_lattices(sK0,sK2) != X1
    | sK0 != sK0 ),
    inference(resolution_lifted,[status(thm)],[c_25,c_821])).

cnf(c_1153,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK0))
    | ~ m1_subset_1(k7_lattices(sK0,sK2),u1_struct_0(sK0))
    | k4_lattices(sK0,k7_lattices(sK0,sK2),X0) != k5_lattices(sK0)
    | k7_lattices(sK0,X0) != k7_lattices(sK0,sK1) ),
    inference(unflattening,[status(thm)],[c_1152])).

cnf(c_1472,plain,
    ( ~ m1_subset_1(X0_52,u1_struct_0(sK0))
    | ~ m1_subset_1(k7_lattices(sK0,sK2),u1_struct_0(sK0))
    | k4_lattices(sK0,k7_lattices(sK0,sK2),X0_52) != k5_lattices(sK0)
    | k7_lattices(sK0,X0_52) != k7_lattices(sK0,sK1) ),
    inference(subtyping,[status(esa)],[c_1153])).

cnf(c_1827,plain,
    ( k4_lattices(sK0,k7_lattices(sK0,sK2),X0_52) != k5_lattices(sK0)
    | k7_lattices(sK0,X0_52) != k7_lattices(sK0,sK1)
    | m1_subset_1(X0_52,u1_struct_0(sK0)) != iProver_top
    | m1_subset_1(k7_lattices(sK0,sK2),u1_struct_0(sK0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1472])).

cnf(c_1520,plain,
    ( k4_lattices(sK0,k7_lattices(sK0,sK2),X0_52) != k5_lattices(sK0)
    | k7_lattices(sK0,X0_52) != k7_lattices(sK0,sK1)
    | m1_subset_1(X0_52,u1_struct_0(sK0)) != iProver_top
    | m1_subset_1(k7_lattices(sK0,sK2),u1_struct_0(sK0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1472])).

cnf(c_2310,plain,
    ( m1_subset_1(X0_52,u1_struct_0(sK0)) != iProver_top
    | k7_lattices(sK0,X0_52) != k7_lattices(sK0,sK1)
    | k4_lattices(sK0,k7_lattices(sK0,sK2),X0_52) != k5_lattices(sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1827,c_38,c_1520,c_1880])).

cnf(c_2311,plain,
    ( k4_lattices(sK0,k7_lattices(sK0,sK2),X0_52) != k5_lattices(sK0)
    | k7_lattices(sK0,X0_52) != k7_lattices(sK0,sK1)
    | m1_subset_1(X0_52,u1_struct_0(sK0)) != iProver_top ),
    inference(renaming,[status(thm)],[c_2310])).

cnf(c_7865,plain,
    ( k4_lattices(sK0,sK1,k7_lattices(sK0,sK2)) != k5_lattices(sK0)
    | k7_lattices(sK0,sK1) != k7_lattices(sK0,sK1)
    | m1_subset_1(sK1,u1_struct_0(sK0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_7850,c_2311])).

cnf(c_7866,plain,
    ( k4_lattices(sK0,sK1,k7_lattices(sK0,sK2)) != k5_lattices(sK0)
    | m1_subset_1(sK1,u1_struct_0(sK0)) != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_7865])).

cnf(c_26,negated_conjecture,
    ( r3_lattices(sK0,sK1,sK2) ),
    inference(cnf_transformation,[],[f90])).

cnf(c_1204,plain,
    ( r1_lattices(sK0,X0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK0))
    | ~ m1_subset_1(X0,u1_struct_0(sK0))
    | sK1 != X0
    | sK2 != X1
    | sK0 != sK0 ),
    inference(resolution_lifted,[status(thm)],[c_26,c_927])).

cnf(c_1205,plain,
    ( r1_lattices(sK0,sK1,sK2)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ m1_subset_1(sK2,u1_struct_0(sK0)) ),
    inference(unflattening,[status(thm)],[c_1204])).

cnf(c_1206,plain,
    ( r1_lattices(sK0,sK1,sK2) = iProver_top
    | m1_subset_1(sK1,u1_struct_0(sK0)) != iProver_top
    | m1_subset_1(sK2,u1_struct_0(sK0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1205])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_114965,c_114541,c_7866,c_1880,c_1206,c_79,c_70,c_38,c_37,c_36,c_33])).


%------------------------------------------------------------------------------
