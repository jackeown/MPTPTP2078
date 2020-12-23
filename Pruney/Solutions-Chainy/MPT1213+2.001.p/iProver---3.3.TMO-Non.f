%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:13:21 EST 2020

% Result     : Timeout 58.61s
% Output     : None 
% Verified   : 
% Statistics : Number of formulae       :  345 (4945 expanded)
%              Number of clauses        :  237 (1339 expanded)
%              Number of leaves         :   27 (1245 expanded)
%              Depth                    :   29
%              Number of atoms          : 1326 (24192 expanded)
%              Number of equality atoms :  402 (4217 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal clause size      :   12 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f24,conjecture,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & v17_lattices(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => k7_lattices(X0,k7_lattices(X0,X1)) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,negated_conjecture,(
    ~ ! [X0] :
        ( ( l3_lattices(X0)
          & v17_lattices(X0)
          & v10_lattices(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => k7_lattices(X0,k7_lattices(X0,X1)) = X1 ) ) ),
    inference(negated_conjecture,[],[f24])).

fof(f73,plain,(
    ? [X0] :
      ( ? [X1] :
          ( k7_lattices(X0,k7_lattices(X0,X1)) != X1
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l3_lattices(X0)
      & v17_lattices(X0)
      & v10_lattices(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f25])).

fof(f74,plain,(
    ? [X0] :
      ( ? [X1] :
          ( k7_lattices(X0,k7_lattices(X0,X1)) != X1
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l3_lattices(X0)
      & v17_lattices(X0)
      & v10_lattices(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f73])).

fof(f100,plain,(
    ! [X0] :
      ( ? [X1] :
          ( k7_lattices(X0,k7_lattices(X0,X1)) != X1
          & m1_subset_1(X1,u1_struct_0(X0)) )
     => ( k7_lattices(X0,k7_lattices(X0,sK10)) != sK10
        & m1_subset_1(sK10,u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f99,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( k7_lattices(X0,k7_lattices(X0,X1)) != X1
            & m1_subset_1(X1,u1_struct_0(X0)) )
        & l3_lattices(X0)
        & v17_lattices(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( k7_lattices(sK9,k7_lattices(sK9,X1)) != X1
          & m1_subset_1(X1,u1_struct_0(sK9)) )
      & l3_lattices(sK9)
      & v17_lattices(sK9)
      & v10_lattices(sK9)
      & ~ v2_struct_0(sK9) ) ),
    introduced(choice_axiom,[])).

fof(f101,plain,
    ( k7_lattices(sK9,k7_lattices(sK9,sK10)) != sK10
    & m1_subset_1(sK10,u1_struct_0(sK9))
    & l3_lattices(sK9)
    & v17_lattices(sK9)
    & v10_lattices(sK9)
    & ~ v2_struct_0(sK9) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK9,sK10])],[f74,f100,f99])).

fof(f154,plain,(
    m1_subset_1(sK10,u1_struct_0(sK9)) ),
    inference(cnf_transformation,[],[f101])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,u1_struct_0(X0))
        & l3_lattices(X0)
        & ~ v2_struct_0(X0) )
     => m1_subset_1(k7_lattices(X0,X1),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f54,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k7_lattices(X0,X1),u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f55,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k7_lattices(X0,X1),u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f54])).

fof(f139,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k7_lattices(X0,X1),u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f150,plain,(
    ~ v2_struct_0(sK9) ),
    inference(cnf_transformation,[],[f101])).

fof(f153,plain,(
    l3_lattices(sK9) ),
    inference(cnf_transformation,[],[f101])).

fof(f7,axiom,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ( v11_lattices(X0)
      <=> ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => ! [X3] :
                    ( m1_subset_1(X3,u1_struct_0(X0))
                   => k1_lattices(X0,k2_lattices(X0,X1,X2),k2_lattices(X0,X1,X3)) = k2_lattices(X0,X1,k1_lattices(X0,X2,X3)) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X0] :
      ( ( v11_lattices(X0)
      <=> ! [X1] :
            ( ! [X2] :
                ( ! [X3] :
                    ( k1_lattices(X0,k2_lattices(X0,X1,X2),k2_lattices(X0,X1,X3)) = k2_lattices(X0,X1,k1_lattices(X0,X2,X3))
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                | ~ m1_subset_1(X2,u1_struct_0(X0)) )
            | ~ m1_subset_1(X1,u1_struct_0(X0)) ) )
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f41,plain,(
    ! [X0] :
      ( ( v11_lattices(X0)
      <=> ! [X1] :
            ( ! [X2] :
                ( ! [X3] :
                    ( k1_lattices(X0,k2_lattices(X0,X1,X2),k2_lattices(X0,X1,X3)) = k2_lattices(X0,X1,k1_lattices(X0,X2,X3))
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                | ~ m1_subset_1(X2,u1_struct_0(X0)) )
            | ~ m1_subset_1(X1,u1_struct_0(X0)) ) )
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f40])).

fof(f75,plain,(
    ! [X0] :
      ( ( ( v11_lattices(X0)
          | ? [X1] :
              ( ? [X2] :
                  ( ? [X3] :
                      ( k1_lattices(X0,k2_lattices(X0,X1,X2),k2_lattices(X0,X1,X3)) != k2_lattices(X0,X1,k1_lattices(X0,X2,X3))
                      & m1_subset_1(X3,u1_struct_0(X0)) )
                  & m1_subset_1(X2,u1_struct_0(X0)) )
              & m1_subset_1(X1,u1_struct_0(X0)) ) )
        & ( ! [X1] :
              ( ! [X2] :
                  ( ! [X3] :
                      ( k1_lattices(X0,k2_lattices(X0,X1,X2),k2_lattices(X0,X1,X3)) = k2_lattices(X0,X1,k1_lattices(X0,X2,X3))
                      | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                  | ~ m1_subset_1(X2,u1_struct_0(X0)) )
              | ~ m1_subset_1(X1,u1_struct_0(X0)) )
          | ~ v11_lattices(X0) ) )
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f41])).

fof(f76,plain,(
    ! [X0] :
      ( ( ( v11_lattices(X0)
          | ? [X1] :
              ( ? [X2] :
                  ( ? [X3] :
                      ( k1_lattices(X0,k2_lattices(X0,X1,X2),k2_lattices(X0,X1,X3)) != k2_lattices(X0,X1,k1_lattices(X0,X2,X3))
                      & m1_subset_1(X3,u1_struct_0(X0)) )
                  & m1_subset_1(X2,u1_struct_0(X0)) )
              & m1_subset_1(X1,u1_struct_0(X0)) ) )
        & ( ! [X4] :
              ( ! [X5] :
                  ( ! [X6] :
                      ( k1_lattices(X0,k2_lattices(X0,X4,X5),k2_lattices(X0,X4,X6)) = k2_lattices(X0,X4,k1_lattices(X0,X5,X6))
                      | ~ m1_subset_1(X6,u1_struct_0(X0)) )
                  | ~ m1_subset_1(X5,u1_struct_0(X0)) )
              | ~ m1_subset_1(X4,u1_struct_0(X0)) )
          | ~ v11_lattices(X0) ) )
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(rectify,[],[f75])).

fof(f79,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( k1_lattices(X0,k2_lattices(X0,X1,X2),k2_lattices(X0,X1,X3)) != k2_lattices(X0,X1,k1_lattices(X0,X2,X3))
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( k1_lattices(X0,k2_lattices(X0,X1,X2),k2_lattices(X0,X1,sK2(X0))) != k2_lattices(X0,X1,k1_lattices(X0,X2,sK2(X0)))
        & m1_subset_1(sK2(X0),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f78,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ? [X3] :
              ( k1_lattices(X0,k2_lattices(X0,X1,X2),k2_lattices(X0,X1,X3)) != k2_lattices(X0,X1,k1_lattices(X0,X2,X3))
              & m1_subset_1(X3,u1_struct_0(X0)) )
          & m1_subset_1(X2,u1_struct_0(X0)) )
     => ( ? [X3] :
            ( k1_lattices(X0,k2_lattices(X0,X1,sK1(X0)),k2_lattices(X0,X1,X3)) != k2_lattices(X0,X1,k1_lattices(X0,sK1(X0),X3))
            & m1_subset_1(X3,u1_struct_0(X0)) )
        & m1_subset_1(sK1(X0),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f77,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( k1_lattices(X0,k2_lattices(X0,X1,X2),k2_lattices(X0,X1,X3)) != k2_lattices(X0,X1,k1_lattices(X0,X2,X3))
                  & m1_subset_1(X3,u1_struct_0(X0)) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
     => ( ? [X2] :
            ( ? [X3] :
                ( k1_lattices(X0,k2_lattices(X0,sK0(X0),X2),k2_lattices(X0,sK0(X0),X3)) != k2_lattices(X0,sK0(X0),k1_lattices(X0,X2,X3))
                & m1_subset_1(X3,u1_struct_0(X0)) )
            & m1_subset_1(X2,u1_struct_0(X0)) )
        & m1_subset_1(sK0(X0),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f80,plain,(
    ! [X0] :
      ( ( ( v11_lattices(X0)
          | ( k1_lattices(X0,k2_lattices(X0,sK0(X0),sK1(X0)),k2_lattices(X0,sK0(X0),sK2(X0))) != k2_lattices(X0,sK0(X0),k1_lattices(X0,sK1(X0),sK2(X0)))
            & m1_subset_1(sK2(X0),u1_struct_0(X0))
            & m1_subset_1(sK1(X0),u1_struct_0(X0))
            & m1_subset_1(sK0(X0),u1_struct_0(X0)) ) )
        & ( ! [X4] :
              ( ! [X5] :
                  ( ! [X6] :
                      ( k1_lattices(X0,k2_lattices(X0,X4,X5),k2_lattices(X0,X4,X6)) = k2_lattices(X0,X4,k1_lattices(X0,X5,X6))
                      | ~ m1_subset_1(X6,u1_struct_0(X0)) )
                  | ~ m1_subset_1(X5,u1_struct_0(X0)) )
              | ~ m1_subset_1(X4,u1_struct_0(X0)) )
          | ~ v11_lattices(X0) ) )
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f76,f79,f78,f77])).

fof(f116,plain,(
    ! [X6,X4,X0,X5] :
      ( k1_lattices(X0,k2_lattices(X0,X4,X5),k2_lattices(X0,X4,X6)) = k2_lattices(X0,X4,k1_lattices(X0,X5,X6))
      | ~ m1_subset_1(X6,u1_struct_0(X0))
      | ~ m1_subset_1(X5,u1_struct_0(X0))
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ v11_lattices(X0)
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f80])).

fof(f4,axiom,(
    ! [X0] :
      ( l3_lattices(X0)
     => ( ( v17_lattices(X0)
          & ~ v2_struct_0(X0) )
       => ( v16_lattices(X0)
          & v15_lattices(X0)
          & v11_lattices(X0)
          & ~ v2_struct_0(X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0] :
      ( l3_lattices(X0)
     => ( ( v17_lattices(X0)
          & ~ v2_struct_0(X0) )
       => ( v15_lattices(X0)
          & v11_lattices(X0)
          & ~ v2_struct_0(X0) ) ) ) ),
    inference(pure_predicate_removal,[],[f4])).

fof(f34,plain,(
    ! [X0] :
      ( ( v15_lattices(X0)
        & v11_lattices(X0)
        & ~ v2_struct_0(X0) )
      | ~ v17_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(ennf_transformation,[],[f26])).

fof(f35,plain,(
    ! [X0] :
      ( ( v15_lattices(X0)
        & v11_lattices(X0)
        & ~ v2_struct_0(X0) )
      | ~ v17_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(flattening,[],[f34])).

fof(f112,plain,(
    ! [X0] :
      ( v11_lattices(X0)
      | ~ v17_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f152,plain,(
    v17_lattices(sK9) ),
    inference(cnf_transformation,[],[f101])).

fof(f2,axiom,(
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

fof(f27,plain,(
    ! [X0] :
      ( l3_lattices(X0)
     => ( ( v10_lattices(X0)
          & ~ v2_struct_0(X0) )
       => ( v9_lattices(X0)
          & v8_lattices(X0)
          & v6_lattices(X0)
          & v5_lattices(X0)
          & v4_lattices(X0)
          & ~ v2_struct_0(X0) ) ) ) ),
    inference(pure_predicate_removal,[],[f2])).

fof(f28,plain,(
    ! [X0] :
      ( l3_lattices(X0)
     => ( ( v10_lattices(X0)
          & ~ v2_struct_0(X0) )
       => ( v9_lattices(X0)
          & v8_lattices(X0)
          & v6_lattices(X0)
          & v4_lattices(X0)
          & ~ v2_struct_0(X0) ) ) ) ),
    inference(pure_predicate_removal,[],[f27])).

fof(f30,plain,(
    ! [X0] :
      ( ( v9_lattices(X0)
        & v8_lattices(X0)
        & v6_lattices(X0)
        & v4_lattices(X0)
        & ~ v2_struct_0(X0) )
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(ennf_transformation,[],[f28])).

fof(f31,plain,(
    ! [X0] :
      ( ( v9_lattices(X0)
        & v8_lattices(X0)
        & v6_lattices(X0)
        & v4_lattices(X0)
        & ~ v2_struct_0(X0) )
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(flattening,[],[f30])).

fof(f105,plain,(
    ! [X0] :
      ( v6_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l1_lattices(X0)
        & v6_lattices(X0)
        & ~ v2_struct_0(X0) )
     => k4_lattices(X0,X1,X2) = k4_lattices(X0,X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0,X1,X2] :
      ( k4_lattices(X0,X1,X2) = k4_lattices(X0,X2,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f39,plain,(
    ! [X0,X1,X2] :
      ( k4_lattices(X0,X1,X2) = k4_lattices(X0,X2,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f38])).

fof(f115,plain,(
    ! [X2,X0,X1] :
      ( k4_lattices(X0,X1,X2) = k4_lattices(X0,X2,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f15,axiom,(
    ! [X0] :
      ( l3_lattices(X0)
     => ( l2_lattices(X0)
        & l1_lattices(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f56,plain,(
    ! [X0] :
      ( ( l2_lattices(X0)
        & l1_lattices(X0) )
      | ~ l3_lattices(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f140,plain,(
    ! [X0] :
      ( l1_lattices(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f56])).

fof(f151,plain,(
    v10_lattices(sK9) ),
    inference(cnf_transformation,[],[f101])).

fof(f22,axiom,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & v17_lattices(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => k4_lattices(X0,k7_lattices(X0,X1),X1) = k5_lattices(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f69,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k4_lattices(X0,k7_lattices(X0,X1),X1) = k5_lattices(X0)
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v17_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f70,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k4_lattices(X0,k7_lattices(X0,X1),X1) = k5_lattices(X0)
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v17_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f69])).

fof(f148,plain,(
    ! [X0,X1] :
      ( k4_lattices(X0,k7_lattices(X0,X1),X1) = k5_lattices(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v17_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f70])).

fof(f17,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l1_lattices(X0)
        & v6_lattices(X0)
        & ~ v2_struct_0(X0) )
     => k4_lattices(X0,X1,X2) = k2_lattices(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f59,plain,(
    ! [X0,X1,X2] :
      ( k4_lattices(X0,X1,X2) = k2_lattices(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f60,plain,(
    ! [X0,X1,X2] :
      ( k4_lattices(X0,X1,X2) = k2_lattices(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f59])).

fof(f143,plain,(
    ! [X2,X0,X1] :
      ( k4_lattices(X0,X1,X2) = k2_lattices(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f60])).

fof(f104,plain,(
    ! [X0] :
      ( v4_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l2_lattices(X0)
        & v4_lattices(X0)
        & ~ v2_struct_0(X0) )
     => k3_lattices(X0,X1,X2) = k3_lattices(X0,X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( k3_lattices(X0,X1,X2) = k3_lattices(X0,X2,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l2_lattices(X0)
      | ~ v4_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( k3_lattices(X0,X1,X2) = k3_lattices(X0,X2,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l2_lattices(X0)
      | ~ v4_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f36])).

fof(f114,plain,(
    ! [X2,X0,X1] :
      ( k3_lattices(X0,X1,X2) = k3_lattices(X0,X2,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l2_lattices(X0)
      | ~ v4_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f141,plain,(
    ! [X0] :
      ( l2_lattices(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f56])).

fof(f23,axiom,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & v17_lattices(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => k3_lattices(X0,k7_lattices(X0,X1),X1) = k6_lattices(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f71,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k3_lattices(X0,k7_lattices(X0,X1),X1) = k6_lattices(X0)
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v17_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f72,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k3_lattices(X0,k7_lattices(X0,X1),X1) = k6_lattices(X0)
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v17_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f71])).

fof(f149,plain,(
    ! [X0,X1] :
      ( k3_lattices(X0,k7_lattices(X0,X1),X1) = k6_lattices(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v17_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f72])).

fof(f16,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l2_lattices(X0)
        & v4_lattices(X0)
        & ~ v2_struct_0(X0) )
     => k3_lattices(X0,X1,X2) = k1_lattices(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f57,plain,(
    ! [X0,X1,X2] :
      ( k3_lattices(X0,X1,X2) = k1_lattices(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l2_lattices(X0)
      | ~ v4_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f58,plain,(
    ! [X0,X1,X2] :
      ( k3_lattices(X0,X1,X2) = k1_lattices(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l2_lattices(X0)
      | ~ v4_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f57])).

fof(f142,plain,(
    ! [X2,X0,X1] :
      ( k3_lattices(X0,X1,X2) = k1_lattices(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l2_lattices(X0)
      | ~ v4_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f58])).

fof(f11,axiom,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ( v9_lattices(X0)
      <=> ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => k2_lattices(X0,X1,k1_lattices(X0,X1,X2)) = X1 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f48,plain,(
    ! [X0] :
      ( ( v9_lattices(X0)
      <=> ! [X1] :
            ( ! [X2] :
                ( k2_lattices(X0,X1,k1_lattices(X0,X1,X2)) = X1
                | ~ m1_subset_1(X2,u1_struct_0(X0)) )
            | ~ m1_subset_1(X1,u1_struct_0(X0)) ) )
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f49,plain,(
    ! [X0] :
      ( ( v9_lattices(X0)
      <=> ! [X1] :
            ( ! [X2] :
                ( k2_lattices(X0,X1,k1_lattices(X0,X1,X2)) = X1
                | ~ m1_subset_1(X2,u1_struct_0(X0)) )
            | ~ m1_subset_1(X1,u1_struct_0(X0)) ) )
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f48])).

fof(f94,plain,(
    ! [X0] :
      ( ( ( v9_lattices(X0)
          | ? [X1] :
              ( ? [X2] :
                  ( k2_lattices(X0,X1,k1_lattices(X0,X1,X2)) != X1
                  & m1_subset_1(X2,u1_struct_0(X0)) )
              & m1_subset_1(X1,u1_struct_0(X0)) ) )
        & ( ! [X1] :
              ( ! [X2] :
                  ( k2_lattices(X0,X1,k1_lattices(X0,X1,X2)) = X1
                  | ~ m1_subset_1(X2,u1_struct_0(X0)) )
              | ~ m1_subset_1(X1,u1_struct_0(X0)) )
          | ~ v9_lattices(X0) ) )
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f49])).

fof(f95,plain,(
    ! [X0] :
      ( ( ( v9_lattices(X0)
          | ? [X1] :
              ( ? [X2] :
                  ( k2_lattices(X0,X1,k1_lattices(X0,X1,X2)) != X1
                  & m1_subset_1(X2,u1_struct_0(X0)) )
              & m1_subset_1(X1,u1_struct_0(X0)) ) )
        & ( ! [X3] :
              ( ! [X4] :
                  ( k2_lattices(X0,X3,k1_lattices(X0,X3,X4)) = X3
                  | ~ m1_subset_1(X4,u1_struct_0(X0)) )
              | ~ m1_subset_1(X3,u1_struct_0(X0)) )
          | ~ v9_lattices(X0) ) )
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(rectify,[],[f94])).

fof(f97,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( k2_lattices(X0,X1,k1_lattices(X0,X1,X2)) != X1
          & m1_subset_1(X2,u1_struct_0(X0)) )
     => ( k2_lattices(X0,X1,k1_lattices(X0,X1,sK8(X0))) != X1
        & m1_subset_1(sK8(X0),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f96,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( k2_lattices(X0,X1,k1_lattices(X0,X1,X2)) != X1
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
     => ( ? [X2] :
            ( k2_lattices(X0,sK7(X0),k1_lattices(X0,sK7(X0),X2)) != sK7(X0)
            & m1_subset_1(X2,u1_struct_0(X0)) )
        & m1_subset_1(sK7(X0),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f98,plain,(
    ! [X0] :
      ( ( ( v9_lattices(X0)
          | ( k2_lattices(X0,sK7(X0),k1_lattices(X0,sK7(X0),sK8(X0))) != sK7(X0)
            & m1_subset_1(sK8(X0),u1_struct_0(X0))
            & m1_subset_1(sK7(X0),u1_struct_0(X0)) ) )
        & ( ! [X3] :
              ( ! [X4] :
                  ( k2_lattices(X0,X3,k1_lattices(X0,X3,X4)) = X3
                  | ~ m1_subset_1(X4,u1_struct_0(X0)) )
              | ~ m1_subset_1(X3,u1_struct_0(X0)) )
          | ~ v9_lattices(X0) ) )
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7,sK8])],[f95,f97,f96])).

fof(f133,plain,(
    ! [X4,X0,X3] :
      ( k2_lattices(X0,X3,k1_lattices(X0,X3,X4)) = X3
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ v9_lattices(X0)
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f98])).

fof(f107,plain,(
    ! [X0] :
      ( v9_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f12,axiom,(
    ! [X0] :
      ( ( l1_lattices(X0)
        & ~ v2_struct_0(X0) )
     => m1_subset_1(k5_lattices(X0),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f50,plain,(
    ! [X0] :
      ( m1_subset_1(k5_lattices(X0),u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f51,plain,(
    ! [X0] :
      ( m1_subset_1(k5_lattices(X0),u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f50])).

fof(f137,plain,(
    ! [X0] :
      ( m1_subset_1(k5_lattices(X0),u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f20,axiom,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & v13_lattices(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => k4_lattices(X0,k5_lattices(X0),X1) = k5_lattices(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f65,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k4_lattices(X0,k5_lattices(X0),X1) = k5_lattices(X0)
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v13_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f66,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k4_lattices(X0,k5_lattices(X0),X1) = k5_lattices(X0)
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v13_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f65])).

fof(f146,plain,(
    ! [X0,X1] :
      ( k4_lattices(X0,k5_lattices(X0),X1) = k5_lattices(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v13_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f66])).

fof(f113,plain,(
    ! [X0] :
      ( v15_lattices(X0)
      | ~ v17_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f3,axiom,(
    ! [X0] :
      ( l3_lattices(X0)
     => ( ( v15_lattices(X0)
          & ~ v2_struct_0(X0) )
       => ( v14_lattices(X0)
          & v13_lattices(X0)
          & ~ v2_struct_0(X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0] :
      ( ( v14_lattices(X0)
        & v13_lattices(X0)
        & ~ v2_struct_0(X0) )
      | ~ v15_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f33,plain,(
    ! [X0] :
      ( ( v14_lattices(X0)
        & v13_lattices(X0)
        & ~ v2_struct_0(X0) )
      | ~ v15_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(flattening,[],[f32])).

fof(f109,plain,(
    ! [X0] :
      ( v13_lattices(X0)
      | ~ v15_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f19,axiom,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & v13_lattices(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => k3_lattices(X0,k5_lattices(X0),X1) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f63,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k3_lattices(X0,k5_lattices(X0),X1) = X1
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v13_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f64,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k3_lattices(X0,k5_lattices(X0),X1) = X1
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v13_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f63])).

fof(f145,plain,(
    ! [X0,X1] :
      ( k3_lattices(X0,k5_lattices(X0),X1) = X1
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v13_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f64])).

fof(f13,axiom,(
    ! [X0] :
      ( ( l2_lattices(X0)
        & ~ v2_struct_0(X0) )
     => m1_subset_1(k6_lattices(X0),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f52,plain,(
    ! [X0] :
      ( m1_subset_1(k6_lattices(X0),u1_struct_0(X0))
      | ~ l2_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f53,plain,(
    ! [X0] :
      ( m1_subset_1(k6_lattices(X0),u1_struct_0(X0))
      | ~ l2_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f52])).

fof(f138,plain,(
    ! [X0] :
      ( m1_subset_1(k6_lattices(X0),u1_struct_0(X0))
      | ~ l2_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f9,axiom,(
    ! [X0] :
      ( ( l2_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ( v14_lattices(X0)
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ( k6_lattices(X0) = X1
            <=> ! [X2] :
                  ( m1_subset_1(X2,u1_struct_0(X0))
                 => ( k1_lattices(X0,X2,X1) = X1
                    & k1_lattices(X0,X1,X2) = X1 ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( k6_lattices(X0) = X1
          <=> ! [X2] :
                ( ( k1_lattices(X0,X2,X1) = X1
                  & k1_lattices(X0,X1,X2) = X1 )
                | ~ m1_subset_1(X2,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ v14_lattices(X0)
      | ~ l2_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f45,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( k6_lattices(X0) = X1
          <=> ! [X2] :
                ( ( k1_lattices(X0,X2,X1) = X1
                  & k1_lattices(X0,X1,X2) = X1 )
                | ~ m1_subset_1(X2,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ v14_lattices(X0)
      | ~ l2_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f44])).

fof(f85,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( k6_lattices(X0) = X1
              | ? [X2] :
                  ( ( k1_lattices(X0,X2,X1) != X1
                    | k1_lattices(X0,X1,X2) != X1 )
                  & m1_subset_1(X2,u1_struct_0(X0)) ) )
            & ( ! [X2] :
                  ( ( k1_lattices(X0,X2,X1) = X1
                    & k1_lattices(X0,X1,X2) = X1 )
                  | ~ m1_subset_1(X2,u1_struct_0(X0)) )
              | k6_lattices(X0) != X1 ) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ v14_lattices(X0)
      | ~ l2_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f45])).

fof(f86,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( k6_lattices(X0) = X1
              | ? [X2] :
                  ( ( k1_lattices(X0,X2,X1) != X1
                    | k1_lattices(X0,X1,X2) != X1 )
                  & m1_subset_1(X2,u1_struct_0(X0)) ) )
            & ( ! [X3] :
                  ( ( k1_lattices(X0,X3,X1) = X1
                    & k1_lattices(X0,X1,X3) = X1 )
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | k6_lattices(X0) != X1 ) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ v14_lattices(X0)
      | ~ l2_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(rectify,[],[f85])).

fof(f87,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( k1_lattices(X0,X2,X1) != X1
            | k1_lattices(X0,X1,X2) != X1 )
          & m1_subset_1(X2,u1_struct_0(X0)) )
     => ( ( k1_lattices(X0,sK4(X0,X1),X1) != X1
          | k1_lattices(X0,X1,sK4(X0,X1)) != X1 )
        & m1_subset_1(sK4(X0,X1),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f88,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( k6_lattices(X0) = X1
              | ( ( k1_lattices(X0,sK4(X0,X1),X1) != X1
                  | k1_lattices(X0,X1,sK4(X0,X1)) != X1 )
                & m1_subset_1(sK4(X0,X1),u1_struct_0(X0)) ) )
            & ( ! [X3] :
                  ( ( k1_lattices(X0,X3,X1) = X1
                    & k1_lattices(X0,X1,X3) = X1 )
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | k6_lattices(X0) != X1 ) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ v14_lattices(X0)
      | ~ l2_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f86,f87])).

fof(f126,plain,(
    ! [X0,X3,X1] :
      ( k1_lattices(X0,X3,X1) = X1
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | k6_lattices(X0) != X1
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ v14_lattices(X0)
      | ~ l2_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f88])).

fof(f158,plain,(
    ! [X0,X3] :
      ( k1_lattices(X0,X3,k6_lattices(X0)) = k6_lattices(X0)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(k6_lattices(X0),u1_struct_0(X0))
      | ~ v14_lattices(X0)
      | ~ l2_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f126])).

fof(f110,plain,(
    ! [X0] :
      ( v14_lattices(X0)
      | ~ v15_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f155,plain,(
    k7_lattices(sK9,k7_lattices(sK9,sK10)) != sK10 ),
    inference(cnf_transformation,[],[f101])).

cnf(c_49,negated_conjecture,
    ( m1_subset_1(sK10,u1_struct_0(sK9)) ),
    inference(cnf_transformation,[],[f154])).

cnf(c_2570,plain,
    ( m1_subset_1(sK10,u1_struct_0(sK9)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_49])).

cnf(c_37,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | m1_subset_1(k7_lattices(X1,X0),u1_struct_0(X1))
    | ~ l3_lattices(X1)
    | v2_struct_0(X1) ),
    inference(cnf_transformation,[],[f139])).

cnf(c_53,negated_conjecture,
    ( ~ v2_struct_0(sK9) ),
    inference(cnf_transformation,[],[f150])).

cnf(c_1863,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | m1_subset_1(k7_lattices(X1,X0),u1_struct_0(X1))
    | ~ l3_lattices(X1)
    | sK9 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_37,c_53])).

cnf(c_1864,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK9))
    | m1_subset_1(k7_lattices(sK9,X0),u1_struct_0(sK9))
    | ~ l3_lattices(sK9) ),
    inference(unflattening,[status(thm)],[c_1863])).

cnf(c_50,negated_conjecture,
    ( l3_lattices(sK9) ),
    inference(cnf_transformation,[],[f153])).

cnf(c_1868,plain,
    ( m1_subset_1(k7_lattices(sK9,X0),u1_struct_0(sK9))
    | ~ m1_subset_1(X0,u1_struct_0(sK9)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1864,c_50])).

cnf(c_1869,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK9))
    | m1_subset_1(k7_lattices(sK9,X0),u1_struct_0(sK9)) ),
    inference(renaming,[status(thm)],[c_1868])).

cnf(c_2546,plain,
    ( m1_subset_1(X0,u1_struct_0(sK9)) != iProver_top
    | m1_subset_1(k7_lattices(sK9,X0),u1_struct_0(sK9)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1869])).

cnf(c_18,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ v11_lattices(X1)
    | ~ l3_lattices(X1)
    | v2_struct_0(X1)
    | k1_lattices(X1,k2_lattices(X1,X3,X2),k2_lattices(X1,X3,X0)) = k2_lattices(X1,X3,k1_lattices(X1,X2,X0)) ),
    inference(cnf_transformation,[],[f116])).

cnf(c_1919,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ v11_lattices(X1)
    | ~ l3_lattices(X1)
    | k1_lattices(X1,k2_lattices(X1,X3,X2),k2_lattices(X1,X3,X0)) = k2_lattices(X1,X3,k1_lattices(X1,X2,X0))
    | sK9 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_18,c_53])).

cnf(c_1920,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK9))
    | ~ m1_subset_1(X1,u1_struct_0(sK9))
    | ~ m1_subset_1(X2,u1_struct_0(sK9))
    | ~ v11_lattices(sK9)
    | ~ l3_lattices(sK9)
    | k1_lattices(sK9,k2_lattices(sK9,X2,X1),k2_lattices(sK9,X2,X0)) = k2_lattices(sK9,X2,k1_lattices(sK9,X1,X0)) ),
    inference(unflattening,[status(thm)],[c_1919])).

cnf(c_10,plain,
    ( v11_lattices(X0)
    | ~ v17_lattices(X0)
    | ~ l3_lattices(X0)
    | v2_struct_0(X0) ),
    inference(cnf_transformation,[],[f112])).

cnf(c_51,negated_conjecture,
    ( v17_lattices(sK9) ),
    inference(cnf_transformation,[],[f152])).

cnf(c_698,plain,
    ( v11_lattices(X0)
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | sK9 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_10,c_51])).

cnf(c_699,plain,
    ( v11_lattices(sK9)
    | ~ l3_lattices(sK9)
    | v2_struct_0(sK9) ),
    inference(unflattening,[status(thm)],[c_698])).

cnf(c_169,plain,
    ( v11_lattices(sK9)
    | ~ v17_lattices(sK9)
    | ~ l3_lattices(sK9)
    | v2_struct_0(sK9) ),
    inference(instantiation,[status(thm)],[c_10])).

cnf(c_701,plain,
    ( v11_lattices(sK9) ),
    inference(global_propositional_subsumption,[status(thm)],[c_699,c_53,c_51,c_50,c_169])).

cnf(c_1765,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ l3_lattices(X1)
    | v2_struct_0(X1)
    | k1_lattices(X1,k2_lattices(X1,X3,X2),k2_lattices(X1,X3,X0)) = k2_lattices(X1,X3,k1_lattices(X1,X2,X0))
    | sK9 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_18,c_701])).

cnf(c_1766,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK9))
    | ~ m1_subset_1(X1,u1_struct_0(sK9))
    | ~ m1_subset_1(X2,u1_struct_0(sK9))
    | ~ l3_lattices(sK9)
    | v2_struct_0(sK9)
    | k1_lattices(sK9,k2_lattices(sK9,X2,X1),k2_lattices(sK9,X2,X0)) = k2_lattices(sK9,X2,k1_lattices(sK9,X1,X0)) ),
    inference(unflattening,[status(thm)],[c_1765])).

cnf(c_1923,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK9))
    | ~ m1_subset_1(X1,u1_struct_0(sK9))
    | ~ m1_subset_1(X2,u1_struct_0(sK9))
    | k1_lattices(sK9,k2_lattices(sK9,X2,X1),k2_lattices(sK9,X2,X0)) = k2_lattices(sK9,X2,k1_lattices(sK9,X1,X0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1920,c_53,c_50,c_1766])).

cnf(c_1924,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK9))
    | ~ m1_subset_1(X1,u1_struct_0(sK9))
    | ~ m1_subset_1(X2,u1_struct_0(sK9))
    | k1_lattices(sK9,k2_lattices(sK9,X1,X2),k2_lattices(sK9,X1,X0)) = k2_lattices(sK9,X1,k1_lattices(sK9,X2,X0)) ),
    inference(renaming,[status(thm)],[c_1923])).

cnf(c_2549,plain,
    ( k1_lattices(sK9,k2_lattices(sK9,X0,X1),k2_lattices(sK9,X0,X2)) = k2_lattices(sK9,X0,k1_lattices(sK9,X1,X2))
    | m1_subset_1(X2,u1_struct_0(sK9)) != iProver_top
    | m1_subset_1(X0,u1_struct_0(sK9)) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK9)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1924])).

cnf(c_3217,plain,
    ( k1_lattices(sK9,k2_lattices(sK9,k7_lattices(sK9,X0),X1),k2_lattices(sK9,k7_lattices(sK9,X0),X2)) = k2_lattices(sK9,k7_lattices(sK9,X0),k1_lattices(sK9,X1,X2))
    | m1_subset_1(X0,u1_struct_0(sK9)) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK9)) != iProver_top
    | m1_subset_1(X2,u1_struct_0(sK9)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2546,c_2549])).

cnf(c_10406,plain,
    ( k1_lattices(sK9,k2_lattices(sK9,k7_lattices(sK9,k7_lattices(sK9,X0)),X1),k2_lattices(sK9,k7_lattices(sK9,k7_lattices(sK9,X0)),X2)) = k2_lattices(sK9,k7_lattices(sK9,k7_lattices(sK9,X0)),k1_lattices(sK9,X1,X2))
    | m1_subset_1(X0,u1_struct_0(sK9)) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK9)) != iProver_top
    | m1_subset_1(X2,u1_struct_0(sK9)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2546,c_3217])).

cnf(c_193769,plain,
    ( k1_lattices(sK9,k2_lattices(sK9,k7_lattices(sK9,k7_lattices(sK9,sK10)),X0),k2_lattices(sK9,k7_lattices(sK9,k7_lattices(sK9,sK10)),X1)) = k2_lattices(sK9,k7_lattices(sK9,k7_lattices(sK9,sK10)),k1_lattices(sK9,X0,X1))
    | m1_subset_1(X0,u1_struct_0(sK9)) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK9)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2570,c_10406])).

cnf(c_193830,plain,
    ( k1_lattices(sK9,k2_lattices(sK9,k7_lattices(sK9,k7_lattices(sK9,sK10)),sK10),k2_lattices(sK9,k7_lattices(sK9,k7_lattices(sK9,sK10)),X0)) = k2_lattices(sK9,k7_lattices(sK9,k7_lattices(sK9,sK10)),k1_lattices(sK9,sK10,X0))
    | m1_subset_1(X0,u1_struct_0(sK9)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2570,c_193769])).

cnf(c_3214,plain,
    ( k1_lattices(sK9,k2_lattices(sK9,sK10,X0),k2_lattices(sK9,sK10,X1)) = k2_lattices(sK9,sK10,k1_lattices(sK9,X0,X1))
    | m1_subset_1(X0,u1_struct_0(sK9)) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK9)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2570,c_2549])).

cnf(c_3244,plain,
    ( k1_lattices(sK9,k2_lattices(sK9,sK10,k7_lattices(sK9,X0)),k2_lattices(sK9,sK10,X1)) = k2_lattices(sK9,sK10,k1_lattices(sK9,k7_lattices(sK9,X0),X1))
    | m1_subset_1(X0,u1_struct_0(sK9)) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK9)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2546,c_3214])).

cnf(c_15460,plain,
    ( k1_lattices(sK9,k2_lattices(sK9,sK10,k7_lattices(sK9,sK10)),k2_lattices(sK9,sK10,X0)) = k2_lattices(sK9,sK10,k1_lattices(sK9,k7_lattices(sK9,sK10),X0))
    | m1_subset_1(X0,u1_struct_0(sK9)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2570,c_3244])).

cnf(c_3,plain,
    ( v6_lattices(X0)
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | ~ v10_lattices(X0) ),
    inference(cnf_transformation,[],[f105])).

cnf(c_13,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l1_lattices(X1)
    | ~ v6_lattices(X1)
    | v2_struct_0(X1)
    | k4_lattices(X1,X0,X2) = k4_lattices(X1,X2,X0) ),
    inference(cnf_transformation,[],[f115])).

cnf(c_814,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l1_lattices(X1)
    | ~ l3_lattices(X3)
    | v2_struct_0(X3)
    | v2_struct_0(X1)
    | ~ v10_lattices(X3)
    | X1 != X3
    | k4_lattices(X1,X0,X2) = k4_lattices(X1,X2,X0) ),
    inference(resolution_lifted,[status(thm)],[c_3,c_13])).

cnf(c_815,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l1_lattices(X1)
    | ~ l3_lattices(X1)
    | v2_struct_0(X1)
    | ~ v10_lattices(X1)
    | k4_lattices(X1,X0,X2) = k4_lattices(X1,X2,X0) ),
    inference(unflattening,[status(thm)],[c_814])).

cnf(c_39,plain,
    ( l1_lattices(X0)
    | ~ l3_lattices(X0) ),
    inference(cnf_transformation,[],[f140])).

cnf(c_833,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l3_lattices(X1)
    | v2_struct_0(X1)
    | ~ v10_lattices(X1)
    | k4_lattices(X1,X0,X2) = k4_lattices(X1,X2,X0) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_815,c_39])).

cnf(c_52,negated_conjecture,
    ( v10_lattices(sK9) ),
    inference(cnf_transformation,[],[f151])).

cnf(c_1304,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l3_lattices(X1)
    | v2_struct_0(X1)
    | k4_lattices(X1,X2,X0) = k4_lattices(X1,X0,X2)
    | sK9 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_833,c_52])).

cnf(c_1305,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK9))
    | ~ m1_subset_1(X1,u1_struct_0(sK9))
    | ~ l3_lattices(sK9)
    | v2_struct_0(sK9)
    | k4_lattices(sK9,X1,X0) = k4_lattices(sK9,X0,X1) ),
    inference(unflattening,[status(thm)],[c_1304])).

cnf(c_1309,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK9))
    | ~ m1_subset_1(X1,u1_struct_0(sK9))
    | k4_lattices(sK9,X1,X0) = k4_lattices(sK9,X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1305,c_53,c_50])).

cnf(c_2556,plain,
    ( k4_lattices(sK9,X0,X1) = k4_lattices(sK9,X1,X0)
    | m1_subset_1(X1,u1_struct_0(sK9)) != iProver_top
    | m1_subset_1(X0,u1_struct_0(sK9)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1309])).

cnf(c_4192,plain,
    ( k4_lattices(sK9,sK10,X0) = k4_lattices(sK9,X0,sK10)
    | m1_subset_1(X0,u1_struct_0(sK9)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2570,c_2556])).

cnf(c_4212,plain,
    ( k4_lattices(sK9,k7_lattices(sK9,X0),sK10) = k4_lattices(sK9,sK10,k7_lattices(sK9,X0))
    | m1_subset_1(X0,u1_struct_0(sK9)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2546,c_4192])).

cnf(c_5553,plain,
    ( k4_lattices(sK9,sK10,k7_lattices(sK9,sK10)) = k4_lattices(sK9,k7_lattices(sK9,sK10),sK10) ),
    inference(superposition,[status(thm)],[c_2570,c_4212])).

cnf(c_46,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ v17_lattices(X1)
    | ~ l3_lattices(X1)
    | v2_struct_0(X1)
    | ~ v10_lattices(X1)
    | k4_lattices(X1,k7_lattices(X1,X0),X0) = k5_lattices(X1) ),
    inference(cnf_transformation,[],[f148])).

cnf(c_727,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ l3_lattices(X1)
    | v2_struct_0(X1)
    | ~ v10_lattices(X1)
    | k4_lattices(X1,k7_lattices(X1,X0),X0) = k5_lattices(X1)
    | sK9 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_46,c_51])).

cnf(c_728,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK9))
    | ~ l3_lattices(sK9)
    | v2_struct_0(sK9)
    | ~ v10_lattices(sK9)
    | k4_lattices(sK9,k7_lattices(sK9,X0),X0) = k5_lattices(sK9) ),
    inference(unflattening,[status(thm)],[c_727])).

cnf(c_732,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK9))
    | k4_lattices(sK9,k7_lattices(sK9,X0),X0) = k5_lattices(sK9) ),
    inference(global_propositional_subsumption,[status(thm)],[c_728,c_53,c_52,c_50])).

cnf(c_2568,plain,
    ( k4_lattices(sK9,k7_lattices(sK9,X0),X0) = k5_lattices(sK9)
    | m1_subset_1(X0,u1_struct_0(sK9)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_732])).

cnf(c_3140,plain,
    ( k4_lattices(sK9,k7_lattices(sK9,sK10),sK10) = k5_lattices(sK9) ),
    inference(superposition,[status(thm)],[c_2570,c_2568])).

cnf(c_5558,plain,
    ( k4_lattices(sK9,sK10,k7_lattices(sK9,sK10)) = k5_lattices(sK9) ),
    inference(light_normalisation,[status(thm)],[c_5553,c_3140])).

cnf(c_41,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l1_lattices(X1)
    | ~ v6_lattices(X1)
    | v2_struct_0(X1)
    | k2_lattices(X1,X2,X0) = k4_lattices(X1,X2,X0) ),
    inference(cnf_transformation,[],[f143])).

cnf(c_785,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l1_lattices(X1)
    | ~ l3_lattices(X3)
    | v2_struct_0(X3)
    | v2_struct_0(X1)
    | ~ v10_lattices(X3)
    | X1 != X3
    | k2_lattices(X1,X2,X0) = k4_lattices(X1,X2,X0) ),
    inference(resolution_lifted,[status(thm)],[c_3,c_41])).

cnf(c_786,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l1_lattices(X1)
    | ~ l3_lattices(X1)
    | v2_struct_0(X1)
    | ~ v10_lattices(X1)
    | k2_lattices(X1,X2,X0) = k4_lattices(X1,X2,X0) ),
    inference(unflattening,[status(thm)],[c_785])).

cnf(c_804,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l3_lattices(X1)
    | v2_struct_0(X1)
    | ~ v10_lattices(X1)
    | k2_lattices(X1,X2,X0) = k4_lattices(X1,X2,X0) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_786,c_39])).

cnf(c_1325,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l3_lattices(X1)
    | v2_struct_0(X1)
    | k2_lattices(X1,X2,X0) = k4_lattices(X1,X2,X0)
    | sK9 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_804,c_52])).

cnf(c_1326,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK9))
    | ~ m1_subset_1(X1,u1_struct_0(sK9))
    | ~ l3_lattices(sK9)
    | v2_struct_0(sK9)
    | k2_lattices(sK9,X1,X0) = k4_lattices(sK9,X1,X0) ),
    inference(unflattening,[status(thm)],[c_1325])).

cnf(c_1330,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK9))
    | ~ m1_subset_1(X1,u1_struct_0(sK9))
    | k2_lattices(sK9,X1,X0) = k4_lattices(sK9,X1,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1326,c_53,c_50])).

cnf(c_2555,plain,
    ( k2_lattices(sK9,X0,X1) = k4_lattices(sK9,X0,X1)
    | m1_subset_1(X1,u1_struct_0(sK9)) != iProver_top
    | m1_subset_1(X0,u1_struct_0(sK9)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1330])).

cnf(c_4038,plain,
    ( k2_lattices(sK9,sK10,X0) = k4_lattices(sK9,sK10,X0)
    | m1_subset_1(X0,u1_struct_0(sK9)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2570,c_2555])).

cnf(c_4186,plain,
    ( k2_lattices(sK9,sK10,k7_lattices(sK9,X0)) = k4_lattices(sK9,sK10,k7_lattices(sK9,X0))
    | m1_subset_1(X0,u1_struct_0(sK9)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2546,c_4038])).

cnf(c_5525,plain,
    ( k2_lattices(sK9,sK10,k7_lattices(sK9,sK10)) = k4_lattices(sK9,sK10,k7_lattices(sK9,sK10)) ),
    inference(superposition,[status(thm)],[c_2570,c_4186])).

cnf(c_5565,plain,
    ( k2_lattices(sK9,sK10,k7_lattices(sK9,sK10)) = k5_lattices(sK9) ),
    inference(demodulation,[status(thm)],[c_5558,c_5525])).

cnf(c_15468,plain,
    ( k2_lattices(sK9,sK10,k1_lattices(sK9,k7_lattices(sK9,sK10),X0)) = k1_lattices(sK9,k5_lattices(sK9),k2_lattices(sK9,sK10,X0))
    | m1_subset_1(X0,u1_struct_0(sK9)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_15460,c_5565])).

cnf(c_15643,plain,
    ( k2_lattices(sK9,sK10,k1_lattices(sK9,k7_lattices(sK9,sK10),k7_lattices(sK9,X0))) = k1_lattices(sK9,k5_lattices(sK9),k2_lattices(sK9,sK10,k7_lattices(sK9,X0)))
    | m1_subset_1(X0,u1_struct_0(sK9)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2546,c_15468])).

cnf(c_52700,plain,
    ( k2_lattices(sK9,sK10,k1_lattices(sK9,k7_lattices(sK9,sK10),k7_lattices(sK9,k7_lattices(sK9,X0)))) = k1_lattices(sK9,k5_lattices(sK9),k2_lattices(sK9,sK10,k7_lattices(sK9,k7_lattices(sK9,X0))))
    | m1_subset_1(X0,u1_struct_0(sK9)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2546,c_15643])).

cnf(c_70476,plain,
    ( k2_lattices(sK9,sK10,k1_lattices(sK9,k7_lattices(sK9,sK10),k7_lattices(sK9,k7_lattices(sK9,sK10)))) = k1_lattices(sK9,k5_lattices(sK9),k2_lattices(sK9,sK10,k7_lattices(sK9,k7_lattices(sK9,sK10)))) ),
    inference(superposition,[status(thm)],[c_2570,c_52700])).

cnf(c_4,plain,
    ( v4_lattices(X0)
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | ~ v10_lattices(X0) ),
    inference(cnf_transformation,[],[f104])).

cnf(c_12,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l2_lattices(X1)
    | ~ v4_lattices(X1)
    | v2_struct_0(X1)
    | k3_lattices(X1,X0,X2) = k3_lattices(X1,X2,X0) ),
    inference(cnf_transformation,[],[f114])).

cnf(c_633,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l2_lattices(X1)
    | ~ l3_lattices(X3)
    | v2_struct_0(X3)
    | v2_struct_0(X1)
    | ~ v10_lattices(X3)
    | X1 != X3
    | k3_lattices(X1,X0,X2) = k3_lattices(X1,X2,X0) ),
    inference(resolution_lifted,[status(thm)],[c_4,c_12])).

cnf(c_634,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l2_lattices(X1)
    | ~ l3_lattices(X1)
    | v2_struct_0(X1)
    | ~ v10_lattices(X1)
    | k3_lattices(X1,X0,X2) = k3_lattices(X1,X2,X0) ),
    inference(unflattening,[status(thm)],[c_633])).

cnf(c_38,plain,
    ( l2_lattices(X0)
    | ~ l3_lattices(X0) ),
    inference(cnf_transformation,[],[f141])).

cnf(c_652,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l3_lattices(X1)
    | v2_struct_0(X1)
    | ~ v10_lattices(X1)
    | k3_lattices(X1,X0,X2) = k3_lattices(X1,X2,X0) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_634,c_38])).

cnf(c_1364,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l3_lattices(X1)
    | v2_struct_0(X1)
    | k3_lattices(X1,X2,X0) = k3_lattices(X1,X0,X2)
    | sK9 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_652,c_52])).

cnf(c_1365,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK9))
    | ~ m1_subset_1(X1,u1_struct_0(sK9))
    | ~ l3_lattices(sK9)
    | v2_struct_0(sK9)
    | k3_lattices(sK9,X1,X0) = k3_lattices(sK9,X0,X1) ),
    inference(unflattening,[status(thm)],[c_1364])).

cnf(c_1369,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK9))
    | ~ m1_subset_1(X1,u1_struct_0(sK9))
    | k3_lattices(sK9,X1,X0) = k3_lattices(sK9,X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1365,c_53,c_50])).

cnf(c_2553,plain,
    ( k3_lattices(sK9,X0,X1) = k3_lattices(sK9,X1,X0)
    | m1_subset_1(X1,u1_struct_0(sK9)) != iProver_top
    | m1_subset_1(X0,u1_struct_0(sK9)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1369])).

cnf(c_3814,plain,
    ( k3_lattices(sK9,sK10,X0) = k3_lattices(sK9,X0,sK10)
    | m1_subset_1(X0,u1_struct_0(sK9)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2570,c_2553])).

cnf(c_3930,plain,
    ( k3_lattices(sK9,k7_lattices(sK9,X0),sK10) = k3_lattices(sK9,sK10,k7_lattices(sK9,X0))
    | m1_subset_1(X0,u1_struct_0(sK9)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2546,c_3814])).

cnf(c_5505,plain,
    ( k3_lattices(sK9,sK10,k7_lattices(sK9,sK10)) = k3_lattices(sK9,k7_lattices(sK9,sK10),sK10) ),
    inference(superposition,[status(thm)],[c_2570,c_3930])).

cnf(c_47,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ v17_lattices(X1)
    | ~ l3_lattices(X1)
    | v2_struct_0(X1)
    | ~ v10_lattices(X1)
    | k3_lattices(X1,k7_lattices(X1,X0),X0) = k6_lattices(X1) ),
    inference(cnf_transformation,[],[f149])).

cnf(c_709,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ l3_lattices(X1)
    | v2_struct_0(X1)
    | ~ v10_lattices(X1)
    | k3_lattices(X1,k7_lattices(X1,X0),X0) = k6_lattices(X1)
    | sK9 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_47,c_51])).

cnf(c_710,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK9))
    | ~ l3_lattices(sK9)
    | v2_struct_0(sK9)
    | ~ v10_lattices(sK9)
    | k3_lattices(sK9,k7_lattices(sK9,X0),X0) = k6_lattices(sK9) ),
    inference(unflattening,[status(thm)],[c_709])).

cnf(c_714,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK9))
    | k3_lattices(sK9,k7_lattices(sK9,X0),X0) = k6_lattices(sK9) ),
    inference(global_propositional_subsumption,[status(thm)],[c_710,c_53,c_52,c_50])).

cnf(c_2569,plain,
    ( k3_lattices(sK9,k7_lattices(sK9,X0),X0) = k6_lattices(sK9)
    | m1_subset_1(X0,u1_struct_0(sK9)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_714])).

cnf(c_3258,plain,
    ( k3_lattices(sK9,k7_lattices(sK9,sK10),sK10) = k6_lattices(sK9) ),
    inference(superposition,[status(thm)],[c_2570,c_2569])).

cnf(c_5510,plain,
    ( k3_lattices(sK9,sK10,k7_lattices(sK9,sK10)) = k6_lattices(sK9) ),
    inference(light_normalisation,[status(thm)],[c_5505,c_3258])).

cnf(c_40,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l2_lattices(X1)
    | ~ v4_lattices(X1)
    | v2_struct_0(X1)
    | k1_lattices(X1,X2,X0) = k3_lattices(X1,X2,X0) ),
    inference(cnf_transformation,[],[f142])).

cnf(c_604,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l2_lattices(X1)
    | ~ l3_lattices(X3)
    | v2_struct_0(X3)
    | v2_struct_0(X1)
    | ~ v10_lattices(X3)
    | X1 != X3
    | k1_lattices(X1,X2,X0) = k3_lattices(X1,X2,X0) ),
    inference(resolution_lifted,[status(thm)],[c_4,c_40])).

cnf(c_605,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l2_lattices(X1)
    | ~ l3_lattices(X1)
    | v2_struct_0(X1)
    | ~ v10_lattices(X1)
    | k1_lattices(X1,X2,X0) = k3_lattices(X1,X2,X0) ),
    inference(unflattening,[status(thm)],[c_604])).

cnf(c_623,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l3_lattices(X1)
    | v2_struct_0(X1)
    | ~ v10_lattices(X1)
    | k1_lattices(X1,X2,X0) = k3_lattices(X1,X2,X0) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_605,c_38])).

cnf(c_1385,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l3_lattices(X1)
    | v2_struct_0(X1)
    | k1_lattices(X1,X2,X0) = k3_lattices(X1,X2,X0)
    | sK9 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_623,c_52])).

cnf(c_1386,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK9))
    | ~ m1_subset_1(X1,u1_struct_0(sK9))
    | ~ l3_lattices(sK9)
    | v2_struct_0(sK9)
    | k1_lattices(sK9,X1,X0) = k3_lattices(sK9,X1,X0) ),
    inference(unflattening,[status(thm)],[c_1385])).

cnf(c_1390,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK9))
    | ~ m1_subset_1(X1,u1_struct_0(sK9))
    | k1_lattices(sK9,X1,X0) = k3_lattices(sK9,X1,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1386,c_53,c_50])).

cnf(c_2552,plain,
    ( k1_lattices(sK9,X0,X1) = k3_lattices(sK9,X0,X1)
    | m1_subset_1(X1,u1_struct_0(sK9)) != iProver_top
    | m1_subset_1(X0,u1_struct_0(sK9)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1390])).

cnf(c_3791,plain,
    ( k1_lattices(sK9,sK10,X0) = k3_lattices(sK9,sK10,X0)
    | m1_subset_1(X0,u1_struct_0(sK9)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2570,c_2552])).

cnf(c_3834,plain,
    ( k1_lattices(sK9,sK10,k7_lattices(sK9,X0)) = k3_lattices(sK9,sK10,k7_lattices(sK9,X0))
    | m1_subset_1(X0,u1_struct_0(sK9)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2546,c_3791])).

cnf(c_5314,plain,
    ( k1_lattices(sK9,sK10,k7_lattices(sK9,sK10)) = k3_lattices(sK9,sK10,k7_lattices(sK9,sK10)) ),
    inference(superposition,[status(thm)],[c_2570,c_3834])).

cnf(c_34,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l3_lattices(X1)
    | v2_struct_0(X1)
    | ~ v9_lattices(X1)
    | k2_lattices(X1,X2,k1_lattices(X1,X2,X0)) = X2 ),
    inference(cnf_transformation,[],[f133])).

cnf(c_1881,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l3_lattices(X1)
    | ~ v9_lattices(X1)
    | k2_lattices(X1,X2,k1_lattices(X1,X2,X0)) = X2
    | sK9 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_34,c_53])).

cnf(c_1882,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK9))
    | ~ m1_subset_1(X1,u1_struct_0(sK9))
    | ~ l3_lattices(sK9)
    | ~ v9_lattices(sK9)
    | k2_lattices(sK9,X1,k1_lattices(sK9,X1,X0)) = X1 ),
    inference(unflattening,[status(thm)],[c_1881])).

cnf(c_1,plain,
    ( ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | ~ v10_lattices(X0)
    | v9_lattices(X0) ),
    inference(cnf_transformation,[],[f107])).

cnf(c_1293,plain,
    ( ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | v9_lattices(X0)
    | sK9 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_1,c_52])).

cnf(c_1294,plain,
    ( ~ l3_lattices(sK9)
    | v2_struct_0(sK9)
    | v9_lattices(sK9) ),
    inference(unflattening,[status(thm)],[c_1293])).

cnf(c_192,plain,
    ( ~ l3_lattices(sK9)
    | v2_struct_0(sK9)
    | ~ v10_lattices(sK9)
    | v9_lattices(sK9) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_1296,plain,
    ( v9_lattices(sK9) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1294,c_53,c_52,c_50,c_192])).

cnf(c_1501,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l3_lattices(X1)
    | v2_struct_0(X1)
    | k2_lattices(X1,X2,k1_lattices(X1,X2,X0)) = X2
    | sK9 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_34,c_1296])).

cnf(c_1502,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK9))
    | ~ m1_subset_1(X1,u1_struct_0(sK9))
    | ~ l3_lattices(sK9)
    | v2_struct_0(sK9)
    | k2_lattices(sK9,X1,k1_lattices(sK9,X1,X0)) = X1 ),
    inference(unflattening,[status(thm)],[c_1501])).

cnf(c_1886,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK9))
    | ~ m1_subset_1(X1,u1_struct_0(sK9))
    | k2_lattices(sK9,X1,k1_lattices(sK9,X1,X0)) = X1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1882,c_53,c_50,c_1502])).

cnf(c_2551,plain,
    ( k2_lattices(sK9,X0,k1_lattices(sK9,X0,X1)) = X0
    | m1_subset_1(X1,u1_struct_0(sK9)) != iProver_top
    | m1_subset_1(X0,u1_struct_0(sK9)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1886])).

cnf(c_3555,plain,
    ( k2_lattices(sK9,sK10,k1_lattices(sK9,sK10,X0)) = sK10
    | m1_subset_1(X0,u1_struct_0(sK9)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2570,c_2551])).

cnf(c_3785,plain,
    ( k2_lattices(sK9,sK10,k1_lattices(sK9,sK10,k7_lattices(sK9,X0))) = sK10
    | m1_subset_1(X0,u1_struct_0(sK9)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2546,c_3555])).

cnf(c_5306,plain,
    ( k2_lattices(sK9,sK10,k1_lattices(sK9,sK10,k7_lattices(sK9,sK10))) = sK10 ),
    inference(superposition,[status(thm)],[c_2570,c_3785])).

cnf(c_5321,plain,
    ( k2_lattices(sK9,sK10,k3_lattices(sK9,sK10,k7_lattices(sK9,sK10))) = sK10 ),
    inference(demodulation,[status(thm)],[c_5314,c_5306])).

cnf(c_5517,plain,
    ( k2_lattices(sK9,sK10,k6_lattices(sK9)) = sK10 ),
    inference(demodulation,[status(thm)],[c_5510,c_5321])).

cnf(c_5529,plain,
    ( k2_lattices(sK9,sK10,k7_lattices(sK9,k7_lattices(sK9,X0))) = k4_lattices(sK9,sK10,k7_lattices(sK9,k7_lattices(sK9,X0)))
    | m1_subset_1(X0,u1_struct_0(sK9)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2546,c_4186])).

cnf(c_36401,plain,
    ( k2_lattices(sK9,sK10,k7_lattices(sK9,k7_lattices(sK9,sK10))) = k4_lattices(sK9,sK10,k7_lattices(sK9,k7_lattices(sK9,sK10))) ),
    inference(superposition,[status(thm)],[c_2570,c_5529])).

cnf(c_3817,plain,
    ( k3_lattices(sK9,X0,k7_lattices(sK9,X1)) = k3_lattices(sK9,k7_lattices(sK9,X1),X0)
    | m1_subset_1(X1,u1_struct_0(sK9)) != iProver_top
    | m1_subset_1(X0,u1_struct_0(sK9)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2546,c_2553])).

cnf(c_18574,plain,
    ( k3_lattices(sK9,k7_lattices(sK9,X0),k7_lattices(sK9,X1)) = k3_lattices(sK9,k7_lattices(sK9,X1),k7_lattices(sK9,X0))
    | m1_subset_1(X1,u1_struct_0(sK9)) != iProver_top
    | m1_subset_1(X0,u1_struct_0(sK9)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2546,c_3817])).

cnf(c_66656,plain,
    ( k3_lattices(sK9,k7_lattices(sK9,X0),k7_lattices(sK9,sK10)) = k3_lattices(sK9,k7_lattices(sK9,sK10),k7_lattices(sK9,X0))
    | m1_subset_1(X0,u1_struct_0(sK9)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2570,c_18574])).

cnf(c_66692,plain,
    ( k3_lattices(sK9,k7_lattices(sK9,k7_lattices(sK9,X0)),k7_lattices(sK9,sK10)) = k3_lattices(sK9,k7_lattices(sK9,sK10),k7_lattices(sK9,k7_lattices(sK9,X0)))
    | m1_subset_1(X0,u1_struct_0(sK9)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2546,c_66656])).

cnf(c_66705,plain,
    ( k3_lattices(sK9,k7_lattices(sK9,sK10),k7_lattices(sK9,k7_lattices(sK9,sK10))) = k3_lattices(sK9,k7_lattices(sK9,k7_lattices(sK9,sK10)),k7_lattices(sK9,sK10)) ),
    inference(superposition,[status(thm)],[c_2570,c_66692])).

cnf(c_3261,plain,
    ( k3_lattices(sK9,k7_lattices(sK9,k7_lattices(sK9,X0)),k7_lattices(sK9,X0)) = k6_lattices(sK9)
    | m1_subset_1(X0,u1_struct_0(sK9)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2546,c_2569])).

cnf(c_15776,plain,
    ( k3_lattices(sK9,k7_lattices(sK9,k7_lattices(sK9,sK10)),k7_lattices(sK9,sK10)) = k6_lattices(sK9) ),
    inference(superposition,[status(thm)],[c_2570,c_3261])).

cnf(c_66713,plain,
    ( k3_lattices(sK9,k7_lattices(sK9,sK10),k7_lattices(sK9,k7_lattices(sK9,sK10))) = k6_lattices(sK9) ),
    inference(light_normalisation,[status(thm)],[c_66705,c_15776])).

cnf(c_3794,plain,
    ( k1_lattices(sK9,k7_lattices(sK9,X0),X1) = k3_lattices(sK9,k7_lattices(sK9,X0),X1)
    | m1_subset_1(X0,u1_struct_0(sK9)) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK9)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2546,c_2552])).

cnf(c_18136,plain,
    ( k1_lattices(sK9,k7_lattices(sK9,sK10),X0) = k3_lattices(sK9,k7_lattices(sK9,sK10),X0)
    | m1_subset_1(X0,u1_struct_0(sK9)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2570,c_3794])).

cnf(c_18195,plain,
    ( k1_lattices(sK9,k7_lattices(sK9,sK10),k7_lattices(sK9,X0)) = k3_lattices(sK9,k7_lattices(sK9,sK10),k7_lattices(sK9,X0))
    | m1_subset_1(X0,u1_struct_0(sK9)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2546,c_18136])).

cnf(c_18987,plain,
    ( k1_lattices(sK9,k7_lattices(sK9,sK10),k7_lattices(sK9,k7_lattices(sK9,X0))) = k3_lattices(sK9,k7_lattices(sK9,sK10),k7_lattices(sK9,k7_lattices(sK9,X0)))
    | m1_subset_1(X0,u1_struct_0(sK9)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2546,c_18195])).

cnf(c_50973,plain,
    ( k1_lattices(sK9,k7_lattices(sK9,sK10),k7_lattices(sK9,k7_lattices(sK9,sK10))) = k3_lattices(sK9,k7_lattices(sK9,sK10),k7_lattices(sK9,k7_lattices(sK9,sK10))) ),
    inference(superposition,[status(thm)],[c_2570,c_18987])).

cnf(c_66768,plain,
    ( k1_lattices(sK9,k7_lattices(sK9,sK10),k7_lattices(sK9,k7_lattices(sK9,sK10))) = k6_lattices(sK9) ),
    inference(demodulation,[status(thm)],[c_66713,c_50973])).

cnf(c_35,plain,
    ( m1_subset_1(k5_lattices(X0),u1_struct_0(X0))
    | ~ l1_lattices(X0)
    | v2_struct_0(X0) ),
    inference(cnf_transformation,[],[f137])).

cnf(c_998,plain,
    ( m1_subset_1(k5_lattices(X0),u1_struct_0(X0))
    | ~ l3_lattices(X0)
    | v2_struct_0(X0) ),
    inference(resolution,[status(thm)],[c_39,c_35])).

cnf(c_1821,plain,
    ( m1_subset_1(k5_lattices(X0),u1_struct_0(X0))
    | ~ l3_lattices(X0)
    | sK9 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_998,c_53])).

cnf(c_1822,plain,
    ( m1_subset_1(k5_lattices(sK9),u1_struct_0(sK9))
    | ~ l3_lattices(sK9) ),
    inference(unflattening,[status(thm)],[c_1821])).

cnf(c_84,plain,
    ( l1_lattices(sK9)
    | ~ l3_lattices(sK9) ),
    inference(instantiation,[status(thm)],[c_39])).

cnf(c_96,plain,
    ( m1_subset_1(k5_lattices(sK9),u1_struct_0(sK9))
    | ~ l1_lattices(sK9)
    | v2_struct_0(sK9) ),
    inference(instantiation,[status(thm)],[c_35])).

cnf(c_1824,plain,
    ( m1_subset_1(k5_lattices(sK9),u1_struct_0(sK9)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1822,c_53,c_50,c_84,c_96])).

cnf(c_2548,plain,
    ( m1_subset_1(k5_lattices(sK9),u1_struct_0(sK9)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1824])).

cnf(c_3243,plain,
    ( k1_lattices(sK9,k2_lattices(sK9,sK10,k5_lattices(sK9)),k2_lattices(sK9,sK10,X0)) = k2_lattices(sK9,sK10,k1_lattices(sK9,k5_lattices(sK9),X0))
    | m1_subset_1(X0,u1_struct_0(sK9)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2548,c_3214])).

cnf(c_4211,plain,
    ( k4_lattices(sK9,sK10,k5_lattices(sK9)) = k4_lattices(sK9,k5_lattices(sK9),sK10) ),
    inference(superposition,[status(thm)],[c_2548,c_4192])).

cnf(c_44,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ v13_lattices(X1)
    | ~ l3_lattices(X1)
    | v2_struct_0(X1)
    | ~ v10_lattices(X1)
    | k4_lattices(X1,k5_lattices(X1),X0) = k5_lattices(X1) ),
    inference(cnf_transformation,[],[f146])).

cnf(c_9,plain,
    ( ~ v17_lattices(X0)
    | v15_lattices(X0)
    | ~ l3_lattices(X0)
    | v2_struct_0(X0) ),
    inference(cnf_transformation,[],[f113])).

cnf(c_7,plain,
    ( v13_lattices(X0)
    | ~ v15_lattices(X0)
    | ~ l3_lattices(X0)
    | v2_struct_0(X0) ),
    inference(cnf_transformation,[],[f109])).

cnf(c_560,plain,
    ( ~ v17_lattices(X0)
    | v13_lattices(X0)
    | ~ l3_lattices(X0)
    | v2_struct_0(X0) ),
    inference(resolution,[status(thm)],[c_9,c_7])).

cnf(c_687,plain,
    ( v13_lattices(X0)
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | sK9 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_560,c_51])).

cnf(c_688,plain,
    ( v13_lattices(sK9)
    | ~ l3_lattices(sK9)
    | v2_struct_0(sK9) ),
    inference(unflattening,[status(thm)],[c_687])).

cnf(c_172,plain,
    ( ~ v17_lattices(sK9)
    | v15_lattices(sK9)
    | ~ l3_lattices(sK9)
    | v2_struct_0(sK9) ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_176,plain,
    ( v13_lattices(sK9)
    | ~ v15_lattices(sK9)
    | ~ l3_lattices(sK9)
    | v2_struct_0(sK9) ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_690,plain,
    ( v13_lattices(sK9) ),
    inference(global_propositional_subsumption,[status(thm)],[c_688,c_53,c_51,c_50,c_172,c_176])).

cnf(c_1225,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ l3_lattices(X1)
    | v2_struct_0(X1)
    | ~ v10_lattices(X1)
    | k4_lattices(X1,k5_lattices(X1),X0) = k5_lattices(X1)
    | sK9 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_44,c_690])).

cnf(c_1226,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK9))
    | ~ l3_lattices(sK9)
    | v2_struct_0(sK9)
    | ~ v10_lattices(sK9)
    | k4_lattices(sK9,k5_lattices(sK9),X0) = k5_lattices(sK9) ),
    inference(unflattening,[status(thm)],[c_1225])).

cnf(c_1230,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK9))
    | k4_lattices(sK9,k5_lattices(sK9),X0) = k5_lattices(sK9) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1226,c_53,c_52,c_50])).

cnf(c_2558,plain,
    ( k4_lattices(sK9,k5_lattices(sK9),X0) = k5_lattices(sK9)
    | m1_subset_1(X0,u1_struct_0(sK9)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1230])).

cnf(c_5258,plain,
    ( k4_lattices(sK9,k5_lattices(sK9),sK10) = k5_lattices(sK9) ),
    inference(superposition,[status(thm)],[c_2570,c_2558])).

cnf(c_5282,plain,
    ( k4_lattices(sK9,sK10,k5_lattices(sK9)) = k5_lattices(sK9) ),
    inference(light_normalisation,[status(thm)],[c_4211,c_5258])).

cnf(c_4185,plain,
    ( k2_lattices(sK9,sK10,k5_lattices(sK9)) = k4_lattices(sK9,sK10,k5_lattices(sK9)) ),
    inference(superposition,[status(thm)],[c_2548,c_4038])).

cnf(c_5283,plain,
    ( k2_lattices(sK9,sK10,k5_lattices(sK9)) = k5_lattices(sK9) ),
    inference(demodulation,[status(thm)],[c_5282,c_4185])).

cnf(c_13256,plain,
    ( k1_lattices(sK9,k5_lattices(sK9),k2_lattices(sK9,sK10,X0)) = k2_lattices(sK9,sK10,k1_lattices(sK9,k5_lattices(sK9),X0))
    | m1_subset_1(X0,u1_struct_0(sK9)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3243,c_5283])).

cnf(c_13265,plain,
    ( k1_lattices(sK9,k5_lattices(sK9),k2_lattices(sK9,sK10,k7_lattices(sK9,X0))) = k2_lattices(sK9,sK10,k1_lattices(sK9,k5_lattices(sK9),k7_lattices(sK9,X0)))
    | m1_subset_1(X0,u1_struct_0(sK9)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2546,c_13256])).

cnf(c_50708,plain,
    ( k1_lattices(sK9,k5_lattices(sK9),k2_lattices(sK9,sK10,k7_lattices(sK9,k7_lattices(sK9,X0)))) = k2_lattices(sK9,sK10,k1_lattices(sK9,k5_lattices(sK9),k7_lattices(sK9,k7_lattices(sK9,X0))))
    | m1_subset_1(X0,u1_struct_0(sK9)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2546,c_13265])).

cnf(c_67436,plain,
    ( k1_lattices(sK9,k5_lattices(sK9),k2_lattices(sK9,sK10,k7_lattices(sK9,k7_lattices(sK9,sK10)))) = k2_lattices(sK9,sK10,k1_lattices(sK9,k5_lattices(sK9),k7_lattices(sK9,k7_lattices(sK9,sK10)))) ),
    inference(superposition,[status(thm)],[c_2570,c_50708])).

cnf(c_3793,plain,
    ( k1_lattices(sK9,k5_lattices(sK9),X0) = k3_lattices(sK9,k5_lattices(sK9),X0)
    | m1_subset_1(X0,u1_struct_0(sK9)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2548,c_2552])).

cnf(c_8049,plain,
    ( k1_lattices(sK9,k5_lattices(sK9),k7_lattices(sK9,X0)) = k3_lattices(sK9,k5_lattices(sK9),k7_lattices(sK9,X0))
    | m1_subset_1(X0,u1_struct_0(sK9)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2546,c_3793])).

cnf(c_20330,plain,
    ( k1_lattices(sK9,k5_lattices(sK9),k7_lattices(sK9,k7_lattices(sK9,X0))) = k3_lattices(sK9,k5_lattices(sK9),k7_lattices(sK9,k7_lattices(sK9,X0)))
    | m1_subset_1(X0,u1_struct_0(sK9)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2546,c_8049])).

cnf(c_48869,plain,
    ( k1_lattices(sK9,k5_lattices(sK9),k7_lattices(sK9,k7_lattices(sK9,sK10))) = k3_lattices(sK9,k5_lattices(sK9),k7_lattices(sK9,k7_lattices(sK9,sK10))) ),
    inference(superposition,[status(thm)],[c_2570,c_20330])).

cnf(c_43,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ v13_lattices(X1)
    | ~ l3_lattices(X1)
    | v2_struct_0(X1)
    | ~ v10_lattices(X1)
    | k3_lattices(X1,k5_lattices(X1),X0) = X0 ),
    inference(cnf_transformation,[],[f145])).

cnf(c_1243,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ l3_lattices(X1)
    | v2_struct_0(X1)
    | ~ v10_lattices(X1)
    | k3_lattices(X1,k5_lattices(X1),X0) = X0
    | sK9 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_43,c_690])).

cnf(c_1244,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK9))
    | ~ l3_lattices(sK9)
    | v2_struct_0(sK9)
    | ~ v10_lattices(sK9)
    | k3_lattices(sK9,k5_lattices(sK9),X0) = X0 ),
    inference(unflattening,[status(thm)],[c_1243])).

cnf(c_1248,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK9))
    | k3_lattices(sK9,k5_lattices(sK9),X0) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1244,c_53,c_52,c_50])).

cnf(c_2557,plain,
    ( k3_lattices(sK9,k5_lattices(sK9),X0) = X0
    | m1_subset_1(X0,u1_struct_0(sK9)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1248])).

cnf(c_4562,plain,
    ( k3_lattices(sK9,k5_lattices(sK9),k7_lattices(sK9,X0)) = k7_lattices(sK9,X0)
    | m1_subset_1(X0,u1_struct_0(sK9)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2546,c_2557])).

cnf(c_9685,plain,
    ( k3_lattices(sK9,k5_lattices(sK9),k7_lattices(sK9,k7_lattices(sK9,X0))) = k7_lattices(sK9,k7_lattices(sK9,X0))
    | m1_subset_1(X0,u1_struct_0(sK9)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2546,c_4562])).

cnf(c_25069,plain,
    ( k3_lattices(sK9,k5_lattices(sK9),k7_lattices(sK9,k7_lattices(sK9,sK10))) = k7_lattices(sK9,k7_lattices(sK9,sK10)) ),
    inference(superposition,[status(thm)],[c_2570,c_9685])).

cnf(c_48877,plain,
    ( k1_lattices(sK9,k5_lattices(sK9),k7_lattices(sK9,k7_lattices(sK9,sK10))) = k7_lattices(sK9,k7_lattices(sK9,sK10)) ),
    inference(light_normalisation,[status(thm)],[c_48869,c_25069])).

cnf(c_67445,plain,
    ( k1_lattices(sK9,k5_lattices(sK9),k4_lattices(sK9,sK10,k7_lattices(sK9,k7_lattices(sK9,sK10)))) = k4_lattices(sK9,sK10,k7_lattices(sK9,k7_lattices(sK9,sK10))) ),
    inference(light_normalisation,[status(thm)],[c_67436,c_36401,c_48877])).

cnf(c_70485,plain,
    ( k4_lattices(sK9,sK10,k7_lattices(sK9,k7_lattices(sK9,sK10))) = sK10 ),
    inference(light_normalisation,[status(thm)],[c_70476,c_5517,c_36401,c_66768,c_67445])).

cnf(c_4041,plain,
    ( k2_lattices(sK9,k7_lattices(sK9,X0),X1) = k4_lattices(sK9,k7_lattices(sK9,X0),X1)
    | m1_subset_1(X0,u1_struct_0(sK9)) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK9)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2546,c_2555])).

cnf(c_24533,plain,
    ( k2_lattices(sK9,k7_lattices(sK9,k7_lattices(sK9,X0)),X1) = k4_lattices(sK9,k7_lattices(sK9,k7_lattices(sK9,X0)),X1)
    | m1_subset_1(X0,u1_struct_0(sK9)) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK9)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2546,c_4041])).

cnf(c_66836,plain,
    ( k2_lattices(sK9,k7_lattices(sK9,k7_lattices(sK9,sK10)),X0) = k4_lattices(sK9,k7_lattices(sK9,k7_lattices(sK9,sK10)),X0)
    | m1_subset_1(X0,u1_struct_0(sK9)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2570,c_24533])).

cnf(c_66876,plain,
    ( k2_lattices(sK9,k7_lattices(sK9,k7_lattices(sK9,sK10)),sK10) = k4_lattices(sK9,k7_lattices(sK9,k7_lattices(sK9,sK10)),sK10) ),
    inference(superposition,[status(thm)],[c_2570,c_66836])).

cnf(c_5557,plain,
    ( k4_lattices(sK9,k7_lattices(sK9,k7_lattices(sK9,X0)),sK10) = k4_lattices(sK9,sK10,k7_lattices(sK9,k7_lattices(sK9,X0)))
    | m1_subset_1(X0,u1_struct_0(sK9)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2546,c_4212])).

cnf(c_36910,plain,
    ( k4_lattices(sK9,sK10,k7_lattices(sK9,k7_lattices(sK9,sK10))) = k4_lattices(sK9,k7_lattices(sK9,k7_lattices(sK9,sK10)),sK10) ),
    inference(superposition,[status(thm)],[c_2570,c_5557])).

cnf(c_66884,plain,
    ( k2_lattices(sK9,k7_lattices(sK9,k7_lattices(sK9,sK10)),sK10) = k4_lattices(sK9,sK10,k7_lattices(sK9,k7_lattices(sK9,sK10))) ),
    inference(light_normalisation,[status(thm)],[c_66876,c_36910])).

cnf(c_70497,plain,
    ( k2_lattices(sK9,k7_lattices(sK9,k7_lattices(sK9,sK10)),sK10) = sK10 ),
    inference(demodulation,[status(thm)],[c_70485,c_66884])).

cnf(c_193838,plain,
    ( k1_lattices(sK9,sK10,k2_lattices(sK9,k7_lattices(sK9,k7_lattices(sK9,sK10)),X0)) = k2_lattices(sK9,k7_lattices(sK9,k7_lattices(sK9,sK10)),k1_lattices(sK9,sK10,X0))
    | m1_subset_1(X0,u1_struct_0(sK9)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_193830,c_70497])).

cnf(c_193901,plain,
    ( k1_lattices(sK9,sK10,k2_lattices(sK9,k7_lattices(sK9,k7_lattices(sK9,sK10)),k7_lattices(sK9,X0))) = k2_lattices(sK9,k7_lattices(sK9,k7_lattices(sK9,sK10)),k1_lattices(sK9,sK10,k7_lattices(sK9,X0)))
    | m1_subset_1(X0,u1_struct_0(sK9)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2546,c_193838])).

cnf(c_193963,plain,
    ( k1_lattices(sK9,sK10,k2_lattices(sK9,k7_lattices(sK9,k7_lattices(sK9,sK10)),k7_lattices(sK9,sK10))) = k2_lattices(sK9,k7_lattices(sK9,k7_lattices(sK9,sK10)),k1_lattices(sK9,sK10,k7_lattices(sK9,sK10))) ),
    inference(superposition,[status(thm)],[c_2570,c_193901])).

cnf(c_3929,plain,
    ( k3_lattices(sK9,sK10,k5_lattices(sK9)) = k3_lattices(sK9,k5_lattices(sK9),sK10) ),
    inference(superposition,[status(thm)],[c_2548,c_3814])).

cnf(c_4559,plain,
    ( k3_lattices(sK9,k5_lattices(sK9),sK10) = sK10 ),
    inference(superposition,[status(thm)],[c_2570,c_2557])).

cnf(c_5274,plain,
    ( k3_lattices(sK9,sK10,k5_lattices(sK9)) = sK10 ),
    inference(light_normalisation,[status(thm)],[c_3929,c_4559])).

cnf(c_3833,plain,
    ( k1_lattices(sK9,sK10,k5_lattices(sK9)) = k3_lattices(sK9,sK10,k5_lattices(sK9)) ),
    inference(superposition,[status(thm)],[c_2548,c_3791])).

cnf(c_5275,plain,
    ( k1_lattices(sK9,sK10,k5_lattices(sK9)) = sK10 ),
    inference(demodulation,[status(thm)],[c_5274,c_3833])).

cnf(c_5518,plain,
    ( k1_lattices(sK9,sK10,k7_lattices(sK9,sK10)) = k6_lattices(sK9) ),
    inference(demodulation,[status(thm)],[c_5510,c_5314])).

cnf(c_66881,plain,
    ( k2_lattices(sK9,k7_lattices(sK9,k7_lattices(sK9,sK10)),k7_lattices(sK9,X0)) = k4_lattices(sK9,k7_lattices(sK9,k7_lattices(sK9,sK10)),k7_lattices(sK9,X0))
    | m1_subset_1(X0,u1_struct_0(sK9)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2546,c_66836])).

cnf(c_66940,plain,
    ( k2_lattices(sK9,k7_lattices(sK9,k7_lattices(sK9,sK10)),k7_lattices(sK9,sK10)) = k4_lattices(sK9,k7_lattices(sK9,k7_lattices(sK9,sK10)),k7_lattices(sK9,sK10)) ),
    inference(superposition,[status(thm)],[c_2570,c_66881])).

cnf(c_3143,plain,
    ( k4_lattices(sK9,k7_lattices(sK9,k7_lattices(sK9,X0)),k7_lattices(sK9,X0)) = k5_lattices(sK9)
    | m1_subset_1(X0,u1_struct_0(sK9)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2546,c_2568])).

cnf(c_6472,plain,
    ( k4_lattices(sK9,k7_lattices(sK9,k7_lattices(sK9,sK10)),k7_lattices(sK9,sK10)) = k5_lattices(sK9) ),
    inference(superposition,[status(thm)],[c_2570,c_3143])).

cnf(c_66948,plain,
    ( k2_lattices(sK9,k7_lattices(sK9,k7_lattices(sK9,sK10)),k7_lattices(sK9,sK10)) = k5_lattices(sK9) ),
    inference(light_normalisation,[status(thm)],[c_66940,c_6472])).

cnf(c_36,plain,
    ( m1_subset_1(k6_lattices(X0),u1_struct_0(X0))
    | ~ l2_lattices(X0)
    | v2_struct_0(X0) ),
    inference(cnf_transformation,[],[f138])).

cnf(c_980,plain,
    ( m1_subset_1(k6_lattices(X0),u1_struct_0(X0))
    | ~ l3_lattices(X0)
    | v2_struct_0(X0) ),
    inference(resolution,[status(thm)],[c_38,c_36])).

cnf(c_1832,plain,
    ( m1_subset_1(k6_lattices(X0),u1_struct_0(X0))
    | ~ l3_lattices(X0)
    | sK9 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_980,c_53])).

cnf(c_1833,plain,
    ( m1_subset_1(k6_lattices(sK9),u1_struct_0(sK9))
    | ~ l3_lattices(sK9) ),
    inference(unflattening,[status(thm)],[c_1832])).

cnf(c_87,plain,
    ( l2_lattices(sK9)
    | ~ l3_lattices(sK9) ),
    inference(instantiation,[status(thm)],[c_38])).

cnf(c_93,plain,
    ( m1_subset_1(k6_lattices(sK9),u1_struct_0(sK9))
    | ~ l2_lattices(sK9)
    | v2_struct_0(sK9) ),
    inference(instantiation,[status(thm)],[c_36])).

cnf(c_1835,plain,
    ( m1_subset_1(k6_lattices(sK9),u1_struct_0(sK9)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1833,c_53,c_50,c_87,c_93])).

cnf(c_2547,plain,
    ( m1_subset_1(k6_lattices(sK9),u1_struct_0(sK9)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1835])).

cnf(c_3558,plain,
    ( k2_lattices(sK9,k7_lattices(sK9,X0),k1_lattices(sK9,k7_lattices(sK9,X0),X1)) = k7_lattices(sK9,X0)
    | m1_subset_1(X0,u1_struct_0(sK9)) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK9)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2546,c_2551])).

cnf(c_17824,plain,
    ( k2_lattices(sK9,k7_lattices(sK9,k7_lattices(sK9,X0)),k1_lattices(sK9,k7_lattices(sK9,k7_lattices(sK9,X0)),X1)) = k7_lattices(sK9,k7_lattices(sK9,X0))
    | m1_subset_1(X0,u1_struct_0(sK9)) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK9)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2546,c_3558])).

cnf(c_87990,plain,
    ( k2_lattices(sK9,k7_lattices(sK9,k7_lattices(sK9,sK10)),k1_lattices(sK9,k7_lattices(sK9,k7_lattices(sK9,sK10)),X0)) = k7_lattices(sK9,k7_lattices(sK9,sK10))
    | m1_subset_1(X0,u1_struct_0(sK9)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2570,c_17824])).

cnf(c_88040,plain,
    ( k2_lattices(sK9,k7_lattices(sK9,k7_lattices(sK9,sK10)),k1_lattices(sK9,k7_lattices(sK9,k7_lattices(sK9,sK10)),k6_lattices(sK9))) = k7_lattices(sK9,k7_lattices(sK9,sK10)) ),
    inference(superposition,[status(thm)],[c_2547,c_87990])).

cnf(c_25,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(k6_lattices(X1),u1_struct_0(X1))
    | ~ l2_lattices(X1)
    | ~ v14_lattices(X1)
    | v2_struct_0(X1)
    | k1_lattices(X1,X0,k6_lattices(X1)) = k6_lattices(X1) ),
    inference(cnf_transformation,[],[f158])).

cnf(c_6,plain,
    ( ~ v15_lattices(X0)
    | v14_lattices(X0)
    | ~ l3_lattices(X0)
    | v2_struct_0(X0) ),
    inference(cnf_transformation,[],[f110])).

cnf(c_577,plain,
    ( ~ v17_lattices(X0)
    | v14_lattices(X0)
    | ~ l3_lattices(X0)
    | v2_struct_0(X0) ),
    inference(resolution,[status(thm)],[c_9,c_6])).

cnf(c_676,plain,
    ( v14_lattices(X0)
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | sK9 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_577,c_51])).

cnf(c_677,plain,
    ( v14_lattices(sK9)
    | ~ l3_lattices(sK9)
    | v2_struct_0(sK9) ),
    inference(unflattening,[status(thm)],[c_676])).

cnf(c_179,plain,
    ( ~ v15_lattices(sK9)
    | v14_lattices(sK9)
    | ~ l3_lattices(sK9)
    | v2_struct_0(sK9) ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_679,plain,
    ( v14_lattices(sK9) ),
    inference(global_propositional_subsumption,[status(thm)],[c_677,c_53,c_51,c_50,c_172,c_179])).

cnf(c_899,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(k6_lattices(X1),u1_struct_0(X1))
    | ~ l2_lattices(X1)
    | v2_struct_0(X1)
    | k1_lattices(X1,X0,k6_lattices(X1)) = k6_lattices(X1)
    | sK9 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_25,c_679])).

cnf(c_900,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK9))
    | ~ m1_subset_1(k6_lattices(sK9),u1_struct_0(sK9))
    | ~ l2_lattices(sK9)
    | v2_struct_0(sK9)
    | k1_lattices(sK9,X0,k6_lattices(sK9)) = k6_lattices(sK9) ),
    inference(unflattening,[status(thm)],[c_899])).

cnf(c_904,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK9))
    | k1_lattices(sK9,X0,k6_lattices(sK9)) = k6_lattices(sK9) ),
    inference(global_propositional_subsumption,[status(thm)],[c_900,c_53,c_50,c_87,c_93])).

cnf(c_2565,plain,
    ( k1_lattices(sK9,X0,k6_lattices(sK9)) = k6_lattices(sK9)
    | m1_subset_1(X0,u1_struct_0(sK9)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_904])).

cnf(c_5541,plain,
    ( k1_lattices(sK9,k7_lattices(sK9,X0),k6_lattices(sK9)) = k6_lattices(sK9)
    | m1_subset_1(X0,u1_struct_0(sK9)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2546,c_2565])).

cnf(c_6152,plain,
    ( k1_lattices(sK9,k7_lattices(sK9,k7_lattices(sK9,X0)),k6_lattices(sK9)) = k6_lattices(sK9)
    | m1_subset_1(X0,u1_struct_0(sK9)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2546,c_5541])).

cnf(c_13240,plain,
    ( k1_lattices(sK9,k7_lattices(sK9,k7_lattices(sK9,sK10)),k6_lattices(sK9)) = k6_lattices(sK9) ),
    inference(superposition,[status(thm)],[c_2570,c_6152])).

cnf(c_66877,plain,
    ( k2_lattices(sK9,k7_lattices(sK9,k7_lattices(sK9,sK10)),k6_lattices(sK9)) = k4_lattices(sK9,k7_lattices(sK9,k7_lattices(sK9,sK10)),k6_lattices(sK9)) ),
    inference(superposition,[status(thm)],[c_2547,c_66836])).

cnf(c_4193,plain,
    ( k4_lattices(sK9,k6_lattices(sK9),X0) = k4_lattices(sK9,X0,k6_lattices(sK9))
    | m1_subset_1(X0,u1_struct_0(sK9)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2547,c_2556])).

cnf(c_8887,plain,
    ( k4_lattices(sK9,k7_lattices(sK9,X0),k6_lattices(sK9)) = k4_lattices(sK9,k6_lattices(sK9),k7_lattices(sK9,X0))
    | m1_subset_1(X0,u1_struct_0(sK9)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2546,c_4193])).

cnf(c_24409,plain,
    ( k4_lattices(sK9,k7_lattices(sK9,k7_lattices(sK9,X0)),k6_lattices(sK9)) = k4_lattices(sK9,k6_lattices(sK9),k7_lattices(sK9,k7_lattices(sK9,X0)))
    | m1_subset_1(X0,u1_struct_0(sK9)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2546,c_8887])).

cnf(c_49315,plain,
    ( k4_lattices(sK9,k6_lattices(sK9),k7_lattices(sK9,k7_lattices(sK9,sK10))) = k4_lattices(sK9,k7_lattices(sK9,k7_lattices(sK9,sK10)),k6_lattices(sK9)) ),
    inference(superposition,[status(thm)],[c_2570,c_24409])).

cnf(c_66883,plain,
    ( k2_lattices(sK9,k7_lattices(sK9,k7_lattices(sK9,sK10)),k6_lattices(sK9)) = k4_lattices(sK9,k6_lattices(sK9),k7_lattices(sK9,k7_lattices(sK9,sK10))) ),
    inference(light_normalisation,[status(thm)],[c_66877,c_49315])).

cnf(c_88046,plain,
    ( k4_lattices(sK9,k6_lattices(sK9),k7_lattices(sK9,k7_lattices(sK9,sK10))) = k7_lattices(sK9,k7_lattices(sK9,sK10)) ),
    inference(light_normalisation,[status(thm)],[c_88040,c_13240,c_66883])).

cnf(c_88058,plain,
    ( k2_lattices(sK9,k7_lattices(sK9,k7_lattices(sK9,sK10)),k6_lattices(sK9)) = k7_lattices(sK9,k7_lattices(sK9,sK10)) ),
    inference(demodulation,[status(thm)],[c_88046,c_66883])).

cnf(c_193973,plain,
    ( k7_lattices(sK9,k7_lattices(sK9,sK10)) = sK10 ),
    inference(light_normalisation,[status(thm)],[c_193963,c_5275,c_5518,c_66948,c_88058])).

cnf(c_48,negated_conjecture,
    ( k7_lattices(sK9,k7_lattices(sK9,sK10)) != sK10 ),
    inference(cnf_transformation,[],[f155])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_193973,c_48])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : iproveropt_run.sh %d %s
% 0.11/0.33  % Computer   : n013.cluster.edu
% 0.11/0.33  % Model      : x86_64 x86_64
% 0.11/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.11/0.33  % Memory     : 8042.1875MB
% 0.11/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.11/0.33  % CPULimit   : 60
% 0.11/0.33  % WCLimit    : 600
% 0.11/0.33  % DateTime   : Tue Dec  1 18:23:24 EST 2020
% 0.11/0.33  % CPUTime    : 
% 0.11/0.34  % Running in FOF mode
% 58.61/8.00  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 58.61/8.00  
% 58.61/8.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 58.61/8.00  
% 58.61/8.00  ------  iProver source info
% 58.61/8.00  
% 58.61/8.00  git: date: 2020-06-30 10:37:57 +0100
% 58.61/8.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 58.61/8.00  git: non_committed_changes: false
% 58.61/8.00  git: last_make_outside_of_git: false
% 58.61/8.00  
% 58.61/8.00  ------ 
% 58.61/8.00  
% 58.61/8.00  ------ Input Options
% 58.61/8.00  
% 58.61/8.00  --out_options                           all
% 58.61/8.00  --tptp_safe_out                         true
% 58.61/8.00  --problem_path                          ""
% 58.61/8.00  --include_path                          ""
% 58.61/8.00  --clausifier                            res/vclausify_rel
% 58.61/8.00  --clausifier_options                    ""
% 58.61/8.00  --stdin                                 false
% 58.61/8.00  --stats_out                             all
% 58.61/8.00  
% 58.61/8.00  ------ General Options
% 58.61/8.00  
% 58.61/8.00  --fof                                   false
% 58.61/8.00  --time_out_real                         305.
% 58.61/8.00  --time_out_virtual                      -1.
% 58.61/8.00  --symbol_type_check                     false
% 58.61/8.00  --clausify_out                          false
% 58.61/8.00  --sig_cnt_out                           false
% 58.61/8.00  --trig_cnt_out                          false
% 58.61/8.00  --trig_cnt_out_tolerance                1.
% 58.61/8.00  --trig_cnt_out_sk_spl                   false
% 58.61/8.00  --abstr_cl_out                          false
% 58.61/8.00  
% 58.61/8.00  ------ Global Options
% 58.61/8.00  
% 58.61/8.00  --schedule                              default
% 58.61/8.00  --add_important_lit                     false
% 58.61/8.00  --prop_solver_per_cl                    1000
% 58.61/8.00  --min_unsat_core                        false
% 58.61/8.00  --soft_assumptions                      false
% 58.61/8.00  --soft_lemma_size                       3
% 58.61/8.00  --prop_impl_unit_size                   0
% 58.61/8.00  --prop_impl_unit                        []
% 58.61/8.00  --share_sel_clauses                     true
% 58.61/8.00  --reset_solvers                         false
% 58.61/8.00  --bc_imp_inh                            [conj_cone]
% 58.61/8.00  --conj_cone_tolerance                   3.
% 58.61/8.00  --extra_neg_conj                        none
% 58.61/8.00  --large_theory_mode                     true
% 58.61/8.00  --prolific_symb_bound                   200
% 58.61/8.00  --lt_threshold                          2000
% 58.61/8.00  --clause_weak_htbl                      true
% 58.61/8.00  --gc_record_bc_elim                     false
% 58.61/8.00  
% 58.61/8.00  ------ Preprocessing Options
% 58.61/8.00  
% 58.61/8.00  --preprocessing_flag                    true
% 58.61/8.00  --time_out_prep_mult                    0.1
% 58.61/8.00  --splitting_mode                        input
% 58.61/8.00  --splitting_grd                         true
% 58.61/8.00  --splitting_cvd                         false
% 58.61/8.00  --splitting_cvd_svl                     false
% 58.61/8.00  --splitting_nvd                         32
% 58.61/8.00  --sub_typing                            true
% 58.61/8.00  --prep_gs_sim                           true
% 58.61/8.00  --prep_unflatten                        true
% 58.61/8.00  --prep_res_sim                          true
% 58.61/8.00  --prep_upred                            true
% 58.61/8.00  --prep_sem_filter                       exhaustive
% 58.61/8.00  --prep_sem_filter_out                   false
% 58.61/8.00  --pred_elim                             true
% 58.61/8.00  --res_sim_input                         true
% 58.61/8.00  --eq_ax_congr_red                       true
% 58.61/8.00  --pure_diseq_elim                       true
% 58.61/8.00  --brand_transform                       false
% 58.61/8.00  --non_eq_to_eq                          false
% 58.61/8.00  --prep_def_merge                        true
% 58.61/8.00  --prep_def_merge_prop_impl              false
% 58.61/8.00  --prep_def_merge_mbd                    true
% 58.61/8.00  --prep_def_merge_tr_red                 false
% 58.61/8.00  --prep_def_merge_tr_cl                  false
% 58.61/8.00  --smt_preprocessing                     true
% 58.61/8.00  --smt_ac_axioms                         fast
% 58.61/8.00  --preprocessed_out                      false
% 58.61/8.00  --preprocessed_stats                    false
% 58.61/8.00  
% 58.61/8.00  ------ Abstraction refinement Options
% 58.61/8.00  
% 58.61/8.00  --abstr_ref                             []
% 58.61/8.00  --abstr_ref_prep                        false
% 58.61/8.00  --abstr_ref_until_sat                   false
% 58.61/8.00  --abstr_ref_sig_restrict                funpre
% 58.61/8.00  --abstr_ref_af_restrict_to_split_sk     false
% 58.61/8.00  --abstr_ref_under                       []
% 58.61/8.00  
% 58.61/8.00  ------ SAT Options
% 58.61/8.00  
% 58.61/8.00  --sat_mode                              false
% 58.61/8.00  --sat_fm_restart_options                ""
% 58.61/8.00  --sat_gr_def                            false
% 58.61/8.00  --sat_epr_types                         true
% 58.61/8.00  --sat_non_cyclic_types                  false
% 58.61/8.00  --sat_finite_models                     false
% 58.61/8.00  --sat_fm_lemmas                         false
% 58.61/8.00  --sat_fm_prep                           false
% 58.61/8.00  --sat_fm_uc_incr                        true
% 58.61/8.00  --sat_out_model                         small
% 58.61/8.00  --sat_out_clauses                       false
% 58.61/8.00  
% 58.61/8.00  ------ QBF Options
% 58.61/8.00  
% 58.61/8.00  --qbf_mode                              false
% 58.61/8.00  --qbf_elim_univ                         false
% 58.61/8.00  --qbf_dom_inst                          none
% 58.61/8.00  --qbf_dom_pre_inst                      false
% 58.61/8.00  --qbf_sk_in                             false
% 58.61/8.00  --qbf_pred_elim                         true
% 58.61/8.00  --qbf_split                             512
% 58.61/8.00  
% 58.61/8.00  ------ BMC1 Options
% 58.61/8.00  
% 58.61/8.00  --bmc1_incremental                      false
% 58.61/8.00  --bmc1_axioms                           reachable_all
% 58.61/8.00  --bmc1_min_bound                        0
% 58.61/8.00  --bmc1_max_bound                        -1
% 58.61/8.00  --bmc1_max_bound_default                -1
% 58.61/8.00  --bmc1_symbol_reachability              true
% 58.61/8.00  --bmc1_property_lemmas                  false
% 58.61/8.00  --bmc1_k_induction                      false
% 58.61/8.00  --bmc1_non_equiv_states                 false
% 58.61/8.00  --bmc1_deadlock                         false
% 58.61/8.00  --bmc1_ucm                              false
% 58.61/8.00  --bmc1_add_unsat_core                   none
% 58.61/8.00  --bmc1_unsat_core_children              false
% 58.61/8.00  --bmc1_unsat_core_extrapolate_axioms    false
% 58.61/8.00  --bmc1_out_stat                         full
% 58.61/8.00  --bmc1_ground_init                      false
% 58.61/8.00  --bmc1_pre_inst_next_state              false
% 58.61/8.00  --bmc1_pre_inst_state                   false
% 58.61/8.00  --bmc1_pre_inst_reach_state             false
% 58.61/8.00  --bmc1_out_unsat_core                   false
% 58.61/8.00  --bmc1_aig_witness_out                  false
% 58.61/8.00  --bmc1_verbose                          false
% 58.61/8.00  --bmc1_dump_clauses_tptp                false
% 58.61/8.00  --bmc1_dump_unsat_core_tptp             false
% 58.61/8.00  --bmc1_dump_file                        -
% 58.61/8.00  --bmc1_ucm_expand_uc_limit              128
% 58.61/8.00  --bmc1_ucm_n_expand_iterations          6
% 58.61/8.00  --bmc1_ucm_extend_mode                  1
% 58.61/8.00  --bmc1_ucm_init_mode                    2
% 58.61/8.00  --bmc1_ucm_cone_mode                    none
% 58.61/8.00  --bmc1_ucm_reduced_relation_type        0
% 58.61/8.00  --bmc1_ucm_relax_model                  4
% 58.61/8.00  --bmc1_ucm_full_tr_after_sat            true
% 58.61/8.00  --bmc1_ucm_expand_neg_assumptions       false
% 58.61/8.00  --bmc1_ucm_layered_model                none
% 58.61/8.00  --bmc1_ucm_max_lemma_size               10
% 58.61/8.00  
% 58.61/8.00  ------ AIG Options
% 58.61/8.00  
% 58.61/8.00  --aig_mode                              false
% 58.61/8.00  
% 58.61/8.00  ------ Instantiation Options
% 58.61/8.00  
% 58.61/8.00  --instantiation_flag                    true
% 58.61/8.00  --inst_sos_flag                         true
% 58.61/8.00  --inst_sos_phase                        true
% 58.61/8.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 58.61/8.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 58.61/8.00  --inst_lit_sel_side                     num_symb
% 58.61/8.00  --inst_solver_per_active                1400
% 58.61/8.00  --inst_solver_calls_frac                1.
% 58.61/8.00  --inst_passive_queue_type               priority_queues
% 58.61/8.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 58.61/8.00  --inst_passive_queues_freq              [25;2]
% 58.61/8.00  --inst_dismatching                      true
% 58.61/8.00  --inst_eager_unprocessed_to_passive     true
% 58.61/8.00  --inst_prop_sim_given                   true
% 58.61/8.00  --inst_prop_sim_new                     false
% 58.61/8.00  --inst_subs_new                         false
% 58.61/8.00  --inst_eq_res_simp                      false
% 58.61/8.00  --inst_subs_given                       false
% 58.61/8.00  --inst_orphan_elimination               true
% 58.61/8.00  --inst_learning_loop_flag               true
% 58.61/8.00  --inst_learning_start                   3000
% 58.61/8.00  --inst_learning_factor                  2
% 58.61/8.00  --inst_start_prop_sim_after_learn       3
% 58.61/8.00  --inst_sel_renew                        solver
% 58.61/8.00  --inst_lit_activity_flag                true
% 58.61/8.00  --inst_restr_to_given                   false
% 58.61/8.00  --inst_activity_threshold               500
% 58.61/8.00  --inst_out_proof                        true
% 58.61/8.00  
% 58.61/8.00  ------ Resolution Options
% 58.61/8.00  
% 58.61/8.00  --resolution_flag                       true
% 58.61/8.00  --res_lit_sel                           adaptive
% 58.61/8.00  --res_lit_sel_side                      none
% 58.61/8.00  --res_ordering                          kbo
% 58.61/8.00  --res_to_prop_solver                    active
% 58.61/8.00  --res_prop_simpl_new                    false
% 58.61/8.00  --res_prop_simpl_given                  true
% 58.61/8.00  --res_passive_queue_type                priority_queues
% 58.61/8.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 58.61/8.00  --res_passive_queues_freq               [15;5]
% 58.61/8.00  --res_forward_subs                      full
% 58.61/8.00  --res_backward_subs                     full
% 58.61/8.00  --res_forward_subs_resolution           true
% 58.61/8.00  --res_backward_subs_resolution          true
% 58.61/8.00  --res_orphan_elimination                true
% 58.61/8.00  --res_time_limit                        2.
% 58.61/8.00  --res_out_proof                         true
% 58.61/8.00  
% 58.61/8.00  ------ Superposition Options
% 58.61/8.00  
% 58.61/8.00  --superposition_flag                    true
% 58.61/8.00  --sup_passive_queue_type                priority_queues
% 58.61/8.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 58.61/8.00  --sup_passive_queues_freq               [8;1;4]
% 58.61/8.00  --demod_completeness_check              fast
% 58.61/8.00  --demod_use_ground                      true
% 58.61/8.00  --sup_to_prop_solver                    passive
% 58.61/8.00  --sup_prop_simpl_new                    true
% 58.61/8.00  --sup_prop_simpl_given                  true
% 58.61/8.00  --sup_fun_splitting                     true
% 58.61/8.00  --sup_smt_interval                      50000
% 58.61/8.00  
% 58.61/8.00  ------ Superposition Simplification Setup
% 58.61/8.00  
% 58.61/8.00  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 58.61/8.00  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 58.61/8.00  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 58.61/8.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 58.61/8.00  --sup_full_triv                         [TrivRules;PropSubs]
% 58.61/8.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 58.61/8.00  --sup_full_bw                           [BwDemod;BwSubsumption]
% 58.61/8.00  --sup_immed_triv                        [TrivRules]
% 58.61/8.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 58.61/8.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 58.61/8.00  --sup_immed_bw_main                     []
% 58.61/8.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 58.61/8.00  --sup_input_triv                        [Unflattening;TrivRules]
% 58.61/8.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 58.61/8.00  --sup_input_bw                          []
% 58.61/8.00  
% 58.61/8.00  ------ Combination Options
% 58.61/8.00  
% 58.61/8.00  --comb_res_mult                         3
% 58.61/8.00  --comb_sup_mult                         2
% 58.61/8.00  --comb_inst_mult                        10
% 58.61/8.00  
% 58.61/8.00  ------ Debug Options
% 58.61/8.00  
% 58.61/8.00  --dbg_backtrace                         false
% 58.61/8.00  --dbg_dump_prop_clauses                 false
% 58.61/8.00  --dbg_dump_prop_clauses_file            -
% 58.61/8.00  --dbg_out_stat                          false
% 58.61/8.00  ------ Parsing...
% 58.61/8.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 58.61/8.00  
% 58.61/8.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe:8:0s pe_e  sf_s  rm: 5 0s  sf_e  pe_s  pe_e 
% 58.61/8.00  
% 58.61/8.00  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 58.61/8.00  
% 58.61/8.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 58.61/8.00  ------ Proving...
% 58.61/8.00  ------ Problem Properties 
% 58.61/8.00  
% 58.61/8.00  
% 58.61/8.00  clauses                                 27
% 58.61/8.00  conjectures                             2
% 58.61/8.00  EPR                                     0
% 58.61/8.00  Horn                                    25
% 58.61/8.00  unary                                   4
% 58.61/8.00  binary                                  12
% 58.61/8.00  lits                                    64
% 58.61/8.00  lits eq                                 28
% 58.61/8.00  fd_pure                                 0
% 58.61/8.00  fd_pseudo                               0
% 58.61/8.00  fd_cond                                 4
% 58.61/8.00  fd_pseudo_cond                          1
% 58.61/8.00  AC symbols                              0
% 58.61/8.00  
% 58.61/8.00  ------ Schedule dynamic 5 is on 
% 58.61/8.00  
% 58.61/8.00  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 58.61/8.00  
% 58.61/8.00  
% 58.61/8.00  ------ 
% 58.61/8.00  Current options:
% 58.61/8.00  ------ 
% 58.61/8.00  
% 58.61/8.00  ------ Input Options
% 58.61/8.00  
% 58.61/8.00  --out_options                           all
% 58.61/8.00  --tptp_safe_out                         true
% 58.61/8.00  --problem_path                          ""
% 58.61/8.00  --include_path                          ""
% 58.61/8.00  --clausifier                            res/vclausify_rel
% 58.61/8.00  --clausifier_options                    ""
% 58.61/8.00  --stdin                                 false
% 58.61/8.00  --stats_out                             all
% 58.61/8.00  
% 58.61/8.00  ------ General Options
% 58.61/8.00  
% 58.61/8.00  --fof                                   false
% 58.61/8.00  --time_out_real                         305.
% 58.61/8.00  --time_out_virtual                      -1.
% 58.61/8.00  --symbol_type_check                     false
% 58.61/8.00  --clausify_out                          false
% 58.61/8.00  --sig_cnt_out                           false
% 58.61/8.00  --trig_cnt_out                          false
% 58.61/8.00  --trig_cnt_out_tolerance                1.
% 58.61/8.00  --trig_cnt_out_sk_spl                   false
% 58.61/8.00  --abstr_cl_out                          false
% 58.61/8.00  
% 58.61/8.00  ------ Global Options
% 58.61/8.00  
% 58.61/8.00  --schedule                              default
% 58.61/8.00  --add_important_lit                     false
% 58.61/8.00  --prop_solver_per_cl                    1000
% 58.61/8.00  --min_unsat_core                        false
% 58.61/8.00  --soft_assumptions                      false
% 58.61/8.00  --soft_lemma_size                       3
% 58.61/8.00  --prop_impl_unit_size                   0
% 58.61/8.00  --prop_impl_unit                        []
% 58.61/8.00  --share_sel_clauses                     true
% 58.61/8.00  --reset_solvers                         false
% 58.61/8.00  --bc_imp_inh                            [conj_cone]
% 58.61/8.00  --conj_cone_tolerance                   3.
% 58.61/8.00  --extra_neg_conj                        none
% 58.61/8.00  --large_theory_mode                     true
% 58.61/8.00  --prolific_symb_bound                   200
% 58.61/8.00  --lt_threshold                          2000
% 58.61/8.00  --clause_weak_htbl                      true
% 58.61/8.00  --gc_record_bc_elim                     false
% 58.61/8.00  
% 58.61/8.00  ------ Preprocessing Options
% 58.61/8.00  
% 58.61/8.00  --preprocessing_flag                    true
% 58.61/8.00  --time_out_prep_mult                    0.1
% 58.61/8.00  --splitting_mode                        input
% 58.61/8.00  --splitting_grd                         true
% 58.61/8.00  --splitting_cvd                         false
% 58.61/8.00  --splitting_cvd_svl                     false
% 58.61/8.00  --splitting_nvd                         32
% 58.61/8.00  --sub_typing                            true
% 58.61/8.00  --prep_gs_sim                           true
% 58.61/8.00  --prep_unflatten                        true
% 58.61/8.00  --prep_res_sim                          true
% 58.61/8.00  --prep_upred                            true
% 58.61/8.00  --prep_sem_filter                       exhaustive
% 58.61/8.00  --prep_sem_filter_out                   false
% 58.61/8.00  --pred_elim                             true
% 58.61/8.00  --res_sim_input                         true
% 58.61/8.00  --eq_ax_congr_red                       true
% 58.61/8.00  --pure_diseq_elim                       true
% 58.61/8.00  --brand_transform                       false
% 58.61/8.00  --non_eq_to_eq                          false
% 58.61/8.00  --prep_def_merge                        true
% 58.61/8.00  --prep_def_merge_prop_impl              false
% 58.61/8.00  --prep_def_merge_mbd                    true
% 58.61/8.00  --prep_def_merge_tr_red                 false
% 58.61/8.00  --prep_def_merge_tr_cl                  false
% 58.61/8.00  --smt_preprocessing                     true
% 58.61/8.00  --smt_ac_axioms                         fast
% 58.61/8.00  --preprocessed_out                      false
% 58.61/8.00  --preprocessed_stats                    false
% 58.61/8.00  
% 58.61/8.00  ------ Abstraction refinement Options
% 58.61/8.00  
% 58.61/8.00  --abstr_ref                             []
% 58.61/8.00  --abstr_ref_prep                        false
% 58.61/8.00  --abstr_ref_until_sat                   false
% 58.61/8.00  --abstr_ref_sig_restrict                funpre
% 58.61/8.00  --abstr_ref_af_restrict_to_split_sk     false
% 58.61/8.00  --abstr_ref_under                       []
% 58.61/8.00  
% 58.61/8.00  ------ SAT Options
% 58.61/8.00  
% 58.61/8.00  --sat_mode                              false
% 58.61/8.00  --sat_fm_restart_options                ""
% 58.61/8.00  --sat_gr_def                            false
% 58.61/8.00  --sat_epr_types                         true
% 58.61/8.00  --sat_non_cyclic_types                  false
% 58.61/8.00  --sat_finite_models                     false
% 58.61/8.00  --sat_fm_lemmas                         false
% 58.61/8.00  --sat_fm_prep                           false
% 58.61/8.00  --sat_fm_uc_incr                        true
% 58.61/8.00  --sat_out_model                         small
% 58.61/8.00  --sat_out_clauses                       false
% 58.61/8.00  
% 58.61/8.00  ------ QBF Options
% 58.61/8.00  
% 58.61/8.00  --qbf_mode                              false
% 58.61/8.00  --qbf_elim_univ                         false
% 58.61/8.00  --qbf_dom_inst                          none
% 58.61/8.00  --qbf_dom_pre_inst                      false
% 58.61/8.00  --qbf_sk_in                             false
% 58.61/8.00  --qbf_pred_elim                         true
% 58.61/8.00  --qbf_split                             512
% 58.61/8.00  
% 58.61/8.00  ------ BMC1 Options
% 58.61/8.00  
% 58.61/8.00  --bmc1_incremental                      false
% 58.61/8.00  --bmc1_axioms                           reachable_all
% 58.61/8.00  --bmc1_min_bound                        0
% 58.61/8.00  --bmc1_max_bound                        -1
% 58.61/8.00  --bmc1_max_bound_default                -1
% 58.61/8.00  --bmc1_symbol_reachability              true
% 58.61/8.00  --bmc1_property_lemmas                  false
% 58.61/8.00  --bmc1_k_induction                      false
% 58.61/8.00  --bmc1_non_equiv_states                 false
% 58.61/8.00  --bmc1_deadlock                         false
% 58.61/8.00  --bmc1_ucm                              false
% 58.61/8.00  --bmc1_add_unsat_core                   none
% 58.61/8.00  --bmc1_unsat_core_children              false
% 58.61/8.00  --bmc1_unsat_core_extrapolate_axioms    false
% 58.61/8.00  --bmc1_out_stat                         full
% 58.61/8.00  --bmc1_ground_init                      false
% 58.61/8.00  --bmc1_pre_inst_next_state              false
% 58.61/8.00  --bmc1_pre_inst_state                   false
% 58.61/8.00  --bmc1_pre_inst_reach_state             false
% 58.61/8.00  --bmc1_out_unsat_core                   false
% 58.61/8.00  --bmc1_aig_witness_out                  false
% 58.61/8.00  --bmc1_verbose                          false
% 58.61/8.00  --bmc1_dump_clauses_tptp                false
% 58.61/8.00  --bmc1_dump_unsat_core_tptp             false
% 58.61/8.00  --bmc1_dump_file                        -
% 58.61/8.00  --bmc1_ucm_expand_uc_limit              128
% 58.61/8.00  --bmc1_ucm_n_expand_iterations          6
% 58.61/8.00  --bmc1_ucm_extend_mode                  1
% 58.61/8.00  --bmc1_ucm_init_mode                    2
% 58.61/8.00  --bmc1_ucm_cone_mode                    none
% 58.61/8.00  --bmc1_ucm_reduced_relation_type        0
% 58.61/8.00  --bmc1_ucm_relax_model                  4
% 58.61/8.00  --bmc1_ucm_full_tr_after_sat            true
% 58.61/8.00  --bmc1_ucm_expand_neg_assumptions       false
% 58.61/8.00  --bmc1_ucm_layered_model                none
% 58.61/8.00  --bmc1_ucm_max_lemma_size               10
% 58.61/8.00  
% 58.61/8.00  ------ AIG Options
% 58.61/8.00  
% 58.61/8.00  --aig_mode                              false
% 58.61/8.00  
% 58.61/8.00  ------ Instantiation Options
% 58.61/8.00  
% 58.61/8.00  --instantiation_flag                    true
% 58.61/8.00  --inst_sos_flag                         true
% 58.61/8.00  --inst_sos_phase                        true
% 58.61/8.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 58.61/8.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 58.61/8.00  --inst_lit_sel_side                     none
% 58.61/8.00  --inst_solver_per_active                1400
% 58.61/8.00  --inst_solver_calls_frac                1.
% 58.61/8.00  --inst_passive_queue_type               priority_queues
% 58.61/8.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 58.61/8.00  --inst_passive_queues_freq              [25;2]
% 58.61/8.00  --inst_dismatching                      true
% 58.61/8.00  --inst_eager_unprocessed_to_passive     true
% 58.61/8.00  --inst_prop_sim_given                   true
% 58.61/8.00  --inst_prop_sim_new                     false
% 58.61/8.00  --inst_subs_new                         false
% 58.61/8.00  --inst_eq_res_simp                      false
% 58.61/8.00  --inst_subs_given                       false
% 58.61/8.00  --inst_orphan_elimination               true
% 58.61/8.00  --inst_learning_loop_flag               true
% 58.61/8.00  --inst_learning_start                   3000
% 58.61/8.00  --inst_learning_factor                  2
% 58.61/8.00  --inst_start_prop_sim_after_learn       3
% 58.61/8.00  --inst_sel_renew                        solver
% 58.61/8.00  --inst_lit_activity_flag                true
% 58.61/8.00  --inst_restr_to_given                   false
% 58.61/8.00  --inst_activity_threshold               500
% 58.61/8.00  --inst_out_proof                        true
% 58.61/8.00  
% 58.61/8.00  ------ Resolution Options
% 58.61/8.00  
% 58.61/8.00  --resolution_flag                       false
% 58.61/8.00  --res_lit_sel                           adaptive
% 58.61/8.00  --res_lit_sel_side                      none
% 58.61/8.00  --res_ordering                          kbo
% 58.61/8.00  --res_to_prop_solver                    active
% 58.61/8.00  --res_prop_simpl_new                    false
% 58.61/8.00  --res_prop_simpl_given                  true
% 58.61/8.00  --res_passive_queue_type                priority_queues
% 58.61/8.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 58.61/8.00  --res_passive_queues_freq               [15;5]
% 58.61/8.00  --res_forward_subs                      full
% 58.61/8.00  --res_backward_subs                     full
% 58.61/8.00  --res_forward_subs_resolution           true
% 58.61/8.00  --res_backward_subs_resolution          true
% 58.61/8.00  --res_orphan_elimination                true
% 58.61/8.00  --res_time_limit                        2.
% 58.61/8.00  --res_out_proof                         true
% 58.61/8.00  
% 58.61/8.00  ------ Superposition Options
% 58.61/8.00  
% 58.61/8.00  --superposition_flag                    true
% 58.61/8.00  --sup_passive_queue_type                priority_queues
% 58.61/8.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 58.61/8.00  --sup_passive_queues_freq               [8;1;4]
% 58.61/8.00  --demod_completeness_check              fast
% 58.61/8.00  --demod_use_ground                      true
% 58.61/8.00  --sup_to_prop_solver                    passive
% 58.61/8.00  --sup_prop_simpl_new                    true
% 58.61/8.00  --sup_prop_simpl_given                  true
% 58.61/8.00  --sup_fun_splitting                     true
% 58.61/8.00  --sup_smt_interval                      50000
% 58.61/8.00  
% 58.61/8.00  ------ Superposition Simplification Setup
% 58.61/8.00  
% 58.61/8.00  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 58.61/8.00  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 58.61/8.00  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 58.61/8.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 58.61/8.00  --sup_full_triv                         [TrivRules;PropSubs]
% 58.61/8.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 58.61/8.00  --sup_full_bw                           [BwDemod;BwSubsumption]
% 58.61/8.00  --sup_immed_triv                        [TrivRules]
% 58.61/8.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 58.61/8.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 58.61/8.00  --sup_immed_bw_main                     []
% 58.61/8.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 58.61/8.00  --sup_input_triv                        [Unflattening;TrivRules]
% 58.61/8.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 58.61/8.00  --sup_input_bw                          []
% 58.61/8.00  
% 58.61/8.00  ------ Combination Options
% 58.61/8.00  
% 58.61/8.00  --comb_res_mult                         3
% 58.61/8.00  --comb_sup_mult                         2
% 58.61/8.00  --comb_inst_mult                        10
% 58.61/8.00  
% 58.61/8.00  ------ Debug Options
% 58.61/8.00  
% 58.61/8.00  --dbg_backtrace                         false
% 58.61/8.00  --dbg_dump_prop_clauses                 false
% 58.61/8.00  --dbg_dump_prop_clauses_file            -
% 58.61/8.00  --dbg_out_stat                          false
% 58.61/8.00  
% 58.61/8.00  
% 58.61/8.00  
% 58.61/8.00  
% 58.61/8.00  ------ Proving...
% 58.61/8.00  
% 58.61/8.00  
% 58.61/8.00  % SZS status Theorem for theBenchmark.p
% 58.61/8.00  
% 58.61/8.00  % SZS output start CNFRefutation for theBenchmark.p
% 58.61/8.00  
% 58.61/8.00  fof(f24,conjecture,(
% 58.61/8.00    ! [X0] : ((l3_lattices(X0) & v17_lattices(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => k7_lattices(X0,k7_lattices(X0,X1)) = X1))),
% 58.61/8.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 58.61/8.00  
% 58.61/8.00  fof(f25,negated_conjecture,(
% 58.61/8.00    ~! [X0] : ((l3_lattices(X0) & v17_lattices(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => k7_lattices(X0,k7_lattices(X0,X1)) = X1))),
% 58.61/8.00    inference(negated_conjecture,[],[f24])).
% 58.61/8.00  
% 58.61/8.00  fof(f73,plain,(
% 58.61/8.00    ? [X0] : (? [X1] : (k7_lattices(X0,k7_lattices(X0,X1)) != X1 & m1_subset_1(X1,u1_struct_0(X0))) & (l3_lattices(X0) & v17_lattices(X0) & v10_lattices(X0) & ~v2_struct_0(X0)))),
% 58.61/8.00    inference(ennf_transformation,[],[f25])).
% 58.61/8.00  
% 58.61/8.00  fof(f74,plain,(
% 58.61/8.00    ? [X0] : (? [X1] : (k7_lattices(X0,k7_lattices(X0,X1)) != X1 & m1_subset_1(X1,u1_struct_0(X0))) & l3_lattices(X0) & v17_lattices(X0) & v10_lattices(X0) & ~v2_struct_0(X0))),
% 58.61/8.00    inference(flattening,[],[f73])).
% 58.61/8.00  
% 58.61/8.00  fof(f100,plain,(
% 58.61/8.00    ( ! [X0] : (? [X1] : (k7_lattices(X0,k7_lattices(X0,X1)) != X1 & m1_subset_1(X1,u1_struct_0(X0))) => (k7_lattices(X0,k7_lattices(X0,sK10)) != sK10 & m1_subset_1(sK10,u1_struct_0(X0)))) )),
% 58.61/8.00    introduced(choice_axiom,[])).
% 58.61/8.00  
% 58.61/8.00  fof(f99,plain,(
% 58.61/8.00    ? [X0] : (? [X1] : (k7_lattices(X0,k7_lattices(X0,X1)) != X1 & m1_subset_1(X1,u1_struct_0(X0))) & l3_lattices(X0) & v17_lattices(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => (? [X1] : (k7_lattices(sK9,k7_lattices(sK9,X1)) != X1 & m1_subset_1(X1,u1_struct_0(sK9))) & l3_lattices(sK9) & v17_lattices(sK9) & v10_lattices(sK9) & ~v2_struct_0(sK9))),
% 58.61/8.00    introduced(choice_axiom,[])).
% 58.61/8.00  
% 58.61/8.00  fof(f101,plain,(
% 58.61/8.00    (k7_lattices(sK9,k7_lattices(sK9,sK10)) != sK10 & m1_subset_1(sK10,u1_struct_0(sK9))) & l3_lattices(sK9) & v17_lattices(sK9) & v10_lattices(sK9) & ~v2_struct_0(sK9)),
% 58.61/8.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK9,sK10])],[f74,f100,f99])).
% 58.61/8.00  
% 58.61/8.00  fof(f154,plain,(
% 58.61/8.00    m1_subset_1(sK10,u1_struct_0(sK9))),
% 58.61/8.00    inference(cnf_transformation,[],[f101])).
% 58.61/8.00  
% 58.61/8.00  fof(f14,axiom,(
% 58.61/8.00    ! [X0,X1] : ((m1_subset_1(X1,u1_struct_0(X0)) & l3_lattices(X0) & ~v2_struct_0(X0)) => m1_subset_1(k7_lattices(X0,X1),u1_struct_0(X0)))),
% 58.61/8.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 58.61/8.00  
% 58.61/8.00  fof(f54,plain,(
% 58.61/8.00    ! [X0,X1] : (m1_subset_1(k7_lattices(X0,X1),u1_struct_0(X0)) | (~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | v2_struct_0(X0)))),
% 58.61/8.00    inference(ennf_transformation,[],[f14])).
% 58.61/8.00  
% 58.61/8.00  fof(f55,plain,(
% 58.61/8.00    ! [X0,X1] : (m1_subset_1(k7_lattices(X0,X1),u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 58.61/8.00    inference(flattening,[],[f54])).
% 58.61/8.00  
% 58.61/8.00  fof(f139,plain,(
% 58.61/8.00    ( ! [X0,X1] : (m1_subset_1(k7_lattices(X0,X1),u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | v2_struct_0(X0)) )),
% 58.61/8.00    inference(cnf_transformation,[],[f55])).
% 58.61/8.00  
% 58.61/8.00  fof(f150,plain,(
% 58.61/8.00    ~v2_struct_0(sK9)),
% 58.61/8.00    inference(cnf_transformation,[],[f101])).
% 58.61/8.00  
% 58.61/8.00  fof(f153,plain,(
% 58.61/8.00    l3_lattices(sK9)),
% 58.61/8.00    inference(cnf_transformation,[],[f101])).
% 58.61/8.00  
% 58.61/8.00  fof(f7,axiom,(
% 58.61/8.00    ! [X0] : ((l3_lattices(X0) & ~v2_struct_0(X0)) => (v11_lattices(X0) <=> ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => k1_lattices(X0,k2_lattices(X0,X1,X2),k2_lattices(X0,X1,X3)) = k2_lattices(X0,X1,k1_lattices(X0,X2,X3)))))))),
% 58.61/8.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 58.61/8.00  
% 58.61/8.00  fof(f40,plain,(
% 58.61/8.00    ! [X0] : ((v11_lattices(X0) <=> ! [X1] : (! [X2] : (! [X3] : (k1_lattices(X0,k2_lattices(X0,X1,X2),k2_lattices(X0,X1,X3)) = k2_lattices(X0,X1,k1_lattices(X0,X2,X3)) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)))) | (~l3_lattices(X0) | v2_struct_0(X0)))),
% 58.61/8.00    inference(ennf_transformation,[],[f7])).
% 58.61/8.00  
% 58.61/8.00  fof(f41,plain,(
% 58.61/8.00    ! [X0] : ((v11_lattices(X0) <=> ! [X1] : (! [X2] : (! [X3] : (k1_lattices(X0,k2_lattices(X0,X1,X2),k2_lattices(X0,X1,X3)) = k2_lattices(X0,X1,k1_lattices(X0,X2,X3)) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 58.61/8.00    inference(flattening,[],[f40])).
% 58.61/8.00  
% 58.61/8.00  fof(f75,plain,(
% 58.61/8.00    ! [X0] : (((v11_lattices(X0) | ? [X1] : (? [X2] : (? [X3] : (k1_lattices(X0,k2_lattices(X0,X1,X2),k2_lattices(X0,X1,X3)) != k2_lattices(X0,X1,k1_lattices(X0,X2,X3)) & m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0)))) & (! [X1] : (! [X2] : (! [X3] : (k1_lattices(X0,k2_lattices(X0,X1,X2),k2_lattices(X0,X1,X3)) = k2_lattices(X0,X1,k1_lattices(X0,X2,X3)) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~v11_lattices(X0))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 58.61/8.00    inference(nnf_transformation,[],[f41])).
% 58.61/8.00  
% 58.61/8.00  fof(f76,plain,(
% 58.61/8.00    ! [X0] : (((v11_lattices(X0) | ? [X1] : (? [X2] : (? [X3] : (k1_lattices(X0,k2_lattices(X0,X1,X2),k2_lattices(X0,X1,X3)) != k2_lattices(X0,X1,k1_lattices(X0,X2,X3)) & m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0)))) & (! [X4] : (! [X5] : (! [X6] : (k1_lattices(X0,k2_lattices(X0,X4,X5),k2_lattices(X0,X4,X6)) = k2_lattices(X0,X4,k1_lattices(X0,X5,X6)) | ~m1_subset_1(X6,u1_struct_0(X0))) | ~m1_subset_1(X5,u1_struct_0(X0))) | ~m1_subset_1(X4,u1_struct_0(X0))) | ~v11_lattices(X0))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 58.61/8.00    inference(rectify,[],[f75])).
% 58.61/8.00  
% 58.61/8.00  fof(f79,plain,(
% 58.61/8.00    ( ! [X2,X1] : (! [X0] : (? [X3] : (k1_lattices(X0,k2_lattices(X0,X1,X2),k2_lattices(X0,X1,X3)) != k2_lattices(X0,X1,k1_lattices(X0,X2,X3)) & m1_subset_1(X3,u1_struct_0(X0))) => (k1_lattices(X0,k2_lattices(X0,X1,X2),k2_lattices(X0,X1,sK2(X0))) != k2_lattices(X0,X1,k1_lattices(X0,X2,sK2(X0))) & m1_subset_1(sK2(X0),u1_struct_0(X0))))) )),
% 58.61/8.00    introduced(choice_axiom,[])).
% 58.61/8.00  
% 58.61/8.00  fof(f78,plain,(
% 58.61/8.00    ( ! [X1] : (! [X0] : (? [X2] : (? [X3] : (k1_lattices(X0,k2_lattices(X0,X1,X2),k2_lattices(X0,X1,X3)) != k2_lattices(X0,X1,k1_lattices(X0,X2,X3)) & m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(X2,u1_struct_0(X0))) => (? [X3] : (k1_lattices(X0,k2_lattices(X0,X1,sK1(X0)),k2_lattices(X0,X1,X3)) != k2_lattices(X0,X1,k1_lattices(X0,sK1(X0),X3)) & m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(sK1(X0),u1_struct_0(X0))))) )),
% 58.61/8.00    introduced(choice_axiom,[])).
% 58.61/8.00  
% 58.61/8.00  fof(f77,plain,(
% 58.61/8.00    ! [X0] : (? [X1] : (? [X2] : (? [X3] : (k1_lattices(X0,k2_lattices(X0,X1,X2),k2_lattices(X0,X1,X3)) != k2_lattices(X0,X1,k1_lattices(X0,X2,X3)) & m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) => (? [X2] : (? [X3] : (k1_lattices(X0,k2_lattices(X0,sK0(X0),X2),k2_lattices(X0,sK0(X0),X3)) != k2_lattices(X0,sK0(X0),k1_lattices(X0,X2,X3)) & m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(sK0(X0),u1_struct_0(X0))))),
% 58.61/8.00    introduced(choice_axiom,[])).
% 58.61/8.00  
% 58.61/8.00  fof(f80,plain,(
% 58.61/8.00    ! [X0] : (((v11_lattices(X0) | (((k1_lattices(X0,k2_lattices(X0,sK0(X0),sK1(X0)),k2_lattices(X0,sK0(X0),sK2(X0))) != k2_lattices(X0,sK0(X0),k1_lattices(X0,sK1(X0),sK2(X0))) & m1_subset_1(sK2(X0),u1_struct_0(X0))) & m1_subset_1(sK1(X0),u1_struct_0(X0))) & m1_subset_1(sK0(X0),u1_struct_0(X0)))) & (! [X4] : (! [X5] : (! [X6] : (k1_lattices(X0,k2_lattices(X0,X4,X5),k2_lattices(X0,X4,X6)) = k2_lattices(X0,X4,k1_lattices(X0,X5,X6)) | ~m1_subset_1(X6,u1_struct_0(X0))) | ~m1_subset_1(X5,u1_struct_0(X0))) | ~m1_subset_1(X4,u1_struct_0(X0))) | ~v11_lattices(X0))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 58.61/8.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f76,f79,f78,f77])).
% 58.61/8.00  
% 58.61/8.00  fof(f116,plain,(
% 58.61/8.00    ( ! [X6,X4,X0,X5] : (k1_lattices(X0,k2_lattices(X0,X4,X5),k2_lattices(X0,X4,X6)) = k2_lattices(X0,X4,k1_lattices(X0,X5,X6)) | ~m1_subset_1(X6,u1_struct_0(X0)) | ~m1_subset_1(X5,u1_struct_0(X0)) | ~m1_subset_1(X4,u1_struct_0(X0)) | ~v11_lattices(X0) | ~l3_lattices(X0) | v2_struct_0(X0)) )),
% 58.61/8.00    inference(cnf_transformation,[],[f80])).
% 58.61/8.00  
% 58.61/8.00  fof(f4,axiom,(
% 58.61/8.00    ! [X0] : (l3_lattices(X0) => ((v17_lattices(X0) & ~v2_struct_0(X0)) => (v16_lattices(X0) & v15_lattices(X0) & v11_lattices(X0) & ~v2_struct_0(X0))))),
% 58.61/8.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 58.61/8.00  
% 58.61/8.00  fof(f26,plain,(
% 58.61/8.00    ! [X0] : (l3_lattices(X0) => ((v17_lattices(X0) & ~v2_struct_0(X0)) => (v15_lattices(X0) & v11_lattices(X0) & ~v2_struct_0(X0))))),
% 58.61/8.00    inference(pure_predicate_removal,[],[f4])).
% 58.61/8.00  
% 58.61/8.00  fof(f34,plain,(
% 58.61/8.00    ! [X0] : (((v15_lattices(X0) & v11_lattices(X0) & ~v2_struct_0(X0)) | (~v17_lattices(X0) | v2_struct_0(X0))) | ~l3_lattices(X0))),
% 58.61/8.00    inference(ennf_transformation,[],[f26])).
% 58.61/8.00  
% 58.61/8.00  fof(f35,plain,(
% 58.61/8.00    ! [X0] : ((v15_lattices(X0) & v11_lattices(X0) & ~v2_struct_0(X0)) | ~v17_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0))),
% 58.61/8.00    inference(flattening,[],[f34])).
% 58.61/8.00  
% 58.61/8.00  fof(f112,plain,(
% 58.61/8.00    ( ! [X0] : (v11_lattices(X0) | ~v17_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0)) )),
% 58.61/8.00    inference(cnf_transformation,[],[f35])).
% 58.61/8.00  
% 58.61/8.00  fof(f152,plain,(
% 58.61/8.00    v17_lattices(sK9)),
% 58.61/8.00    inference(cnf_transformation,[],[f101])).
% 58.61/8.00  
% 58.61/8.00  fof(f2,axiom,(
% 58.61/8.00    ! [X0] : (l3_lattices(X0) => ((v10_lattices(X0) & ~v2_struct_0(X0)) => (v9_lattices(X0) & v8_lattices(X0) & v7_lattices(X0) & v6_lattices(X0) & v5_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0))))),
% 58.61/8.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 58.61/8.00  
% 58.61/8.00  fof(f27,plain,(
% 58.61/8.00    ! [X0] : (l3_lattices(X0) => ((v10_lattices(X0) & ~v2_struct_0(X0)) => (v9_lattices(X0) & v8_lattices(X0) & v6_lattices(X0) & v5_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0))))),
% 58.61/8.00    inference(pure_predicate_removal,[],[f2])).
% 58.61/8.00  
% 58.61/8.00  fof(f28,plain,(
% 58.61/8.00    ! [X0] : (l3_lattices(X0) => ((v10_lattices(X0) & ~v2_struct_0(X0)) => (v9_lattices(X0) & v8_lattices(X0) & v6_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0))))),
% 58.61/8.00    inference(pure_predicate_removal,[],[f27])).
% 58.61/8.00  
% 58.61/8.00  fof(f30,plain,(
% 58.61/8.00    ! [X0] : (((v9_lattices(X0) & v8_lattices(X0) & v6_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0)) | (~v10_lattices(X0) | v2_struct_0(X0))) | ~l3_lattices(X0))),
% 58.61/8.00    inference(ennf_transformation,[],[f28])).
% 58.61/8.00  
% 58.61/8.00  fof(f31,plain,(
% 58.61/8.00    ! [X0] : ((v9_lattices(X0) & v8_lattices(X0) & v6_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0)) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0))),
% 58.61/8.00    inference(flattening,[],[f30])).
% 58.61/8.00  
% 58.61/8.00  fof(f105,plain,(
% 58.61/8.00    ( ! [X0] : (v6_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0)) )),
% 58.61/8.00    inference(cnf_transformation,[],[f31])).
% 58.61/8.00  
% 58.61/8.00  fof(f6,axiom,(
% 58.61/8.00    ! [X0,X1,X2] : ((m1_subset_1(X2,u1_struct_0(X0)) & m1_subset_1(X1,u1_struct_0(X0)) & l1_lattices(X0) & v6_lattices(X0) & ~v2_struct_0(X0)) => k4_lattices(X0,X1,X2) = k4_lattices(X0,X2,X1))),
% 58.61/8.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 58.61/8.00  
% 58.61/8.00  fof(f38,plain,(
% 58.61/8.00    ! [X0,X1,X2] : (k4_lattices(X0,X1,X2) = k4_lattices(X0,X2,X1) | (~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0)))),
% 58.61/8.00    inference(ennf_transformation,[],[f6])).
% 58.61/8.00  
% 58.61/8.00  fof(f39,plain,(
% 58.61/8.00    ! [X0,X1,X2] : (k4_lattices(X0,X1,X2) = k4_lattices(X0,X2,X1) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0))),
% 58.61/8.00    inference(flattening,[],[f38])).
% 58.61/8.00  
% 58.61/8.00  fof(f115,plain,(
% 58.61/8.00    ( ! [X2,X0,X1] : (k4_lattices(X0,X1,X2) = k4_lattices(X0,X2,X1) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0)) )),
% 58.61/8.00    inference(cnf_transformation,[],[f39])).
% 58.61/8.00  
% 58.61/8.00  fof(f15,axiom,(
% 58.61/8.00    ! [X0] : (l3_lattices(X0) => (l2_lattices(X0) & l1_lattices(X0)))),
% 58.61/8.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 58.61/8.00  
% 58.61/8.00  fof(f56,plain,(
% 58.61/8.00    ! [X0] : ((l2_lattices(X0) & l1_lattices(X0)) | ~l3_lattices(X0))),
% 58.61/8.00    inference(ennf_transformation,[],[f15])).
% 58.61/8.00  
% 58.61/8.00  fof(f140,plain,(
% 58.61/8.00    ( ! [X0] : (l1_lattices(X0) | ~l3_lattices(X0)) )),
% 58.61/8.00    inference(cnf_transformation,[],[f56])).
% 58.61/8.00  
% 58.61/8.00  fof(f151,plain,(
% 58.61/8.00    v10_lattices(sK9)),
% 58.61/8.00    inference(cnf_transformation,[],[f101])).
% 58.61/8.00  
% 58.61/8.00  fof(f22,axiom,(
% 58.61/8.00    ! [X0] : ((l3_lattices(X0) & v17_lattices(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => k4_lattices(X0,k7_lattices(X0,X1),X1) = k5_lattices(X0)))),
% 58.61/8.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 58.61/8.00  
% 58.61/8.00  fof(f69,plain,(
% 58.61/8.00    ! [X0] : (! [X1] : (k4_lattices(X0,k7_lattices(X0,X1),X1) = k5_lattices(X0) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l3_lattices(X0) | ~v17_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0)))),
% 58.61/8.00    inference(ennf_transformation,[],[f22])).
% 58.61/8.00  
% 58.61/8.00  fof(f70,plain,(
% 58.61/8.00    ! [X0] : (! [X1] : (k4_lattices(X0,k7_lattices(X0,X1),X1) = k5_lattices(X0) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v17_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0))),
% 58.61/8.00    inference(flattening,[],[f69])).
% 58.61/8.00  
% 58.61/8.00  fof(f148,plain,(
% 58.61/8.00    ( ! [X0,X1] : (k4_lattices(X0,k7_lattices(X0,X1),X1) = k5_lattices(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v17_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0)) )),
% 58.61/8.00    inference(cnf_transformation,[],[f70])).
% 58.61/8.00  
% 58.61/8.00  fof(f17,axiom,(
% 58.61/8.00    ! [X0,X1,X2] : ((m1_subset_1(X2,u1_struct_0(X0)) & m1_subset_1(X1,u1_struct_0(X0)) & l1_lattices(X0) & v6_lattices(X0) & ~v2_struct_0(X0)) => k4_lattices(X0,X1,X2) = k2_lattices(X0,X1,X2))),
% 58.61/8.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 58.61/8.00  
% 58.61/8.00  fof(f59,plain,(
% 58.61/8.00    ! [X0,X1,X2] : (k4_lattices(X0,X1,X2) = k2_lattices(X0,X1,X2) | (~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0)))),
% 58.61/8.00    inference(ennf_transformation,[],[f17])).
% 58.61/8.00  
% 58.61/8.00  fof(f60,plain,(
% 58.61/8.00    ! [X0,X1,X2] : (k4_lattices(X0,X1,X2) = k2_lattices(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0))),
% 58.61/8.00    inference(flattening,[],[f59])).
% 58.61/8.00  
% 58.61/8.00  fof(f143,plain,(
% 58.61/8.00    ( ! [X2,X0,X1] : (k4_lattices(X0,X1,X2) = k2_lattices(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0)) )),
% 58.61/8.00    inference(cnf_transformation,[],[f60])).
% 58.61/8.00  
% 58.61/8.00  fof(f104,plain,(
% 58.61/8.00    ( ! [X0] : (v4_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0)) )),
% 58.61/8.00    inference(cnf_transformation,[],[f31])).
% 58.61/8.00  
% 58.61/8.00  fof(f5,axiom,(
% 58.61/8.00    ! [X0,X1,X2] : ((m1_subset_1(X2,u1_struct_0(X0)) & m1_subset_1(X1,u1_struct_0(X0)) & l2_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0)) => k3_lattices(X0,X1,X2) = k3_lattices(X0,X2,X1))),
% 58.61/8.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 58.61/8.00  
% 58.61/8.00  fof(f36,plain,(
% 58.61/8.00    ! [X0,X1,X2] : (k3_lattices(X0,X1,X2) = k3_lattices(X0,X2,X1) | (~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l2_lattices(X0) | ~v4_lattices(X0) | v2_struct_0(X0)))),
% 58.61/8.00    inference(ennf_transformation,[],[f5])).
% 58.61/8.00  
% 58.61/8.00  fof(f37,plain,(
% 58.61/8.00    ! [X0,X1,X2] : (k3_lattices(X0,X1,X2) = k3_lattices(X0,X2,X1) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l2_lattices(X0) | ~v4_lattices(X0) | v2_struct_0(X0))),
% 58.61/8.00    inference(flattening,[],[f36])).
% 58.61/8.00  
% 58.61/8.00  fof(f114,plain,(
% 58.61/8.00    ( ! [X2,X0,X1] : (k3_lattices(X0,X1,X2) = k3_lattices(X0,X2,X1) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l2_lattices(X0) | ~v4_lattices(X0) | v2_struct_0(X0)) )),
% 58.61/8.00    inference(cnf_transformation,[],[f37])).
% 58.61/8.00  
% 58.61/8.00  fof(f141,plain,(
% 58.61/8.00    ( ! [X0] : (l2_lattices(X0) | ~l3_lattices(X0)) )),
% 58.61/8.00    inference(cnf_transformation,[],[f56])).
% 58.61/8.00  
% 58.61/8.00  fof(f23,axiom,(
% 58.61/8.00    ! [X0] : ((l3_lattices(X0) & v17_lattices(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => k3_lattices(X0,k7_lattices(X0,X1),X1) = k6_lattices(X0)))),
% 58.61/8.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 58.61/8.00  
% 58.61/8.00  fof(f71,plain,(
% 58.61/8.00    ! [X0] : (! [X1] : (k3_lattices(X0,k7_lattices(X0,X1),X1) = k6_lattices(X0) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l3_lattices(X0) | ~v17_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0)))),
% 58.61/8.00    inference(ennf_transformation,[],[f23])).
% 58.61/8.00  
% 58.61/8.00  fof(f72,plain,(
% 58.61/8.00    ! [X0] : (! [X1] : (k3_lattices(X0,k7_lattices(X0,X1),X1) = k6_lattices(X0) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v17_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0))),
% 58.61/8.00    inference(flattening,[],[f71])).
% 58.61/8.00  
% 58.61/8.00  fof(f149,plain,(
% 58.61/8.00    ( ! [X0,X1] : (k3_lattices(X0,k7_lattices(X0,X1),X1) = k6_lattices(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v17_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0)) )),
% 58.61/8.00    inference(cnf_transformation,[],[f72])).
% 58.61/8.00  
% 58.61/8.00  fof(f16,axiom,(
% 58.61/8.00    ! [X0,X1,X2] : ((m1_subset_1(X2,u1_struct_0(X0)) & m1_subset_1(X1,u1_struct_0(X0)) & l2_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0)) => k3_lattices(X0,X1,X2) = k1_lattices(X0,X1,X2))),
% 58.61/8.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 58.61/8.00  
% 58.61/8.00  fof(f57,plain,(
% 58.61/8.00    ! [X0,X1,X2] : (k3_lattices(X0,X1,X2) = k1_lattices(X0,X1,X2) | (~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l2_lattices(X0) | ~v4_lattices(X0) | v2_struct_0(X0)))),
% 58.61/8.00    inference(ennf_transformation,[],[f16])).
% 58.61/8.00  
% 58.61/8.00  fof(f58,plain,(
% 58.61/8.00    ! [X0,X1,X2] : (k3_lattices(X0,X1,X2) = k1_lattices(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l2_lattices(X0) | ~v4_lattices(X0) | v2_struct_0(X0))),
% 58.61/8.00    inference(flattening,[],[f57])).
% 58.61/8.00  
% 58.61/8.00  fof(f142,plain,(
% 58.61/8.00    ( ! [X2,X0,X1] : (k3_lattices(X0,X1,X2) = k1_lattices(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l2_lattices(X0) | ~v4_lattices(X0) | v2_struct_0(X0)) )),
% 58.61/8.00    inference(cnf_transformation,[],[f58])).
% 58.61/8.00  
% 58.61/8.00  fof(f11,axiom,(
% 58.61/8.00    ! [X0] : ((l3_lattices(X0) & ~v2_struct_0(X0)) => (v9_lattices(X0) <=> ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => k2_lattices(X0,X1,k1_lattices(X0,X1,X2)) = X1))))),
% 58.61/8.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 58.61/8.00  
% 58.61/8.00  fof(f48,plain,(
% 58.61/8.00    ! [X0] : ((v9_lattices(X0) <=> ! [X1] : (! [X2] : (k2_lattices(X0,X1,k1_lattices(X0,X1,X2)) = X1 | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)))) | (~l3_lattices(X0) | v2_struct_0(X0)))),
% 58.61/8.00    inference(ennf_transformation,[],[f11])).
% 58.61/8.00  
% 58.61/8.00  fof(f49,plain,(
% 58.61/8.00    ! [X0] : ((v9_lattices(X0) <=> ! [X1] : (! [X2] : (k2_lattices(X0,X1,k1_lattices(X0,X1,X2)) = X1 | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 58.61/8.00    inference(flattening,[],[f48])).
% 58.61/8.00  
% 58.61/8.00  fof(f94,plain,(
% 58.61/8.00    ! [X0] : (((v9_lattices(X0) | ? [X1] : (? [X2] : (k2_lattices(X0,X1,k1_lattices(X0,X1,X2)) != X1 & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0)))) & (! [X1] : (! [X2] : (k2_lattices(X0,X1,k1_lattices(X0,X1,X2)) = X1 | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~v9_lattices(X0))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 58.61/8.00    inference(nnf_transformation,[],[f49])).
% 58.61/8.00  
% 58.61/8.00  fof(f95,plain,(
% 58.61/8.00    ! [X0] : (((v9_lattices(X0) | ? [X1] : (? [X2] : (k2_lattices(X0,X1,k1_lattices(X0,X1,X2)) != X1 & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0)))) & (! [X3] : (! [X4] : (k2_lattices(X0,X3,k1_lattices(X0,X3,X4)) = X3 | ~m1_subset_1(X4,u1_struct_0(X0))) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~v9_lattices(X0))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 58.61/8.00    inference(rectify,[],[f94])).
% 58.61/8.00  
% 58.61/8.00  fof(f97,plain,(
% 58.61/8.00    ( ! [X1] : (! [X0] : (? [X2] : (k2_lattices(X0,X1,k1_lattices(X0,X1,X2)) != X1 & m1_subset_1(X2,u1_struct_0(X0))) => (k2_lattices(X0,X1,k1_lattices(X0,X1,sK8(X0))) != X1 & m1_subset_1(sK8(X0),u1_struct_0(X0))))) )),
% 58.61/8.00    introduced(choice_axiom,[])).
% 58.61/8.00  
% 58.61/8.00  fof(f96,plain,(
% 58.61/8.00    ! [X0] : (? [X1] : (? [X2] : (k2_lattices(X0,X1,k1_lattices(X0,X1,X2)) != X1 & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) => (? [X2] : (k2_lattices(X0,sK7(X0),k1_lattices(X0,sK7(X0),X2)) != sK7(X0) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(sK7(X0),u1_struct_0(X0))))),
% 58.61/8.00    introduced(choice_axiom,[])).
% 58.61/8.00  
% 58.61/8.00  fof(f98,plain,(
% 58.61/8.00    ! [X0] : (((v9_lattices(X0) | ((k2_lattices(X0,sK7(X0),k1_lattices(X0,sK7(X0),sK8(X0))) != sK7(X0) & m1_subset_1(sK8(X0),u1_struct_0(X0))) & m1_subset_1(sK7(X0),u1_struct_0(X0)))) & (! [X3] : (! [X4] : (k2_lattices(X0,X3,k1_lattices(X0,X3,X4)) = X3 | ~m1_subset_1(X4,u1_struct_0(X0))) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~v9_lattices(X0))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 58.61/8.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7,sK8])],[f95,f97,f96])).
% 58.61/8.00  
% 58.61/8.00  fof(f133,plain,(
% 58.61/8.00    ( ! [X4,X0,X3] : (k2_lattices(X0,X3,k1_lattices(X0,X3,X4)) = X3 | ~m1_subset_1(X4,u1_struct_0(X0)) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~v9_lattices(X0) | ~l3_lattices(X0) | v2_struct_0(X0)) )),
% 58.61/8.00    inference(cnf_transformation,[],[f98])).
% 58.61/8.00  
% 58.61/8.00  fof(f107,plain,(
% 58.61/8.00    ( ! [X0] : (v9_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0)) )),
% 58.61/8.00    inference(cnf_transformation,[],[f31])).
% 58.61/8.00  
% 58.61/8.00  fof(f12,axiom,(
% 58.61/8.00    ! [X0] : ((l1_lattices(X0) & ~v2_struct_0(X0)) => m1_subset_1(k5_lattices(X0),u1_struct_0(X0)))),
% 58.61/8.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 58.61/8.00  
% 58.61/8.00  fof(f50,plain,(
% 58.61/8.00    ! [X0] : (m1_subset_1(k5_lattices(X0),u1_struct_0(X0)) | (~l1_lattices(X0) | v2_struct_0(X0)))),
% 58.61/8.00    inference(ennf_transformation,[],[f12])).
% 58.61/8.00  
% 58.61/8.00  fof(f51,plain,(
% 58.61/8.00    ! [X0] : (m1_subset_1(k5_lattices(X0),u1_struct_0(X0)) | ~l1_lattices(X0) | v2_struct_0(X0))),
% 58.61/8.00    inference(flattening,[],[f50])).
% 58.61/8.00  
% 58.61/8.00  fof(f137,plain,(
% 58.61/8.00    ( ! [X0] : (m1_subset_1(k5_lattices(X0),u1_struct_0(X0)) | ~l1_lattices(X0) | v2_struct_0(X0)) )),
% 58.61/8.00    inference(cnf_transformation,[],[f51])).
% 58.61/8.00  
% 58.61/8.00  fof(f20,axiom,(
% 58.61/8.00    ! [X0] : ((l3_lattices(X0) & v13_lattices(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => k4_lattices(X0,k5_lattices(X0),X1) = k5_lattices(X0)))),
% 58.61/8.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 58.61/8.00  
% 58.61/8.00  fof(f65,plain,(
% 58.61/8.00    ! [X0] : (! [X1] : (k4_lattices(X0,k5_lattices(X0),X1) = k5_lattices(X0) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l3_lattices(X0) | ~v13_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0)))),
% 58.61/8.00    inference(ennf_transformation,[],[f20])).
% 58.61/8.00  
% 58.61/8.00  fof(f66,plain,(
% 58.61/8.00    ! [X0] : (! [X1] : (k4_lattices(X0,k5_lattices(X0),X1) = k5_lattices(X0) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v13_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0))),
% 58.61/8.00    inference(flattening,[],[f65])).
% 58.61/8.00  
% 58.61/8.00  fof(f146,plain,(
% 58.61/8.00    ( ! [X0,X1] : (k4_lattices(X0,k5_lattices(X0),X1) = k5_lattices(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v13_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0)) )),
% 58.61/8.00    inference(cnf_transformation,[],[f66])).
% 58.61/8.00  
% 58.61/8.00  fof(f113,plain,(
% 58.61/8.00    ( ! [X0] : (v15_lattices(X0) | ~v17_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0)) )),
% 58.61/8.00    inference(cnf_transformation,[],[f35])).
% 58.61/8.00  
% 58.61/8.00  fof(f3,axiom,(
% 58.61/8.00    ! [X0] : (l3_lattices(X0) => ((v15_lattices(X0) & ~v2_struct_0(X0)) => (v14_lattices(X0) & v13_lattices(X0) & ~v2_struct_0(X0))))),
% 58.61/8.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 58.61/8.00  
% 58.61/8.00  fof(f32,plain,(
% 58.61/8.00    ! [X0] : (((v14_lattices(X0) & v13_lattices(X0) & ~v2_struct_0(X0)) | (~v15_lattices(X0) | v2_struct_0(X0))) | ~l3_lattices(X0))),
% 58.61/8.00    inference(ennf_transformation,[],[f3])).
% 58.61/8.00  
% 58.61/8.00  fof(f33,plain,(
% 58.61/8.00    ! [X0] : ((v14_lattices(X0) & v13_lattices(X0) & ~v2_struct_0(X0)) | ~v15_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0))),
% 58.61/8.00    inference(flattening,[],[f32])).
% 58.61/8.00  
% 58.61/8.00  fof(f109,plain,(
% 58.61/8.00    ( ! [X0] : (v13_lattices(X0) | ~v15_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0)) )),
% 58.61/8.00    inference(cnf_transformation,[],[f33])).
% 58.61/8.00  
% 58.61/8.00  fof(f19,axiom,(
% 58.61/8.00    ! [X0] : ((l3_lattices(X0) & v13_lattices(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => k3_lattices(X0,k5_lattices(X0),X1) = X1))),
% 58.61/8.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 58.61/8.00  
% 58.61/8.00  fof(f63,plain,(
% 58.61/8.00    ! [X0] : (! [X1] : (k3_lattices(X0,k5_lattices(X0),X1) = X1 | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l3_lattices(X0) | ~v13_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0)))),
% 58.61/8.00    inference(ennf_transformation,[],[f19])).
% 58.61/8.00  
% 58.61/8.00  fof(f64,plain,(
% 58.61/8.00    ! [X0] : (! [X1] : (k3_lattices(X0,k5_lattices(X0),X1) = X1 | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v13_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0))),
% 58.61/8.00    inference(flattening,[],[f63])).
% 58.61/8.00  
% 58.61/8.00  fof(f145,plain,(
% 58.61/8.00    ( ! [X0,X1] : (k3_lattices(X0,k5_lattices(X0),X1) = X1 | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v13_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0)) )),
% 58.61/8.00    inference(cnf_transformation,[],[f64])).
% 58.61/8.00  
% 58.61/8.00  fof(f13,axiom,(
% 58.61/8.00    ! [X0] : ((l2_lattices(X0) & ~v2_struct_0(X0)) => m1_subset_1(k6_lattices(X0),u1_struct_0(X0)))),
% 58.61/8.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 58.61/8.00  
% 58.61/8.00  fof(f52,plain,(
% 58.61/8.00    ! [X0] : (m1_subset_1(k6_lattices(X0),u1_struct_0(X0)) | (~l2_lattices(X0) | v2_struct_0(X0)))),
% 58.61/8.00    inference(ennf_transformation,[],[f13])).
% 58.61/8.00  
% 58.61/8.00  fof(f53,plain,(
% 58.61/8.00    ! [X0] : (m1_subset_1(k6_lattices(X0),u1_struct_0(X0)) | ~l2_lattices(X0) | v2_struct_0(X0))),
% 58.61/8.00    inference(flattening,[],[f52])).
% 58.61/8.00  
% 58.61/8.00  fof(f138,plain,(
% 58.61/8.00    ( ! [X0] : (m1_subset_1(k6_lattices(X0),u1_struct_0(X0)) | ~l2_lattices(X0) | v2_struct_0(X0)) )),
% 58.61/8.00    inference(cnf_transformation,[],[f53])).
% 58.61/8.00  
% 58.61/8.00  fof(f9,axiom,(
% 58.61/8.00    ! [X0] : ((l2_lattices(X0) & ~v2_struct_0(X0)) => (v14_lattices(X0) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => (k6_lattices(X0) = X1 <=> ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (k1_lattices(X0,X2,X1) = X1 & k1_lattices(X0,X1,X2) = X1))))))),
% 58.61/8.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 58.61/8.00  
% 58.61/8.00  fof(f44,plain,(
% 58.61/8.00    ! [X0] : ((! [X1] : ((k6_lattices(X0) = X1 <=> ! [X2] : ((k1_lattices(X0,X2,X1) = X1 & k1_lattices(X0,X1,X2) = X1) | ~m1_subset_1(X2,u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~v14_lattices(X0)) | (~l2_lattices(X0) | v2_struct_0(X0)))),
% 58.61/8.00    inference(ennf_transformation,[],[f9])).
% 58.61/8.00  
% 58.61/8.00  fof(f45,plain,(
% 58.61/8.00    ! [X0] : (! [X1] : ((k6_lattices(X0) = X1 <=> ! [X2] : ((k1_lattices(X0,X2,X1) = X1 & k1_lattices(X0,X1,X2) = X1) | ~m1_subset_1(X2,u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~v14_lattices(X0) | ~l2_lattices(X0) | v2_struct_0(X0))),
% 58.61/8.00    inference(flattening,[],[f44])).
% 58.61/8.00  
% 58.61/8.00  fof(f85,plain,(
% 58.61/8.00    ! [X0] : (! [X1] : (((k6_lattices(X0) = X1 | ? [X2] : ((k1_lattices(X0,X2,X1) != X1 | k1_lattices(X0,X1,X2) != X1) & m1_subset_1(X2,u1_struct_0(X0)))) & (! [X2] : ((k1_lattices(X0,X2,X1) = X1 & k1_lattices(X0,X1,X2) = X1) | ~m1_subset_1(X2,u1_struct_0(X0))) | k6_lattices(X0) != X1)) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~v14_lattices(X0) | ~l2_lattices(X0) | v2_struct_0(X0))),
% 58.61/8.00    inference(nnf_transformation,[],[f45])).
% 58.61/8.00  
% 58.61/8.00  fof(f86,plain,(
% 58.61/8.00    ! [X0] : (! [X1] : (((k6_lattices(X0) = X1 | ? [X2] : ((k1_lattices(X0,X2,X1) != X1 | k1_lattices(X0,X1,X2) != X1) & m1_subset_1(X2,u1_struct_0(X0)))) & (! [X3] : ((k1_lattices(X0,X3,X1) = X1 & k1_lattices(X0,X1,X3) = X1) | ~m1_subset_1(X3,u1_struct_0(X0))) | k6_lattices(X0) != X1)) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~v14_lattices(X0) | ~l2_lattices(X0) | v2_struct_0(X0))),
% 58.61/8.00    inference(rectify,[],[f85])).
% 58.61/8.00  
% 58.61/8.00  fof(f87,plain,(
% 58.61/8.00    ! [X1,X0] : (? [X2] : ((k1_lattices(X0,X2,X1) != X1 | k1_lattices(X0,X1,X2) != X1) & m1_subset_1(X2,u1_struct_0(X0))) => ((k1_lattices(X0,sK4(X0,X1),X1) != X1 | k1_lattices(X0,X1,sK4(X0,X1)) != X1) & m1_subset_1(sK4(X0,X1),u1_struct_0(X0))))),
% 58.61/8.00    introduced(choice_axiom,[])).
% 58.61/8.00  
% 58.61/8.00  fof(f88,plain,(
% 58.61/8.00    ! [X0] : (! [X1] : (((k6_lattices(X0) = X1 | ((k1_lattices(X0,sK4(X0,X1),X1) != X1 | k1_lattices(X0,X1,sK4(X0,X1)) != X1) & m1_subset_1(sK4(X0,X1),u1_struct_0(X0)))) & (! [X3] : ((k1_lattices(X0,X3,X1) = X1 & k1_lattices(X0,X1,X3) = X1) | ~m1_subset_1(X3,u1_struct_0(X0))) | k6_lattices(X0) != X1)) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~v14_lattices(X0) | ~l2_lattices(X0) | v2_struct_0(X0))),
% 58.61/8.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f86,f87])).
% 58.61/8.00  
% 58.61/8.00  fof(f126,plain,(
% 58.61/8.00    ( ! [X0,X3,X1] : (k1_lattices(X0,X3,X1) = X1 | ~m1_subset_1(X3,u1_struct_0(X0)) | k6_lattices(X0) != X1 | ~m1_subset_1(X1,u1_struct_0(X0)) | ~v14_lattices(X0) | ~l2_lattices(X0) | v2_struct_0(X0)) )),
% 58.61/8.00    inference(cnf_transformation,[],[f88])).
% 58.61/8.00  
% 58.61/8.00  fof(f158,plain,(
% 58.61/8.00    ( ! [X0,X3] : (k1_lattices(X0,X3,k6_lattices(X0)) = k6_lattices(X0) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~m1_subset_1(k6_lattices(X0),u1_struct_0(X0)) | ~v14_lattices(X0) | ~l2_lattices(X0) | v2_struct_0(X0)) )),
% 58.61/8.00    inference(equality_resolution,[],[f126])).
% 58.61/8.00  
% 58.61/8.00  fof(f110,plain,(
% 58.61/8.00    ( ! [X0] : (v14_lattices(X0) | ~v15_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0)) )),
% 58.61/8.00    inference(cnf_transformation,[],[f33])).
% 58.61/8.00  
% 58.61/8.00  fof(f155,plain,(
% 58.61/8.00    k7_lattices(sK9,k7_lattices(sK9,sK10)) != sK10),
% 58.61/8.00    inference(cnf_transformation,[],[f101])).
% 58.61/8.00  
% 58.61/8.00  cnf(c_49,negated_conjecture,
% 58.61/8.00      ( m1_subset_1(sK10,u1_struct_0(sK9)) ),
% 58.61/8.00      inference(cnf_transformation,[],[f154]) ).
% 58.61/8.00  
% 58.61/8.00  cnf(c_2570,plain,
% 58.61/8.00      ( m1_subset_1(sK10,u1_struct_0(sK9)) = iProver_top ),
% 58.61/8.00      inference(predicate_to_equality,[status(thm)],[c_49]) ).
% 58.61/8.00  
% 58.61/8.00  cnf(c_37,plain,
% 58.61/8.00      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 58.61/8.00      | m1_subset_1(k7_lattices(X1,X0),u1_struct_0(X1))
% 58.61/8.00      | ~ l3_lattices(X1)
% 58.61/8.00      | v2_struct_0(X1) ),
% 58.61/8.00      inference(cnf_transformation,[],[f139]) ).
% 58.61/8.00  
% 58.61/8.00  cnf(c_53,negated_conjecture,
% 58.61/8.00      ( ~ v2_struct_0(sK9) ),
% 58.61/8.00      inference(cnf_transformation,[],[f150]) ).
% 58.61/8.00  
% 58.61/8.00  cnf(c_1863,plain,
% 58.61/8.00      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 58.61/8.00      | m1_subset_1(k7_lattices(X1,X0),u1_struct_0(X1))
% 58.61/8.00      | ~ l3_lattices(X1)
% 58.61/8.00      | sK9 != X1 ),
% 58.61/8.00      inference(resolution_lifted,[status(thm)],[c_37,c_53]) ).
% 58.61/8.00  
% 58.61/8.00  cnf(c_1864,plain,
% 58.61/8.00      ( ~ m1_subset_1(X0,u1_struct_0(sK9))
% 58.61/8.00      | m1_subset_1(k7_lattices(sK9,X0),u1_struct_0(sK9))
% 58.61/8.00      | ~ l3_lattices(sK9) ),
% 58.61/8.00      inference(unflattening,[status(thm)],[c_1863]) ).
% 58.61/8.00  
% 58.61/8.00  cnf(c_50,negated_conjecture,
% 58.61/8.00      ( l3_lattices(sK9) ),
% 58.61/8.00      inference(cnf_transformation,[],[f153]) ).
% 58.61/8.00  
% 58.61/8.00  cnf(c_1868,plain,
% 58.61/8.00      ( m1_subset_1(k7_lattices(sK9,X0),u1_struct_0(sK9))
% 58.61/8.00      | ~ m1_subset_1(X0,u1_struct_0(sK9)) ),
% 58.61/8.00      inference(global_propositional_subsumption,
% 58.61/8.00                [status(thm)],
% 58.61/8.00                [c_1864,c_50]) ).
% 58.61/8.00  
% 58.61/8.00  cnf(c_1869,plain,
% 58.61/8.00      ( ~ m1_subset_1(X0,u1_struct_0(sK9))
% 58.61/8.00      | m1_subset_1(k7_lattices(sK9,X0),u1_struct_0(sK9)) ),
% 58.61/8.00      inference(renaming,[status(thm)],[c_1868]) ).
% 58.61/8.00  
% 58.61/8.00  cnf(c_2546,plain,
% 58.61/8.00      ( m1_subset_1(X0,u1_struct_0(sK9)) != iProver_top
% 58.61/8.00      | m1_subset_1(k7_lattices(sK9,X0),u1_struct_0(sK9)) = iProver_top ),
% 58.61/8.00      inference(predicate_to_equality,[status(thm)],[c_1869]) ).
% 58.61/8.00  
% 58.61/8.00  cnf(c_18,plain,
% 58.61/8.00      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 58.61/8.00      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 58.61/8.00      | ~ m1_subset_1(X3,u1_struct_0(X1))
% 58.61/8.00      | ~ v11_lattices(X1)
% 58.61/8.00      | ~ l3_lattices(X1)
% 58.61/8.00      | v2_struct_0(X1)
% 58.61/8.00      | k1_lattices(X1,k2_lattices(X1,X3,X2),k2_lattices(X1,X3,X0)) = k2_lattices(X1,X3,k1_lattices(X1,X2,X0)) ),
% 58.61/8.00      inference(cnf_transformation,[],[f116]) ).
% 58.61/8.00  
% 58.61/8.00  cnf(c_1919,plain,
% 58.61/8.00      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 58.61/8.00      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 58.61/8.00      | ~ m1_subset_1(X3,u1_struct_0(X1))
% 58.61/8.00      | ~ v11_lattices(X1)
% 58.61/8.00      | ~ l3_lattices(X1)
% 58.61/8.00      | k1_lattices(X1,k2_lattices(X1,X3,X2),k2_lattices(X1,X3,X0)) = k2_lattices(X1,X3,k1_lattices(X1,X2,X0))
% 58.61/8.00      | sK9 != X1 ),
% 58.61/8.00      inference(resolution_lifted,[status(thm)],[c_18,c_53]) ).
% 58.61/8.00  
% 58.61/8.00  cnf(c_1920,plain,
% 58.61/8.00      ( ~ m1_subset_1(X0,u1_struct_0(sK9))
% 58.61/8.00      | ~ m1_subset_1(X1,u1_struct_0(sK9))
% 58.61/8.00      | ~ m1_subset_1(X2,u1_struct_0(sK9))
% 58.61/8.00      | ~ v11_lattices(sK9)
% 58.61/8.00      | ~ l3_lattices(sK9)
% 58.61/8.00      | k1_lattices(sK9,k2_lattices(sK9,X2,X1),k2_lattices(sK9,X2,X0)) = k2_lattices(sK9,X2,k1_lattices(sK9,X1,X0)) ),
% 58.61/8.00      inference(unflattening,[status(thm)],[c_1919]) ).
% 58.61/8.00  
% 58.61/8.00  cnf(c_10,plain,
% 58.61/8.00      ( v11_lattices(X0)
% 58.61/8.00      | ~ v17_lattices(X0)
% 58.61/8.00      | ~ l3_lattices(X0)
% 58.61/8.00      | v2_struct_0(X0) ),
% 58.61/8.00      inference(cnf_transformation,[],[f112]) ).
% 58.61/8.00  
% 58.61/8.00  cnf(c_51,negated_conjecture,
% 58.61/8.00      ( v17_lattices(sK9) ),
% 58.61/8.00      inference(cnf_transformation,[],[f152]) ).
% 58.61/8.00  
% 58.61/8.00  cnf(c_698,plain,
% 58.61/8.00      ( v11_lattices(X0)
% 58.61/8.00      | ~ l3_lattices(X0)
% 58.61/8.00      | v2_struct_0(X0)
% 58.61/8.00      | sK9 != X0 ),
% 58.61/8.00      inference(resolution_lifted,[status(thm)],[c_10,c_51]) ).
% 58.61/8.00  
% 58.61/8.00  cnf(c_699,plain,
% 58.61/8.00      ( v11_lattices(sK9) | ~ l3_lattices(sK9) | v2_struct_0(sK9) ),
% 58.61/8.00      inference(unflattening,[status(thm)],[c_698]) ).
% 58.61/8.00  
% 58.61/8.00  cnf(c_169,plain,
% 58.61/8.00      ( v11_lattices(sK9)
% 58.61/8.00      | ~ v17_lattices(sK9)
% 58.61/8.00      | ~ l3_lattices(sK9)
% 58.61/8.00      | v2_struct_0(sK9) ),
% 58.61/8.00      inference(instantiation,[status(thm)],[c_10]) ).
% 58.61/8.00  
% 58.61/8.00  cnf(c_701,plain,
% 58.61/8.00      ( v11_lattices(sK9) ),
% 58.61/8.00      inference(global_propositional_subsumption,
% 58.61/8.00                [status(thm)],
% 58.61/8.00                [c_699,c_53,c_51,c_50,c_169]) ).
% 58.61/8.00  
% 58.61/8.00  cnf(c_1765,plain,
% 58.61/8.00      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 58.61/8.00      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 58.61/8.00      | ~ m1_subset_1(X3,u1_struct_0(X1))
% 58.61/8.00      | ~ l3_lattices(X1)
% 58.61/8.00      | v2_struct_0(X1)
% 58.61/8.00      | k1_lattices(X1,k2_lattices(X1,X3,X2),k2_lattices(X1,X3,X0)) = k2_lattices(X1,X3,k1_lattices(X1,X2,X0))
% 58.61/8.00      | sK9 != X1 ),
% 58.61/8.00      inference(resolution_lifted,[status(thm)],[c_18,c_701]) ).
% 58.61/8.00  
% 58.61/8.00  cnf(c_1766,plain,
% 58.61/8.00      ( ~ m1_subset_1(X0,u1_struct_0(sK9))
% 58.61/8.00      | ~ m1_subset_1(X1,u1_struct_0(sK9))
% 58.61/8.00      | ~ m1_subset_1(X2,u1_struct_0(sK9))
% 58.61/8.00      | ~ l3_lattices(sK9)
% 58.61/8.00      | v2_struct_0(sK9)
% 58.61/8.00      | k1_lattices(sK9,k2_lattices(sK9,X2,X1),k2_lattices(sK9,X2,X0)) = k2_lattices(sK9,X2,k1_lattices(sK9,X1,X0)) ),
% 58.61/8.00      inference(unflattening,[status(thm)],[c_1765]) ).
% 58.61/8.00  
% 58.61/8.00  cnf(c_1923,plain,
% 58.61/8.00      ( ~ m1_subset_1(X0,u1_struct_0(sK9))
% 58.61/8.00      | ~ m1_subset_1(X1,u1_struct_0(sK9))
% 58.61/8.00      | ~ m1_subset_1(X2,u1_struct_0(sK9))
% 58.61/8.00      | k1_lattices(sK9,k2_lattices(sK9,X2,X1),k2_lattices(sK9,X2,X0)) = k2_lattices(sK9,X2,k1_lattices(sK9,X1,X0)) ),
% 58.61/8.00      inference(global_propositional_subsumption,
% 58.61/8.00                [status(thm)],
% 58.61/8.00                [c_1920,c_53,c_50,c_1766]) ).
% 58.61/8.00  
% 58.61/8.00  cnf(c_1924,plain,
% 58.61/8.00      ( ~ m1_subset_1(X0,u1_struct_0(sK9))
% 58.61/8.00      | ~ m1_subset_1(X1,u1_struct_0(sK9))
% 58.61/8.00      | ~ m1_subset_1(X2,u1_struct_0(sK9))
% 58.61/8.00      | k1_lattices(sK9,k2_lattices(sK9,X1,X2),k2_lattices(sK9,X1,X0)) = k2_lattices(sK9,X1,k1_lattices(sK9,X2,X0)) ),
% 58.61/8.00      inference(renaming,[status(thm)],[c_1923]) ).
% 58.61/8.00  
% 58.61/8.00  cnf(c_2549,plain,
% 58.61/8.00      ( k1_lattices(sK9,k2_lattices(sK9,X0,X1),k2_lattices(sK9,X0,X2)) = k2_lattices(sK9,X0,k1_lattices(sK9,X1,X2))
% 58.61/8.00      | m1_subset_1(X2,u1_struct_0(sK9)) != iProver_top
% 58.61/8.00      | m1_subset_1(X0,u1_struct_0(sK9)) != iProver_top
% 58.61/8.00      | m1_subset_1(X1,u1_struct_0(sK9)) != iProver_top ),
% 58.61/8.00      inference(predicate_to_equality,[status(thm)],[c_1924]) ).
% 58.61/8.00  
% 58.61/8.00  cnf(c_3217,plain,
% 58.61/8.00      ( k1_lattices(sK9,k2_lattices(sK9,k7_lattices(sK9,X0),X1),k2_lattices(sK9,k7_lattices(sK9,X0),X2)) = k2_lattices(sK9,k7_lattices(sK9,X0),k1_lattices(sK9,X1,X2))
% 58.61/8.00      | m1_subset_1(X0,u1_struct_0(sK9)) != iProver_top
% 58.61/8.00      | m1_subset_1(X1,u1_struct_0(sK9)) != iProver_top
% 58.61/8.00      | m1_subset_1(X2,u1_struct_0(sK9)) != iProver_top ),
% 58.61/8.00      inference(superposition,[status(thm)],[c_2546,c_2549]) ).
% 58.61/8.00  
% 58.61/8.00  cnf(c_10406,plain,
% 58.61/8.00      ( k1_lattices(sK9,k2_lattices(sK9,k7_lattices(sK9,k7_lattices(sK9,X0)),X1),k2_lattices(sK9,k7_lattices(sK9,k7_lattices(sK9,X0)),X2)) = k2_lattices(sK9,k7_lattices(sK9,k7_lattices(sK9,X0)),k1_lattices(sK9,X1,X2))
% 58.61/8.00      | m1_subset_1(X0,u1_struct_0(sK9)) != iProver_top
% 58.61/8.00      | m1_subset_1(X1,u1_struct_0(sK9)) != iProver_top
% 58.61/8.00      | m1_subset_1(X2,u1_struct_0(sK9)) != iProver_top ),
% 58.61/8.00      inference(superposition,[status(thm)],[c_2546,c_3217]) ).
% 58.61/8.00  
% 58.61/8.00  cnf(c_193769,plain,
% 58.61/8.00      ( k1_lattices(sK9,k2_lattices(sK9,k7_lattices(sK9,k7_lattices(sK9,sK10)),X0),k2_lattices(sK9,k7_lattices(sK9,k7_lattices(sK9,sK10)),X1)) = k2_lattices(sK9,k7_lattices(sK9,k7_lattices(sK9,sK10)),k1_lattices(sK9,X0,X1))
% 58.61/8.00      | m1_subset_1(X0,u1_struct_0(sK9)) != iProver_top
% 58.61/8.00      | m1_subset_1(X1,u1_struct_0(sK9)) != iProver_top ),
% 58.61/8.00      inference(superposition,[status(thm)],[c_2570,c_10406]) ).
% 58.61/8.00  
% 58.61/8.00  cnf(c_193830,plain,
% 58.61/8.00      ( k1_lattices(sK9,k2_lattices(sK9,k7_lattices(sK9,k7_lattices(sK9,sK10)),sK10),k2_lattices(sK9,k7_lattices(sK9,k7_lattices(sK9,sK10)),X0)) = k2_lattices(sK9,k7_lattices(sK9,k7_lattices(sK9,sK10)),k1_lattices(sK9,sK10,X0))
% 58.61/8.00      | m1_subset_1(X0,u1_struct_0(sK9)) != iProver_top ),
% 58.61/8.00      inference(superposition,[status(thm)],[c_2570,c_193769]) ).
% 58.61/8.00  
% 58.61/8.00  cnf(c_3214,plain,
% 58.61/8.00      ( k1_lattices(sK9,k2_lattices(sK9,sK10,X0),k2_lattices(sK9,sK10,X1)) = k2_lattices(sK9,sK10,k1_lattices(sK9,X0,X1))
% 58.61/8.00      | m1_subset_1(X0,u1_struct_0(sK9)) != iProver_top
% 58.61/8.00      | m1_subset_1(X1,u1_struct_0(sK9)) != iProver_top ),
% 58.61/8.00      inference(superposition,[status(thm)],[c_2570,c_2549]) ).
% 58.61/8.00  
% 58.61/8.00  cnf(c_3244,plain,
% 58.61/8.00      ( k1_lattices(sK9,k2_lattices(sK9,sK10,k7_lattices(sK9,X0)),k2_lattices(sK9,sK10,X1)) = k2_lattices(sK9,sK10,k1_lattices(sK9,k7_lattices(sK9,X0),X1))
% 58.61/8.00      | m1_subset_1(X0,u1_struct_0(sK9)) != iProver_top
% 58.61/8.00      | m1_subset_1(X1,u1_struct_0(sK9)) != iProver_top ),
% 58.61/8.00      inference(superposition,[status(thm)],[c_2546,c_3214]) ).
% 58.61/8.00  
% 58.61/8.00  cnf(c_15460,plain,
% 58.61/8.00      ( k1_lattices(sK9,k2_lattices(sK9,sK10,k7_lattices(sK9,sK10)),k2_lattices(sK9,sK10,X0)) = k2_lattices(sK9,sK10,k1_lattices(sK9,k7_lattices(sK9,sK10),X0))
% 58.61/8.00      | m1_subset_1(X0,u1_struct_0(sK9)) != iProver_top ),
% 58.61/8.00      inference(superposition,[status(thm)],[c_2570,c_3244]) ).
% 58.61/8.00  
% 58.61/8.00  cnf(c_3,plain,
% 58.61/8.00      ( v6_lattices(X0)
% 58.61/8.00      | ~ l3_lattices(X0)
% 58.61/8.00      | v2_struct_0(X0)
% 58.61/8.00      | ~ v10_lattices(X0) ),
% 58.61/8.00      inference(cnf_transformation,[],[f105]) ).
% 58.61/8.00  
% 58.61/8.00  cnf(c_13,plain,
% 58.61/8.00      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 58.61/8.00      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 58.61/8.00      | ~ l1_lattices(X1)
% 58.61/8.00      | ~ v6_lattices(X1)
% 58.61/8.00      | v2_struct_0(X1)
% 58.61/8.00      | k4_lattices(X1,X0,X2) = k4_lattices(X1,X2,X0) ),
% 58.61/8.00      inference(cnf_transformation,[],[f115]) ).
% 58.61/8.00  
% 58.61/8.00  cnf(c_814,plain,
% 58.61/8.00      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 58.61/8.00      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 58.61/8.00      | ~ l1_lattices(X1)
% 58.61/8.00      | ~ l3_lattices(X3)
% 58.61/8.00      | v2_struct_0(X3)
% 58.61/8.00      | v2_struct_0(X1)
% 58.61/8.00      | ~ v10_lattices(X3)
% 58.61/8.00      | X1 != X3
% 58.61/8.00      | k4_lattices(X1,X0,X2) = k4_lattices(X1,X2,X0) ),
% 58.61/8.00      inference(resolution_lifted,[status(thm)],[c_3,c_13]) ).
% 58.61/8.00  
% 58.61/8.00  cnf(c_815,plain,
% 58.61/8.00      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 58.61/8.00      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 58.61/8.00      | ~ l1_lattices(X1)
% 58.61/8.00      | ~ l3_lattices(X1)
% 58.61/8.00      | v2_struct_0(X1)
% 58.61/8.00      | ~ v10_lattices(X1)
% 58.61/8.00      | k4_lattices(X1,X0,X2) = k4_lattices(X1,X2,X0) ),
% 58.61/8.00      inference(unflattening,[status(thm)],[c_814]) ).
% 58.61/8.00  
% 58.61/8.00  cnf(c_39,plain,
% 58.61/8.00      ( l1_lattices(X0) | ~ l3_lattices(X0) ),
% 58.61/8.00      inference(cnf_transformation,[],[f140]) ).
% 58.61/8.00  
% 58.61/8.00  cnf(c_833,plain,
% 58.61/8.00      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 58.61/8.00      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 58.61/8.00      | ~ l3_lattices(X1)
% 58.61/8.00      | v2_struct_0(X1)
% 58.61/8.00      | ~ v10_lattices(X1)
% 58.61/8.00      | k4_lattices(X1,X0,X2) = k4_lattices(X1,X2,X0) ),
% 58.61/8.00      inference(forward_subsumption_resolution,
% 58.61/8.00                [status(thm)],
% 58.61/8.00                [c_815,c_39]) ).
% 58.61/8.00  
% 58.61/8.00  cnf(c_52,negated_conjecture,
% 58.61/8.00      ( v10_lattices(sK9) ),
% 58.61/8.00      inference(cnf_transformation,[],[f151]) ).
% 58.61/8.00  
% 58.61/8.00  cnf(c_1304,plain,
% 58.61/8.00      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 58.61/8.00      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 58.61/8.00      | ~ l3_lattices(X1)
% 58.61/8.00      | v2_struct_0(X1)
% 58.61/8.00      | k4_lattices(X1,X2,X0) = k4_lattices(X1,X0,X2)
% 58.61/8.00      | sK9 != X1 ),
% 58.61/8.00      inference(resolution_lifted,[status(thm)],[c_833,c_52]) ).
% 58.61/8.00  
% 58.61/8.00  cnf(c_1305,plain,
% 58.61/8.00      ( ~ m1_subset_1(X0,u1_struct_0(sK9))
% 58.61/8.00      | ~ m1_subset_1(X1,u1_struct_0(sK9))
% 58.61/8.00      | ~ l3_lattices(sK9)
% 58.61/8.00      | v2_struct_0(sK9)
% 58.61/8.00      | k4_lattices(sK9,X1,X0) = k4_lattices(sK9,X0,X1) ),
% 58.61/8.00      inference(unflattening,[status(thm)],[c_1304]) ).
% 58.61/8.00  
% 58.61/8.00  cnf(c_1309,plain,
% 58.61/8.00      ( ~ m1_subset_1(X0,u1_struct_0(sK9))
% 58.61/8.00      | ~ m1_subset_1(X1,u1_struct_0(sK9))
% 58.61/8.00      | k4_lattices(sK9,X1,X0) = k4_lattices(sK9,X0,X1) ),
% 58.61/8.00      inference(global_propositional_subsumption,
% 58.61/8.00                [status(thm)],
% 58.61/8.00                [c_1305,c_53,c_50]) ).
% 58.61/8.00  
% 58.61/8.00  cnf(c_2556,plain,
% 58.61/8.00      ( k4_lattices(sK9,X0,X1) = k4_lattices(sK9,X1,X0)
% 58.61/8.00      | m1_subset_1(X1,u1_struct_0(sK9)) != iProver_top
% 58.61/8.00      | m1_subset_1(X0,u1_struct_0(sK9)) != iProver_top ),
% 58.61/8.00      inference(predicate_to_equality,[status(thm)],[c_1309]) ).
% 58.61/8.00  
% 58.61/8.00  cnf(c_4192,plain,
% 58.61/8.00      ( k4_lattices(sK9,sK10,X0) = k4_lattices(sK9,X0,sK10)
% 58.61/8.00      | m1_subset_1(X0,u1_struct_0(sK9)) != iProver_top ),
% 58.61/8.00      inference(superposition,[status(thm)],[c_2570,c_2556]) ).
% 58.61/8.00  
% 58.61/8.00  cnf(c_4212,plain,
% 58.61/8.00      ( k4_lattices(sK9,k7_lattices(sK9,X0),sK10) = k4_lattices(sK9,sK10,k7_lattices(sK9,X0))
% 58.61/8.00      | m1_subset_1(X0,u1_struct_0(sK9)) != iProver_top ),
% 58.61/8.00      inference(superposition,[status(thm)],[c_2546,c_4192]) ).
% 58.61/8.00  
% 58.61/8.00  cnf(c_5553,plain,
% 58.61/8.00      ( k4_lattices(sK9,sK10,k7_lattices(sK9,sK10)) = k4_lattices(sK9,k7_lattices(sK9,sK10),sK10) ),
% 58.61/8.00      inference(superposition,[status(thm)],[c_2570,c_4212]) ).
% 58.61/8.00  
% 58.61/8.00  cnf(c_46,plain,
% 58.61/8.00      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 58.61/8.00      | ~ v17_lattices(X1)
% 58.61/8.00      | ~ l3_lattices(X1)
% 58.61/8.00      | v2_struct_0(X1)
% 58.61/8.00      | ~ v10_lattices(X1)
% 58.61/8.00      | k4_lattices(X1,k7_lattices(X1,X0),X0) = k5_lattices(X1) ),
% 58.61/8.00      inference(cnf_transformation,[],[f148]) ).
% 58.61/8.00  
% 58.61/8.00  cnf(c_727,plain,
% 58.61/8.00      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 58.61/8.00      | ~ l3_lattices(X1)
% 58.61/8.00      | v2_struct_0(X1)
% 58.61/8.00      | ~ v10_lattices(X1)
% 58.61/8.00      | k4_lattices(X1,k7_lattices(X1,X0),X0) = k5_lattices(X1)
% 58.61/8.00      | sK9 != X1 ),
% 58.61/8.00      inference(resolution_lifted,[status(thm)],[c_46,c_51]) ).
% 58.61/8.00  
% 58.61/8.00  cnf(c_728,plain,
% 58.61/8.00      ( ~ m1_subset_1(X0,u1_struct_0(sK9))
% 58.61/8.00      | ~ l3_lattices(sK9)
% 58.61/8.00      | v2_struct_0(sK9)
% 58.61/8.00      | ~ v10_lattices(sK9)
% 58.61/8.00      | k4_lattices(sK9,k7_lattices(sK9,X0),X0) = k5_lattices(sK9) ),
% 58.61/8.00      inference(unflattening,[status(thm)],[c_727]) ).
% 58.61/8.00  
% 58.61/8.00  cnf(c_732,plain,
% 58.61/8.00      ( ~ m1_subset_1(X0,u1_struct_0(sK9))
% 58.61/8.00      | k4_lattices(sK9,k7_lattices(sK9,X0),X0) = k5_lattices(sK9) ),
% 58.61/8.00      inference(global_propositional_subsumption,
% 58.61/8.00                [status(thm)],
% 58.61/8.00                [c_728,c_53,c_52,c_50]) ).
% 58.61/8.00  
% 58.61/8.00  cnf(c_2568,plain,
% 58.61/8.00      ( k4_lattices(sK9,k7_lattices(sK9,X0),X0) = k5_lattices(sK9)
% 58.61/8.00      | m1_subset_1(X0,u1_struct_0(sK9)) != iProver_top ),
% 58.61/8.00      inference(predicate_to_equality,[status(thm)],[c_732]) ).
% 58.61/8.00  
% 58.61/8.00  cnf(c_3140,plain,
% 58.61/8.00      ( k4_lattices(sK9,k7_lattices(sK9,sK10),sK10) = k5_lattices(sK9) ),
% 58.61/8.00      inference(superposition,[status(thm)],[c_2570,c_2568]) ).
% 58.61/8.00  
% 58.61/8.00  cnf(c_5558,plain,
% 58.61/8.00      ( k4_lattices(sK9,sK10,k7_lattices(sK9,sK10)) = k5_lattices(sK9) ),
% 58.61/8.00      inference(light_normalisation,[status(thm)],[c_5553,c_3140]) ).
% 58.61/8.00  
% 58.61/8.00  cnf(c_41,plain,
% 58.61/8.00      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 58.61/8.00      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 58.61/8.00      | ~ l1_lattices(X1)
% 58.61/8.00      | ~ v6_lattices(X1)
% 58.61/8.00      | v2_struct_0(X1)
% 58.61/8.00      | k2_lattices(X1,X2,X0) = k4_lattices(X1,X2,X0) ),
% 58.61/8.00      inference(cnf_transformation,[],[f143]) ).
% 58.61/8.00  
% 58.61/8.00  cnf(c_785,plain,
% 58.61/8.00      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 58.61/8.00      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 58.61/8.00      | ~ l1_lattices(X1)
% 58.61/8.00      | ~ l3_lattices(X3)
% 58.61/8.00      | v2_struct_0(X3)
% 58.61/8.00      | v2_struct_0(X1)
% 58.61/8.00      | ~ v10_lattices(X3)
% 58.61/8.00      | X1 != X3
% 58.61/8.00      | k2_lattices(X1,X2,X0) = k4_lattices(X1,X2,X0) ),
% 58.61/8.00      inference(resolution_lifted,[status(thm)],[c_3,c_41]) ).
% 58.61/8.00  
% 58.61/8.00  cnf(c_786,plain,
% 58.61/8.00      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 58.61/8.00      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 58.61/8.00      | ~ l1_lattices(X1)
% 58.61/8.00      | ~ l3_lattices(X1)
% 58.61/8.00      | v2_struct_0(X1)
% 58.61/8.00      | ~ v10_lattices(X1)
% 58.61/8.00      | k2_lattices(X1,X2,X0) = k4_lattices(X1,X2,X0) ),
% 58.61/8.00      inference(unflattening,[status(thm)],[c_785]) ).
% 58.61/8.00  
% 58.61/8.00  cnf(c_804,plain,
% 58.61/8.00      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 58.61/8.00      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 58.61/8.00      | ~ l3_lattices(X1)
% 58.61/8.00      | v2_struct_0(X1)
% 58.61/8.00      | ~ v10_lattices(X1)
% 58.61/8.00      | k2_lattices(X1,X2,X0) = k4_lattices(X1,X2,X0) ),
% 58.61/8.00      inference(forward_subsumption_resolution,
% 58.61/8.00                [status(thm)],
% 58.61/8.00                [c_786,c_39]) ).
% 58.61/8.00  
% 58.61/8.00  cnf(c_1325,plain,
% 58.61/8.00      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 58.61/8.00      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 58.61/8.00      | ~ l3_lattices(X1)
% 58.61/8.00      | v2_struct_0(X1)
% 58.61/8.00      | k2_lattices(X1,X2,X0) = k4_lattices(X1,X2,X0)
% 58.61/8.00      | sK9 != X1 ),
% 58.61/8.00      inference(resolution_lifted,[status(thm)],[c_804,c_52]) ).
% 58.61/8.00  
% 58.61/8.00  cnf(c_1326,plain,
% 58.61/8.00      ( ~ m1_subset_1(X0,u1_struct_0(sK9))
% 58.61/8.00      | ~ m1_subset_1(X1,u1_struct_0(sK9))
% 58.61/8.00      | ~ l3_lattices(sK9)
% 58.61/8.00      | v2_struct_0(sK9)
% 58.61/8.00      | k2_lattices(sK9,X1,X0) = k4_lattices(sK9,X1,X0) ),
% 58.61/8.00      inference(unflattening,[status(thm)],[c_1325]) ).
% 58.61/8.00  
% 58.61/8.00  cnf(c_1330,plain,
% 58.61/8.00      ( ~ m1_subset_1(X0,u1_struct_0(sK9))
% 58.61/8.00      | ~ m1_subset_1(X1,u1_struct_0(sK9))
% 58.61/8.00      | k2_lattices(sK9,X1,X0) = k4_lattices(sK9,X1,X0) ),
% 58.61/8.00      inference(global_propositional_subsumption,
% 58.61/8.00                [status(thm)],
% 58.61/8.00                [c_1326,c_53,c_50]) ).
% 58.61/8.00  
% 58.61/8.00  cnf(c_2555,plain,
% 58.61/8.00      ( k2_lattices(sK9,X0,X1) = k4_lattices(sK9,X0,X1)
% 58.61/8.00      | m1_subset_1(X1,u1_struct_0(sK9)) != iProver_top
% 58.61/8.00      | m1_subset_1(X0,u1_struct_0(sK9)) != iProver_top ),
% 58.61/8.00      inference(predicate_to_equality,[status(thm)],[c_1330]) ).
% 58.61/8.00  
% 58.61/8.00  cnf(c_4038,plain,
% 58.61/8.00      ( k2_lattices(sK9,sK10,X0) = k4_lattices(sK9,sK10,X0)
% 58.61/8.00      | m1_subset_1(X0,u1_struct_0(sK9)) != iProver_top ),
% 58.61/8.00      inference(superposition,[status(thm)],[c_2570,c_2555]) ).
% 58.61/8.00  
% 58.61/8.00  cnf(c_4186,plain,
% 58.61/8.00      ( k2_lattices(sK9,sK10,k7_lattices(sK9,X0)) = k4_lattices(sK9,sK10,k7_lattices(sK9,X0))
% 58.61/8.00      | m1_subset_1(X0,u1_struct_0(sK9)) != iProver_top ),
% 58.61/8.00      inference(superposition,[status(thm)],[c_2546,c_4038]) ).
% 58.61/8.00  
% 58.61/8.00  cnf(c_5525,plain,
% 58.61/8.00      ( k2_lattices(sK9,sK10,k7_lattices(sK9,sK10)) = k4_lattices(sK9,sK10,k7_lattices(sK9,sK10)) ),
% 58.61/8.00      inference(superposition,[status(thm)],[c_2570,c_4186]) ).
% 58.61/8.00  
% 58.61/8.00  cnf(c_5565,plain,
% 58.61/8.00      ( k2_lattices(sK9,sK10,k7_lattices(sK9,sK10)) = k5_lattices(sK9) ),
% 58.61/8.00      inference(demodulation,[status(thm)],[c_5558,c_5525]) ).
% 58.61/8.00  
% 58.61/8.00  cnf(c_15468,plain,
% 58.61/8.00      ( k2_lattices(sK9,sK10,k1_lattices(sK9,k7_lattices(sK9,sK10),X0)) = k1_lattices(sK9,k5_lattices(sK9),k2_lattices(sK9,sK10,X0))
% 58.61/8.00      | m1_subset_1(X0,u1_struct_0(sK9)) != iProver_top ),
% 58.61/8.00      inference(light_normalisation,[status(thm)],[c_15460,c_5565]) ).
% 58.61/8.00  
% 58.61/8.00  cnf(c_15643,plain,
% 58.61/8.00      ( k2_lattices(sK9,sK10,k1_lattices(sK9,k7_lattices(sK9,sK10),k7_lattices(sK9,X0))) = k1_lattices(sK9,k5_lattices(sK9),k2_lattices(sK9,sK10,k7_lattices(sK9,X0)))
% 58.61/8.00      | m1_subset_1(X0,u1_struct_0(sK9)) != iProver_top ),
% 58.61/8.00      inference(superposition,[status(thm)],[c_2546,c_15468]) ).
% 58.61/8.00  
% 58.61/8.00  cnf(c_52700,plain,
% 58.61/8.00      ( k2_lattices(sK9,sK10,k1_lattices(sK9,k7_lattices(sK9,sK10),k7_lattices(sK9,k7_lattices(sK9,X0)))) = k1_lattices(sK9,k5_lattices(sK9),k2_lattices(sK9,sK10,k7_lattices(sK9,k7_lattices(sK9,X0))))
% 58.61/8.00      | m1_subset_1(X0,u1_struct_0(sK9)) != iProver_top ),
% 58.61/8.00      inference(superposition,[status(thm)],[c_2546,c_15643]) ).
% 58.61/8.00  
% 58.61/8.00  cnf(c_70476,plain,
% 58.61/8.00      ( k2_lattices(sK9,sK10,k1_lattices(sK9,k7_lattices(sK9,sK10),k7_lattices(sK9,k7_lattices(sK9,sK10)))) = k1_lattices(sK9,k5_lattices(sK9),k2_lattices(sK9,sK10,k7_lattices(sK9,k7_lattices(sK9,sK10)))) ),
% 58.61/8.00      inference(superposition,[status(thm)],[c_2570,c_52700]) ).
% 58.61/8.00  
% 58.61/8.00  cnf(c_4,plain,
% 58.61/8.00      ( v4_lattices(X0)
% 58.61/8.00      | ~ l3_lattices(X0)
% 58.61/8.00      | v2_struct_0(X0)
% 58.61/8.00      | ~ v10_lattices(X0) ),
% 58.61/8.00      inference(cnf_transformation,[],[f104]) ).
% 58.61/8.00  
% 58.61/8.00  cnf(c_12,plain,
% 58.61/8.00      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 58.61/8.00      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 58.61/8.00      | ~ l2_lattices(X1)
% 58.61/8.00      | ~ v4_lattices(X1)
% 58.61/8.00      | v2_struct_0(X1)
% 58.61/8.00      | k3_lattices(X1,X0,X2) = k3_lattices(X1,X2,X0) ),
% 58.61/8.00      inference(cnf_transformation,[],[f114]) ).
% 58.61/8.00  
% 58.61/8.00  cnf(c_633,plain,
% 58.61/8.00      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 58.61/8.00      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 58.61/8.00      | ~ l2_lattices(X1)
% 58.61/8.00      | ~ l3_lattices(X3)
% 58.61/8.00      | v2_struct_0(X3)
% 58.61/8.00      | v2_struct_0(X1)
% 58.61/8.00      | ~ v10_lattices(X3)
% 58.61/8.00      | X1 != X3
% 58.61/8.00      | k3_lattices(X1,X0,X2) = k3_lattices(X1,X2,X0) ),
% 58.61/8.00      inference(resolution_lifted,[status(thm)],[c_4,c_12]) ).
% 58.61/8.00  
% 58.61/8.00  cnf(c_634,plain,
% 58.61/8.00      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 58.61/8.00      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 58.61/8.00      | ~ l2_lattices(X1)
% 58.61/8.00      | ~ l3_lattices(X1)
% 58.61/8.00      | v2_struct_0(X1)
% 58.61/8.00      | ~ v10_lattices(X1)
% 58.61/8.00      | k3_lattices(X1,X0,X2) = k3_lattices(X1,X2,X0) ),
% 58.61/8.00      inference(unflattening,[status(thm)],[c_633]) ).
% 58.61/8.00  
% 58.61/8.00  cnf(c_38,plain,
% 58.61/8.00      ( l2_lattices(X0) | ~ l3_lattices(X0) ),
% 58.61/8.00      inference(cnf_transformation,[],[f141]) ).
% 58.61/8.00  
% 58.61/8.00  cnf(c_652,plain,
% 58.61/8.00      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 58.61/8.00      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 58.61/8.00      | ~ l3_lattices(X1)
% 58.61/8.00      | v2_struct_0(X1)
% 58.61/8.00      | ~ v10_lattices(X1)
% 58.61/8.00      | k3_lattices(X1,X0,X2) = k3_lattices(X1,X2,X0) ),
% 58.61/8.00      inference(forward_subsumption_resolution,
% 58.61/8.00                [status(thm)],
% 58.61/8.00                [c_634,c_38]) ).
% 58.61/8.00  
% 58.61/8.00  cnf(c_1364,plain,
% 58.61/8.00      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 58.61/8.00      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 58.61/8.00      | ~ l3_lattices(X1)
% 58.61/8.00      | v2_struct_0(X1)
% 58.61/8.00      | k3_lattices(X1,X2,X0) = k3_lattices(X1,X0,X2)
% 58.61/8.00      | sK9 != X1 ),
% 58.61/8.00      inference(resolution_lifted,[status(thm)],[c_652,c_52]) ).
% 58.61/8.00  
% 58.61/8.00  cnf(c_1365,plain,
% 58.61/8.00      ( ~ m1_subset_1(X0,u1_struct_0(sK9))
% 58.61/8.00      | ~ m1_subset_1(X1,u1_struct_0(sK9))
% 58.61/8.00      | ~ l3_lattices(sK9)
% 58.61/8.00      | v2_struct_0(sK9)
% 58.61/8.00      | k3_lattices(sK9,X1,X0) = k3_lattices(sK9,X0,X1) ),
% 58.61/8.00      inference(unflattening,[status(thm)],[c_1364]) ).
% 58.61/8.00  
% 58.61/8.00  cnf(c_1369,plain,
% 58.61/8.00      ( ~ m1_subset_1(X0,u1_struct_0(sK9))
% 58.61/8.00      | ~ m1_subset_1(X1,u1_struct_0(sK9))
% 58.61/8.00      | k3_lattices(sK9,X1,X0) = k3_lattices(sK9,X0,X1) ),
% 58.61/8.00      inference(global_propositional_subsumption,
% 58.61/8.00                [status(thm)],
% 58.61/8.00                [c_1365,c_53,c_50]) ).
% 58.61/8.00  
% 58.61/8.00  cnf(c_2553,plain,
% 58.61/8.00      ( k3_lattices(sK9,X0,X1) = k3_lattices(sK9,X1,X0)
% 58.61/8.00      | m1_subset_1(X1,u1_struct_0(sK9)) != iProver_top
% 58.61/8.00      | m1_subset_1(X0,u1_struct_0(sK9)) != iProver_top ),
% 58.61/8.00      inference(predicate_to_equality,[status(thm)],[c_1369]) ).
% 58.61/8.00  
% 58.61/8.00  cnf(c_3814,plain,
% 58.61/8.00      ( k3_lattices(sK9,sK10,X0) = k3_lattices(sK9,X0,sK10)
% 58.61/8.00      | m1_subset_1(X0,u1_struct_0(sK9)) != iProver_top ),
% 58.61/8.00      inference(superposition,[status(thm)],[c_2570,c_2553]) ).
% 58.61/8.00  
% 58.61/8.00  cnf(c_3930,plain,
% 58.61/8.00      ( k3_lattices(sK9,k7_lattices(sK9,X0),sK10) = k3_lattices(sK9,sK10,k7_lattices(sK9,X0))
% 58.61/8.00      | m1_subset_1(X0,u1_struct_0(sK9)) != iProver_top ),
% 58.61/8.00      inference(superposition,[status(thm)],[c_2546,c_3814]) ).
% 58.61/8.00  
% 58.61/8.00  cnf(c_5505,plain,
% 58.61/8.00      ( k3_lattices(sK9,sK10,k7_lattices(sK9,sK10)) = k3_lattices(sK9,k7_lattices(sK9,sK10),sK10) ),
% 58.61/8.00      inference(superposition,[status(thm)],[c_2570,c_3930]) ).
% 58.61/8.00  
% 58.61/8.00  cnf(c_47,plain,
% 58.61/8.00      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 58.61/8.00      | ~ v17_lattices(X1)
% 58.61/8.00      | ~ l3_lattices(X1)
% 58.61/8.00      | v2_struct_0(X1)
% 58.61/8.00      | ~ v10_lattices(X1)
% 58.61/8.00      | k3_lattices(X1,k7_lattices(X1,X0),X0) = k6_lattices(X1) ),
% 58.61/8.00      inference(cnf_transformation,[],[f149]) ).
% 58.61/8.00  
% 58.61/8.00  cnf(c_709,plain,
% 58.61/8.00      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 58.61/8.00      | ~ l3_lattices(X1)
% 58.61/8.00      | v2_struct_0(X1)
% 58.61/8.00      | ~ v10_lattices(X1)
% 58.61/8.00      | k3_lattices(X1,k7_lattices(X1,X0),X0) = k6_lattices(X1)
% 58.61/8.00      | sK9 != X1 ),
% 58.61/8.00      inference(resolution_lifted,[status(thm)],[c_47,c_51]) ).
% 58.61/8.00  
% 58.61/8.00  cnf(c_710,plain,
% 58.61/8.00      ( ~ m1_subset_1(X0,u1_struct_0(sK9))
% 58.61/8.00      | ~ l3_lattices(sK9)
% 58.61/8.00      | v2_struct_0(sK9)
% 58.61/8.00      | ~ v10_lattices(sK9)
% 58.61/8.00      | k3_lattices(sK9,k7_lattices(sK9,X0),X0) = k6_lattices(sK9) ),
% 58.61/8.00      inference(unflattening,[status(thm)],[c_709]) ).
% 58.61/8.00  
% 58.61/8.00  cnf(c_714,plain,
% 58.61/8.00      ( ~ m1_subset_1(X0,u1_struct_0(sK9))
% 58.61/8.00      | k3_lattices(sK9,k7_lattices(sK9,X0),X0) = k6_lattices(sK9) ),
% 58.61/8.00      inference(global_propositional_subsumption,
% 58.61/8.00                [status(thm)],
% 58.61/8.00                [c_710,c_53,c_52,c_50]) ).
% 58.61/8.00  
% 58.61/8.00  cnf(c_2569,plain,
% 58.61/8.00      ( k3_lattices(sK9,k7_lattices(sK9,X0),X0) = k6_lattices(sK9)
% 58.61/8.00      | m1_subset_1(X0,u1_struct_0(sK9)) != iProver_top ),
% 58.61/8.00      inference(predicate_to_equality,[status(thm)],[c_714]) ).
% 58.61/8.00  
% 58.61/8.00  cnf(c_3258,plain,
% 58.61/8.00      ( k3_lattices(sK9,k7_lattices(sK9,sK10),sK10) = k6_lattices(sK9) ),
% 58.61/8.00      inference(superposition,[status(thm)],[c_2570,c_2569]) ).
% 58.61/8.00  
% 58.61/8.00  cnf(c_5510,plain,
% 58.61/8.00      ( k3_lattices(sK9,sK10,k7_lattices(sK9,sK10)) = k6_lattices(sK9) ),
% 58.61/8.00      inference(light_normalisation,[status(thm)],[c_5505,c_3258]) ).
% 58.61/8.00  
% 58.61/8.00  cnf(c_40,plain,
% 58.61/8.00      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 58.61/8.00      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 58.61/8.00      | ~ l2_lattices(X1)
% 58.61/8.00      | ~ v4_lattices(X1)
% 58.61/8.00      | v2_struct_0(X1)
% 58.61/8.00      | k1_lattices(X1,X2,X0) = k3_lattices(X1,X2,X0) ),
% 58.61/8.00      inference(cnf_transformation,[],[f142]) ).
% 58.61/8.00  
% 58.61/8.00  cnf(c_604,plain,
% 58.61/8.00      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 58.61/8.00      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 58.61/8.00      | ~ l2_lattices(X1)
% 58.61/8.00      | ~ l3_lattices(X3)
% 58.61/8.00      | v2_struct_0(X3)
% 58.61/8.00      | v2_struct_0(X1)
% 58.61/8.00      | ~ v10_lattices(X3)
% 58.61/8.00      | X1 != X3
% 58.61/8.00      | k1_lattices(X1,X2,X0) = k3_lattices(X1,X2,X0) ),
% 58.61/8.00      inference(resolution_lifted,[status(thm)],[c_4,c_40]) ).
% 58.61/8.00  
% 58.61/8.00  cnf(c_605,plain,
% 58.61/8.00      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 58.61/8.00      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 58.61/8.00      | ~ l2_lattices(X1)
% 58.61/8.00      | ~ l3_lattices(X1)
% 58.61/8.00      | v2_struct_0(X1)
% 58.61/8.00      | ~ v10_lattices(X1)
% 58.61/8.00      | k1_lattices(X1,X2,X0) = k3_lattices(X1,X2,X0) ),
% 58.61/8.00      inference(unflattening,[status(thm)],[c_604]) ).
% 58.61/8.00  
% 58.61/8.00  cnf(c_623,plain,
% 58.61/8.00      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 58.61/8.00      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 58.61/8.00      | ~ l3_lattices(X1)
% 58.61/8.00      | v2_struct_0(X1)
% 58.61/8.00      | ~ v10_lattices(X1)
% 58.61/8.00      | k1_lattices(X1,X2,X0) = k3_lattices(X1,X2,X0) ),
% 58.61/8.00      inference(forward_subsumption_resolution,
% 58.61/8.00                [status(thm)],
% 58.61/8.00                [c_605,c_38]) ).
% 58.61/8.00  
% 58.61/8.00  cnf(c_1385,plain,
% 58.61/8.00      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 58.61/8.00      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 58.61/8.00      | ~ l3_lattices(X1)
% 58.61/8.00      | v2_struct_0(X1)
% 58.61/8.00      | k1_lattices(X1,X2,X0) = k3_lattices(X1,X2,X0)
% 58.61/8.00      | sK9 != X1 ),
% 58.61/8.00      inference(resolution_lifted,[status(thm)],[c_623,c_52]) ).
% 58.61/8.00  
% 58.61/8.00  cnf(c_1386,plain,
% 58.61/8.00      ( ~ m1_subset_1(X0,u1_struct_0(sK9))
% 58.61/8.00      | ~ m1_subset_1(X1,u1_struct_0(sK9))
% 58.61/8.00      | ~ l3_lattices(sK9)
% 58.61/8.00      | v2_struct_0(sK9)
% 58.61/8.00      | k1_lattices(sK9,X1,X0) = k3_lattices(sK9,X1,X0) ),
% 58.61/8.00      inference(unflattening,[status(thm)],[c_1385]) ).
% 58.61/8.00  
% 58.61/8.00  cnf(c_1390,plain,
% 58.61/8.00      ( ~ m1_subset_1(X0,u1_struct_0(sK9))
% 58.61/8.00      | ~ m1_subset_1(X1,u1_struct_0(sK9))
% 58.61/8.00      | k1_lattices(sK9,X1,X0) = k3_lattices(sK9,X1,X0) ),
% 58.61/8.00      inference(global_propositional_subsumption,
% 58.61/8.00                [status(thm)],
% 58.61/8.00                [c_1386,c_53,c_50]) ).
% 58.61/8.00  
% 58.61/8.00  cnf(c_2552,plain,
% 58.61/8.00      ( k1_lattices(sK9,X0,X1) = k3_lattices(sK9,X0,X1)
% 58.61/8.00      | m1_subset_1(X1,u1_struct_0(sK9)) != iProver_top
% 58.61/8.00      | m1_subset_1(X0,u1_struct_0(sK9)) != iProver_top ),
% 58.61/8.00      inference(predicate_to_equality,[status(thm)],[c_1390]) ).
% 58.61/8.00  
% 58.61/8.00  cnf(c_3791,plain,
% 58.61/8.00      ( k1_lattices(sK9,sK10,X0) = k3_lattices(sK9,sK10,X0)
% 58.61/8.00      | m1_subset_1(X0,u1_struct_0(sK9)) != iProver_top ),
% 58.61/8.00      inference(superposition,[status(thm)],[c_2570,c_2552]) ).
% 58.61/8.00  
% 58.61/8.00  cnf(c_3834,plain,
% 58.61/8.00      ( k1_lattices(sK9,sK10,k7_lattices(sK9,X0)) = k3_lattices(sK9,sK10,k7_lattices(sK9,X0))
% 58.61/8.00      | m1_subset_1(X0,u1_struct_0(sK9)) != iProver_top ),
% 58.61/8.00      inference(superposition,[status(thm)],[c_2546,c_3791]) ).
% 58.61/8.00  
% 58.61/8.00  cnf(c_5314,plain,
% 58.61/8.00      ( k1_lattices(sK9,sK10,k7_lattices(sK9,sK10)) = k3_lattices(sK9,sK10,k7_lattices(sK9,sK10)) ),
% 58.61/8.00      inference(superposition,[status(thm)],[c_2570,c_3834]) ).
% 58.61/8.00  
% 58.61/8.00  cnf(c_34,plain,
% 58.61/8.00      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 58.61/8.00      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 58.61/8.00      | ~ l3_lattices(X1)
% 58.61/8.00      | v2_struct_0(X1)
% 58.61/8.00      | ~ v9_lattices(X1)
% 58.61/8.00      | k2_lattices(X1,X2,k1_lattices(X1,X2,X0)) = X2 ),
% 58.61/8.00      inference(cnf_transformation,[],[f133]) ).
% 58.61/8.00  
% 58.61/8.00  cnf(c_1881,plain,
% 58.61/8.00      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 58.61/8.00      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 58.61/8.00      | ~ l3_lattices(X1)
% 58.61/8.00      | ~ v9_lattices(X1)
% 58.61/8.00      | k2_lattices(X1,X2,k1_lattices(X1,X2,X0)) = X2
% 58.61/8.00      | sK9 != X1 ),
% 58.61/8.00      inference(resolution_lifted,[status(thm)],[c_34,c_53]) ).
% 58.61/8.00  
% 58.61/8.00  cnf(c_1882,plain,
% 58.61/8.00      ( ~ m1_subset_1(X0,u1_struct_0(sK9))
% 58.61/8.00      | ~ m1_subset_1(X1,u1_struct_0(sK9))
% 58.61/8.00      | ~ l3_lattices(sK9)
% 58.61/8.00      | ~ v9_lattices(sK9)
% 58.61/8.00      | k2_lattices(sK9,X1,k1_lattices(sK9,X1,X0)) = X1 ),
% 58.61/8.00      inference(unflattening,[status(thm)],[c_1881]) ).
% 58.61/8.00  
% 58.61/8.00  cnf(c_1,plain,
% 58.61/8.00      ( ~ l3_lattices(X0)
% 58.61/8.00      | v2_struct_0(X0)
% 58.61/8.00      | ~ v10_lattices(X0)
% 58.61/8.00      | v9_lattices(X0) ),
% 58.61/8.00      inference(cnf_transformation,[],[f107]) ).
% 58.61/8.00  
% 58.61/8.00  cnf(c_1293,plain,
% 58.61/8.00      ( ~ l3_lattices(X0)
% 58.61/8.00      | v2_struct_0(X0)
% 58.61/8.00      | v9_lattices(X0)
% 58.61/8.00      | sK9 != X0 ),
% 58.61/8.00      inference(resolution_lifted,[status(thm)],[c_1,c_52]) ).
% 58.61/8.00  
% 58.61/8.00  cnf(c_1294,plain,
% 58.61/8.00      ( ~ l3_lattices(sK9) | v2_struct_0(sK9) | v9_lattices(sK9) ),
% 58.61/8.00      inference(unflattening,[status(thm)],[c_1293]) ).
% 58.61/8.00  
% 58.61/8.00  cnf(c_192,plain,
% 58.61/8.00      ( ~ l3_lattices(sK9)
% 58.61/8.00      | v2_struct_0(sK9)
% 58.61/8.00      | ~ v10_lattices(sK9)
% 58.61/8.00      | v9_lattices(sK9) ),
% 58.61/8.00      inference(instantiation,[status(thm)],[c_1]) ).
% 58.61/8.00  
% 58.61/8.00  cnf(c_1296,plain,
% 58.61/8.00      ( v9_lattices(sK9) ),
% 58.61/8.00      inference(global_propositional_subsumption,
% 58.61/8.00                [status(thm)],
% 58.61/8.00                [c_1294,c_53,c_52,c_50,c_192]) ).
% 58.61/8.00  
% 58.61/8.00  cnf(c_1501,plain,
% 58.61/8.00      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 58.61/8.00      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 58.61/8.00      | ~ l3_lattices(X1)
% 58.61/8.00      | v2_struct_0(X1)
% 58.61/8.00      | k2_lattices(X1,X2,k1_lattices(X1,X2,X0)) = X2
% 58.61/8.00      | sK9 != X1 ),
% 58.61/8.00      inference(resolution_lifted,[status(thm)],[c_34,c_1296]) ).
% 58.61/8.00  
% 58.61/8.00  cnf(c_1502,plain,
% 58.61/8.00      ( ~ m1_subset_1(X0,u1_struct_0(sK9))
% 58.61/8.00      | ~ m1_subset_1(X1,u1_struct_0(sK9))
% 58.61/8.00      | ~ l3_lattices(sK9)
% 58.61/8.00      | v2_struct_0(sK9)
% 58.61/8.00      | k2_lattices(sK9,X1,k1_lattices(sK9,X1,X0)) = X1 ),
% 58.61/8.00      inference(unflattening,[status(thm)],[c_1501]) ).
% 58.61/8.00  
% 58.61/8.00  cnf(c_1886,plain,
% 58.61/8.00      ( ~ m1_subset_1(X0,u1_struct_0(sK9))
% 58.61/8.00      | ~ m1_subset_1(X1,u1_struct_0(sK9))
% 58.61/8.00      | k2_lattices(sK9,X1,k1_lattices(sK9,X1,X0)) = X1 ),
% 58.61/8.00      inference(global_propositional_subsumption,
% 58.61/8.00                [status(thm)],
% 58.61/8.00                [c_1882,c_53,c_50,c_1502]) ).
% 58.61/8.00  
% 58.61/8.00  cnf(c_2551,plain,
% 58.61/8.00      ( k2_lattices(sK9,X0,k1_lattices(sK9,X0,X1)) = X0
% 58.61/8.00      | m1_subset_1(X1,u1_struct_0(sK9)) != iProver_top
% 58.61/8.01      | m1_subset_1(X0,u1_struct_0(sK9)) != iProver_top ),
% 58.61/8.01      inference(predicate_to_equality,[status(thm)],[c_1886]) ).
% 58.61/8.01  
% 58.61/8.01  cnf(c_3555,plain,
% 58.61/8.01      ( k2_lattices(sK9,sK10,k1_lattices(sK9,sK10,X0)) = sK10
% 58.61/8.01      | m1_subset_1(X0,u1_struct_0(sK9)) != iProver_top ),
% 58.61/8.01      inference(superposition,[status(thm)],[c_2570,c_2551]) ).
% 58.61/8.01  
% 58.61/8.01  cnf(c_3785,plain,
% 58.61/8.01      ( k2_lattices(sK9,sK10,k1_lattices(sK9,sK10,k7_lattices(sK9,X0))) = sK10
% 58.61/8.01      | m1_subset_1(X0,u1_struct_0(sK9)) != iProver_top ),
% 58.61/8.01      inference(superposition,[status(thm)],[c_2546,c_3555]) ).
% 58.61/8.01  
% 58.61/8.01  cnf(c_5306,plain,
% 58.61/8.01      ( k2_lattices(sK9,sK10,k1_lattices(sK9,sK10,k7_lattices(sK9,sK10))) = sK10 ),
% 58.61/8.01      inference(superposition,[status(thm)],[c_2570,c_3785]) ).
% 58.61/8.01  
% 58.61/8.01  cnf(c_5321,plain,
% 58.61/8.01      ( k2_lattices(sK9,sK10,k3_lattices(sK9,sK10,k7_lattices(sK9,sK10))) = sK10 ),
% 58.61/8.01      inference(demodulation,[status(thm)],[c_5314,c_5306]) ).
% 58.61/8.01  
% 58.61/8.01  cnf(c_5517,plain,
% 58.61/8.01      ( k2_lattices(sK9,sK10,k6_lattices(sK9)) = sK10 ),
% 58.61/8.01      inference(demodulation,[status(thm)],[c_5510,c_5321]) ).
% 58.61/8.01  
% 58.61/8.01  cnf(c_5529,plain,
% 58.61/8.01      ( k2_lattices(sK9,sK10,k7_lattices(sK9,k7_lattices(sK9,X0))) = k4_lattices(sK9,sK10,k7_lattices(sK9,k7_lattices(sK9,X0)))
% 58.61/8.01      | m1_subset_1(X0,u1_struct_0(sK9)) != iProver_top ),
% 58.61/8.01      inference(superposition,[status(thm)],[c_2546,c_4186]) ).
% 58.61/8.01  
% 58.61/8.01  cnf(c_36401,plain,
% 58.61/8.01      ( k2_lattices(sK9,sK10,k7_lattices(sK9,k7_lattices(sK9,sK10))) = k4_lattices(sK9,sK10,k7_lattices(sK9,k7_lattices(sK9,sK10))) ),
% 58.61/8.01      inference(superposition,[status(thm)],[c_2570,c_5529]) ).
% 58.61/8.01  
% 58.61/8.01  cnf(c_3817,plain,
% 58.61/8.01      ( k3_lattices(sK9,X0,k7_lattices(sK9,X1)) = k3_lattices(sK9,k7_lattices(sK9,X1),X0)
% 58.61/8.01      | m1_subset_1(X1,u1_struct_0(sK9)) != iProver_top
% 58.61/8.01      | m1_subset_1(X0,u1_struct_0(sK9)) != iProver_top ),
% 58.61/8.01      inference(superposition,[status(thm)],[c_2546,c_2553]) ).
% 58.61/8.01  
% 58.61/8.01  cnf(c_18574,plain,
% 58.61/8.01      ( k3_lattices(sK9,k7_lattices(sK9,X0),k7_lattices(sK9,X1)) = k3_lattices(sK9,k7_lattices(sK9,X1),k7_lattices(sK9,X0))
% 58.61/8.01      | m1_subset_1(X1,u1_struct_0(sK9)) != iProver_top
% 58.61/8.01      | m1_subset_1(X0,u1_struct_0(sK9)) != iProver_top ),
% 58.61/8.01      inference(superposition,[status(thm)],[c_2546,c_3817]) ).
% 58.61/8.01  
% 58.61/8.01  cnf(c_66656,plain,
% 58.61/8.01      ( k3_lattices(sK9,k7_lattices(sK9,X0),k7_lattices(sK9,sK10)) = k3_lattices(sK9,k7_lattices(sK9,sK10),k7_lattices(sK9,X0))
% 58.61/8.01      | m1_subset_1(X0,u1_struct_0(sK9)) != iProver_top ),
% 58.61/8.01      inference(superposition,[status(thm)],[c_2570,c_18574]) ).
% 58.61/8.01  
% 58.61/8.01  cnf(c_66692,plain,
% 58.61/8.01      ( k3_lattices(sK9,k7_lattices(sK9,k7_lattices(sK9,X0)),k7_lattices(sK9,sK10)) = k3_lattices(sK9,k7_lattices(sK9,sK10),k7_lattices(sK9,k7_lattices(sK9,X0)))
% 58.61/8.01      | m1_subset_1(X0,u1_struct_0(sK9)) != iProver_top ),
% 58.61/8.01      inference(superposition,[status(thm)],[c_2546,c_66656]) ).
% 58.61/8.01  
% 58.61/8.01  cnf(c_66705,plain,
% 58.61/8.01      ( k3_lattices(sK9,k7_lattices(sK9,sK10),k7_lattices(sK9,k7_lattices(sK9,sK10))) = k3_lattices(sK9,k7_lattices(sK9,k7_lattices(sK9,sK10)),k7_lattices(sK9,sK10)) ),
% 58.61/8.01      inference(superposition,[status(thm)],[c_2570,c_66692]) ).
% 58.61/8.01  
% 58.61/8.01  cnf(c_3261,plain,
% 58.61/8.01      ( k3_lattices(sK9,k7_lattices(sK9,k7_lattices(sK9,X0)),k7_lattices(sK9,X0)) = k6_lattices(sK9)
% 58.61/8.01      | m1_subset_1(X0,u1_struct_0(sK9)) != iProver_top ),
% 58.61/8.01      inference(superposition,[status(thm)],[c_2546,c_2569]) ).
% 58.61/8.01  
% 58.61/8.01  cnf(c_15776,plain,
% 58.61/8.01      ( k3_lattices(sK9,k7_lattices(sK9,k7_lattices(sK9,sK10)),k7_lattices(sK9,sK10)) = k6_lattices(sK9) ),
% 58.61/8.01      inference(superposition,[status(thm)],[c_2570,c_3261]) ).
% 58.61/8.01  
% 58.61/8.01  cnf(c_66713,plain,
% 58.61/8.01      ( k3_lattices(sK9,k7_lattices(sK9,sK10),k7_lattices(sK9,k7_lattices(sK9,sK10))) = k6_lattices(sK9) ),
% 58.61/8.01      inference(light_normalisation,[status(thm)],[c_66705,c_15776]) ).
% 58.61/8.01  
% 58.61/8.01  cnf(c_3794,plain,
% 58.61/8.01      ( k1_lattices(sK9,k7_lattices(sK9,X0),X1) = k3_lattices(sK9,k7_lattices(sK9,X0),X1)
% 58.61/8.01      | m1_subset_1(X0,u1_struct_0(sK9)) != iProver_top
% 58.61/8.01      | m1_subset_1(X1,u1_struct_0(sK9)) != iProver_top ),
% 58.61/8.01      inference(superposition,[status(thm)],[c_2546,c_2552]) ).
% 58.61/8.01  
% 58.61/8.01  cnf(c_18136,plain,
% 58.61/8.01      ( k1_lattices(sK9,k7_lattices(sK9,sK10),X0) = k3_lattices(sK9,k7_lattices(sK9,sK10),X0)
% 58.61/8.01      | m1_subset_1(X0,u1_struct_0(sK9)) != iProver_top ),
% 58.61/8.01      inference(superposition,[status(thm)],[c_2570,c_3794]) ).
% 58.61/8.01  
% 58.61/8.01  cnf(c_18195,plain,
% 58.61/8.01      ( k1_lattices(sK9,k7_lattices(sK9,sK10),k7_lattices(sK9,X0)) = k3_lattices(sK9,k7_lattices(sK9,sK10),k7_lattices(sK9,X0))
% 58.61/8.01      | m1_subset_1(X0,u1_struct_0(sK9)) != iProver_top ),
% 58.61/8.01      inference(superposition,[status(thm)],[c_2546,c_18136]) ).
% 58.61/8.01  
% 58.61/8.01  cnf(c_18987,plain,
% 58.61/8.01      ( k1_lattices(sK9,k7_lattices(sK9,sK10),k7_lattices(sK9,k7_lattices(sK9,X0))) = k3_lattices(sK9,k7_lattices(sK9,sK10),k7_lattices(sK9,k7_lattices(sK9,X0)))
% 58.61/8.01      | m1_subset_1(X0,u1_struct_0(sK9)) != iProver_top ),
% 58.61/8.01      inference(superposition,[status(thm)],[c_2546,c_18195]) ).
% 58.61/8.01  
% 58.61/8.01  cnf(c_50973,plain,
% 58.61/8.01      ( k1_lattices(sK9,k7_lattices(sK9,sK10),k7_lattices(sK9,k7_lattices(sK9,sK10))) = k3_lattices(sK9,k7_lattices(sK9,sK10),k7_lattices(sK9,k7_lattices(sK9,sK10))) ),
% 58.61/8.01      inference(superposition,[status(thm)],[c_2570,c_18987]) ).
% 58.61/8.01  
% 58.61/8.01  cnf(c_66768,plain,
% 58.61/8.01      ( k1_lattices(sK9,k7_lattices(sK9,sK10),k7_lattices(sK9,k7_lattices(sK9,sK10))) = k6_lattices(sK9) ),
% 58.61/8.01      inference(demodulation,[status(thm)],[c_66713,c_50973]) ).
% 58.61/8.01  
% 58.61/8.01  cnf(c_35,plain,
% 58.61/8.01      ( m1_subset_1(k5_lattices(X0),u1_struct_0(X0))
% 58.61/8.01      | ~ l1_lattices(X0)
% 58.61/8.01      | v2_struct_0(X0) ),
% 58.61/8.01      inference(cnf_transformation,[],[f137]) ).
% 58.61/8.01  
% 58.61/8.01  cnf(c_998,plain,
% 58.61/8.01      ( m1_subset_1(k5_lattices(X0),u1_struct_0(X0))
% 58.61/8.01      | ~ l3_lattices(X0)
% 58.61/8.01      | v2_struct_0(X0) ),
% 58.61/8.01      inference(resolution,[status(thm)],[c_39,c_35]) ).
% 58.61/8.01  
% 58.61/8.01  cnf(c_1821,plain,
% 58.61/8.01      ( m1_subset_1(k5_lattices(X0),u1_struct_0(X0))
% 58.61/8.01      | ~ l3_lattices(X0)
% 58.61/8.01      | sK9 != X0 ),
% 58.61/8.01      inference(resolution_lifted,[status(thm)],[c_998,c_53]) ).
% 58.61/8.01  
% 58.61/8.01  cnf(c_1822,plain,
% 58.61/8.01      ( m1_subset_1(k5_lattices(sK9),u1_struct_0(sK9))
% 58.61/8.01      | ~ l3_lattices(sK9) ),
% 58.61/8.01      inference(unflattening,[status(thm)],[c_1821]) ).
% 58.61/8.01  
% 58.61/8.01  cnf(c_84,plain,
% 58.61/8.01      ( l1_lattices(sK9) | ~ l3_lattices(sK9) ),
% 58.61/8.01      inference(instantiation,[status(thm)],[c_39]) ).
% 58.61/8.01  
% 58.61/8.01  cnf(c_96,plain,
% 58.61/8.01      ( m1_subset_1(k5_lattices(sK9),u1_struct_0(sK9))
% 58.61/8.01      | ~ l1_lattices(sK9)
% 58.61/8.01      | v2_struct_0(sK9) ),
% 58.61/8.01      inference(instantiation,[status(thm)],[c_35]) ).
% 58.61/8.01  
% 58.61/8.01  cnf(c_1824,plain,
% 58.61/8.01      ( m1_subset_1(k5_lattices(sK9),u1_struct_0(sK9)) ),
% 58.61/8.01      inference(global_propositional_subsumption,
% 58.61/8.01                [status(thm)],
% 58.61/8.01                [c_1822,c_53,c_50,c_84,c_96]) ).
% 58.61/8.01  
% 58.61/8.01  cnf(c_2548,plain,
% 58.61/8.01      ( m1_subset_1(k5_lattices(sK9),u1_struct_0(sK9)) = iProver_top ),
% 58.61/8.01      inference(predicate_to_equality,[status(thm)],[c_1824]) ).
% 58.61/8.01  
% 58.61/8.01  cnf(c_3243,plain,
% 58.61/8.01      ( k1_lattices(sK9,k2_lattices(sK9,sK10,k5_lattices(sK9)),k2_lattices(sK9,sK10,X0)) = k2_lattices(sK9,sK10,k1_lattices(sK9,k5_lattices(sK9),X0))
% 58.61/8.01      | m1_subset_1(X0,u1_struct_0(sK9)) != iProver_top ),
% 58.61/8.01      inference(superposition,[status(thm)],[c_2548,c_3214]) ).
% 58.61/8.01  
% 58.61/8.01  cnf(c_4211,plain,
% 58.61/8.01      ( k4_lattices(sK9,sK10,k5_lattices(sK9)) = k4_lattices(sK9,k5_lattices(sK9),sK10) ),
% 58.61/8.01      inference(superposition,[status(thm)],[c_2548,c_4192]) ).
% 58.61/8.01  
% 58.61/8.01  cnf(c_44,plain,
% 58.61/8.01      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 58.61/8.01      | ~ v13_lattices(X1)
% 58.61/8.01      | ~ l3_lattices(X1)
% 58.61/8.01      | v2_struct_0(X1)
% 58.61/8.01      | ~ v10_lattices(X1)
% 58.61/8.01      | k4_lattices(X1,k5_lattices(X1),X0) = k5_lattices(X1) ),
% 58.61/8.01      inference(cnf_transformation,[],[f146]) ).
% 58.61/8.01  
% 58.61/8.01  cnf(c_9,plain,
% 58.61/8.01      ( ~ v17_lattices(X0)
% 58.61/8.01      | v15_lattices(X0)
% 58.61/8.01      | ~ l3_lattices(X0)
% 58.61/8.01      | v2_struct_0(X0) ),
% 58.61/8.01      inference(cnf_transformation,[],[f113]) ).
% 58.61/8.01  
% 58.61/8.01  cnf(c_7,plain,
% 58.61/8.01      ( v13_lattices(X0)
% 58.61/8.01      | ~ v15_lattices(X0)
% 58.61/8.01      | ~ l3_lattices(X0)
% 58.61/8.01      | v2_struct_0(X0) ),
% 58.61/8.01      inference(cnf_transformation,[],[f109]) ).
% 58.61/8.01  
% 58.61/8.01  cnf(c_560,plain,
% 58.61/8.01      ( ~ v17_lattices(X0)
% 58.61/8.01      | v13_lattices(X0)
% 58.61/8.01      | ~ l3_lattices(X0)
% 58.61/8.01      | v2_struct_0(X0) ),
% 58.61/8.01      inference(resolution,[status(thm)],[c_9,c_7]) ).
% 58.61/8.01  
% 58.61/8.01  cnf(c_687,plain,
% 58.61/8.01      ( v13_lattices(X0)
% 58.61/8.01      | ~ l3_lattices(X0)
% 58.61/8.01      | v2_struct_0(X0)
% 58.61/8.01      | sK9 != X0 ),
% 58.61/8.01      inference(resolution_lifted,[status(thm)],[c_560,c_51]) ).
% 58.61/8.01  
% 58.61/8.01  cnf(c_688,plain,
% 58.61/8.01      ( v13_lattices(sK9) | ~ l3_lattices(sK9) | v2_struct_0(sK9) ),
% 58.61/8.01      inference(unflattening,[status(thm)],[c_687]) ).
% 58.61/8.01  
% 58.61/8.01  cnf(c_172,plain,
% 58.61/8.01      ( ~ v17_lattices(sK9)
% 58.61/8.01      | v15_lattices(sK9)
% 58.61/8.01      | ~ l3_lattices(sK9)
% 58.61/8.01      | v2_struct_0(sK9) ),
% 58.61/8.01      inference(instantiation,[status(thm)],[c_9]) ).
% 58.61/8.01  
% 58.61/8.01  cnf(c_176,plain,
% 58.61/8.01      ( v13_lattices(sK9)
% 58.61/8.01      | ~ v15_lattices(sK9)
% 58.61/8.01      | ~ l3_lattices(sK9)
% 58.61/8.01      | v2_struct_0(sK9) ),
% 58.61/8.01      inference(instantiation,[status(thm)],[c_7]) ).
% 58.61/8.01  
% 58.61/8.01  cnf(c_690,plain,
% 58.61/8.01      ( v13_lattices(sK9) ),
% 58.61/8.01      inference(global_propositional_subsumption,
% 58.61/8.01                [status(thm)],
% 58.61/8.01                [c_688,c_53,c_51,c_50,c_172,c_176]) ).
% 58.61/8.01  
% 58.61/8.01  cnf(c_1225,plain,
% 58.61/8.01      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 58.61/8.01      | ~ l3_lattices(X1)
% 58.61/8.01      | v2_struct_0(X1)
% 58.61/8.01      | ~ v10_lattices(X1)
% 58.61/8.01      | k4_lattices(X1,k5_lattices(X1),X0) = k5_lattices(X1)
% 58.61/8.01      | sK9 != X1 ),
% 58.61/8.01      inference(resolution_lifted,[status(thm)],[c_44,c_690]) ).
% 58.61/8.01  
% 58.61/8.01  cnf(c_1226,plain,
% 58.61/8.01      ( ~ m1_subset_1(X0,u1_struct_0(sK9))
% 58.61/8.01      | ~ l3_lattices(sK9)
% 58.61/8.01      | v2_struct_0(sK9)
% 58.61/8.01      | ~ v10_lattices(sK9)
% 58.61/8.01      | k4_lattices(sK9,k5_lattices(sK9),X0) = k5_lattices(sK9) ),
% 58.61/8.01      inference(unflattening,[status(thm)],[c_1225]) ).
% 58.61/8.01  
% 58.61/8.01  cnf(c_1230,plain,
% 58.61/8.01      ( ~ m1_subset_1(X0,u1_struct_0(sK9))
% 58.61/8.01      | k4_lattices(sK9,k5_lattices(sK9),X0) = k5_lattices(sK9) ),
% 58.61/8.01      inference(global_propositional_subsumption,
% 58.61/8.01                [status(thm)],
% 58.61/8.01                [c_1226,c_53,c_52,c_50]) ).
% 58.61/8.01  
% 58.61/8.01  cnf(c_2558,plain,
% 58.61/8.01      ( k4_lattices(sK9,k5_lattices(sK9),X0) = k5_lattices(sK9)
% 58.61/8.01      | m1_subset_1(X0,u1_struct_0(sK9)) != iProver_top ),
% 58.61/8.01      inference(predicate_to_equality,[status(thm)],[c_1230]) ).
% 58.61/8.01  
% 58.61/8.01  cnf(c_5258,plain,
% 58.61/8.01      ( k4_lattices(sK9,k5_lattices(sK9),sK10) = k5_lattices(sK9) ),
% 58.61/8.01      inference(superposition,[status(thm)],[c_2570,c_2558]) ).
% 58.61/8.01  
% 58.61/8.01  cnf(c_5282,plain,
% 58.61/8.01      ( k4_lattices(sK9,sK10,k5_lattices(sK9)) = k5_lattices(sK9) ),
% 58.61/8.01      inference(light_normalisation,[status(thm)],[c_4211,c_5258]) ).
% 58.61/8.01  
% 58.61/8.01  cnf(c_4185,plain,
% 58.61/8.01      ( k2_lattices(sK9,sK10,k5_lattices(sK9)) = k4_lattices(sK9,sK10,k5_lattices(sK9)) ),
% 58.61/8.01      inference(superposition,[status(thm)],[c_2548,c_4038]) ).
% 58.61/8.01  
% 58.61/8.01  cnf(c_5283,plain,
% 58.61/8.01      ( k2_lattices(sK9,sK10,k5_lattices(sK9)) = k5_lattices(sK9) ),
% 58.61/8.01      inference(demodulation,[status(thm)],[c_5282,c_4185]) ).
% 58.61/8.01  
% 58.61/8.01  cnf(c_13256,plain,
% 58.61/8.01      ( k1_lattices(sK9,k5_lattices(sK9),k2_lattices(sK9,sK10,X0)) = k2_lattices(sK9,sK10,k1_lattices(sK9,k5_lattices(sK9),X0))
% 58.61/8.01      | m1_subset_1(X0,u1_struct_0(sK9)) != iProver_top ),
% 58.61/8.01      inference(light_normalisation,[status(thm)],[c_3243,c_5283]) ).
% 58.61/8.01  
% 58.61/8.01  cnf(c_13265,plain,
% 58.61/8.01      ( k1_lattices(sK9,k5_lattices(sK9),k2_lattices(sK9,sK10,k7_lattices(sK9,X0))) = k2_lattices(sK9,sK10,k1_lattices(sK9,k5_lattices(sK9),k7_lattices(sK9,X0)))
% 58.61/8.01      | m1_subset_1(X0,u1_struct_0(sK9)) != iProver_top ),
% 58.61/8.01      inference(superposition,[status(thm)],[c_2546,c_13256]) ).
% 58.61/8.01  
% 58.61/8.01  cnf(c_50708,plain,
% 58.61/8.01      ( k1_lattices(sK9,k5_lattices(sK9),k2_lattices(sK9,sK10,k7_lattices(sK9,k7_lattices(sK9,X0)))) = k2_lattices(sK9,sK10,k1_lattices(sK9,k5_lattices(sK9),k7_lattices(sK9,k7_lattices(sK9,X0))))
% 58.61/8.01      | m1_subset_1(X0,u1_struct_0(sK9)) != iProver_top ),
% 58.61/8.01      inference(superposition,[status(thm)],[c_2546,c_13265]) ).
% 58.61/8.01  
% 58.61/8.01  cnf(c_67436,plain,
% 58.61/8.01      ( k1_lattices(sK9,k5_lattices(sK9),k2_lattices(sK9,sK10,k7_lattices(sK9,k7_lattices(sK9,sK10)))) = k2_lattices(sK9,sK10,k1_lattices(sK9,k5_lattices(sK9),k7_lattices(sK9,k7_lattices(sK9,sK10)))) ),
% 58.61/8.01      inference(superposition,[status(thm)],[c_2570,c_50708]) ).
% 58.61/8.01  
% 58.61/8.01  cnf(c_3793,plain,
% 58.61/8.01      ( k1_lattices(sK9,k5_lattices(sK9),X0) = k3_lattices(sK9,k5_lattices(sK9),X0)
% 58.61/8.01      | m1_subset_1(X0,u1_struct_0(sK9)) != iProver_top ),
% 58.61/8.01      inference(superposition,[status(thm)],[c_2548,c_2552]) ).
% 58.61/8.01  
% 58.61/8.01  cnf(c_8049,plain,
% 58.61/8.01      ( k1_lattices(sK9,k5_lattices(sK9),k7_lattices(sK9,X0)) = k3_lattices(sK9,k5_lattices(sK9),k7_lattices(sK9,X0))
% 58.61/8.01      | m1_subset_1(X0,u1_struct_0(sK9)) != iProver_top ),
% 58.61/8.01      inference(superposition,[status(thm)],[c_2546,c_3793]) ).
% 58.61/8.01  
% 58.61/8.01  cnf(c_20330,plain,
% 58.61/8.01      ( k1_lattices(sK9,k5_lattices(sK9),k7_lattices(sK9,k7_lattices(sK9,X0))) = k3_lattices(sK9,k5_lattices(sK9),k7_lattices(sK9,k7_lattices(sK9,X0)))
% 58.61/8.01      | m1_subset_1(X0,u1_struct_0(sK9)) != iProver_top ),
% 58.61/8.01      inference(superposition,[status(thm)],[c_2546,c_8049]) ).
% 58.61/8.01  
% 58.61/8.01  cnf(c_48869,plain,
% 58.61/8.01      ( k1_lattices(sK9,k5_lattices(sK9),k7_lattices(sK9,k7_lattices(sK9,sK10))) = k3_lattices(sK9,k5_lattices(sK9),k7_lattices(sK9,k7_lattices(sK9,sK10))) ),
% 58.61/8.01      inference(superposition,[status(thm)],[c_2570,c_20330]) ).
% 58.61/8.01  
% 58.61/8.01  cnf(c_43,plain,
% 58.61/8.01      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 58.61/8.01      | ~ v13_lattices(X1)
% 58.61/8.01      | ~ l3_lattices(X1)
% 58.61/8.01      | v2_struct_0(X1)
% 58.61/8.01      | ~ v10_lattices(X1)
% 58.61/8.01      | k3_lattices(X1,k5_lattices(X1),X0) = X0 ),
% 58.61/8.01      inference(cnf_transformation,[],[f145]) ).
% 58.61/8.01  
% 58.61/8.01  cnf(c_1243,plain,
% 58.61/8.01      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 58.61/8.01      | ~ l3_lattices(X1)
% 58.61/8.01      | v2_struct_0(X1)
% 58.61/8.01      | ~ v10_lattices(X1)
% 58.61/8.01      | k3_lattices(X1,k5_lattices(X1),X0) = X0
% 58.61/8.01      | sK9 != X1 ),
% 58.61/8.01      inference(resolution_lifted,[status(thm)],[c_43,c_690]) ).
% 58.61/8.01  
% 58.61/8.01  cnf(c_1244,plain,
% 58.61/8.01      ( ~ m1_subset_1(X0,u1_struct_0(sK9))
% 58.61/8.01      | ~ l3_lattices(sK9)
% 58.61/8.01      | v2_struct_0(sK9)
% 58.61/8.01      | ~ v10_lattices(sK9)
% 58.61/8.01      | k3_lattices(sK9,k5_lattices(sK9),X0) = X0 ),
% 58.61/8.01      inference(unflattening,[status(thm)],[c_1243]) ).
% 58.61/8.01  
% 58.61/8.01  cnf(c_1248,plain,
% 58.61/8.01      ( ~ m1_subset_1(X0,u1_struct_0(sK9))
% 58.61/8.01      | k3_lattices(sK9,k5_lattices(sK9),X0) = X0 ),
% 58.61/8.01      inference(global_propositional_subsumption,
% 58.61/8.01                [status(thm)],
% 58.61/8.01                [c_1244,c_53,c_52,c_50]) ).
% 58.61/8.01  
% 58.61/8.01  cnf(c_2557,plain,
% 58.61/8.01      ( k3_lattices(sK9,k5_lattices(sK9),X0) = X0
% 58.61/8.01      | m1_subset_1(X0,u1_struct_0(sK9)) != iProver_top ),
% 58.61/8.01      inference(predicate_to_equality,[status(thm)],[c_1248]) ).
% 58.61/8.01  
% 58.61/8.01  cnf(c_4562,plain,
% 58.61/8.01      ( k3_lattices(sK9,k5_lattices(sK9),k7_lattices(sK9,X0)) = k7_lattices(sK9,X0)
% 58.61/8.01      | m1_subset_1(X0,u1_struct_0(sK9)) != iProver_top ),
% 58.61/8.01      inference(superposition,[status(thm)],[c_2546,c_2557]) ).
% 58.61/8.01  
% 58.61/8.01  cnf(c_9685,plain,
% 58.61/8.01      ( k3_lattices(sK9,k5_lattices(sK9),k7_lattices(sK9,k7_lattices(sK9,X0))) = k7_lattices(sK9,k7_lattices(sK9,X0))
% 58.61/8.01      | m1_subset_1(X0,u1_struct_0(sK9)) != iProver_top ),
% 58.61/8.01      inference(superposition,[status(thm)],[c_2546,c_4562]) ).
% 58.61/8.01  
% 58.61/8.01  cnf(c_25069,plain,
% 58.61/8.01      ( k3_lattices(sK9,k5_lattices(sK9),k7_lattices(sK9,k7_lattices(sK9,sK10))) = k7_lattices(sK9,k7_lattices(sK9,sK10)) ),
% 58.61/8.01      inference(superposition,[status(thm)],[c_2570,c_9685]) ).
% 58.61/8.01  
% 58.61/8.01  cnf(c_48877,plain,
% 58.61/8.01      ( k1_lattices(sK9,k5_lattices(sK9),k7_lattices(sK9,k7_lattices(sK9,sK10))) = k7_lattices(sK9,k7_lattices(sK9,sK10)) ),
% 58.61/8.01      inference(light_normalisation,[status(thm)],[c_48869,c_25069]) ).
% 58.61/8.01  
% 58.61/8.01  cnf(c_67445,plain,
% 58.61/8.01      ( k1_lattices(sK9,k5_lattices(sK9),k4_lattices(sK9,sK10,k7_lattices(sK9,k7_lattices(sK9,sK10)))) = k4_lattices(sK9,sK10,k7_lattices(sK9,k7_lattices(sK9,sK10))) ),
% 58.61/8.01      inference(light_normalisation,
% 58.61/8.01                [status(thm)],
% 58.61/8.01                [c_67436,c_36401,c_48877]) ).
% 58.61/8.01  
% 58.61/8.01  cnf(c_70485,plain,
% 58.61/8.01      ( k4_lattices(sK9,sK10,k7_lattices(sK9,k7_lattices(sK9,sK10))) = sK10 ),
% 58.61/8.01      inference(light_normalisation,
% 58.61/8.01                [status(thm)],
% 58.61/8.01                [c_70476,c_5517,c_36401,c_66768,c_67445]) ).
% 58.61/8.01  
% 58.61/8.01  cnf(c_4041,plain,
% 58.61/8.01      ( k2_lattices(sK9,k7_lattices(sK9,X0),X1) = k4_lattices(sK9,k7_lattices(sK9,X0),X1)
% 58.61/8.01      | m1_subset_1(X0,u1_struct_0(sK9)) != iProver_top
% 58.61/8.01      | m1_subset_1(X1,u1_struct_0(sK9)) != iProver_top ),
% 58.61/8.01      inference(superposition,[status(thm)],[c_2546,c_2555]) ).
% 58.61/8.01  
% 58.61/8.01  cnf(c_24533,plain,
% 58.61/8.01      ( k2_lattices(sK9,k7_lattices(sK9,k7_lattices(sK9,X0)),X1) = k4_lattices(sK9,k7_lattices(sK9,k7_lattices(sK9,X0)),X1)
% 58.61/8.01      | m1_subset_1(X0,u1_struct_0(sK9)) != iProver_top
% 58.61/8.01      | m1_subset_1(X1,u1_struct_0(sK9)) != iProver_top ),
% 58.61/8.01      inference(superposition,[status(thm)],[c_2546,c_4041]) ).
% 58.61/8.01  
% 58.61/8.01  cnf(c_66836,plain,
% 58.61/8.01      ( k2_lattices(sK9,k7_lattices(sK9,k7_lattices(sK9,sK10)),X0) = k4_lattices(sK9,k7_lattices(sK9,k7_lattices(sK9,sK10)),X0)
% 58.61/8.01      | m1_subset_1(X0,u1_struct_0(sK9)) != iProver_top ),
% 58.61/8.01      inference(superposition,[status(thm)],[c_2570,c_24533]) ).
% 58.61/8.01  
% 58.61/8.01  cnf(c_66876,plain,
% 58.61/8.01      ( k2_lattices(sK9,k7_lattices(sK9,k7_lattices(sK9,sK10)),sK10) = k4_lattices(sK9,k7_lattices(sK9,k7_lattices(sK9,sK10)),sK10) ),
% 58.61/8.01      inference(superposition,[status(thm)],[c_2570,c_66836]) ).
% 58.61/8.01  
% 58.61/8.01  cnf(c_5557,plain,
% 58.61/8.01      ( k4_lattices(sK9,k7_lattices(sK9,k7_lattices(sK9,X0)),sK10) = k4_lattices(sK9,sK10,k7_lattices(sK9,k7_lattices(sK9,X0)))
% 58.61/8.01      | m1_subset_1(X0,u1_struct_0(sK9)) != iProver_top ),
% 58.61/8.01      inference(superposition,[status(thm)],[c_2546,c_4212]) ).
% 58.61/8.01  
% 58.61/8.01  cnf(c_36910,plain,
% 58.61/8.01      ( k4_lattices(sK9,sK10,k7_lattices(sK9,k7_lattices(sK9,sK10))) = k4_lattices(sK9,k7_lattices(sK9,k7_lattices(sK9,sK10)),sK10) ),
% 58.61/8.01      inference(superposition,[status(thm)],[c_2570,c_5557]) ).
% 58.61/8.01  
% 58.61/8.01  cnf(c_66884,plain,
% 58.61/8.01      ( k2_lattices(sK9,k7_lattices(sK9,k7_lattices(sK9,sK10)),sK10) = k4_lattices(sK9,sK10,k7_lattices(sK9,k7_lattices(sK9,sK10))) ),
% 58.61/8.01      inference(light_normalisation,[status(thm)],[c_66876,c_36910]) ).
% 58.61/8.01  
% 58.61/8.01  cnf(c_70497,plain,
% 58.61/8.01      ( k2_lattices(sK9,k7_lattices(sK9,k7_lattices(sK9,sK10)),sK10) = sK10 ),
% 58.61/8.01      inference(demodulation,[status(thm)],[c_70485,c_66884]) ).
% 58.61/8.01  
% 58.61/8.01  cnf(c_193838,plain,
% 58.61/8.01      ( k1_lattices(sK9,sK10,k2_lattices(sK9,k7_lattices(sK9,k7_lattices(sK9,sK10)),X0)) = k2_lattices(sK9,k7_lattices(sK9,k7_lattices(sK9,sK10)),k1_lattices(sK9,sK10,X0))
% 58.61/8.01      | m1_subset_1(X0,u1_struct_0(sK9)) != iProver_top ),
% 58.61/8.01      inference(light_normalisation,[status(thm)],[c_193830,c_70497]) ).
% 58.61/8.01  
% 58.61/8.01  cnf(c_193901,plain,
% 58.61/8.01      ( k1_lattices(sK9,sK10,k2_lattices(sK9,k7_lattices(sK9,k7_lattices(sK9,sK10)),k7_lattices(sK9,X0))) = k2_lattices(sK9,k7_lattices(sK9,k7_lattices(sK9,sK10)),k1_lattices(sK9,sK10,k7_lattices(sK9,X0)))
% 58.61/8.01      | m1_subset_1(X0,u1_struct_0(sK9)) != iProver_top ),
% 58.61/8.01      inference(superposition,[status(thm)],[c_2546,c_193838]) ).
% 58.61/8.01  
% 58.61/8.01  cnf(c_193963,plain,
% 58.61/8.01      ( k1_lattices(sK9,sK10,k2_lattices(sK9,k7_lattices(sK9,k7_lattices(sK9,sK10)),k7_lattices(sK9,sK10))) = k2_lattices(sK9,k7_lattices(sK9,k7_lattices(sK9,sK10)),k1_lattices(sK9,sK10,k7_lattices(sK9,sK10))) ),
% 58.61/8.01      inference(superposition,[status(thm)],[c_2570,c_193901]) ).
% 58.61/8.01  
% 58.61/8.01  cnf(c_3929,plain,
% 58.61/8.01      ( k3_lattices(sK9,sK10,k5_lattices(sK9)) = k3_lattices(sK9,k5_lattices(sK9),sK10) ),
% 58.61/8.01      inference(superposition,[status(thm)],[c_2548,c_3814]) ).
% 58.61/8.01  
% 58.61/8.01  cnf(c_4559,plain,
% 58.61/8.01      ( k3_lattices(sK9,k5_lattices(sK9),sK10) = sK10 ),
% 58.61/8.01      inference(superposition,[status(thm)],[c_2570,c_2557]) ).
% 58.61/8.01  
% 58.61/8.01  cnf(c_5274,plain,
% 58.61/8.01      ( k3_lattices(sK9,sK10,k5_lattices(sK9)) = sK10 ),
% 58.61/8.01      inference(light_normalisation,[status(thm)],[c_3929,c_4559]) ).
% 58.61/8.01  
% 58.61/8.01  cnf(c_3833,plain,
% 58.61/8.01      ( k1_lattices(sK9,sK10,k5_lattices(sK9)) = k3_lattices(sK9,sK10,k5_lattices(sK9)) ),
% 58.61/8.01      inference(superposition,[status(thm)],[c_2548,c_3791]) ).
% 58.61/8.01  
% 58.61/8.01  cnf(c_5275,plain,
% 58.61/8.01      ( k1_lattices(sK9,sK10,k5_lattices(sK9)) = sK10 ),
% 58.61/8.01      inference(demodulation,[status(thm)],[c_5274,c_3833]) ).
% 58.61/8.01  
% 58.61/8.01  cnf(c_5518,plain,
% 58.61/8.01      ( k1_lattices(sK9,sK10,k7_lattices(sK9,sK10)) = k6_lattices(sK9) ),
% 58.61/8.01      inference(demodulation,[status(thm)],[c_5510,c_5314]) ).
% 58.61/8.01  
% 58.61/8.01  cnf(c_66881,plain,
% 58.61/8.01      ( k2_lattices(sK9,k7_lattices(sK9,k7_lattices(sK9,sK10)),k7_lattices(sK9,X0)) = k4_lattices(sK9,k7_lattices(sK9,k7_lattices(sK9,sK10)),k7_lattices(sK9,X0))
% 58.61/8.01      | m1_subset_1(X0,u1_struct_0(sK9)) != iProver_top ),
% 58.61/8.01      inference(superposition,[status(thm)],[c_2546,c_66836]) ).
% 58.61/8.01  
% 58.61/8.01  cnf(c_66940,plain,
% 58.61/8.01      ( k2_lattices(sK9,k7_lattices(sK9,k7_lattices(sK9,sK10)),k7_lattices(sK9,sK10)) = k4_lattices(sK9,k7_lattices(sK9,k7_lattices(sK9,sK10)),k7_lattices(sK9,sK10)) ),
% 58.61/8.01      inference(superposition,[status(thm)],[c_2570,c_66881]) ).
% 58.61/8.01  
% 58.61/8.01  cnf(c_3143,plain,
% 58.61/8.01      ( k4_lattices(sK9,k7_lattices(sK9,k7_lattices(sK9,X0)),k7_lattices(sK9,X0)) = k5_lattices(sK9)
% 58.61/8.01      | m1_subset_1(X0,u1_struct_0(sK9)) != iProver_top ),
% 58.61/8.01      inference(superposition,[status(thm)],[c_2546,c_2568]) ).
% 58.61/8.01  
% 58.61/8.01  cnf(c_6472,plain,
% 58.61/8.01      ( k4_lattices(sK9,k7_lattices(sK9,k7_lattices(sK9,sK10)),k7_lattices(sK9,sK10)) = k5_lattices(sK9) ),
% 58.61/8.01      inference(superposition,[status(thm)],[c_2570,c_3143]) ).
% 58.61/8.01  
% 58.61/8.01  cnf(c_66948,plain,
% 58.61/8.01      ( k2_lattices(sK9,k7_lattices(sK9,k7_lattices(sK9,sK10)),k7_lattices(sK9,sK10)) = k5_lattices(sK9) ),
% 58.61/8.01      inference(light_normalisation,[status(thm)],[c_66940,c_6472]) ).
% 58.61/8.01  
% 58.61/8.01  cnf(c_36,plain,
% 58.61/8.01      ( m1_subset_1(k6_lattices(X0),u1_struct_0(X0))
% 58.61/8.01      | ~ l2_lattices(X0)
% 58.61/8.01      | v2_struct_0(X0) ),
% 58.61/8.01      inference(cnf_transformation,[],[f138]) ).
% 58.61/8.01  
% 58.61/8.01  cnf(c_980,plain,
% 58.61/8.01      ( m1_subset_1(k6_lattices(X0),u1_struct_0(X0))
% 58.61/8.01      | ~ l3_lattices(X0)
% 58.61/8.01      | v2_struct_0(X0) ),
% 58.61/8.01      inference(resolution,[status(thm)],[c_38,c_36]) ).
% 58.61/8.01  
% 58.61/8.01  cnf(c_1832,plain,
% 58.61/8.01      ( m1_subset_1(k6_lattices(X0),u1_struct_0(X0))
% 58.61/8.01      | ~ l3_lattices(X0)
% 58.61/8.01      | sK9 != X0 ),
% 58.61/8.01      inference(resolution_lifted,[status(thm)],[c_980,c_53]) ).
% 58.61/8.01  
% 58.61/8.01  cnf(c_1833,plain,
% 58.61/8.01      ( m1_subset_1(k6_lattices(sK9),u1_struct_0(sK9))
% 58.61/8.01      | ~ l3_lattices(sK9) ),
% 58.61/8.01      inference(unflattening,[status(thm)],[c_1832]) ).
% 58.61/8.01  
% 58.61/8.01  cnf(c_87,plain,
% 58.61/8.01      ( l2_lattices(sK9) | ~ l3_lattices(sK9) ),
% 58.61/8.01      inference(instantiation,[status(thm)],[c_38]) ).
% 58.61/8.01  
% 58.61/8.01  cnf(c_93,plain,
% 58.61/8.01      ( m1_subset_1(k6_lattices(sK9),u1_struct_0(sK9))
% 58.61/8.01      | ~ l2_lattices(sK9)
% 58.61/8.01      | v2_struct_0(sK9) ),
% 58.61/8.01      inference(instantiation,[status(thm)],[c_36]) ).
% 58.61/8.01  
% 58.61/8.01  cnf(c_1835,plain,
% 58.61/8.01      ( m1_subset_1(k6_lattices(sK9),u1_struct_0(sK9)) ),
% 58.61/8.01      inference(global_propositional_subsumption,
% 58.61/8.01                [status(thm)],
% 58.61/8.01                [c_1833,c_53,c_50,c_87,c_93]) ).
% 58.61/8.01  
% 58.61/8.01  cnf(c_2547,plain,
% 58.61/8.01      ( m1_subset_1(k6_lattices(sK9),u1_struct_0(sK9)) = iProver_top ),
% 58.61/8.01      inference(predicate_to_equality,[status(thm)],[c_1835]) ).
% 58.61/8.01  
% 58.61/8.01  cnf(c_3558,plain,
% 58.61/8.01      ( k2_lattices(sK9,k7_lattices(sK9,X0),k1_lattices(sK9,k7_lattices(sK9,X0),X1)) = k7_lattices(sK9,X0)
% 58.61/8.01      | m1_subset_1(X0,u1_struct_0(sK9)) != iProver_top
% 58.61/8.01      | m1_subset_1(X1,u1_struct_0(sK9)) != iProver_top ),
% 58.61/8.01      inference(superposition,[status(thm)],[c_2546,c_2551]) ).
% 58.61/8.01  
% 58.61/8.01  cnf(c_17824,plain,
% 58.61/8.01      ( k2_lattices(sK9,k7_lattices(sK9,k7_lattices(sK9,X0)),k1_lattices(sK9,k7_lattices(sK9,k7_lattices(sK9,X0)),X1)) = k7_lattices(sK9,k7_lattices(sK9,X0))
% 58.61/8.01      | m1_subset_1(X0,u1_struct_0(sK9)) != iProver_top
% 58.61/8.01      | m1_subset_1(X1,u1_struct_0(sK9)) != iProver_top ),
% 58.61/8.01      inference(superposition,[status(thm)],[c_2546,c_3558]) ).
% 58.61/8.01  
% 58.61/8.01  cnf(c_87990,plain,
% 58.61/8.01      ( k2_lattices(sK9,k7_lattices(sK9,k7_lattices(sK9,sK10)),k1_lattices(sK9,k7_lattices(sK9,k7_lattices(sK9,sK10)),X0)) = k7_lattices(sK9,k7_lattices(sK9,sK10))
% 58.61/8.01      | m1_subset_1(X0,u1_struct_0(sK9)) != iProver_top ),
% 58.61/8.01      inference(superposition,[status(thm)],[c_2570,c_17824]) ).
% 58.61/8.01  
% 58.61/8.01  cnf(c_88040,plain,
% 58.61/8.01      ( k2_lattices(sK9,k7_lattices(sK9,k7_lattices(sK9,sK10)),k1_lattices(sK9,k7_lattices(sK9,k7_lattices(sK9,sK10)),k6_lattices(sK9))) = k7_lattices(sK9,k7_lattices(sK9,sK10)) ),
% 58.61/8.01      inference(superposition,[status(thm)],[c_2547,c_87990]) ).
% 58.61/8.01  
% 58.61/8.01  cnf(c_25,plain,
% 58.61/8.01      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 58.61/8.01      | ~ m1_subset_1(k6_lattices(X1),u1_struct_0(X1))
% 58.61/8.01      | ~ l2_lattices(X1)
% 58.61/8.01      | ~ v14_lattices(X1)
% 58.61/8.01      | v2_struct_0(X1)
% 58.61/8.01      | k1_lattices(X1,X0,k6_lattices(X1)) = k6_lattices(X1) ),
% 58.61/8.01      inference(cnf_transformation,[],[f158]) ).
% 58.61/8.01  
% 58.61/8.01  cnf(c_6,plain,
% 58.61/8.01      ( ~ v15_lattices(X0)
% 58.61/8.01      | v14_lattices(X0)
% 58.61/8.01      | ~ l3_lattices(X0)
% 58.61/8.01      | v2_struct_0(X0) ),
% 58.61/8.01      inference(cnf_transformation,[],[f110]) ).
% 58.61/8.01  
% 58.61/8.01  cnf(c_577,plain,
% 58.61/8.01      ( ~ v17_lattices(X0)
% 58.61/8.01      | v14_lattices(X0)
% 58.61/8.01      | ~ l3_lattices(X0)
% 58.61/8.01      | v2_struct_0(X0) ),
% 58.61/8.01      inference(resolution,[status(thm)],[c_9,c_6]) ).
% 58.61/8.01  
% 58.61/8.01  cnf(c_676,plain,
% 58.61/8.01      ( v14_lattices(X0)
% 58.61/8.01      | ~ l3_lattices(X0)
% 58.61/8.01      | v2_struct_0(X0)
% 58.61/8.01      | sK9 != X0 ),
% 58.61/8.01      inference(resolution_lifted,[status(thm)],[c_577,c_51]) ).
% 58.61/8.01  
% 58.61/8.01  cnf(c_677,plain,
% 58.61/8.01      ( v14_lattices(sK9) | ~ l3_lattices(sK9) | v2_struct_0(sK9) ),
% 58.61/8.01      inference(unflattening,[status(thm)],[c_676]) ).
% 58.61/8.01  
% 58.61/8.01  cnf(c_179,plain,
% 58.61/8.01      ( ~ v15_lattices(sK9)
% 58.61/8.01      | v14_lattices(sK9)
% 58.61/8.01      | ~ l3_lattices(sK9)
% 58.61/8.01      | v2_struct_0(sK9) ),
% 58.61/8.01      inference(instantiation,[status(thm)],[c_6]) ).
% 58.61/8.01  
% 58.61/8.01  cnf(c_679,plain,
% 58.61/8.01      ( v14_lattices(sK9) ),
% 58.61/8.01      inference(global_propositional_subsumption,
% 58.61/8.01                [status(thm)],
% 58.61/8.01                [c_677,c_53,c_51,c_50,c_172,c_179]) ).
% 58.61/8.01  
% 58.61/8.01  cnf(c_899,plain,
% 58.61/8.01      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 58.61/8.01      | ~ m1_subset_1(k6_lattices(X1),u1_struct_0(X1))
% 58.61/8.01      | ~ l2_lattices(X1)
% 58.61/8.01      | v2_struct_0(X1)
% 58.61/8.01      | k1_lattices(X1,X0,k6_lattices(X1)) = k6_lattices(X1)
% 58.61/8.01      | sK9 != X1 ),
% 58.61/8.01      inference(resolution_lifted,[status(thm)],[c_25,c_679]) ).
% 58.61/8.01  
% 58.61/8.01  cnf(c_900,plain,
% 58.61/8.01      ( ~ m1_subset_1(X0,u1_struct_0(sK9))
% 58.61/8.01      | ~ m1_subset_1(k6_lattices(sK9),u1_struct_0(sK9))
% 58.61/8.01      | ~ l2_lattices(sK9)
% 58.61/8.01      | v2_struct_0(sK9)
% 58.61/8.01      | k1_lattices(sK9,X0,k6_lattices(sK9)) = k6_lattices(sK9) ),
% 58.61/8.01      inference(unflattening,[status(thm)],[c_899]) ).
% 58.61/8.01  
% 58.61/8.01  cnf(c_904,plain,
% 58.61/8.01      ( ~ m1_subset_1(X0,u1_struct_0(sK9))
% 58.61/8.01      | k1_lattices(sK9,X0,k6_lattices(sK9)) = k6_lattices(sK9) ),
% 58.61/8.01      inference(global_propositional_subsumption,
% 58.61/8.01                [status(thm)],
% 58.61/8.01                [c_900,c_53,c_50,c_87,c_93]) ).
% 58.61/8.01  
% 58.61/8.01  cnf(c_2565,plain,
% 58.61/8.01      ( k1_lattices(sK9,X0,k6_lattices(sK9)) = k6_lattices(sK9)
% 58.61/8.01      | m1_subset_1(X0,u1_struct_0(sK9)) != iProver_top ),
% 58.61/8.01      inference(predicate_to_equality,[status(thm)],[c_904]) ).
% 58.61/8.01  
% 58.61/8.01  cnf(c_5541,plain,
% 58.61/8.01      ( k1_lattices(sK9,k7_lattices(sK9,X0),k6_lattices(sK9)) = k6_lattices(sK9)
% 58.61/8.01      | m1_subset_1(X0,u1_struct_0(sK9)) != iProver_top ),
% 58.61/8.01      inference(superposition,[status(thm)],[c_2546,c_2565]) ).
% 58.61/8.01  
% 58.61/8.01  cnf(c_6152,plain,
% 58.61/8.01      ( k1_lattices(sK9,k7_lattices(sK9,k7_lattices(sK9,X0)),k6_lattices(sK9)) = k6_lattices(sK9)
% 58.61/8.01      | m1_subset_1(X0,u1_struct_0(sK9)) != iProver_top ),
% 58.61/8.01      inference(superposition,[status(thm)],[c_2546,c_5541]) ).
% 58.61/8.01  
% 58.61/8.01  cnf(c_13240,plain,
% 58.61/8.01      ( k1_lattices(sK9,k7_lattices(sK9,k7_lattices(sK9,sK10)),k6_lattices(sK9)) = k6_lattices(sK9) ),
% 58.61/8.01      inference(superposition,[status(thm)],[c_2570,c_6152]) ).
% 58.61/8.01  
% 58.61/8.01  cnf(c_66877,plain,
% 58.61/8.01      ( k2_lattices(sK9,k7_lattices(sK9,k7_lattices(sK9,sK10)),k6_lattices(sK9)) = k4_lattices(sK9,k7_lattices(sK9,k7_lattices(sK9,sK10)),k6_lattices(sK9)) ),
% 58.61/8.01      inference(superposition,[status(thm)],[c_2547,c_66836]) ).
% 58.61/8.01  
% 58.61/8.01  cnf(c_4193,plain,
% 58.61/8.01      ( k4_lattices(sK9,k6_lattices(sK9),X0) = k4_lattices(sK9,X0,k6_lattices(sK9))
% 58.61/8.01      | m1_subset_1(X0,u1_struct_0(sK9)) != iProver_top ),
% 58.61/8.01      inference(superposition,[status(thm)],[c_2547,c_2556]) ).
% 58.61/8.01  
% 58.61/8.01  cnf(c_8887,plain,
% 58.61/8.01      ( k4_lattices(sK9,k7_lattices(sK9,X0),k6_lattices(sK9)) = k4_lattices(sK9,k6_lattices(sK9),k7_lattices(sK9,X0))
% 58.61/8.01      | m1_subset_1(X0,u1_struct_0(sK9)) != iProver_top ),
% 58.61/8.01      inference(superposition,[status(thm)],[c_2546,c_4193]) ).
% 58.61/8.01  
% 58.61/8.01  cnf(c_24409,plain,
% 58.61/8.01      ( k4_lattices(sK9,k7_lattices(sK9,k7_lattices(sK9,X0)),k6_lattices(sK9)) = k4_lattices(sK9,k6_lattices(sK9),k7_lattices(sK9,k7_lattices(sK9,X0)))
% 58.61/8.01      | m1_subset_1(X0,u1_struct_0(sK9)) != iProver_top ),
% 58.61/8.01      inference(superposition,[status(thm)],[c_2546,c_8887]) ).
% 58.61/8.01  
% 58.61/8.01  cnf(c_49315,plain,
% 58.61/8.01      ( k4_lattices(sK9,k6_lattices(sK9),k7_lattices(sK9,k7_lattices(sK9,sK10))) = k4_lattices(sK9,k7_lattices(sK9,k7_lattices(sK9,sK10)),k6_lattices(sK9)) ),
% 58.61/8.01      inference(superposition,[status(thm)],[c_2570,c_24409]) ).
% 58.61/8.01  
% 58.61/8.01  cnf(c_66883,plain,
% 58.61/8.01      ( k2_lattices(sK9,k7_lattices(sK9,k7_lattices(sK9,sK10)),k6_lattices(sK9)) = k4_lattices(sK9,k6_lattices(sK9),k7_lattices(sK9,k7_lattices(sK9,sK10))) ),
% 58.61/8.01      inference(light_normalisation,[status(thm)],[c_66877,c_49315]) ).
% 58.61/8.01  
% 58.61/8.01  cnf(c_88046,plain,
% 58.61/8.01      ( k4_lattices(sK9,k6_lattices(sK9),k7_lattices(sK9,k7_lattices(sK9,sK10))) = k7_lattices(sK9,k7_lattices(sK9,sK10)) ),
% 58.61/8.01      inference(light_normalisation,
% 58.61/8.01                [status(thm)],
% 58.61/8.01                [c_88040,c_13240,c_66883]) ).
% 58.61/8.01  
% 58.61/8.01  cnf(c_88058,plain,
% 58.61/8.01      ( k2_lattices(sK9,k7_lattices(sK9,k7_lattices(sK9,sK10)),k6_lattices(sK9)) = k7_lattices(sK9,k7_lattices(sK9,sK10)) ),
% 58.61/8.01      inference(demodulation,[status(thm)],[c_88046,c_66883]) ).
% 58.61/8.01  
% 58.61/8.01  cnf(c_193973,plain,
% 58.61/8.01      ( k7_lattices(sK9,k7_lattices(sK9,sK10)) = sK10 ),
% 58.61/8.01      inference(light_normalisation,
% 58.61/8.01                [status(thm)],
% 58.61/8.01                [c_193963,c_5275,c_5518,c_66948,c_88058]) ).
% 58.61/8.01  
% 58.61/8.01  cnf(c_48,negated_conjecture,
% 58.61/8.01      ( k7_lattices(sK9,k7_lattices(sK9,sK10)) != sK10 ),
% 58.61/8.01      inference(cnf_transformation,[],[f155]) ).
% 58.61/8.01  
% 58.61/8.01  cnf(contradiction,plain,
% 58.61/8.01      ( $false ),
% 58.61/8.01      inference(minisat,[status(thm)],[c_193973,c_48]) ).
% 58.61/8.01  
% 58.61/8.01  
% 58.61/8.01  % SZS output end CNFRefutation for theBenchmark.p
% 58.61/8.01  
% 58.61/8.01  ------                               Statistics
% 58.61/8.01  
% 58.61/8.01  ------ General
% 58.61/8.01  
% 58.61/8.01  abstr_ref_over_cycles:                  0
% 58.61/8.01  abstr_ref_under_cycles:                 0
% 58.61/8.01  gc_basic_clause_elim:                   0
% 58.61/8.01  forced_gc_time:                         0
% 58.61/8.01  parsing_time:                           0.011
% 58.61/8.01  unif_index_cands_time:                  0.
% 58.61/8.01  unif_index_add_time:                    0.
% 58.61/8.01  orderings_time:                         0.
% 58.61/8.01  out_proof_time:                         0.032
% 58.61/8.01  total_time:                             7.156
% 58.61/8.01  num_of_symbols:                         66
% 58.61/8.01  num_of_terms:                           179499
% 58.61/8.01  
% 58.61/8.01  ------ Preprocessing
% 58.61/8.01  
% 58.61/8.01  num_of_splits:                          0
% 58.61/8.01  num_of_split_atoms:                     0
% 58.61/8.01  num_of_reused_defs:                     0
% 58.61/8.01  num_eq_ax_congr_red:                    43
% 58.61/8.01  num_of_sem_filtered_clauses:            1
% 58.61/8.01  num_of_subtypes:                        0
% 58.61/8.01  monotx_restored_types:                  0
% 58.61/8.01  sat_num_of_epr_types:                   0
% 58.61/8.01  sat_num_of_non_cyclic_types:            0
% 58.61/8.01  sat_guarded_non_collapsed_types:        0
% 58.61/8.01  num_pure_diseq_elim:                    0
% 58.61/8.01  simp_replaced_by:                       0
% 58.61/8.01  res_preprocessed:                       159
% 58.61/8.01  prep_upred:                             0
% 58.61/8.01  prep_unflattend:                        61
% 58.61/8.01  smt_new_axioms:                         0
% 58.61/8.01  pred_elim_cands:                        1
% 58.61/8.01  pred_elim:                              14
% 58.61/8.01  pred_elim_cl:                           24
% 58.61/8.01  pred_elim_cycles:                       19
% 58.61/8.01  merged_defs:                            0
% 58.61/8.01  merged_defs_ncl:                        0
% 58.61/8.01  bin_hyper_res:                          0
% 58.61/8.01  prep_cycles:                            4
% 58.61/8.01  pred_elim_time:                         0.032
% 58.61/8.01  splitting_time:                         0.
% 58.61/8.01  sem_filter_time:                        0.
% 58.61/8.01  monotx_time:                            0.001
% 58.61/8.01  subtype_inf_time:                       0.
% 58.61/8.01  
% 58.61/8.01  ------ Problem properties
% 58.61/8.01  
% 58.61/8.01  clauses:                                27
% 58.61/8.01  conjectures:                            2
% 58.61/8.01  epr:                                    0
% 58.61/8.01  horn:                                   25
% 58.61/8.01  ground:                                 4
% 58.61/8.01  unary:                                  4
% 58.61/8.01  binary:                                 12
% 58.61/8.01  lits:                                   64
% 58.61/8.01  lits_eq:                                28
% 58.61/8.01  fd_pure:                                0
% 58.61/8.01  fd_pseudo:                              0
% 58.61/8.01  fd_cond:                                4
% 58.61/8.01  fd_pseudo_cond:                         1
% 58.61/8.01  ac_symbols:                             0
% 58.61/8.01  
% 58.61/8.01  ------ Propositional Solver
% 58.61/8.01  
% 58.61/8.01  prop_solver_calls:                      69
% 58.61/8.01  prop_fast_solver_calls:                 5466
% 58.61/8.01  smt_solver_calls:                       0
% 58.61/8.01  smt_fast_solver_calls:                  0
% 58.61/8.01  prop_num_of_clauses:                    66409
% 58.61/8.01  prop_preprocess_simplified:             137808
% 58.61/8.01  prop_fo_subsumed:                       122
% 58.61/8.01  prop_solver_time:                       0.
% 58.61/8.01  smt_solver_time:                        0.
% 58.61/8.01  smt_fast_solver_time:                   0.
% 58.61/8.01  prop_fast_solver_time:                  0.
% 58.61/8.01  prop_unsat_core_time:                   0.008
% 58.61/8.01  
% 58.61/8.01  ------ QBF
% 58.61/8.01  
% 58.61/8.01  qbf_q_res:                              0
% 58.61/8.01  qbf_num_tautologies:                    0
% 58.61/8.01  qbf_prep_cycles:                        0
% 58.61/8.01  
% 58.61/8.01  ------ BMC1
% 58.61/8.01  
% 58.61/8.01  bmc1_current_bound:                     -1
% 58.61/8.01  bmc1_last_solved_bound:                 -1
% 58.61/8.01  bmc1_unsat_core_size:                   -1
% 58.61/8.01  bmc1_unsat_core_parents_size:           -1
% 58.61/8.01  bmc1_merge_next_fun:                    0
% 58.61/8.01  bmc1_unsat_core_clauses_time:           0.
% 58.61/8.01  
% 58.61/8.01  ------ Instantiation
% 58.61/8.01  
% 58.61/8.01  inst_num_of_clauses:                    4274
% 58.61/8.01  inst_num_in_passive:                    2385
% 58.61/8.01  inst_num_in_active:                     8856
% 58.61/8.01  inst_num_in_unprocessed:                381
% 58.61/8.01  inst_num_of_loops:                      10648
% 58.61/8.01  inst_num_of_learning_restarts:          2
% 58.61/8.01  inst_num_moves_active_passive:          1785
% 58.61/8.01  inst_lit_activity:                      0
% 58.61/8.01  inst_lit_activity_moves:                13
% 58.61/8.01  inst_num_tautologies:                   0
% 58.61/8.01  inst_num_prop_implied:                  0
% 58.61/8.01  inst_num_existing_simplified:           0
% 58.61/8.01  inst_num_eq_res_simplified:             0
% 58.61/8.01  inst_num_child_elim:                    0
% 58.61/8.01  inst_num_of_dismatching_blockings:      54154
% 58.61/8.01  inst_num_of_non_proper_insts:           33325
% 58.61/8.01  inst_num_of_duplicates:                 0
% 58.61/8.01  inst_inst_num_from_inst_to_res:         0
% 58.61/8.01  inst_dismatching_checking_time:         0.
% 58.61/8.01  
% 58.61/8.01  ------ Resolution
% 58.61/8.01  
% 58.61/8.01  res_num_of_clauses:                     40
% 58.61/8.01  res_num_in_passive:                     40
% 58.61/8.01  res_num_in_active:                      0
% 58.61/8.01  res_num_of_loops:                       163
% 58.61/8.01  res_forward_subset_subsumed:            1153
% 58.61/8.01  res_backward_subset_subsumed:           6
% 58.61/8.01  res_forward_subsumed:                   0
% 58.61/8.01  res_backward_subsumed:                  0
% 58.61/8.01  res_forward_subsumption_resolution:     8
% 58.61/8.01  res_backward_subsumption_resolution:    0
% 58.61/8.01  res_clause_to_clause_subsumption:       38544
% 58.61/8.01  res_orphan_elimination:                 0
% 58.61/8.01  res_tautology_del:                      1252
% 58.61/8.01  res_num_eq_res_simplified:              0
% 58.61/8.01  res_num_sel_changes:                    0
% 58.61/8.01  res_moves_from_active_to_pass:          0
% 58.61/8.01  
% 58.61/8.01  ------ Superposition
% 58.61/8.01  
% 58.61/8.01  sup_time_total:                         0.
% 58.61/8.01  sup_time_generating:                    0.
% 58.61/8.01  sup_time_sim_full:                      0.
% 58.61/8.01  sup_time_sim_immed:                     0.
% 58.61/8.01  
% 58.61/8.01  sup_num_of_clauses:                     4433
% 58.61/8.01  sup_num_in_active:                      1972
% 58.61/8.01  sup_num_in_passive:                     2461
% 58.61/8.01  sup_num_of_loops:                       2129
% 58.61/8.01  sup_fw_superposition:                   6086
% 58.61/8.01  sup_bw_superposition:                   120
% 58.61/8.01  sup_immediate_simplified:               1750
% 58.61/8.01  sup_given_eliminated:                   2
% 58.61/8.01  comparisons_done:                       0
% 58.61/8.01  comparisons_avoided:                    1654
% 58.61/8.01  
% 58.61/8.01  ------ Simplifications
% 58.61/8.01  
% 58.61/8.01  
% 58.61/8.01  sim_fw_subset_subsumed:                 10
% 58.61/8.01  sim_bw_subset_subsumed:                 1
% 58.61/8.01  sim_fw_subsumed:                        0
% 58.61/8.01  sim_bw_subsumed:                        0
% 58.61/8.01  sim_fw_subsumption_res:                 0
% 58.61/8.01  sim_bw_subsumption_res:                 0
% 58.61/8.01  sim_tautology_del:                      0
% 58.61/8.01  sim_eq_tautology_del:                   1422
% 58.61/8.01  sim_eq_res_simp:                        0
% 58.61/8.01  sim_fw_demodulated:                     120
% 58.61/8.01  sim_bw_demodulated:                     168
% 58.61/8.01  sim_light_normalised:                   1785
% 58.61/8.01  sim_joinable_taut:                      0
% 58.61/8.01  sim_joinable_simp:                      0
% 58.61/8.01  sim_ac_normalised:                      0
% 58.61/8.01  sim_smt_subsumption:                    0
% 58.61/8.01  
%------------------------------------------------------------------------------
