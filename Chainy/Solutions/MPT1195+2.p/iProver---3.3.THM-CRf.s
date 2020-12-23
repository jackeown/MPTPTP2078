%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT1195+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:09:01 EST 2020

% Result     : Theorem 55.35s
% Output     : CNFRefutation 55.35s
% Verified   : 
% Statistics : Number of formulae       :   89 ( 517 expanded)
%              Number of clauses        :   44 ( 104 expanded)
%              Number of leaves         :   12 ( 145 expanded)
%              Depth                    :   16
%              Number of atoms          :  406 (3996 expanded)
%              Number of equality atoms :  140 ( 943 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal clause size      :   20 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2040,conjecture,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & v9_lattices(X0)
        & v8_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( r1_lattices(X0,X1,X2)
              <=> k2_lattices(X0,X1,X2) = X1 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f2041,negated_conjecture,(
    ~ ! [X0] :
        ( ( l3_lattices(X0)
          & v9_lattices(X0)
          & v8_lattices(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => ( r1_lattices(X0,X1,X2)
                <=> k2_lattices(X0,X1,X2) = X1 ) ) ) ) ),
    inference(negated_conjecture,[],[f2040])).

fof(f4494,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( r1_lattices(X0,X1,X2)
              <~> k2_lattices(X0,X1,X2) = X1 )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l3_lattices(X0)
      & v9_lattices(X0)
      & v8_lattices(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f2041])).

fof(f4495,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( r1_lattices(X0,X1,X2)
              <~> k2_lattices(X0,X1,X2) = X1 )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l3_lattices(X0)
      & v9_lattices(X0)
      & v8_lattices(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f4494])).

fof(f6349,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( k2_lattices(X0,X1,X2) != X1
                | ~ r1_lattices(X0,X1,X2) )
              & ( k2_lattices(X0,X1,X2) = X1
                | r1_lattices(X0,X1,X2) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l3_lattices(X0)
      & v9_lattices(X0)
      & v8_lattices(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f4495])).

fof(f6350,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( k2_lattices(X0,X1,X2) != X1
                | ~ r1_lattices(X0,X1,X2) )
              & ( k2_lattices(X0,X1,X2) = X1
                | r1_lattices(X0,X1,X2) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l3_lattices(X0)
      & v9_lattices(X0)
      & v8_lattices(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f6349])).

fof(f6353,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ( k2_lattices(X0,X1,X2) != X1
            | ~ r1_lattices(X0,X1,X2) )
          & ( k2_lattices(X0,X1,X2) = X1
            | r1_lattices(X0,X1,X2) )
          & m1_subset_1(X2,u1_struct_0(X0)) )
     => ( ( k2_lattices(X0,X1,sK757) != X1
          | ~ r1_lattices(X0,X1,sK757) )
        & ( k2_lattices(X0,X1,sK757) = X1
          | r1_lattices(X0,X1,sK757) )
        & m1_subset_1(sK757,u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f6352,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( k2_lattices(X0,X1,X2) != X1
                | ~ r1_lattices(X0,X1,X2) )
              & ( k2_lattices(X0,X1,X2) = X1
                | r1_lattices(X0,X1,X2) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
     => ( ? [X2] :
            ( ( k2_lattices(X0,sK756,X2) != sK756
              | ~ r1_lattices(X0,sK756,X2) )
            & ( k2_lattices(X0,sK756,X2) = sK756
              | r1_lattices(X0,sK756,X2) )
            & m1_subset_1(X2,u1_struct_0(X0)) )
        & m1_subset_1(sK756,u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f6351,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ( k2_lattices(X0,X1,X2) != X1
                  | ~ r1_lattices(X0,X1,X2) )
                & ( k2_lattices(X0,X1,X2) = X1
                  | r1_lattices(X0,X1,X2) )
                & m1_subset_1(X2,u1_struct_0(X0)) )
            & m1_subset_1(X1,u1_struct_0(X0)) )
        & l3_lattices(X0)
        & v9_lattices(X0)
        & v8_lattices(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ( k2_lattices(sK755,X1,X2) != X1
                | ~ r1_lattices(sK755,X1,X2) )
              & ( k2_lattices(sK755,X1,X2) = X1
                | r1_lattices(sK755,X1,X2) )
              & m1_subset_1(X2,u1_struct_0(sK755)) )
          & m1_subset_1(X1,u1_struct_0(sK755)) )
      & l3_lattices(sK755)
      & v9_lattices(sK755)
      & v8_lattices(sK755)
      & ~ v2_struct_0(sK755) ) ),
    introduced(choice_axiom,[])).

fof(f6354,plain,
    ( ( k2_lattices(sK755,sK756,sK757) != sK756
      | ~ r1_lattices(sK755,sK756,sK757) )
    & ( k2_lattices(sK755,sK756,sK757) = sK756
      | r1_lattices(sK755,sK756,sK757) )
    & m1_subset_1(sK757,u1_struct_0(sK755))
    & m1_subset_1(sK756,u1_struct_0(sK755))
    & l3_lattices(sK755)
    & v9_lattices(sK755)
    & v8_lattices(sK755)
    & ~ v2_struct_0(sK755) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK755,sK756,sK757])],[f6350,f6353,f6352,f6351])).

fof(f10393,plain,
    ( k2_lattices(sK755,sK756,sK757) = sK756
    | r1_lattices(sK755,sK756,sK757) ),
    inference(cnf_transformation,[],[f6354])).

fof(f2015,axiom,(
    ! [X0] :
      ( ( l2_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( r1_lattices(X0,X1,X2)
              <=> k1_lattices(X0,X1,X2) = X2 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f4457,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r1_lattices(X0,X1,X2)
              <=> k1_lattices(X0,X1,X2) = X2 )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l2_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f2015])).

fof(f4458,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r1_lattices(X0,X1,X2)
              <=> k1_lattices(X0,X1,X2) = X2 )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l2_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f4457])).

fof(f6311,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( r1_lattices(X0,X1,X2)
                  | k1_lattices(X0,X1,X2) != X2 )
                & ( k1_lattices(X0,X1,X2) = X2
                  | ~ r1_lattices(X0,X1,X2) ) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l2_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f4458])).

fof(f10336,plain,(
    ! [X2,X0,X1] :
      ( k1_lattices(X0,X1,X2) = X2
      | ~ r1_lattices(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l2_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f6311])).

fof(f10387,plain,(
    ~ v2_struct_0(sK755) ),
    inference(cnf_transformation,[],[f6354])).

fof(f10390,plain,(
    l3_lattices(sK755) ),
    inference(cnf_transformation,[],[f6354])).

fof(f10391,plain,(
    m1_subset_1(sK756,u1_struct_0(sK755)) ),
    inference(cnf_transformation,[],[f6354])).

fof(f10392,plain,(
    m1_subset_1(sK757,u1_struct_0(sK755)) ),
    inference(cnf_transformation,[],[f6354])).

fof(f2028,axiom,(
    ! [X0] :
      ( l3_lattices(X0)
     => ( l2_lattices(X0)
        & l1_lattices(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f4479,plain,(
    ! [X0] :
      ( ( l2_lattices(X0)
        & l1_lattices(X0) )
      | ~ l3_lattices(X0) ) ),
    inference(ennf_transformation,[],[f2028])).

fof(f10364,plain,(
    ! [X0] :
      ( l2_lattices(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f4479])).

fof(f2018,axiom,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ( v8_lattices(X0)
      <=> ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => k1_lattices(X0,k2_lattices(X0,X1,X2),X2) = X2 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f4463,plain,(
    ! [X0] :
      ( ( v8_lattices(X0)
      <=> ! [X1] :
            ( ! [X2] :
                ( k1_lattices(X0,k2_lattices(X0,X1,X2),X2) = X2
                | ~ m1_subset_1(X2,u1_struct_0(X0)) )
            | ~ m1_subset_1(X1,u1_struct_0(X0)) ) )
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f2018])).

fof(f4464,plain,(
    ! [X0] :
      ( ( v8_lattices(X0)
      <=> ! [X1] :
            ( ! [X2] :
                ( k1_lattices(X0,k2_lattices(X0,X1,X2),X2) = X2
                | ~ m1_subset_1(X2,u1_struct_0(X0)) )
            | ~ m1_subset_1(X1,u1_struct_0(X0)) ) )
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f4463])).

fof(f6324,plain,(
    ! [X0] :
      ( ( ( v8_lattices(X0)
          | ? [X1] :
              ( ? [X2] :
                  ( k1_lattices(X0,k2_lattices(X0,X1,X2),X2) != X2
                  & m1_subset_1(X2,u1_struct_0(X0)) )
              & m1_subset_1(X1,u1_struct_0(X0)) ) )
        & ( ! [X1] :
              ( ! [X2] :
                  ( k1_lattices(X0,k2_lattices(X0,X1,X2),X2) = X2
                  | ~ m1_subset_1(X2,u1_struct_0(X0)) )
              | ~ m1_subset_1(X1,u1_struct_0(X0)) )
          | ~ v8_lattices(X0) ) )
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f4464])).

fof(f6325,plain,(
    ! [X0] :
      ( ( ( v8_lattices(X0)
          | ? [X1] :
              ( ? [X2] :
                  ( k1_lattices(X0,k2_lattices(X0,X1,X2),X2) != X2
                  & m1_subset_1(X2,u1_struct_0(X0)) )
              & m1_subset_1(X1,u1_struct_0(X0)) ) )
        & ( ! [X3] :
              ( ! [X4] :
                  ( k1_lattices(X0,k2_lattices(X0,X3,X4),X4) = X4
                  | ~ m1_subset_1(X4,u1_struct_0(X0)) )
              | ~ m1_subset_1(X3,u1_struct_0(X0)) )
          | ~ v8_lattices(X0) ) )
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(rectify,[],[f6324])).

fof(f6327,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( k1_lattices(X0,k2_lattices(X0,X1,X2),X2) != X2
          & m1_subset_1(X2,u1_struct_0(X0)) )
     => ( k1_lattices(X0,k2_lattices(X0,X1,sK743(X0)),sK743(X0)) != sK743(X0)
        & m1_subset_1(sK743(X0),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f6326,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( k1_lattices(X0,k2_lattices(X0,X1,X2),X2) != X2
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
     => ( ? [X2] :
            ( k1_lattices(X0,k2_lattices(X0,sK742(X0),X2),X2) != X2
            & m1_subset_1(X2,u1_struct_0(X0)) )
        & m1_subset_1(sK742(X0),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f6328,plain,(
    ! [X0] :
      ( ( ( v8_lattices(X0)
          | ( k1_lattices(X0,k2_lattices(X0,sK742(X0),sK743(X0)),sK743(X0)) != sK743(X0)
            & m1_subset_1(sK743(X0),u1_struct_0(X0))
            & m1_subset_1(sK742(X0),u1_struct_0(X0)) ) )
        & ( ! [X3] :
              ( ! [X4] :
                  ( k1_lattices(X0,k2_lattices(X0,X3,X4),X4) = X4
                  | ~ m1_subset_1(X4,u1_struct_0(X0)) )
              | ~ m1_subset_1(X3,u1_struct_0(X0)) )
          | ~ v8_lattices(X0) ) )
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK742,sK743])],[f6325,f6327,f6326])).

fof(f10348,plain,(
    ! [X4,X0,X3] :
      ( k1_lattices(X0,k2_lattices(X0,X3,X4),X4) = X4
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ v8_lattices(X0)
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f6328])).

fof(f10388,plain,(
    v8_lattices(sK755) ),
    inference(cnf_transformation,[],[f6354])).

fof(f10337,plain,(
    ! [X2,X0,X1] :
      ( r1_lattices(X0,X1,X2)
      | k1_lattices(X0,X1,X2) != X2
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l2_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f6311])).

fof(f2019,axiom,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ( v9_lattices(X0)
      <=> ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => k2_lattices(X0,X1,k1_lattices(X0,X1,X2)) = X1 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f4465,plain,(
    ! [X0] :
      ( ( v9_lattices(X0)
      <=> ! [X1] :
            ( ! [X2] :
                ( k2_lattices(X0,X1,k1_lattices(X0,X1,X2)) = X1
                | ~ m1_subset_1(X2,u1_struct_0(X0)) )
            | ~ m1_subset_1(X1,u1_struct_0(X0)) ) )
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f2019])).

fof(f4466,plain,(
    ! [X0] :
      ( ( v9_lattices(X0)
      <=> ! [X1] :
            ( ! [X2] :
                ( k2_lattices(X0,X1,k1_lattices(X0,X1,X2)) = X1
                | ~ m1_subset_1(X2,u1_struct_0(X0)) )
            | ~ m1_subset_1(X1,u1_struct_0(X0)) ) )
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f4465])).

fof(f6329,plain,(
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
    inference(nnf_transformation,[],[f4466])).

fof(f6330,plain,(
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
    inference(rectify,[],[f6329])).

fof(f6332,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( k2_lattices(X0,X1,k1_lattices(X0,X1,X2)) != X1
          & m1_subset_1(X2,u1_struct_0(X0)) )
     => ( k2_lattices(X0,X1,k1_lattices(X0,X1,sK745(X0))) != X1
        & m1_subset_1(sK745(X0),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f6331,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( k2_lattices(X0,X1,k1_lattices(X0,X1,X2)) != X1
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
     => ( ? [X2] :
            ( k2_lattices(X0,sK744(X0),k1_lattices(X0,sK744(X0),X2)) != sK744(X0)
            & m1_subset_1(X2,u1_struct_0(X0)) )
        & m1_subset_1(sK744(X0),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f6333,plain,(
    ! [X0] :
      ( ( ( v9_lattices(X0)
          | ( k2_lattices(X0,sK744(X0),k1_lattices(X0,sK744(X0),sK745(X0))) != sK744(X0)
            & m1_subset_1(sK745(X0),u1_struct_0(X0))
            & m1_subset_1(sK744(X0),u1_struct_0(X0)) ) )
        & ( ! [X3] :
              ( ! [X4] :
                  ( k2_lattices(X0,X3,k1_lattices(X0,X3,X4)) = X3
                  | ~ m1_subset_1(X4,u1_struct_0(X0)) )
              | ~ m1_subset_1(X3,u1_struct_0(X0)) )
          | ~ v9_lattices(X0) ) )
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK744,sK745])],[f6330,f6332,f6331])).

fof(f10352,plain,(
    ! [X4,X0,X3] :
      ( k2_lattices(X0,X3,k1_lattices(X0,X3,X4)) = X3
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ v9_lattices(X0)
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f6333])).

fof(f10389,plain,(
    v9_lattices(sK755) ),
    inference(cnf_transformation,[],[f6354])).

fof(f10394,plain,
    ( k2_lattices(sK755,sK756,sK757) != sK756
    | ~ r1_lattices(sK755,sK756,sK757) ),
    inference(cnf_transformation,[],[f6354])).

cnf(c_4005,negated_conjecture,
    ( r1_lattices(sK755,sK756,sK757)
    | k2_lattices(sK755,sK756,sK757) = sK756 ),
    inference(cnf_transformation,[],[f10393])).

cnf(c_117789,plain,
    ( k2_lattices(sK755,sK756,sK757) = sK756
    | r1_lattices(sK755,sK756,sK757) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4005])).

cnf(c_3954,plain,
    ( ~ r1_lattices(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ l2_lattices(X0)
    | v2_struct_0(X0)
    | k1_lattices(X0,X1,X2) = X2 ),
    inference(cnf_transformation,[],[f10336])).

cnf(c_117826,plain,
    ( k1_lattices(X0,X1,X2) = X2
    | r1_lattices(X0,X1,X2) != iProver_top
    | m1_subset_1(X2,u1_struct_0(X0)) != iProver_top
    | m1_subset_1(X1,u1_struct_0(X0)) != iProver_top
    | l2_lattices(X0) != iProver_top
    | v2_struct_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3954])).

cnf(c_163921,plain,
    ( k2_lattices(sK755,sK756,sK757) = sK756
    | k1_lattices(sK755,sK756,sK757) = sK757
    | m1_subset_1(sK757,u1_struct_0(sK755)) != iProver_top
    | m1_subset_1(sK756,u1_struct_0(sK755)) != iProver_top
    | l2_lattices(sK755) != iProver_top
    | v2_struct_0(sK755) = iProver_top ),
    inference(superposition,[status(thm)],[c_117789,c_117826])).

cnf(c_4011,negated_conjecture,
    ( ~ v2_struct_0(sK755) ),
    inference(cnf_transformation,[],[f10387])).

cnf(c_4008,negated_conjecture,
    ( l3_lattices(sK755) ),
    inference(cnf_transformation,[],[f10390])).

cnf(c_4007,negated_conjecture,
    ( m1_subset_1(sK756,u1_struct_0(sK755)) ),
    inference(cnf_transformation,[],[f10391])).

cnf(c_4006,negated_conjecture,
    ( m1_subset_1(sK757,u1_struct_0(sK755)) ),
    inference(cnf_transformation,[],[f10392])).

cnf(c_3980,plain,
    ( l2_lattices(X0)
    | ~ l3_lattices(X0) ),
    inference(cnf_transformation,[],[f10364])).

cnf(c_155956,plain,
    ( l2_lattices(sK755)
    | ~ l3_lattices(sK755) ),
    inference(instantiation,[status(thm)],[c_3980])).

cnf(c_163922,plain,
    ( ~ m1_subset_1(sK757,u1_struct_0(sK755))
    | ~ m1_subset_1(sK756,u1_struct_0(sK755))
    | ~ l2_lattices(sK755)
    | v2_struct_0(sK755)
    | k2_lattices(sK755,sK756,sK757) = sK756
    | k1_lattices(sK755,sK756,sK757) = sK757 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_163921])).

cnf(c_164436,plain,
    ( k2_lattices(sK755,sK756,sK757) = sK756
    | k1_lattices(sK755,sK756,sK757) = sK757 ),
    inference(global_propositional_subsumption,[status(thm)],[c_163921,c_4011,c_4008,c_4007,c_4006,c_155956,c_163922])).

cnf(c_117787,plain,
    ( m1_subset_1(sK756,u1_struct_0(sK755)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4007])).

cnf(c_117788,plain,
    ( m1_subset_1(sK757,u1_struct_0(sK755)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4006])).

cnf(c_3968,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v8_lattices(X1)
    | ~ l3_lattices(X1)
    | v2_struct_0(X1)
    | k1_lattices(X1,k2_lattices(X1,X0,X2),X2) = X2 ),
    inference(cnf_transformation,[],[f10348])).

cnf(c_117812,plain,
    ( k1_lattices(X0,k2_lattices(X0,X1,X2),X2) = X2
    | m1_subset_1(X1,u1_struct_0(X0)) != iProver_top
    | m1_subset_1(X2,u1_struct_0(X0)) != iProver_top
    | v8_lattices(X0) != iProver_top
    | l3_lattices(X0) != iProver_top
    | v2_struct_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3968])).

cnf(c_158516,plain,
    ( k1_lattices(sK755,k2_lattices(sK755,X0,sK757),sK757) = sK757
    | m1_subset_1(X0,u1_struct_0(sK755)) != iProver_top
    | v8_lattices(sK755) != iProver_top
    | l3_lattices(sK755) != iProver_top
    | v2_struct_0(sK755) = iProver_top ),
    inference(superposition,[status(thm)],[c_117788,c_117812])).

cnf(c_4012,plain,
    ( v2_struct_0(sK755) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4011])).

cnf(c_4010,negated_conjecture,
    ( v8_lattices(sK755) ),
    inference(cnf_transformation,[],[f10388])).

cnf(c_4013,plain,
    ( v8_lattices(sK755) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4010])).

cnf(c_4015,plain,
    ( l3_lattices(sK755) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4008])).

cnf(c_159265,plain,
    ( m1_subset_1(X0,u1_struct_0(sK755)) != iProver_top
    | k1_lattices(sK755,k2_lattices(sK755,X0,sK757),sK757) = sK757 ),
    inference(global_propositional_subsumption,[status(thm)],[c_158516,c_4012,c_4013,c_4015])).

cnf(c_159266,plain,
    ( k1_lattices(sK755,k2_lattices(sK755,X0,sK757),sK757) = sK757
    | m1_subset_1(X0,u1_struct_0(sK755)) != iProver_top ),
    inference(renaming,[status(thm)],[c_159265])).

cnf(c_159277,plain,
    ( k1_lattices(sK755,k2_lattices(sK755,sK756,sK757),sK757) = sK757 ),
    inference(superposition,[status(thm)],[c_117787,c_159266])).

cnf(c_164444,plain,
    ( k1_lattices(sK755,sK756,sK757) = sK757 ),
    inference(superposition,[status(thm)],[c_164436,c_159277])).

cnf(c_3953,plain,
    ( r1_lattices(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ l2_lattices(X0)
    | v2_struct_0(X0)
    | k1_lattices(X0,X1,X2) != X2 ),
    inference(cnf_transformation,[],[f10337])).

cnf(c_117827,plain,
    ( k1_lattices(X0,X1,X2) != X2
    | r1_lattices(X0,X1,X2) = iProver_top
    | m1_subset_1(X2,u1_struct_0(X0)) != iProver_top
    | m1_subset_1(X1,u1_struct_0(X0)) != iProver_top
    | l2_lattices(X0) != iProver_top
    | v2_struct_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3953])).

cnf(c_165090,plain,
    ( r1_lattices(sK755,sK756,sK757) = iProver_top
    | m1_subset_1(sK757,u1_struct_0(sK755)) != iProver_top
    | m1_subset_1(sK756,u1_struct_0(sK755)) != iProver_top
    | l2_lattices(sK755) != iProver_top
    | v2_struct_0(sK755) = iProver_top ),
    inference(superposition,[status(thm)],[c_164444,c_117827])).

cnf(c_3972,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l3_lattices(X1)
    | ~ v9_lattices(X1)
    | v2_struct_0(X1)
    | k2_lattices(X1,X0,k1_lattices(X1,X0,X2)) = X0 ),
    inference(cnf_transformation,[],[f10352])).

cnf(c_117808,plain,
    ( k2_lattices(X0,X1,k1_lattices(X0,X1,X2)) = X1
    | m1_subset_1(X1,u1_struct_0(X0)) != iProver_top
    | m1_subset_1(X2,u1_struct_0(X0)) != iProver_top
    | l3_lattices(X0) != iProver_top
    | v9_lattices(X0) != iProver_top
    | v2_struct_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3972])).

cnf(c_156661,plain,
    ( k2_lattices(sK755,X0,k1_lattices(sK755,X0,sK757)) = X0
    | m1_subset_1(X0,u1_struct_0(sK755)) != iProver_top
    | l3_lattices(sK755) != iProver_top
    | v9_lattices(sK755) != iProver_top
    | v2_struct_0(sK755) = iProver_top ),
    inference(superposition,[status(thm)],[c_117788,c_117808])).

cnf(c_4009,negated_conjecture,
    ( v9_lattices(sK755) ),
    inference(cnf_transformation,[],[f10389])).

cnf(c_4014,plain,
    ( v9_lattices(sK755) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4009])).

cnf(c_156750,plain,
    ( m1_subset_1(X0,u1_struct_0(sK755)) != iProver_top
    | k2_lattices(sK755,X0,k1_lattices(sK755,X0,sK757)) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_156661,c_4012,c_4014,c_4015])).

cnf(c_156751,plain,
    ( k2_lattices(sK755,X0,k1_lattices(sK755,X0,sK757)) = X0
    | m1_subset_1(X0,u1_struct_0(sK755)) != iProver_top ),
    inference(renaming,[status(thm)],[c_156750])).

cnf(c_156760,plain,
    ( k2_lattices(sK755,sK756,k1_lattices(sK755,sK756,sK757)) = sK756 ),
    inference(superposition,[status(thm)],[c_117787,c_156751])).

cnf(c_164501,plain,
    ( k2_lattices(sK755,sK756,sK757) = sK756 ),
    inference(demodulation,[status(thm)],[c_164444,c_156760])).

cnf(c_155957,plain,
    ( l2_lattices(sK755) = iProver_top
    | l3_lattices(sK755) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_155956])).

cnf(c_4004,negated_conjecture,
    ( ~ r1_lattices(sK755,sK756,sK757)
    | k2_lattices(sK755,sK756,sK757) != sK756 ),
    inference(cnf_transformation,[],[f10394])).

cnf(c_4019,plain,
    ( k2_lattices(sK755,sK756,sK757) != sK756
    | r1_lattices(sK755,sK756,sK757) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4004])).

cnf(c_4017,plain,
    ( m1_subset_1(sK757,u1_struct_0(sK755)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4006])).

cnf(c_4016,plain,
    ( m1_subset_1(sK756,u1_struct_0(sK755)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4007])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_165090,c_164501,c_155957,c_4019,c_4017,c_4016,c_4015,c_4012])).

%------------------------------------------------------------------------------
