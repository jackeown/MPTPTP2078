%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT1198+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:09:02 EST 2020

% Result     : Timeout 59.11s
% Output     : None 
% Verified   : 
% Statistics : Number of formulae       :   74 ( 367 expanded)
%              Number of clauses        :   40 (  77 expanded)
%              Number of leaves         :   10 ( 138 expanded)
%              Depth                    :   17
%              Number of atoms          :  316 (2809 expanded)
%              Number of equality atoms :   91 ( 142 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal clause size      :   18 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2043,conjecture,(
    ! [X0] :
      ( ( l2_lattices(X0)
        & v5_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ! [X3] :
                  ( m1_subset_1(X3,u1_struct_0(X0))
                 => ( ( r1_lattices(X0,X2,X3)
                      & r1_lattices(X0,X1,X2) )
                   => r1_lattices(X0,X1,X3) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f2044,negated_conjecture,(
    ~ ! [X0] :
        ( ( l2_lattices(X0)
          & v5_lattices(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => ! [X3] :
                    ( m1_subset_1(X3,u1_struct_0(X0))
                   => ( ( r1_lattices(X0,X2,X3)
                        & r1_lattices(X0,X1,X2) )
                     => r1_lattices(X0,X1,X3) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f2043])).

fof(f4503,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ r1_lattices(X0,X1,X3)
                  & r1_lattices(X0,X2,X3)
                  & r1_lattices(X0,X1,X2)
                  & m1_subset_1(X3,u1_struct_0(X0)) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l2_lattices(X0)
      & v5_lattices(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f2044])).

fof(f4504,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ r1_lattices(X0,X1,X3)
                  & r1_lattices(X0,X2,X3)
                  & r1_lattices(X0,X1,X2)
                  & m1_subset_1(X3,u1_struct_0(X0)) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l2_lattices(X0)
      & v5_lattices(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f4503])).

fof(f6362,plain,(
    ! [X2,X0,X1] :
      ( ? [X3] :
          ( ~ r1_lattices(X0,X1,X3)
          & r1_lattices(X0,X2,X3)
          & r1_lattices(X0,X1,X2)
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ~ r1_lattices(X0,X1,sK758)
        & r1_lattices(X0,X2,sK758)
        & r1_lattices(X0,X1,X2)
        & m1_subset_1(sK758,u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f6361,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ? [X3] :
              ( ~ r1_lattices(X0,X1,X3)
              & r1_lattices(X0,X2,X3)
              & r1_lattices(X0,X1,X2)
              & m1_subset_1(X3,u1_struct_0(X0)) )
          & m1_subset_1(X2,u1_struct_0(X0)) )
     => ( ? [X3] :
            ( ~ r1_lattices(X0,X1,X3)
            & r1_lattices(X0,sK757,X3)
            & r1_lattices(X0,X1,sK757)
            & m1_subset_1(X3,u1_struct_0(X0)) )
        & m1_subset_1(sK757,u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f6360,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ r1_lattices(X0,X1,X3)
                  & r1_lattices(X0,X2,X3)
                  & r1_lattices(X0,X1,X2)
                  & m1_subset_1(X3,u1_struct_0(X0)) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
     => ( ? [X2] :
            ( ? [X3] :
                ( ~ r1_lattices(X0,sK756,X3)
                & r1_lattices(X0,X2,X3)
                & r1_lattices(X0,sK756,X2)
                & m1_subset_1(X3,u1_struct_0(X0)) )
            & m1_subset_1(X2,u1_struct_0(X0)) )
        & m1_subset_1(sK756,u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f6359,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ? [X3] :
                    ( ~ r1_lattices(X0,X1,X3)
                    & r1_lattices(X0,X2,X3)
                    & r1_lattices(X0,X1,X2)
                    & m1_subset_1(X3,u1_struct_0(X0)) )
                & m1_subset_1(X2,u1_struct_0(X0)) )
            & m1_subset_1(X1,u1_struct_0(X0)) )
        & l2_lattices(X0)
        & v5_lattices(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ r1_lattices(sK755,X1,X3)
                  & r1_lattices(sK755,X2,X3)
                  & r1_lattices(sK755,X1,X2)
                  & m1_subset_1(X3,u1_struct_0(sK755)) )
              & m1_subset_1(X2,u1_struct_0(sK755)) )
          & m1_subset_1(X1,u1_struct_0(sK755)) )
      & l2_lattices(sK755)
      & v5_lattices(sK755)
      & ~ v2_struct_0(sK755) ) ),
    introduced(choice_axiom,[])).

fof(f6363,plain,
    ( ~ r1_lattices(sK755,sK756,sK758)
    & r1_lattices(sK755,sK757,sK758)
    & r1_lattices(sK755,sK756,sK757)
    & m1_subset_1(sK758,u1_struct_0(sK755))
    & m1_subset_1(sK757,u1_struct_0(sK755))
    & m1_subset_1(sK756,u1_struct_0(sK755))
    & l2_lattices(sK755)
    & v5_lattices(sK755)
    & ~ v2_struct_0(sK755) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK755,sK756,sK757,sK758])],[f4504,f6362,f6361,f6360,f6359])).

fof(f10407,plain,(
    r1_lattices(sK755,sK757,sK758) ),
    inference(cnf_transformation,[],[f6363])).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f4460,plain,(
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

fof(f4461,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r1_lattices(X0,X1,X2)
              <=> k1_lattices(X0,X1,X2) = X2 )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l2_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f4460])).

fof(f6320,plain,(
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
    inference(nnf_transformation,[],[f4461])).

fof(f10345,plain,(
    ! [X2,X0,X1] :
      ( k1_lattices(X0,X1,X2) = X2
      | ~ r1_lattices(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l2_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f6320])).

fof(f10400,plain,(
    ~ v2_struct_0(sK755) ),
    inference(cnf_transformation,[],[f6363])).

fof(f10402,plain,(
    l2_lattices(sK755) ),
    inference(cnf_transformation,[],[f6363])).

fof(f10404,plain,(
    m1_subset_1(sK757,u1_struct_0(sK755)) ),
    inference(cnf_transformation,[],[f6363])).

fof(f10405,plain,(
    m1_subset_1(sK758,u1_struct_0(sK755)) ),
    inference(cnf_transformation,[],[f6363])).

fof(f10403,plain,(
    m1_subset_1(sK756,u1_struct_0(sK755)) ),
    inference(cnf_transformation,[],[f6363])).

fof(f2016,axiom,(
    ! [X0] :
      ( ( l2_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ( v5_lattices(X0)
      <=> ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => ! [X3] :
                    ( m1_subset_1(X3,u1_struct_0(X0))
                   => k1_lattices(X0,X1,k1_lattices(X0,X2,X3)) = k1_lattices(X0,k1_lattices(X0,X1,X2),X3) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f4462,plain,(
    ! [X0] :
      ( ( v5_lattices(X0)
      <=> ! [X1] :
            ( ! [X2] :
                ( ! [X3] :
                    ( k1_lattices(X0,X1,k1_lattices(X0,X2,X3)) = k1_lattices(X0,k1_lattices(X0,X1,X2),X3)
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                | ~ m1_subset_1(X2,u1_struct_0(X0)) )
            | ~ m1_subset_1(X1,u1_struct_0(X0)) ) )
      | ~ l2_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f2016])).

fof(f4463,plain,(
    ! [X0] :
      ( ( v5_lattices(X0)
      <=> ! [X1] :
            ( ! [X2] :
                ( ! [X3] :
                    ( k1_lattices(X0,X1,k1_lattices(X0,X2,X3)) = k1_lattices(X0,k1_lattices(X0,X1,X2),X3)
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                | ~ m1_subset_1(X2,u1_struct_0(X0)) )
            | ~ m1_subset_1(X1,u1_struct_0(X0)) ) )
      | ~ l2_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f4462])).

fof(f6321,plain,(
    ! [X0] :
      ( ( ( v5_lattices(X0)
          | ? [X1] :
              ( ? [X2] :
                  ( ? [X3] :
                      ( k1_lattices(X0,X1,k1_lattices(X0,X2,X3)) != k1_lattices(X0,k1_lattices(X0,X1,X2),X3)
                      & m1_subset_1(X3,u1_struct_0(X0)) )
                  & m1_subset_1(X2,u1_struct_0(X0)) )
              & m1_subset_1(X1,u1_struct_0(X0)) ) )
        & ( ! [X1] :
              ( ! [X2] :
                  ( ! [X3] :
                      ( k1_lattices(X0,X1,k1_lattices(X0,X2,X3)) = k1_lattices(X0,k1_lattices(X0,X1,X2),X3)
                      | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                  | ~ m1_subset_1(X2,u1_struct_0(X0)) )
              | ~ m1_subset_1(X1,u1_struct_0(X0)) )
          | ~ v5_lattices(X0) ) )
      | ~ l2_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f4463])).

fof(f6322,plain,(
    ! [X0] :
      ( ( ( v5_lattices(X0)
          | ? [X1] :
              ( ? [X2] :
                  ( ? [X3] :
                      ( k1_lattices(X0,X1,k1_lattices(X0,X2,X3)) != k1_lattices(X0,k1_lattices(X0,X1,X2),X3)
                      & m1_subset_1(X3,u1_struct_0(X0)) )
                  & m1_subset_1(X2,u1_struct_0(X0)) )
              & m1_subset_1(X1,u1_struct_0(X0)) ) )
        & ( ! [X4] :
              ( ! [X5] :
                  ( ! [X6] :
                      ( k1_lattices(X0,X4,k1_lattices(X0,X5,X6)) = k1_lattices(X0,k1_lattices(X0,X4,X5),X6)
                      | ~ m1_subset_1(X6,u1_struct_0(X0)) )
                  | ~ m1_subset_1(X5,u1_struct_0(X0)) )
              | ~ m1_subset_1(X4,u1_struct_0(X0)) )
          | ~ v5_lattices(X0) ) )
      | ~ l2_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(rectify,[],[f6321])).

fof(f6325,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( k1_lattices(X0,X1,k1_lattices(X0,X2,X3)) != k1_lattices(X0,k1_lattices(X0,X1,X2),X3)
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( k1_lattices(X0,X1,k1_lattices(X0,X2,sK738(X0))) != k1_lattices(X0,k1_lattices(X0,X1,X2),sK738(X0))
        & m1_subset_1(sK738(X0),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f6324,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ? [X3] :
              ( k1_lattices(X0,X1,k1_lattices(X0,X2,X3)) != k1_lattices(X0,k1_lattices(X0,X1,X2),X3)
              & m1_subset_1(X3,u1_struct_0(X0)) )
          & m1_subset_1(X2,u1_struct_0(X0)) )
     => ( ? [X3] :
            ( k1_lattices(X0,X1,k1_lattices(X0,sK737(X0),X3)) != k1_lattices(X0,k1_lattices(X0,X1,sK737(X0)),X3)
            & m1_subset_1(X3,u1_struct_0(X0)) )
        & m1_subset_1(sK737(X0),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f6323,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( k1_lattices(X0,X1,k1_lattices(X0,X2,X3)) != k1_lattices(X0,k1_lattices(X0,X1,X2),X3)
                  & m1_subset_1(X3,u1_struct_0(X0)) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
     => ( ? [X2] :
            ( ? [X3] :
                ( k1_lattices(X0,k1_lattices(X0,sK736(X0),X2),X3) != k1_lattices(X0,sK736(X0),k1_lattices(X0,X2,X3))
                & m1_subset_1(X3,u1_struct_0(X0)) )
            & m1_subset_1(X2,u1_struct_0(X0)) )
        & m1_subset_1(sK736(X0),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f6326,plain,(
    ! [X0] :
      ( ( ( v5_lattices(X0)
          | ( k1_lattices(X0,k1_lattices(X0,sK736(X0),sK737(X0)),sK738(X0)) != k1_lattices(X0,sK736(X0),k1_lattices(X0,sK737(X0),sK738(X0)))
            & m1_subset_1(sK738(X0),u1_struct_0(X0))
            & m1_subset_1(sK737(X0),u1_struct_0(X0))
            & m1_subset_1(sK736(X0),u1_struct_0(X0)) ) )
        & ( ! [X4] :
              ( ! [X5] :
                  ( ! [X6] :
                      ( k1_lattices(X0,X4,k1_lattices(X0,X5,X6)) = k1_lattices(X0,k1_lattices(X0,X4,X5),X6)
                      | ~ m1_subset_1(X6,u1_struct_0(X0)) )
                  | ~ m1_subset_1(X5,u1_struct_0(X0)) )
              | ~ m1_subset_1(X4,u1_struct_0(X0)) )
          | ~ v5_lattices(X0) ) )
      | ~ l2_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK736,sK737,sK738])],[f6322,f6325,f6324,f6323])).

fof(f10347,plain,(
    ! [X6,X4,X0,X5] :
      ( k1_lattices(X0,X4,k1_lattices(X0,X5,X6)) = k1_lattices(X0,k1_lattices(X0,X4,X5),X6)
      | ~ m1_subset_1(X6,u1_struct_0(X0))
      | ~ m1_subset_1(X5,u1_struct_0(X0))
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ v5_lattices(X0)
      | ~ l2_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f6326])).

fof(f10401,plain,(
    v5_lattices(sK755) ),
    inference(cnf_transformation,[],[f6363])).

fof(f10406,plain,(
    r1_lattices(sK755,sK756,sK757) ),
    inference(cnf_transformation,[],[f6363])).

fof(f10346,plain,(
    ! [X2,X0,X1] :
      ( r1_lattices(X0,X1,X2)
      | k1_lattices(X0,X1,X2) != X2
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l2_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f6320])).

fof(f10408,plain,(
    ~ r1_lattices(sK755,sK756,sK758) ),
    inference(cnf_transformation,[],[f6363])).

cnf(c_4009,negated_conjecture,
    ( r1_lattices(sK755,sK757,sK758) ),
    inference(cnf_transformation,[],[f10407])).

cnf(c_117844,plain,
    ( r1_lattices(sK755,sK757,sK758) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4009])).

cnf(c_3954,plain,
    ( ~ r1_lattices(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ l2_lattices(X0)
    | v2_struct_0(X0)
    | k1_lattices(X0,X1,X2) = X2 ),
    inference(cnf_transformation,[],[f10345])).

cnf(c_117883,plain,
    ( k1_lattices(X0,X1,X2) = X2
    | r1_lattices(X0,X1,X2) != iProver_top
    | m1_subset_1(X2,u1_struct_0(X0)) != iProver_top
    | m1_subset_1(X1,u1_struct_0(X0)) != iProver_top
    | l2_lattices(X0) != iProver_top
    | v2_struct_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3954])).

cnf(c_167940,plain,
    ( k1_lattices(sK755,sK757,sK758) = sK758
    | m1_subset_1(sK757,u1_struct_0(sK755)) != iProver_top
    | m1_subset_1(sK758,u1_struct_0(sK755)) != iProver_top
    | l2_lattices(sK755) != iProver_top
    | v2_struct_0(sK755) = iProver_top ),
    inference(superposition,[status(thm)],[c_117844,c_117883])).

cnf(c_4016,negated_conjecture,
    ( ~ v2_struct_0(sK755) ),
    inference(cnf_transformation,[],[f10400])).

cnf(c_4017,plain,
    ( v2_struct_0(sK755) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4016])).

cnf(c_4014,negated_conjecture,
    ( l2_lattices(sK755) ),
    inference(cnf_transformation,[],[f10402])).

cnf(c_4019,plain,
    ( l2_lattices(sK755) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4014])).

cnf(c_4012,negated_conjecture,
    ( m1_subset_1(sK757,u1_struct_0(sK755)) ),
    inference(cnf_transformation,[],[f10404])).

cnf(c_4021,plain,
    ( m1_subset_1(sK757,u1_struct_0(sK755)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4012])).

cnf(c_4011,negated_conjecture,
    ( m1_subset_1(sK758,u1_struct_0(sK755)) ),
    inference(cnf_transformation,[],[f10405])).

cnf(c_4022,plain,
    ( m1_subset_1(sK758,u1_struct_0(sK755)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4011])).

cnf(c_168405,plain,
    ( k1_lattices(sK755,sK757,sK758) = sK758 ),
    inference(global_propositional_subsumption,[status(thm)],[c_167940,c_4017,c_4019,c_4021,c_4022])).

cnf(c_117842,plain,
    ( m1_subset_1(sK758,u1_struct_0(sK755)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4011])).

cnf(c_4013,negated_conjecture,
    ( m1_subset_1(sK756,u1_struct_0(sK755)) ),
    inference(cnf_transformation,[],[f10403])).

cnf(c_117840,plain,
    ( m1_subset_1(sK756,u1_struct_0(sK755)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4013])).

cnf(c_117841,plain,
    ( m1_subset_1(sK757,u1_struct_0(sK755)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4012])).

cnf(c_3959,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ l2_lattices(X1)
    | ~ v5_lattices(X1)
    | v2_struct_0(X1)
    | k1_lattices(X1,k1_lattices(X1,X0,X3),X2) = k1_lattices(X1,X0,k1_lattices(X1,X3,X2)) ),
    inference(cnf_transformation,[],[f10347])).

cnf(c_117878,plain,
    ( k1_lattices(X0,k1_lattices(X0,X1,X2),X3) = k1_lattices(X0,X1,k1_lattices(X0,X2,X3))
    | m1_subset_1(X1,u1_struct_0(X0)) != iProver_top
    | m1_subset_1(X3,u1_struct_0(X0)) != iProver_top
    | m1_subset_1(X2,u1_struct_0(X0)) != iProver_top
    | l2_lattices(X0) != iProver_top
    | v5_lattices(X0) != iProver_top
    | v2_struct_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3959])).

cnf(c_162401,plain,
    ( k1_lattices(sK755,X0,k1_lattices(sK755,sK757,X1)) = k1_lattices(sK755,k1_lattices(sK755,X0,sK757),X1)
    | m1_subset_1(X0,u1_struct_0(sK755)) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK755)) != iProver_top
    | l2_lattices(sK755) != iProver_top
    | v5_lattices(sK755) != iProver_top
    | v2_struct_0(sK755) = iProver_top ),
    inference(superposition,[status(thm)],[c_117841,c_117878])).

cnf(c_4015,negated_conjecture,
    ( v5_lattices(sK755) ),
    inference(cnf_transformation,[],[f10401])).

cnf(c_4018,plain,
    ( v5_lattices(sK755) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4015])).

cnf(c_164014,plain,
    ( m1_subset_1(X1,u1_struct_0(sK755)) != iProver_top
    | m1_subset_1(X0,u1_struct_0(sK755)) != iProver_top
    | k1_lattices(sK755,X0,k1_lattices(sK755,sK757,X1)) = k1_lattices(sK755,k1_lattices(sK755,X0,sK757),X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_162401,c_4017,c_4018,c_4019])).

cnf(c_164015,plain,
    ( k1_lattices(sK755,X0,k1_lattices(sK755,sK757,X1)) = k1_lattices(sK755,k1_lattices(sK755,X0,sK757),X1)
    | m1_subset_1(X0,u1_struct_0(sK755)) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK755)) != iProver_top ),
    inference(renaming,[status(thm)],[c_164014])).

cnf(c_164027,plain,
    ( k1_lattices(sK755,k1_lattices(sK755,sK756,sK757),X0) = k1_lattices(sK755,sK756,k1_lattices(sK755,sK757,X0))
    | m1_subset_1(X0,u1_struct_0(sK755)) != iProver_top ),
    inference(superposition,[status(thm)],[c_117840,c_164015])).

cnf(c_165431,plain,
    ( k1_lattices(sK755,sK756,k1_lattices(sK755,sK757,sK758)) = k1_lattices(sK755,k1_lattices(sK755,sK756,sK757),sK758) ),
    inference(superposition,[status(thm)],[c_117842,c_164027])).

cnf(c_168408,plain,
    ( k1_lattices(sK755,k1_lattices(sK755,sK756,sK757),sK758) = k1_lattices(sK755,sK756,sK758) ),
    inference(demodulation,[status(thm)],[c_168405,c_165431])).

cnf(c_4010,negated_conjecture,
    ( r1_lattices(sK755,sK756,sK757) ),
    inference(cnf_transformation,[],[f10406])).

cnf(c_117843,plain,
    ( r1_lattices(sK755,sK756,sK757) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4010])).

cnf(c_167941,plain,
    ( k1_lattices(sK755,sK756,sK757) = sK757
    | m1_subset_1(sK757,u1_struct_0(sK755)) != iProver_top
    | m1_subset_1(sK756,u1_struct_0(sK755)) != iProver_top
    | l2_lattices(sK755) != iProver_top
    | v2_struct_0(sK755) = iProver_top ),
    inference(superposition,[status(thm)],[c_117843,c_117883])).

cnf(c_4020,plain,
    ( m1_subset_1(sK756,u1_struct_0(sK755)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4013])).

cnf(c_168490,plain,
    ( k1_lattices(sK755,sK756,sK757) = sK757 ),
    inference(global_propositional_subsumption,[status(thm)],[c_167941,c_4017,c_4019,c_4020,c_4021])).

cnf(c_168785,plain,
    ( k1_lattices(sK755,sK756,sK758) = sK758 ),
    inference(light_normalisation,[status(thm)],[c_168408,c_168405,c_168490])).

cnf(c_3953,plain,
    ( r1_lattices(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ l2_lattices(X0)
    | v2_struct_0(X0)
    | k1_lattices(X0,X1,X2) != X2 ),
    inference(cnf_transformation,[],[f10346])).

cnf(c_117884,plain,
    ( k1_lattices(X0,X1,X2) != X2
    | r1_lattices(X0,X1,X2) = iProver_top
    | m1_subset_1(X2,u1_struct_0(X0)) != iProver_top
    | m1_subset_1(X1,u1_struct_0(X0)) != iProver_top
    | l2_lattices(X0) != iProver_top
    | v2_struct_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3953])).

cnf(c_168906,plain,
    ( r1_lattices(sK755,sK756,sK758) = iProver_top
    | m1_subset_1(sK758,u1_struct_0(sK755)) != iProver_top
    | m1_subset_1(sK756,u1_struct_0(sK755)) != iProver_top
    | l2_lattices(sK755) != iProver_top
    | v2_struct_0(sK755) = iProver_top ),
    inference(superposition,[status(thm)],[c_168785,c_117884])).

cnf(c_4008,negated_conjecture,
    ( ~ r1_lattices(sK755,sK756,sK758) ),
    inference(cnf_transformation,[],[f10408])).

cnf(c_4025,plain,
    ( r1_lattices(sK755,sK756,sK758) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4008])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_168906,c_4025,c_4022,c_4020,c_4019,c_4017])).

%------------------------------------------------------------------------------
