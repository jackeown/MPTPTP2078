%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0418+1.002 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n029.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:43:15 EST 2020

% Result     : Theorem 1.44s
% Output     : CNFRefutation 1.44s
% Verified   : 
% Statistics : Number of formulae       :   70 ( 166 expanded)
%              Number of clauses        :   38 (  58 expanded)
%              Number of leaves         :    8 (  34 expanded)
%              Depth                    :   15
%              Number of atoms          :  268 ( 762 expanded)
%              Number of equality atoms :   64 (  89 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal clause size      :   14 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f5,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X0))
         => ( r2_hidden(k3_subset_1(X0,X2),k7_setfam_1(X0,X1))
          <=> r2_hidden(X2,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f6,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(X0))
           => ( r2_hidden(k3_subset_1(X0,X2),k7_setfam_1(X0,X1))
            <=> r2_hidden(X2,X1) ) ) ) ),
    inference(negated_conjecture,[],[f5])).

fof(f11,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ( r2_hidden(k3_subset_1(X0,X2),k7_setfam_1(X0,X1))
          <~> r2_hidden(X2,X1) )
          & m1_subset_1(X2,k1_zfmisc_1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f17,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(k3_subset_1(X0,X2),k7_setfam_1(X0,X1)) )
          & ( r2_hidden(X2,X1)
            | r2_hidden(k3_subset_1(X0,X2),k7_setfam_1(X0,X1)) )
          & m1_subset_1(X2,k1_zfmisc_1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(nnf_transformation,[],[f11])).

fof(f18,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(k3_subset_1(X0,X2),k7_setfam_1(X0,X1)) )
          & ( r2_hidden(X2,X1)
            | r2_hidden(k3_subset_1(X0,X2),k7_setfam_1(X0,X1)) )
          & m1_subset_1(X2,k1_zfmisc_1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(flattening,[],[f17])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(k3_subset_1(X0,X2),k7_setfam_1(X0,X1)) )
          & ( r2_hidden(X2,X1)
            | r2_hidden(k3_subset_1(X0,X2),k7_setfam_1(X0,X1)) )
          & m1_subset_1(X2,k1_zfmisc_1(X0)) )
     => ( ( ~ r2_hidden(sK3,X1)
          | ~ r2_hidden(k3_subset_1(X0,sK3),k7_setfam_1(X0,X1)) )
        & ( r2_hidden(sK3,X1)
          | r2_hidden(k3_subset_1(X0,sK3),k7_setfam_1(X0,X1)) )
        & m1_subset_1(sK3,k1_zfmisc_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,
    ( ? [X0,X1] :
        ( ? [X2] :
            ( ( ~ r2_hidden(X2,X1)
              | ~ r2_hidden(k3_subset_1(X0,X2),k7_setfam_1(X0,X1)) )
            & ( r2_hidden(X2,X1)
              | r2_hidden(k3_subset_1(X0,X2),k7_setfam_1(X0,X1)) )
            & m1_subset_1(X2,k1_zfmisc_1(X0)) )
        & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) )
   => ( ? [X2] :
          ( ( ~ r2_hidden(X2,sK2)
            | ~ r2_hidden(k3_subset_1(sK1,X2),k7_setfam_1(sK1,sK2)) )
          & ( r2_hidden(X2,sK2)
            | r2_hidden(k3_subset_1(sK1,X2),k7_setfam_1(sK1,sK2)) )
          & m1_subset_1(X2,k1_zfmisc_1(sK1)) )
      & m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK1))) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,
    ( ( ~ r2_hidden(sK3,sK2)
      | ~ r2_hidden(k3_subset_1(sK1,sK3),k7_setfam_1(sK1,sK2)) )
    & ( r2_hidden(sK3,sK2)
      | r2_hidden(k3_subset_1(sK1,sK3),k7_setfam_1(sK1,sK2)) )
    & m1_subset_1(sK3,k1_zfmisc_1(sK1))
    & m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK1))) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f18,f20,f19])).

fof(f32,plain,
    ( r2_hidden(sK3,sK2)
    | r2_hidden(k3_subset_1(sK1,sK3),k7_setfam_1(sK1,sK2)) ),
    inference(cnf_transformation,[],[f21])).

fof(f30,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK1))) ),
    inference(cnf_transformation,[],[f21])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))
         => ( k7_setfam_1(X0,X1) = X2
          <=> ! [X3] :
                ( m1_subset_1(X3,k1_zfmisc_1(X0))
               => ( r2_hidden(X3,X2)
                <=> r2_hidden(k3_subset_1(X0,X3),X1) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f7,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( k7_setfam_1(X0,X1) = X2
          <=> ! [X3] :
                ( ( r2_hidden(X3,X2)
                <=> r2_hidden(k3_subset_1(X0,X3),X1) )
                | ~ m1_subset_1(X3,k1_zfmisc_1(X0)) ) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f12,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( ( k7_setfam_1(X0,X1) = X2
              | ? [X3] :
                  ( ( ~ r2_hidden(k3_subset_1(X0,X3),X1)
                    | ~ r2_hidden(X3,X2) )
                  & ( r2_hidden(k3_subset_1(X0,X3),X1)
                    | r2_hidden(X3,X2) )
                  & m1_subset_1(X3,k1_zfmisc_1(X0)) ) )
            & ( ! [X3] :
                  ( ( ( r2_hidden(X3,X2)
                      | ~ r2_hidden(k3_subset_1(X0,X3),X1) )
                    & ( r2_hidden(k3_subset_1(X0,X3),X1)
                      | ~ r2_hidden(X3,X2) ) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(X0)) )
              | k7_setfam_1(X0,X1) != X2 ) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(nnf_transformation,[],[f7])).

fof(f13,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( ( k7_setfam_1(X0,X1) = X2
              | ? [X3] :
                  ( ( ~ r2_hidden(k3_subset_1(X0,X3),X1)
                    | ~ r2_hidden(X3,X2) )
                  & ( r2_hidden(k3_subset_1(X0,X3),X1)
                    | r2_hidden(X3,X2) )
                  & m1_subset_1(X3,k1_zfmisc_1(X0)) ) )
            & ( ! [X3] :
                  ( ( ( r2_hidden(X3,X2)
                      | ~ r2_hidden(k3_subset_1(X0,X3),X1) )
                    & ( r2_hidden(k3_subset_1(X0,X3),X1)
                      | ~ r2_hidden(X3,X2) ) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(X0)) )
              | k7_setfam_1(X0,X1) != X2 ) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(flattening,[],[f12])).

fof(f14,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( ( k7_setfam_1(X0,X1) = X2
              | ? [X3] :
                  ( ( ~ r2_hidden(k3_subset_1(X0,X3),X1)
                    | ~ r2_hidden(X3,X2) )
                  & ( r2_hidden(k3_subset_1(X0,X3),X1)
                    | r2_hidden(X3,X2) )
                  & m1_subset_1(X3,k1_zfmisc_1(X0)) ) )
            & ( ! [X4] :
                  ( ( ( r2_hidden(X4,X2)
                      | ~ r2_hidden(k3_subset_1(X0,X4),X1) )
                    & ( r2_hidden(k3_subset_1(X0,X4),X1)
                      | ~ r2_hidden(X4,X2) ) )
                  | ~ m1_subset_1(X4,k1_zfmisc_1(X0)) )
              | k7_setfam_1(X0,X1) != X2 ) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(rectify,[],[f13])).

fof(f15,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ~ r2_hidden(k3_subset_1(X0,X3),X1)
            | ~ r2_hidden(X3,X2) )
          & ( r2_hidden(k3_subset_1(X0,X3),X1)
            | r2_hidden(X3,X2) )
          & m1_subset_1(X3,k1_zfmisc_1(X0)) )
     => ( ( ~ r2_hidden(k3_subset_1(X0,sK0(X0,X1,X2)),X1)
          | ~ r2_hidden(sK0(X0,X1,X2),X2) )
        & ( r2_hidden(k3_subset_1(X0,sK0(X0,X1,X2)),X1)
          | r2_hidden(sK0(X0,X1,X2),X2) )
        & m1_subset_1(sK0(X0,X1,X2),k1_zfmisc_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( ( k7_setfam_1(X0,X1) = X2
              | ( ( ~ r2_hidden(k3_subset_1(X0,sK0(X0,X1,X2)),X1)
                  | ~ r2_hidden(sK0(X0,X1,X2),X2) )
                & ( r2_hidden(k3_subset_1(X0,sK0(X0,X1,X2)),X1)
                  | r2_hidden(sK0(X0,X1,X2),X2) )
                & m1_subset_1(sK0(X0,X1,X2),k1_zfmisc_1(X0)) ) )
            & ( ! [X4] :
                  ( ( ( r2_hidden(X4,X2)
                      | ~ r2_hidden(k3_subset_1(X0,X4),X1) )
                    & ( r2_hidden(k3_subset_1(X0,X4),X1)
                      | ~ r2_hidden(X4,X2) ) )
                  | ~ m1_subset_1(X4,k1_zfmisc_1(X0)) )
              | k7_setfam_1(X0,X1) != X2 ) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f14,f15])).

fof(f22,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(k3_subset_1(X0,X4),X1)
      | ~ r2_hidden(X4,X2)
      | ~ m1_subset_1(X4,k1_zfmisc_1(X0))
      | k7_setfam_1(X0,X1) != X2
      | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f35,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(k3_subset_1(X0,X4),X1)
      | ~ r2_hidden(X4,k7_setfam_1(X0,X1))
      | ~ m1_subset_1(X4,k1_zfmisc_1(X0))
      | ~ m1_subset_1(k7_setfam_1(X0,X1),k1_zfmisc_1(k1_zfmisc_1(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(equality_resolution,[],[f22])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => m1_subset_1(k7_setfam_1(X0,X1),k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f9,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k7_setfam_1(X0,X1),k1_zfmisc_1(k1_zfmisc_1(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f28,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k7_setfam_1(X0,X1),k1_zfmisc_1(k1_zfmisc_1(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f31,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(sK1)) ),
    inference(cnf_transformation,[],[f21])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f10,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f29,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f23,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(k3_subset_1(X0,X4),X1)
      | ~ m1_subset_1(X4,k1_zfmisc_1(X0))
      | k7_setfam_1(X0,X1) != X2
      | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f34,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k7_setfam_1(X0,X1))
      | ~ r2_hidden(k3_subset_1(X0,X4),X1)
      | ~ m1_subset_1(X4,k1_zfmisc_1(X0))
      | ~ m1_subset_1(k7_setfam_1(X0,X1),k1_zfmisc_1(k1_zfmisc_1(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(equality_resolution,[],[f23])).

fof(f33,plain,
    ( ~ r2_hidden(sK3,sK2)
    | ~ r2_hidden(k3_subset_1(sK1,sK3),k7_setfam_1(sK1,sK2)) ),
    inference(cnf_transformation,[],[f21])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f8,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f27,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f8])).

cnf(c_9,negated_conjecture,
    ( r2_hidden(k3_subset_1(sK1,sK3),k7_setfam_1(sK1,sK2))
    | r2_hidden(sK3,sK2) ),
    inference(cnf_transformation,[],[f32])).

cnf(c_168,negated_conjecture,
    ( r2_hidden(k3_subset_1(sK1,sK3),k7_setfam_1(sK1,sK2))
    | r2_hidden(sK3,sK2) ),
    inference(subtyping,[status(esa)],[c_9])).

cnf(c_505,plain,
    ( r2_hidden(k3_subset_1(sK1,sK3),k7_setfam_1(sK1,sK2)) = iProver_top
    | r2_hidden(sK3,sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_168])).

cnf(c_11,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK1))) ),
    inference(cnf_transformation,[],[f30])).

cnf(c_166,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK1))) ),
    inference(subtyping,[status(esa)],[c_11])).

cnf(c_507,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_166])).

cnf(c_4,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))
    | ~ m1_subset_1(k7_setfam_1(X1,X2),k1_zfmisc_1(k1_zfmisc_1(X1)))
    | ~ r2_hidden(X0,k7_setfam_1(X1,X2))
    | r2_hidden(k3_subset_1(X1,X0),X2) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_173,plain,
    ( ~ m1_subset_1(X0_37,k1_zfmisc_1(X0_38))
    | ~ m1_subset_1(X1_37,k1_zfmisc_1(k1_zfmisc_1(X0_38)))
    | ~ m1_subset_1(k7_setfam_1(X0_38,X1_37),k1_zfmisc_1(k1_zfmisc_1(X0_38)))
    | ~ r2_hidden(X0_37,k7_setfam_1(X0_38,X1_37))
    | r2_hidden(k3_subset_1(X0_38,X0_37),X1_37) ),
    inference(subtyping,[status(esa)],[c_4])).

cnf(c_500,plain,
    ( m1_subset_1(X0_37,k1_zfmisc_1(X0_38)) != iProver_top
    | m1_subset_1(X1_37,k1_zfmisc_1(k1_zfmisc_1(X0_38))) != iProver_top
    | m1_subset_1(k7_setfam_1(X0_38,X1_37),k1_zfmisc_1(k1_zfmisc_1(X0_38))) != iProver_top
    | r2_hidden(X0_37,k7_setfam_1(X0_38,X1_37)) != iProver_top
    | r2_hidden(k3_subset_1(X0_38,X0_37),X1_37) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_173])).

cnf(c_6,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))
    | m1_subset_1(k7_setfam_1(X1,X0),k1_zfmisc_1(k1_zfmisc_1(X1))) ),
    inference(cnf_transformation,[],[f28])).

cnf(c_171,plain,
    ( ~ m1_subset_1(X0_37,k1_zfmisc_1(k1_zfmisc_1(X0_38)))
    | m1_subset_1(k7_setfam_1(X0_38,X0_37),k1_zfmisc_1(k1_zfmisc_1(X0_38))) ),
    inference(subtyping,[status(esa)],[c_6])).

cnf(c_502,plain,
    ( m1_subset_1(X0_37,k1_zfmisc_1(k1_zfmisc_1(X0_38))) != iProver_top
    | m1_subset_1(k7_setfam_1(X0_38,X0_37),k1_zfmisc_1(k1_zfmisc_1(X0_38))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_171])).

cnf(c_565,plain,
    ( m1_subset_1(X0_37,k1_zfmisc_1(X0_38)) != iProver_top
    | m1_subset_1(X1_37,k1_zfmisc_1(k1_zfmisc_1(X0_38))) != iProver_top
    | r2_hidden(X0_37,k7_setfam_1(X0_38,X1_37)) != iProver_top
    | r2_hidden(k3_subset_1(X0_38,X0_37),X1_37) = iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_500,c_502])).

cnf(c_2421,plain,
    ( m1_subset_1(X0_37,k1_zfmisc_1(sK1)) != iProver_top
    | r2_hidden(X0_37,k7_setfam_1(sK1,sK2)) != iProver_top
    | r2_hidden(k3_subset_1(sK1,X0_37),sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_507,c_565])).

cnf(c_2537,plain,
    ( m1_subset_1(k3_subset_1(sK1,sK3),k1_zfmisc_1(sK1)) != iProver_top
    | r2_hidden(k3_subset_1(sK1,k3_subset_1(sK1,sK3)),sK2) = iProver_top
    | r2_hidden(sK3,sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_505,c_2421])).

cnf(c_10,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(sK1)) ),
    inference(cnf_transformation,[],[f31])).

cnf(c_167,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(sK1)) ),
    inference(subtyping,[status(esa)],[c_10])).

cnf(c_506,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_167])).

cnf(c_7,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k3_subset_1(X1,k3_subset_1(X1,X0)) = X0 ),
    inference(cnf_transformation,[],[f29])).

cnf(c_170,plain,
    ( ~ m1_subset_1(X0_37,k1_zfmisc_1(X0_38))
    | k3_subset_1(X0_38,k3_subset_1(X0_38,X0_37)) = X0_37 ),
    inference(subtyping,[status(esa)],[c_7])).

cnf(c_503,plain,
    ( k3_subset_1(X0_38,k3_subset_1(X0_38,X0_37)) = X0_37
    | m1_subset_1(X0_37,k1_zfmisc_1(X0_38)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_170])).

cnf(c_794,plain,
    ( k3_subset_1(sK1,k3_subset_1(sK1,sK3)) = sK3 ),
    inference(superposition,[status(thm)],[c_506,c_503])).

cnf(c_2579,plain,
    ( m1_subset_1(k3_subset_1(sK1,sK3),k1_zfmisc_1(sK1)) != iProver_top
    | r2_hidden(sK3,sK2) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2537,c_794])).

cnf(c_3,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))
    | ~ m1_subset_1(k7_setfam_1(X1,X2),k1_zfmisc_1(k1_zfmisc_1(X1)))
    | r2_hidden(X0,k7_setfam_1(X1,X2))
    | ~ r2_hidden(k3_subset_1(X1,X0),X2) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_174,plain,
    ( ~ m1_subset_1(X0_37,k1_zfmisc_1(X0_38))
    | ~ m1_subset_1(X1_37,k1_zfmisc_1(k1_zfmisc_1(X0_38)))
    | ~ m1_subset_1(k7_setfam_1(X0_38,X1_37),k1_zfmisc_1(k1_zfmisc_1(X0_38)))
    | r2_hidden(X0_37,k7_setfam_1(X0_38,X1_37))
    | ~ r2_hidden(k3_subset_1(X0_38,X0_37),X1_37) ),
    inference(subtyping,[status(esa)],[c_3])).

cnf(c_499,plain,
    ( m1_subset_1(X0_37,k1_zfmisc_1(X0_38)) != iProver_top
    | m1_subset_1(X1_37,k1_zfmisc_1(k1_zfmisc_1(X0_38))) != iProver_top
    | m1_subset_1(k7_setfam_1(X0_38,X1_37),k1_zfmisc_1(k1_zfmisc_1(X0_38))) != iProver_top
    | r2_hidden(X0_37,k7_setfam_1(X0_38,X1_37)) = iProver_top
    | r2_hidden(k3_subset_1(X0_38,X0_37),X1_37) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_174])).

cnf(c_555,plain,
    ( m1_subset_1(X0_37,k1_zfmisc_1(X0_38)) != iProver_top
    | m1_subset_1(X1_37,k1_zfmisc_1(k1_zfmisc_1(X0_38))) != iProver_top
    | r2_hidden(X0_37,k7_setfam_1(X0_38,X1_37)) = iProver_top
    | r2_hidden(k3_subset_1(X0_38,X0_37),X1_37) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_499,c_502])).

cnf(c_1673,plain,
    ( m1_subset_1(X0_37,k1_zfmisc_1(sK1)) != iProver_top
    | r2_hidden(X0_37,k7_setfam_1(sK1,sK2)) = iProver_top
    | r2_hidden(k3_subset_1(sK1,X0_37),sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_507,c_555])).

cnf(c_1864,plain,
    ( m1_subset_1(k3_subset_1(sK1,sK3),k1_zfmisc_1(sK1)) != iProver_top
    | r2_hidden(k3_subset_1(sK1,sK3),k7_setfam_1(sK1,sK2)) = iProver_top
    | r2_hidden(sK3,sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_794,c_1673])).

cnf(c_13,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_8,negated_conjecture,
    ( ~ r2_hidden(k3_subset_1(sK1,sK3),k7_setfam_1(sK1,sK2))
    | ~ r2_hidden(sK3,sK2) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_15,plain,
    ( r2_hidden(k3_subset_1(sK1,sK3),k7_setfam_1(sK1,sK2)) != iProver_top
    | r2_hidden(sK3,sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_5,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | m1_subset_1(k3_subset_1(X1,X0),k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f27])).

cnf(c_172,plain,
    ( ~ m1_subset_1(X0_37,k1_zfmisc_1(X0_38))
    | m1_subset_1(k3_subset_1(X0_38,X0_37),k1_zfmisc_1(X0_38)) ),
    inference(subtyping,[status(esa)],[c_5])).

cnf(c_610,plain,
    ( m1_subset_1(k3_subset_1(sK1,sK3),k1_zfmisc_1(sK1))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(sK1)) ),
    inference(instantiation,[status(thm)],[c_172])).

cnf(c_611,plain,
    ( m1_subset_1(k3_subset_1(sK1,sK3),k1_zfmisc_1(sK1)) = iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(sK1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_610])).

cnf(c_2102,plain,
    ( r2_hidden(sK3,sK2) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1864,c_13,c_15,c_611])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_2579,c_2102,c_611,c_13])).


%------------------------------------------------------------------------------
