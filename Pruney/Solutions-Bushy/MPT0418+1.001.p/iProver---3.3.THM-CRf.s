%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0418+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n031.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:43:15 EST 2020

% Result     : Theorem 1.23s
% Output     : CNFRefutation 1.23s
% Verified   : 
% Statistics : Number of formulae       :   64 ( 153 expanded)
%              Number of clauses        :   35 (  54 expanded)
%              Number of leaves         :    7 (  31 expanded)
%              Depth                    :   16
%              Number of atoms          :  264 ( 712 expanded)
%              Number of equality atoms :   71 (  97 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal clause size      :   14 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f4,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X0))
         => ( r2_hidden(k3_subset_1(X0,X2),k7_setfam_1(X0,X1))
          <=> r2_hidden(X2,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f5,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(X0))
           => ( r2_hidden(k3_subset_1(X0,X2),k7_setfam_1(X0,X1))
            <=> r2_hidden(X2,X1) ) ) ) ),
    inference(negated_conjecture,[],[f4])).

fof(f9,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ( r2_hidden(k3_subset_1(X0,X2),k7_setfam_1(X0,X1))
          <~> r2_hidden(X2,X1) )
          & m1_subset_1(X2,k1_zfmisc_1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f15,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(k3_subset_1(X0,X2),k7_setfam_1(X0,X1)) )
          & ( r2_hidden(X2,X1)
            | r2_hidden(k3_subset_1(X0,X2),k7_setfam_1(X0,X1)) )
          & m1_subset_1(X2,k1_zfmisc_1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(nnf_transformation,[],[f9])).

fof(f16,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(k3_subset_1(X0,X2),k7_setfam_1(X0,X1)) )
          & ( r2_hidden(X2,X1)
            | r2_hidden(k3_subset_1(X0,X2),k7_setfam_1(X0,X1)) )
          & m1_subset_1(X2,k1_zfmisc_1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(flattening,[],[f15])).

fof(f18,plain,(
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

fof(f17,plain,
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

fof(f19,plain,
    ( ( ~ r2_hidden(sK3,sK2)
      | ~ r2_hidden(k3_subset_1(sK1,sK3),k7_setfam_1(sK1,sK2)) )
    & ( r2_hidden(sK3,sK2)
      | r2_hidden(k3_subset_1(sK1,sK3),k7_setfam_1(sK1,sK2)) )
    & m1_subset_1(sK3,k1_zfmisc_1(sK1))
    & m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK1))) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f16,f18,f17])).

fof(f27,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK1))) ),
    inference(cnf_transformation,[],[f19])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => k7_setfam_1(X0,k7_setfam_1(X0,X1)) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f8,plain,(
    ! [X0,X1] :
      ( k7_setfam_1(X0,k7_setfam_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f26,plain,(
    ! [X0,X1] :
      ( k7_setfam_1(X0,k7_setfam_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f8])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => m1_subset_1(k7_setfam_1(X0,X1),k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f7,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k7_setfam_1(X0,X1),k1_zfmisc_1(k1_zfmisc_1(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f25,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k7_setfam_1(X0,X1),k1_zfmisc_1(k1_zfmisc_1(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f7])).

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

fof(f6,plain,(
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

fof(f10,plain,(
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
    inference(nnf_transformation,[],[f6])).

fof(f11,plain,(
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
    inference(flattening,[],[f10])).

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
            & ( ! [X4] :
                  ( ( ( r2_hidden(X4,X2)
                      | ~ r2_hidden(k3_subset_1(X0,X4),X1) )
                    & ( r2_hidden(k3_subset_1(X0,X4),X1)
                      | ~ r2_hidden(X4,X2) ) )
                  | ~ m1_subset_1(X4,k1_zfmisc_1(X0)) )
              | k7_setfam_1(X0,X1) != X2 ) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(rectify,[],[f11])).

fof(f13,plain,(
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

fof(f14,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f12,f13])).

fof(f20,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(k3_subset_1(X0,X4),X1)
      | ~ r2_hidden(X4,X2)
      | ~ m1_subset_1(X4,k1_zfmisc_1(X0))
      | k7_setfam_1(X0,X1) != X2
      | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f32,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(k3_subset_1(X0,X4),X1)
      | ~ r2_hidden(X4,k7_setfam_1(X0,X1))
      | ~ m1_subset_1(X4,k1_zfmisc_1(X0))
      | ~ m1_subset_1(k7_setfam_1(X0,X1),k1_zfmisc_1(k1_zfmisc_1(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(equality_resolution,[],[f20])).

fof(f30,plain,
    ( ~ r2_hidden(sK3,sK2)
    | ~ r2_hidden(k3_subset_1(sK1,sK3),k7_setfam_1(sK1,sK2)) ),
    inference(cnf_transformation,[],[f19])).

fof(f29,plain,
    ( r2_hidden(sK3,sK2)
    | r2_hidden(k3_subset_1(sK1,sK3),k7_setfam_1(sK1,sK2)) ),
    inference(cnf_transformation,[],[f19])).

fof(f21,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(k3_subset_1(X0,X4),X1)
      | ~ m1_subset_1(X4,k1_zfmisc_1(X0))
      | k7_setfam_1(X0,X1) != X2
      | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f31,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k7_setfam_1(X0,X1))
      | ~ r2_hidden(k3_subset_1(X0,X4),X1)
      | ~ m1_subset_1(X4,k1_zfmisc_1(X0))
      | ~ m1_subset_1(k7_setfam_1(X0,X1),k1_zfmisc_1(k1_zfmisc_1(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(equality_resolution,[],[f21])).

fof(f28,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(sK1)) ),
    inference(cnf_transformation,[],[f19])).

cnf(c_10,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK1))) ),
    inference(cnf_transformation,[],[f27])).

cnf(c_153,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK1))) ),
    inference(subtyping,[status(esa)],[c_10])).

cnf(c_472,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_153])).

cnf(c_6,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))
    | k7_setfam_1(X1,k7_setfam_1(X1,X0)) = X0 ),
    inference(cnf_transformation,[],[f26])).

cnf(c_157,plain,
    ( ~ m1_subset_1(X0_37,k1_zfmisc_1(k1_zfmisc_1(X0_38)))
    | k7_setfam_1(X0_38,k7_setfam_1(X0_38,X0_37)) = X0_37 ),
    inference(subtyping,[status(esa)],[c_6])).

cnf(c_468,plain,
    ( k7_setfam_1(X0_38,k7_setfam_1(X0_38,X0_37)) = X0_37
    | m1_subset_1(X0_37,k1_zfmisc_1(k1_zfmisc_1(X0_38))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_157])).

cnf(c_787,plain,
    ( k7_setfam_1(sK1,k7_setfam_1(sK1,sK2)) = sK2 ),
    inference(superposition,[status(thm)],[c_472,c_468])).

cnf(c_5,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))
    | m1_subset_1(k7_setfam_1(X1,X0),k1_zfmisc_1(k1_zfmisc_1(X1))) ),
    inference(cnf_transformation,[],[f25])).

cnf(c_158,plain,
    ( ~ m1_subset_1(X0_37,k1_zfmisc_1(k1_zfmisc_1(X0_38)))
    | m1_subset_1(k7_setfam_1(X0_38,X0_37),k1_zfmisc_1(k1_zfmisc_1(X0_38))) ),
    inference(subtyping,[status(esa)],[c_5])).

cnf(c_467,plain,
    ( m1_subset_1(X0_37,k1_zfmisc_1(k1_zfmisc_1(X0_38))) != iProver_top
    | m1_subset_1(k7_setfam_1(X0_38,X0_37),k1_zfmisc_1(k1_zfmisc_1(X0_38))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_158])).

cnf(c_4,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))
    | ~ m1_subset_1(k7_setfam_1(X1,X2),k1_zfmisc_1(k1_zfmisc_1(X1)))
    | ~ r2_hidden(X0,k7_setfam_1(X1,X2))
    | r2_hidden(k3_subset_1(X1,X0),X2) ),
    inference(cnf_transformation,[],[f32])).

cnf(c_159,plain,
    ( ~ m1_subset_1(X0_37,k1_zfmisc_1(X0_38))
    | ~ m1_subset_1(X1_37,k1_zfmisc_1(k1_zfmisc_1(X0_38)))
    | ~ m1_subset_1(k7_setfam_1(X0_38,X1_37),k1_zfmisc_1(k1_zfmisc_1(X0_38)))
    | ~ r2_hidden(X0_37,k7_setfam_1(X0_38,X1_37))
    | r2_hidden(k3_subset_1(X0_38,X0_37),X1_37) ),
    inference(subtyping,[status(esa)],[c_4])).

cnf(c_466,plain,
    ( m1_subset_1(X0_37,k1_zfmisc_1(X0_38)) != iProver_top
    | m1_subset_1(X1_37,k1_zfmisc_1(k1_zfmisc_1(X0_38))) != iProver_top
    | m1_subset_1(k7_setfam_1(X0_38,X1_37),k1_zfmisc_1(k1_zfmisc_1(X0_38))) != iProver_top
    | r2_hidden(X0_37,k7_setfam_1(X0_38,X1_37)) != iProver_top
    | r2_hidden(k3_subset_1(X0_38,X0_37),X1_37) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_159])).

cnf(c_526,plain,
    ( m1_subset_1(X0_37,k1_zfmisc_1(X0_38)) != iProver_top
    | m1_subset_1(X1_37,k1_zfmisc_1(k1_zfmisc_1(X0_38))) != iProver_top
    | r2_hidden(X0_37,k7_setfam_1(X0_38,X1_37)) != iProver_top
    | r2_hidden(k3_subset_1(X0_38,X0_37),X1_37) = iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_466,c_467])).

cnf(c_1304,plain,
    ( m1_subset_1(X0_37,k1_zfmisc_1(X0_38)) != iProver_top
    | m1_subset_1(X1_37,k1_zfmisc_1(k1_zfmisc_1(X0_38))) != iProver_top
    | r2_hidden(X0_37,k7_setfam_1(X0_38,k7_setfam_1(X0_38,X1_37))) != iProver_top
    | r2_hidden(k3_subset_1(X0_38,X0_37),k7_setfam_1(X0_38,X1_37)) = iProver_top ),
    inference(superposition,[status(thm)],[c_467,c_526])).

cnf(c_1799,plain,
    ( m1_subset_1(X0_37,k1_zfmisc_1(sK1)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK1))) != iProver_top
    | r2_hidden(X0_37,sK2) != iProver_top
    | r2_hidden(k3_subset_1(sK1,X0_37),k7_setfam_1(sK1,sK2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_787,c_1304])).

cnf(c_11,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_1904,plain,
    ( m1_subset_1(X0_37,k1_zfmisc_1(sK1)) != iProver_top
    | r2_hidden(X0_37,sK2) != iProver_top
    | r2_hidden(k3_subset_1(sK1,X0_37),k7_setfam_1(sK1,sK2)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1799,c_11])).

cnf(c_7,negated_conjecture,
    ( ~ r2_hidden(k3_subset_1(sK1,sK3),k7_setfam_1(sK1,sK2))
    | ~ r2_hidden(sK3,sK2) ),
    inference(cnf_transformation,[],[f30])).

cnf(c_156,negated_conjecture,
    ( ~ r2_hidden(k3_subset_1(sK1,sK3),k7_setfam_1(sK1,sK2))
    | ~ r2_hidden(sK3,sK2) ),
    inference(subtyping,[status(esa)],[c_7])).

cnf(c_469,plain,
    ( r2_hidden(k3_subset_1(sK1,sK3),k7_setfam_1(sK1,sK2)) != iProver_top
    | r2_hidden(sK3,sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_156])).

cnf(c_1913,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(sK1)) != iProver_top
    | r2_hidden(sK3,sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1904,c_469])).

cnf(c_8,negated_conjecture,
    ( r2_hidden(k3_subset_1(sK1,sK3),k7_setfam_1(sK1,sK2))
    | r2_hidden(sK3,sK2) ),
    inference(cnf_transformation,[],[f29])).

cnf(c_155,negated_conjecture,
    ( r2_hidden(k3_subset_1(sK1,sK3),k7_setfam_1(sK1,sK2))
    | r2_hidden(sK3,sK2) ),
    inference(subtyping,[status(esa)],[c_8])).

cnf(c_470,plain,
    ( r2_hidden(k3_subset_1(sK1,sK3),k7_setfam_1(sK1,sK2)) = iProver_top
    | r2_hidden(sK3,sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_155])).

cnf(c_3,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))
    | ~ m1_subset_1(k7_setfam_1(X1,X2),k1_zfmisc_1(k1_zfmisc_1(X1)))
    | r2_hidden(X0,k7_setfam_1(X1,X2))
    | ~ r2_hidden(k3_subset_1(X1,X0),X2) ),
    inference(cnf_transformation,[],[f31])).

cnf(c_160,plain,
    ( ~ m1_subset_1(X0_37,k1_zfmisc_1(X0_38))
    | ~ m1_subset_1(X1_37,k1_zfmisc_1(k1_zfmisc_1(X0_38)))
    | ~ m1_subset_1(k7_setfam_1(X0_38,X1_37),k1_zfmisc_1(k1_zfmisc_1(X0_38)))
    | r2_hidden(X0_37,k7_setfam_1(X0_38,X1_37))
    | ~ r2_hidden(k3_subset_1(X0_38,X0_37),X1_37) ),
    inference(subtyping,[status(esa)],[c_3])).

cnf(c_465,plain,
    ( m1_subset_1(X0_37,k1_zfmisc_1(X0_38)) != iProver_top
    | m1_subset_1(X1_37,k1_zfmisc_1(k1_zfmisc_1(X0_38))) != iProver_top
    | m1_subset_1(k7_setfam_1(X0_38,X1_37),k1_zfmisc_1(k1_zfmisc_1(X0_38))) != iProver_top
    | r2_hidden(X0_37,k7_setfam_1(X0_38,X1_37)) = iProver_top
    | r2_hidden(k3_subset_1(X0_38,X0_37),X1_37) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_160])).

cnf(c_516,plain,
    ( m1_subset_1(X0_37,k1_zfmisc_1(X0_38)) != iProver_top
    | m1_subset_1(X1_37,k1_zfmisc_1(k1_zfmisc_1(X0_38))) != iProver_top
    | r2_hidden(X0_37,k7_setfam_1(X0_38,X1_37)) = iProver_top
    | r2_hidden(k3_subset_1(X0_38,X0_37),X1_37) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_465,c_467])).

cnf(c_1192,plain,
    ( m1_subset_1(X0_37,k1_zfmisc_1(X0_38)) != iProver_top
    | m1_subset_1(X1_37,k1_zfmisc_1(k1_zfmisc_1(X0_38))) != iProver_top
    | r2_hidden(X0_37,k7_setfam_1(X0_38,k7_setfam_1(X0_38,X1_37))) = iProver_top
    | r2_hidden(k3_subset_1(X0_38,X0_37),k7_setfam_1(X0_38,X1_37)) != iProver_top ),
    inference(superposition,[status(thm)],[c_467,c_516])).

cnf(c_1759,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK1))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(sK1)) != iProver_top
    | r2_hidden(sK3,k7_setfam_1(sK1,k7_setfam_1(sK1,sK2))) = iProver_top
    | r2_hidden(sK3,sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_470,c_1192])).

cnf(c_1785,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK1))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(sK1)) != iProver_top
    | r2_hidden(sK3,sK2) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1759,c_787])).

cnf(c_9,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(sK1)) ),
    inference(cnf_transformation,[],[f28])).

cnf(c_12,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_1913,c_1785,c_12,c_11])).


%------------------------------------------------------------------------------
