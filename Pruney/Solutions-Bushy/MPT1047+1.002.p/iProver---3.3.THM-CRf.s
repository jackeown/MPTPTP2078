%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT1047+1.002 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n029.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:44:45 EST 2020

% Result     : Theorem 23.57s
% Output     : CNFRefutation 23.57s
% Verified   : 
% Statistics : Number of formulae       :  124 ( 238 expanded)
%              Number of clauses        :   60 (  70 expanded)
%              Number of leaves         :   19 (  61 expanded)
%              Depth                    :   14
%              Number of atoms          :  635 (1339 expanded)
%              Number of equality atoms :  156 ( 293 expanded)
%              Maximal formula depth    :   16 (   7 average)
%              Maximal clause size      :   26 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => ! [X3] :
          ( r2_hidden(X3,k5_partfun1(X0,X1,X2))
         => ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
            & v1_funct_2(X3,X0,X1)
            & v1_funct_1(X3) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
            & v1_funct_2(X3,X0,X1)
            & v1_funct_1(X3) )
          | ~ r2_hidden(X3,k5_partfun1(X0,X1,X2)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
            & v1_funct_2(X3,X0,X1)
            & v1_funct_1(X3) )
          | ~ r2_hidden(X3,k5_partfun1(X0,X1,X2)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f26])).

fof(f83,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r2_hidden(X3,k5_partfun1(X0,X1,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f82,plain,(
    ! [X2,X0,X3,X1] :
      ( v1_funct_2(X3,X0,X1)
      | ~ r2_hidden(X3,k5_partfun1(X0,X1,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f21,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f20])).

fof(f50,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( r2_relset_1(X0,X1,X2,X3)
          | X2 != X3 )
        & ( X2 = X3
          | ~ r2_relset_1(X0,X1,X2,X3) ) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(nnf_transformation,[],[f21])).

fof(f77,plain,(
    ! [X2,X0,X3,X1] :
      ( X2 = X3
      | ~ r2_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
        & v1_funct_2(X2,X0,k1_tarski(X1))
        & v1_funct_1(X2) )
     => ! [X3] :
          ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
            & v1_funct_2(X3,X0,k1_tarski(X1))
            & v1_funct_1(X3) )
         => r2_relset_1(X0,k1_tarski(X1),X2,X3) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( r2_relset_1(X0,k1_tarski(X1),X2,X3)
          | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
          | ~ v1_funct_2(X3,X0,k1_tarski(X1))
          | ~ v1_funct_1(X3) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
      | ~ v1_funct_2(X2,X0,k1_tarski(X1))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( r2_relset_1(X0,k1_tarski(X1),X2,X3)
          | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
          | ~ v1_funct_2(X3,X0,k1_tarski(X1))
          | ~ v1_funct_1(X3) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
      | ~ v1_funct_2(X2,X0,k1_tarski(X1))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f31])).

fof(f86,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_relset_1(X0,k1_tarski(X1),X2,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
      | ~ v1_funct_2(X3,X0,k1_tarski(X1))
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
      | ~ v1_funct_2(X2,X0,k1_tarski(X1))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f13,conjecture,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
        & v1_funct_1(X2) )
     => ! [X3] :
          ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
            & v1_funct_2(X3,X0,k1_tarski(X1))
            & v1_funct_1(X3) )
         => k1_tarski(X3) = k5_partfun1(X0,k1_tarski(X1),X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f14,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
          & v1_funct_1(X2) )
       => ! [X3] :
            ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
              & v1_funct_2(X3,X0,k1_tarski(X1))
              & v1_funct_1(X3) )
           => k1_tarski(X3) = k5_partfun1(X0,k1_tarski(X1),X2) ) ) ),
    inference(negated_conjecture,[],[f13])).

fof(f33,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( k1_tarski(X3) != k5_partfun1(X0,k1_tarski(X1),X2)
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
          & v1_funct_2(X3,X0,k1_tarski(X1))
          & v1_funct_1(X3) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f34,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( k1_tarski(X3) != k5_partfun1(X0,k1_tarski(X1),X2)
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
          & v1_funct_2(X3,X0,k1_tarski(X1))
          & v1_funct_1(X3) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f33])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( ? [X3] :
          ( k1_tarski(X3) != k5_partfun1(X0,k1_tarski(X1),X2)
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
          & v1_funct_2(X3,X0,k1_tarski(X1))
          & v1_funct_1(X3) )
     => ( k1_tarski(sK9) != k5_partfun1(X0,k1_tarski(X1),X2)
        & m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
        & v1_funct_2(sK9,X0,k1_tarski(X1))
        & v1_funct_1(sK9) ) ) ),
    introduced(choice_axiom,[])).

fof(f51,plain,
    ( ? [X0,X1,X2] :
        ( ? [X3] :
            ( k1_tarski(X3) != k5_partfun1(X0,k1_tarski(X1),X2)
            & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
            & v1_funct_2(X3,X0,k1_tarski(X1))
            & v1_funct_1(X3) )
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
        & v1_funct_1(X2) )
   => ( ? [X3] :
          ( k1_tarski(X3) != k5_partfun1(sK6,k1_tarski(sK7),sK8)
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK6,k1_tarski(sK7))))
          & v1_funct_2(X3,sK6,k1_tarski(sK7))
          & v1_funct_1(X3) )
      & m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK6,k1_tarski(sK7))))
      & v1_funct_1(sK8) ) ),
    introduced(choice_axiom,[])).

fof(f53,plain,
    ( k1_tarski(sK9) != k5_partfun1(sK6,k1_tarski(sK7),sK8)
    & m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(sK6,k1_tarski(sK7))))
    & v1_funct_2(sK9,sK6,k1_tarski(sK7))
    & v1_funct_1(sK9)
    & m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK6,k1_tarski(sK7))))
    & v1_funct_1(sK8) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7,sK8,sK9])],[f34,f52,f51])).

fof(f88,plain,(
    m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK6,k1_tarski(sK7)))) ),
    inference(cnf_transformation,[],[f53])).

fof(f36,plain,(
    ! [X1,X0,X2] :
      ( ! [X3] :
          ( k5_partfun1(X0,X1,X2) = X3
        <=> sP0(X2,X0,X1,X3) )
      | ~ sP1(X1,X0,X2) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f42,plain,(
    ! [X1,X0,X2] :
      ( ! [X3] :
          ( ( k5_partfun1(X0,X1,X2) = X3
            | ~ sP0(X2,X0,X1,X3) )
          & ( sP0(X2,X0,X1,X3)
            | k5_partfun1(X0,X1,X2) != X3 ) )
      | ~ sP1(X1,X0,X2) ) ),
    inference(nnf_transformation,[],[f36])).

fof(f43,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( ( k5_partfun1(X1,X0,X2) = X3
            | ~ sP0(X2,X1,X0,X3) )
          & ( sP0(X2,X1,X0,X3)
            | k5_partfun1(X1,X0,X2) != X3 ) )
      | ~ sP1(X0,X1,X2) ) ),
    inference(rectify,[],[f42])).

fof(f61,plain,(
    ! [X2,X0,X3,X1] :
      ( sP0(X2,X1,X0,X3)
      | k5_partfun1(X1,X0,X2) != X3
      | ~ sP1(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f96,plain,(
    ! [X2,X0,X1] :
      ( sP0(X2,X1,X0,k5_partfun1(X1,X0,X2))
      | ~ sP1(X0,X1,X2) ) ),
    inference(equality_resolution,[],[f61])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => ! [X3] :
          ( k5_partfun1(X0,X1,X2) = X3
        <=> ! [X4] :
              ( r2_hidden(X4,X3)
            <=> ? [X5] :
                  ( r1_partfun1(X2,X5)
                  & v1_partfun1(X5,X0)
                  & X4 = X5
                  & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
                  & v1_funct_1(X5) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( k5_partfun1(X0,X1,X2) = X3
        <=> ! [X4] :
              ( r2_hidden(X4,X3)
            <=> ? [X5] :
                  ( r1_partfun1(X2,X5)
                  & v1_partfun1(X5,X0)
                  & X4 = X5
                  & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
                  & v1_funct_1(X5) ) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( k5_partfun1(X0,X1,X2) = X3
        <=> ! [X4] :
              ( r2_hidden(X4,X3)
            <=> ? [X5] :
                  ( r1_partfun1(X2,X5)
                  & v1_partfun1(X5,X0)
                  & X4 = X5
                  & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
                  & v1_funct_1(X5) ) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f18])).

fof(f35,plain,(
    ! [X2,X0,X1,X3] :
      ( sP0(X2,X0,X1,X3)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ? [X5] :
              ( r1_partfun1(X2,X5)
              & v1_partfun1(X5,X0)
              & X4 = X5
              & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
              & v1_funct_1(X5) ) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( sP1(X1,X0,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(definition_folding,[],[f19,f36,f35])).

fof(f75,plain,(
    ! [X2,X0,X1] :
      ( sP1(X1,X0,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f91,plain,(
    m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(sK6,k1_tarski(sK7)))) ),
    inference(cnf_transformation,[],[f53])).

fof(f44,plain,(
    ! [X2,X0,X1,X3] :
      ( ( sP0(X2,X0,X1,X3)
        | ? [X4] :
            ( ( ! [X5] :
                  ( ~ r1_partfun1(X2,X5)
                  | ~ v1_partfun1(X5,X0)
                  | X4 != X5
                  | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
                  | ~ v1_funct_1(X5) )
              | ~ r2_hidden(X4,X3) )
            & ( ? [X5] :
                  ( r1_partfun1(X2,X5)
                  & v1_partfun1(X5,X0)
                  & X4 = X5
                  & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
                  & v1_funct_1(X5) )
              | r2_hidden(X4,X3) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X3)
              | ! [X5] :
                  ( ~ r1_partfun1(X2,X5)
                  | ~ v1_partfun1(X5,X0)
                  | X4 != X5
                  | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
                  | ~ v1_funct_1(X5) ) )
            & ( ? [X5] :
                  ( r1_partfun1(X2,X5)
                  & v1_partfun1(X5,X0)
                  & X4 = X5
                  & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
                  & v1_funct_1(X5) )
              | ~ r2_hidden(X4,X3) ) )
        | ~ sP0(X2,X0,X1,X3) ) ) ),
    inference(nnf_transformation,[],[f35])).

fof(f45,plain,(
    ! [X0,X1,X2,X3] :
      ( ( sP0(X0,X1,X2,X3)
        | ? [X4] :
            ( ( ! [X5] :
                  ( ~ r1_partfun1(X0,X5)
                  | ~ v1_partfun1(X5,X1)
                  | X4 != X5
                  | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
                  | ~ v1_funct_1(X5) )
              | ~ r2_hidden(X4,X3) )
            & ( ? [X6] :
                  ( r1_partfun1(X0,X6)
                  & v1_partfun1(X6,X1)
                  & X4 = X6
                  & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
                  & v1_funct_1(X6) )
              | r2_hidden(X4,X3) ) ) )
      & ( ! [X7] :
            ( ( r2_hidden(X7,X3)
              | ! [X8] :
                  ( ~ r1_partfun1(X0,X8)
                  | ~ v1_partfun1(X8,X1)
                  | X7 != X8
                  | ~ m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
                  | ~ v1_funct_1(X8) ) )
            & ( ? [X9] :
                  ( r1_partfun1(X0,X9)
                  & v1_partfun1(X9,X1)
                  & X7 = X9
                  & m1_subset_1(X9,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
                  & v1_funct_1(X9) )
              | ~ r2_hidden(X7,X3) ) )
        | ~ sP0(X0,X1,X2,X3) ) ) ),
    inference(rectify,[],[f44])).

fof(f48,plain,(
    ! [X7,X2,X1,X0] :
      ( ? [X9] :
          ( r1_partfun1(X0,X9)
          & v1_partfun1(X9,X1)
          & X7 = X9
          & m1_subset_1(X9,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
          & v1_funct_1(X9) )
     => ( r1_partfun1(X0,sK5(X0,X1,X2,X7))
        & v1_partfun1(sK5(X0,X1,X2,X7),X1)
        & sK5(X0,X1,X2,X7) = X7
        & m1_subset_1(sK5(X0,X1,X2,X7),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        & v1_funct_1(sK5(X0,X1,X2,X7)) ) ) ),
    introduced(choice_axiom,[])).

fof(f47,plain,(
    ! [X4,X3,X2,X1,X0] :
      ( ? [X6] :
          ( r1_partfun1(X0,X6)
          & v1_partfun1(X6,X1)
          & X4 = X6
          & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
          & v1_funct_1(X6) )
     => ( r1_partfun1(X0,sK4(X0,X1,X2,X3))
        & v1_partfun1(sK4(X0,X1,X2,X3),X1)
        & sK4(X0,X1,X2,X3) = X4
        & m1_subset_1(sK4(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        & v1_funct_1(sK4(X0,X1,X2,X3)) ) ) ),
    introduced(choice_axiom,[])).

fof(f46,plain,(
    ! [X3,X2,X1,X0] :
      ( ? [X4] :
          ( ( ! [X5] :
                ( ~ r1_partfun1(X0,X5)
                | ~ v1_partfun1(X5,X1)
                | X4 != X5
                | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
                | ~ v1_funct_1(X5) )
            | ~ r2_hidden(X4,X3) )
          & ( ? [X6] :
                ( r1_partfun1(X0,X6)
                & v1_partfun1(X6,X1)
                & X4 = X6
                & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
                & v1_funct_1(X6) )
            | r2_hidden(X4,X3) ) )
     => ( ( ! [X5] :
              ( ~ r1_partfun1(X0,X5)
              | ~ v1_partfun1(X5,X1)
              | sK3(X0,X1,X2,X3) != X5
              | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
              | ~ v1_funct_1(X5) )
          | ~ r2_hidden(sK3(X0,X1,X2,X3),X3) )
        & ( ? [X6] :
              ( r1_partfun1(X0,X6)
              & v1_partfun1(X6,X1)
              & sK3(X0,X1,X2,X3) = X6
              & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
              & v1_funct_1(X6) )
          | r2_hidden(sK3(X0,X1,X2,X3),X3) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f49,plain,(
    ! [X0,X1,X2,X3] :
      ( ( sP0(X0,X1,X2,X3)
        | ( ( ! [X5] :
                ( ~ r1_partfun1(X0,X5)
                | ~ v1_partfun1(X5,X1)
                | sK3(X0,X1,X2,X3) != X5
                | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
                | ~ v1_funct_1(X5) )
            | ~ r2_hidden(sK3(X0,X1,X2,X3),X3) )
          & ( ( r1_partfun1(X0,sK4(X0,X1,X2,X3))
              & v1_partfun1(sK4(X0,X1,X2,X3),X1)
              & sK3(X0,X1,X2,X3) = sK4(X0,X1,X2,X3)
              & m1_subset_1(sK4(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
              & v1_funct_1(sK4(X0,X1,X2,X3)) )
            | r2_hidden(sK3(X0,X1,X2,X3),X3) ) ) )
      & ( ! [X7] :
            ( ( r2_hidden(X7,X3)
              | ! [X8] :
                  ( ~ r1_partfun1(X0,X8)
                  | ~ v1_partfun1(X8,X1)
                  | X7 != X8
                  | ~ m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
                  | ~ v1_funct_1(X8) ) )
            & ( ( r1_partfun1(X0,sK5(X0,X1,X2,X7))
                & v1_partfun1(sK5(X0,X1,X2,X7),X1)
                & sK5(X0,X1,X2,X7) = X7
                & m1_subset_1(sK5(X0,X1,X2,X7),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
                & v1_funct_1(sK5(X0,X1,X2,X7)) )
              | ~ r2_hidden(X7,X3) ) )
        | ~ sP0(X0,X1,X2,X3) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5])],[f45,f48,f47,f46])).

fof(f68,plain,(
    ! [X2,X0,X8,X7,X3,X1] :
      ( r2_hidden(X7,X3)
      | ~ r1_partfun1(X0,X8)
      | ~ v1_partfun1(X8,X1)
      | X7 != X8
      | ~ m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ v1_funct_1(X8)
      | ~ sP0(X0,X1,X2,X3) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f98,plain,(
    ! [X2,X0,X8,X3,X1] :
      ( r2_hidden(X8,X3)
      | ~ r1_partfun1(X0,X8)
      | ~ v1_partfun1(X8,X1)
      | ~ m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ v1_funct_1(X8)
      | ~ sP0(X0,X1,X2,X3) ) ),
    inference(equality_resolution,[],[f68])).

fof(f89,plain,(
    v1_funct_1(sK9) ),
    inference(cnf_transformation,[],[f53])).

fof(f90,plain,(
    v1_funct_2(sK9,sK6,k1_tarski(sK7)) ),
    inference(cnf_transformation,[],[f53])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
         => ( ( v1_funct_2(X2,X0,X1)
              & v1_funct_1(X2) )
           => ( v1_partfun1(X2,X0)
              & v1_funct_1(X2) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( v1_partfun1(X2,X0)
            & v1_funct_1(X2) )
          | ~ v1_funct_2(X2,X0,X1)
          | ~ v1_funct_1(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | v1_xboole_0(X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f17,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( v1_partfun1(X2,X0)
            & v1_funct_1(X2) )
          | ~ v1_funct_2(X2,X0,X1)
          | ~ v1_funct_1(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | v1_xboole_0(X1) ) ),
    inference(flattening,[],[f16])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( v1_partfun1(X2,X0)
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f5,axiom,(
    ! [X0] : ~ v1_xboole_0(k1_tarski(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f76,plain,(
    ! [X0] : ~ v1_xboole_0(k1_tarski(X0)) ),
    inference(cnf_transformation,[],[f5])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
        & v1_funct_1(X2) )
     => ! [X3] :
          ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
            & v1_funct_1(X3) )
         => r1_partfun1(X2,X3) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( r1_partfun1(X2,X3)
          | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
          | ~ v1_funct_1(X3) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( r1_partfun1(X2,X3)
          | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
          | ~ v1_funct_1(X3) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f24])).

fof(f80,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_partfun1(X2,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f81,plain,(
    ! [X2,X0,X3,X1] :
      ( v1_funct_1(X3)
      | ~ r2_hidden(X3,k5_partfun1(X0,X1,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ? [X2] :
            ( ( X0 != X2
              | ~ r2_hidden(X2,X1) )
            & ( X0 = X2
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | X0 != X2 )
            & ( X0 = X2
              | ~ r2_hidden(X2,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ? [X2] :
            ( ( X0 != X2
              | ~ r2_hidden(X2,X1) )
            & ( X0 = X2
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(rectify,[],[f38])).

fof(f40,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( X0 != X2
            | ~ r2_hidden(X2,X1) )
          & ( X0 = X2
            | r2_hidden(X2,X1) ) )
     => ( ( sK2(X0,X1) != X0
          | ~ r2_hidden(sK2(X0,X1),X1) )
        & ( sK2(X0,X1) = X0
          | r2_hidden(sK2(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ( ( sK2(X0,X1) != X0
            | ~ r2_hidden(sK2(X0,X1),X1) )
          & ( sK2(X0,X1) = X0
            | r2_hidden(sK2(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f39,f40])).

fof(f59,plain,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
      | sK2(X0,X1) = X0
      | r2_hidden(sK2(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f60,plain,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
      | sK2(X0,X1) != X0
      | ~ r2_hidden(sK2(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f92,plain,(
    k1_tarski(sK9) != k5_partfun1(sK6,k1_tarski(sK7),sK8) ),
    inference(cnf_transformation,[],[f53])).

fof(f87,plain,(
    v1_funct_1(sK8) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_27,plain,
    ( ~ r2_hidden(X0,k5_partfun1(X1,X2,X3))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X3) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_17692,plain,
    ( ~ r2_hidden(X0,k5_partfun1(sK6,k1_tarski(sK7),X1))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK6,k1_tarski(sK7))))
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK6,k1_tarski(sK7))))
    | ~ v1_funct_1(X1) ),
    inference(instantiation,[status(thm)],[c_27])).

cnf(c_36482,plain,
    ( ~ r2_hidden(X0,k5_partfun1(sK6,k1_tarski(sK7),sK8))
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK6,k1_tarski(sK7))))
    | ~ m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK6,k1_tarski(sK7))))
    | ~ v1_funct_1(sK8) ),
    inference(instantiation,[status(thm)],[c_17692])).

cnf(c_55432,plain,
    ( ~ r2_hidden(sK2(sK9,k5_partfun1(sK6,k1_tarski(sK7),sK8)),k5_partfun1(sK6,k1_tarski(sK7),sK8))
    | m1_subset_1(sK2(sK9,k5_partfun1(sK6,k1_tarski(sK7),sK8)),k1_zfmisc_1(k2_zfmisc_1(sK6,k1_tarski(sK7))))
    | ~ m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK6,k1_tarski(sK7))))
    | ~ v1_funct_1(sK8) ),
    inference(instantiation,[status(thm)],[c_36482])).

cnf(c_8119,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_8810,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(sK2(sK9,k5_partfun1(sK6,k1_tarski(sK7),sK8)),k5_partfun1(sK6,k1_tarski(sK7),sK8))
    | k5_partfun1(sK6,k1_tarski(sK7),sK8) != X1
    | sK2(sK9,k5_partfun1(sK6,k1_tarski(sK7),sK8)) != X0 ),
    inference(instantiation,[status(thm)],[c_8119])).

cnf(c_8926,plain,
    ( ~ r2_hidden(X0,k5_partfun1(sK6,k1_tarski(sK7),sK8))
    | r2_hidden(sK2(sK9,k5_partfun1(sK6,k1_tarski(sK7),sK8)),k5_partfun1(sK6,k1_tarski(sK7),sK8))
    | k5_partfun1(sK6,k1_tarski(sK7),sK8) != k5_partfun1(sK6,k1_tarski(sK7),sK8)
    | sK2(sK9,k5_partfun1(sK6,k1_tarski(sK7),sK8)) != X0 ),
    inference(instantiation,[status(thm)],[c_8810])).

cnf(c_17911,plain,
    ( r2_hidden(sK2(sK9,k5_partfun1(sK6,k1_tarski(sK7),sK8)),k5_partfun1(sK6,k1_tarski(sK7),sK8))
    | ~ r2_hidden(sK9,k5_partfun1(sK6,k1_tarski(sK7),sK8))
    | k5_partfun1(sK6,k1_tarski(sK7),sK8) != k5_partfun1(sK6,k1_tarski(sK7),sK8)
    | sK2(sK9,k5_partfun1(sK6,k1_tarski(sK7),sK8)) != sK9 ),
    inference(instantiation,[status(thm)],[c_8926])).

cnf(c_28,plain,
    ( v1_funct_2(X0,X1,X2)
    | ~ r2_hidden(X0,k5_partfun1(X1,X2,X3))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X3) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_16510,plain,
    ( v1_funct_2(sK2(sK9,k5_partfun1(sK6,k1_tarski(sK7),sK8)),sK6,k1_tarski(sK7))
    | ~ r2_hidden(sK2(sK9,k5_partfun1(sK6,k1_tarski(sK7),sK8)),k5_partfun1(sK6,k1_tarski(sK7),X0))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK6,k1_tarski(sK7))))
    | ~ v1_funct_1(X0) ),
    inference(instantiation,[status(thm)],[c_28])).

cnf(c_17689,plain,
    ( v1_funct_2(sK2(sK9,k5_partfun1(sK6,k1_tarski(sK7),sK8)),sK6,k1_tarski(sK7))
    | ~ r2_hidden(sK2(sK9,k5_partfun1(sK6,k1_tarski(sK7),sK8)),k5_partfun1(sK6,k1_tarski(sK7),sK8))
    | ~ m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK6,k1_tarski(sK7))))
    | ~ v1_funct_1(sK8) ),
    inference(instantiation,[status(thm)],[c_16510])).

cnf(c_24,plain,
    ( ~ r2_relset_1(X0,X1,X2,X3)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | X3 = X2 ),
    inference(cnf_transformation,[],[f77])).

cnf(c_32,plain,
    ( r2_relset_1(X0,k1_tarski(X1),X2,X3)
    | ~ v1_funct_2(X3,X0,k1_tarski(X1))
    | ~ v1_funct_2(X2,X0,k1_tarski(X1))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
    | ~ v1_funct_1(X2)
    | ~ v1_funct_1(X3) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_497,plain,
    ( ~ v1_funct_2(X0,X1,k1_tarski(X2))
    | ~ v1_funct_2(X3,X1,k1_tarski(X2))
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X5,X6)))
    | ~ m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(X5,X6)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k1_tarski(X2))))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,k1_tarski(X2))))
    | ~ v1_funct_1(X3)
    | ~ v1_funct_1(X0)
    | X1 != X5
    | X3 != X4
    | X0 != X7
    | X7 = X4
    | k1_tarski(X2) != X6 ),
    inference(resolution_lifted,[status(thm)],[c_24,c_32])).

cnf(c_498,plain,
    ( ~ v1_funct_2(X0,X1,k1_tarski(X2))
    | ~ v1_funct_2(X3,X1,k1_tarski(X2))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k1_tarski(X2))))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,k1_tarski(X2))))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3)
    | X3 = X0 ),
    inference(unflattening,[status(thm)],[c_497])).

cnf(c_8752,plain,
    ( ~ v1_funct_2(sK2(sK9,k5_partfun1(sK6,k1_tarski(sK7),sK8)),X0,k1_tarski(X1))
    | ~ v1_funct_2(sK9,X0,k1_tarski(X1))
    | ~ m1_subset_1(sK2(sK9,k5_partfun1(sK6,k1_tarski(sK7),sK8)),k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
    | ~ m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
    | ~ v1_funct_1(sK2(sK9,k5_partfun1(sK6,k1_tarski(sK7),sK8)))
    | ~ v1_funct_1(sK9)
    | sK2(sK9,k5_partfun1(sK6,k1_tarski(sK7),sK8)) = sK9 ),
    inference(instantiation,[status(thm)],[c_498])).

cnf(c_13005,plain,
    ( ~ v1_funct_2(sK2(sK9,k5_partfun1(sK6,k1_tarski(sK7),sK8)),sK6,k1_tarski(sK7))
    | ~ v1_funct_2(sK9,sK6,k1_tarski(sK7))
    | ~ m1_subset_1(sK2(sK9,k5_partfun1(sK6,k1_tarski(sK7),sK8)),k1_zfmisc_1(k2_zfmisc_1(sK6,k1_tarski(sK7))))
    | ~ m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(sK6,k1_tarski(sK7))))
    | ~ v1_funct_1(sK2(sK9,k5_partfun1(sK6,k1_tarski(sK7),sK8)))
    | ~ v1_funct_1(sK9)
    | sK2(sK9,k5_partfun1(sK6,k1_tarski(sK7),sK8)) = sK9 ),
    inference(instantiation,[status(thm)],[c_8752])).

cnf(c_37,negated_conjecture,
    ( m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK6,k1_tarski(sK7)))) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_8668,plain,
    ( m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK6,k1_tarski(sK7)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_37])).

cnf(c_8,plain,
    ( sP0(X0,X1,X2,k5_partfun1(X1,X2,X0))
    | ~ sP1(X2,X1,X0) ),
    inference(cnf_transformation,[],[f96])).

cnf(c_21,plain,
    ( sP1(X0,X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
    | ~ v1_funct_1(X2) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_453,plain,
    ( sP0(X0,X1,X2,k5_partfun1(X1,X2,X0))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
    | ~ v1_funct_1(X3)
    | X5 != X2
    | X4 != X1
    | X3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_8,c_21])).

cnf(c_454,plain,
    ( sP0(X0,X1,X2,k5_partfun1(X1,X2,X0))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0) ),
    inference(unflattening,[status(thm)],[c_453])).

cnf(c_8664,plain,
    ( sP0(X0,X1,X2,k5_partfun1(X1,X2,X0)) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_454])).

cnf(c_34,negated_conjecture,
    ( m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(sK6,k1_tarski(sK7)))) ),
    inference(cnf_transformation,[],[f91])).

cnf(c_8671,plain,
    ( m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(sK6,k1_tarski(sK7)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_34])).

cnf(c_15,plain,
    ( ~ sP0(X0,X1,X2,X3)
    | ~ r1_partfun1(X0,X4)
    | r2_hidden(X4,X3)
    | ~ v1_partfun1(X4,X1)
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X4) ),
    inference(cnf_transformation,[],[f98])).

cnf(c_8683,plain,
    ( sP0(X0,X1,X2,X3) != iProver_top
    | r1_partfun1(X0,X4) != iProver_top
    | r2_hidden(X4,X3) = iProver_top
    | v1_partfun1(X4,X1) != iProver_top
    | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | v1_funct_1(X4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_11732,plain,
    ( sP0(X0,sK6,k1_tarski(sK7),X1) != iProver_top
    | r1_partfun1(X0,sK9) != iProver_top
    | r2_hidden(sK9,X1) = iProver_top
    | v1_partfun1(sK9,sK6) != iProver_top
    | v1_funct_1(sK9) != iProver_top ),
    inference(superposition,[status(thm)],[c_8671,c_8683])).

cnf(c_36,negated_conjecture,
    ( v1_funct_1(sK9) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_41,plain,
    ( v1_funct_1(sK9) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_36])).

cnf(c_35,negated_conjecture,
    ( v1_funct_2(sK9,sK6,k1_tarski(sK7)) ),
    inference(cnf_transformation,[],[f90])).

cnf(c_42,plain,
    ( v1_funct_2(sK9,sK6,k1_tarski(sK7)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_35])).

cnf(c_1,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | v1_partfun1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_xboole_0(X2)
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_22,plain,
    ( ~ v1_xboole_0(k1_tarski(X0)) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_417,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | v1_partfun1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | k1_tarski(X3) != X2 ),
    inference(resolution_lifted,[status(thm)],[c_1,c_22])).

cnf(c_418,plain,
    ( ~ v1_funct_2(X0,X1,k1_tarski(X2))
    | v1_partfun1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k1_tarski(X2))))
    | ~ v1_funct_1(X0) ),
    inference(unflattening,[status(thm)],[c_417])).

cnf(c_8666,plain,
    ( v1_funct_2(X0,X1,k1_tarski(X2)) != iProver_top
    | v1_partfun1(X0,X1) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k1_tarski(X2)))) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_418])).

cnf(c_10531,plain,
    ( v1_funct_2(sK9,sK6,k1_tarski(sK7)) != iProver_top
    | v1_partfun1(sK9,sK6) = iProver_top
    | v1_funct_1(sK9) != iProver_top ),
    inference(superposition,[status(thm)],[c_8671,c_8666])).

cnf(c_12432,plain,
    ( sP0(X0,sK6,k1_tarski(sK7),X1) != iProver_top
    | r1_partfun1(X0,sK9) != iProver_top
    | r2_hidden(sK9,X1) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_11732,c_41,c_42,c_10531])).

cnf(c_12438,plain,
    ( r1_partfun1(X0,sK9) != iProver_top
    | r2_hidden(sK9,k5_partfun1(sK6,k1_tarski(sK7),X0)) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK6,k1_tarski(sK7)))) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_8664,c_12432])).

cnf(c_26,plain,
    ( r1_partfun1(X0,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,k1_tarski(X3))))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,k1_tarski(X3))))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X1) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_8676,plain,
    ( r1_partfun1(X0,X1) = iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,k1_tarski(X3)))) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,k1_tarski(X3)))) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_11536,plain,
    ( r1_partfun1(X0,sK9) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK6,k1_tarski(sK7)))) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(sK9) != iProver_top ),
    inference(superposition,[status(thm)],[c_8671,c_8676])).

cnf(c_12874,plain,
    ( r2_hidden(sK9,k5_partfun1(sK6,k1_tarski(sK7),X0)) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK6,k1_tarski(sK7)))) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_12438,c_41,c_11536])).

cnf(c_12882,plain,
    ( r2_hidden(sK9,k5_partfun1(sK6,k1_tarski(sK7),sK8)) = iProver_top
    | v1_funct_1(sK8) != iProver_top ),
    inference(superposition,[status(thm)],[c_8668,c_12874])).

cnf(c_12891,plain,
    ( r2_hidden(sK9,k5_partfun1(sK6,k1_tarski(sK7),sK8))
    | ~ v1_funct_1(sK8) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_12882])).

cnf(c_29,plain,
    ( ~ r2_hidden(X0,k5_partfun1(X1,X2,X3))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X3)
    | v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_9276,plain,
    ( ~ r2_hidden(X0,k5_partfun1(X1,X2,sK8))
    | ~ m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_funct_1(X0)
    | ~ v1_funct_1(sK8) ),
    inference(instantiation,[status(thm)],[c_29])).

cnf(c_9489,plain,
    ( ~ r2_hidden(X0,k5_partfun1(sK6,k1_tarski(sK7),sK8))
    | ~ m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK6,k1_tarski(sK7))))
    | v1_funct_1(X0)
    | ~ v1_funct_1(sK8) ),
    inference(instantiation,[status(thm)],[c_9276])).

cnf(c_10375,plain,
    ( ~ r2_hidden(sK2(sK9,k5_partfun1(sK6,k1_tarski(sK7),sK8)),k5_partfun1(sK6,k1_tarski(sK7),sK8))
    | ~ m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK6,k1_tarski(sK7))))
    | v1_funct_1(sK2(sK9,k5_partfun1(sK6,k1_tarski(sK7),sK8)))
    | ~ v1_funct_1(sK8) ),
    inference(instantiation,[status(thm)],[c_9489])).

cnf(c_8110,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_9239,plain,
    ( k5_partfun1(sK6,k1_tarski(sK7),sK8) = k5_partfun1(sK6,k1_tarski(sK7),sK8) ),
    inference(instantiation,[status(thm)],[c_8110])).

cnf(c_4,plain,
    ( r2_hidden(sK2(X0,X1),X1)
    | sK2(X0,X1) = X0
    | k1_tarski(X0) = X1 ),
    inference(cnf_transformation,[],[f59])).

cnf(c_8746,plain,
    ( r2_hidden(sK2(sK9,k5_partfun1(sK6,k1_tarski(sK7),sK8)),k5_partfun1(sK6,k1_tarski(sK7),sK8))
    | sK2(sK9,k5_partfun1(sK6,k1_tarski(sK7),sK8)) = sK9
    | k1_tarski(sK9) = k5_partfun1(sK6,k1_tarski(sK7),sK8) ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_3,plain,
    ( ~ r2_hidden(sK2(X0,X1),X1)
    | sK2(X0,X1) != X0
    | k1_tarski(X0) = X1 ),
    inference(cnf_transformation,[],[f60])).

cnf(c_8733,plain,
    ( ~ r2_hidden(sK2(sK9,k5_partfun1(sK6,k1_tarski(sK7),sK8)),k5_partfun1(sK6,k1_tarski(sK7),sK8))
    | sK2(sK9,k5_partfun1(sK6,k1_tarski(sK7),sK8)) != sK9
    | k1_tarski(sK9) = k5_partfun1(sK6,k1_tarski(sK7),sK8) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_33,negated_conjecture,
    ( k1_tarski(sK9) != k5_partfun1(sK6,k1_tarski(sK7),sK8) ),
    inference(cnf_transformation,[],[f92])).

cnf(c_38,negated_conjecture,
    ( v1_funct_1(sK8) ),
    inference(cnf_transformation,[],[f87])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_55432,c_17911,c_17689,c_13005,c_12891,c_10375,c_9239,c_8746,c_8733,c_33,c_34,c_35,c_36,c_37,c_38])).


%------------------------------------------------------------------------------
