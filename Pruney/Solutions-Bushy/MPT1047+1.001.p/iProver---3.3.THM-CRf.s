%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT1047+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n032.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:44:45 EST 2020

% Result     : Theorem 7.93s
% Output     : CNFRefutation 7.93s
% Verified   : 
% Statistics : Number of formulae       :  129 ( 262 expanded)
%              Number of clauses        :   65 (  78 expanded)
%              Number of leaves         :   19 (  67 expanded)
%              Depth                    :   16
%              Number of atoms          :  644 (1453 expanded)
%              Number of equality atoms :  184 ( 340 expanded)
%              Maximal formula depth    :   16 (   6 average)
%              Maximal clause size      :   26 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f8,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f26,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f25])).

fof(f60,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( r2_relset_1(X0,X1,X2,X3)
          | X2 != X3 )
        & ( X2 = X3
          | ~ r2_relset_1(X0,X1,X2,X3) ) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(nnf_transformation,[],[f26])).

fof(f89,plain,(
    ! [X2,X0,X3,X1] :
      ( X2 = X3
      | ~ r2_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f60])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
        & v1_funct_2(X2,X0,k1_tarski(X1))
        & v1_funct_1(X2) )
     => ! [X3] :
          ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
            & v1_funct_2(X3,X0,k1_tarski(X1))
            & v1_funct_1(X3) )
         => r2_relset_1(X0,k1_tarski(X1),X2,X3) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( r2_relset_1(X0,k1_tarski(X1),X2,X3)
          | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
          | ~ v1_funct_2(X3,X0,k1_tarski(X1))
          | ~ v1_funct_1(X3) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
      | ~ v1_funct_2(X2,X0,k1_tarski(X1))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( r2_relset_1(X0,k1_tarski(X1),X2,X3)
          | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
          | ~ v1_funct_2(X3,X0,k1_tarski(X1))
          | ~ v1_funct_1(X3) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
      | ~ v1_funct_2(X2,X0,k1_tarski(X1))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f36])).

fof(f98,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_relset_1(X0,k1_tarski(X1),X2,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
      | ~ v1_funct_2(X3,X0,k1_tarski(X1))
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
      | ~ v1_funct_2(X2,X0,k1_tarski(X1))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => ! [X3] :
          ( r2_hidden(X3,k5_partfun1(X0,X1,X2))
         => ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
            & v1_funct_2(X3,X0,X1)
            & v1_funct_1(X3) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
            & v1_funct_2(X3,X0,X1)
            & v1_funct_1(X3) )
          | ~ r2_hidden(X3,k5_partfun1(X0,X1,X2)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
            & v1_funct_2(X3,X0,X1)
            & v1_funct_1(X3) )
          | ~ r2_hidden(X3,k5_partfun1(X0,X1,X2)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f31])).

fof(f94,plain,(
    ! [X2,X0,X3,X1] :
      ( v1_funct_2(X3,X0,X1)
      | ~ r2_hidden(X3,k5_partfun1(X0,X1,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f95,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r2_hidden(X3,k5_partfun1(X0,X1,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f7,axiom,(
    ! [X0] : ~ v1_xboole_0(k1_tarski(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f88,plain,(
    ! [X0] : ~ v1_xboole_0(k1_tarski(X0)) ),
    inference(cnf_transformation,[],[f7])).

fof(f18,conjecture,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
        & v1_funct_1(X2) )
     => ! [X3] :
          ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
            & v1_funct_2(X3,X0,k1_tarski(X1))
            & v1_funct_1(X3) )
         => k1_tarski(X3) = k5_partfun1(X0,k1_tarski(X1),X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
          & v1_funct_1(X2) )
       => ! [X3] :
            ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
              & v1_funct_2(X3,X0,k1_tarski(X1))
              & v1_funct_1(X3) )
           => k1_tarski(X3) = k5_partfun1(X0,k1_tarski(X1),X2) ) ) ),
    inference(negated_conjecture,[],[f18])).

fof(f41,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( k1_tarski(X3) != k5_partfun1(X0,k1_tarski(X1),X2)
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
          & v1_funct_2(X3,X0,k1_tarski(X1))
          & v1_funct_1(X3) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f42,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( k1_tarski(X3) != k5_partfun1(X0,k1_tarski(X1),X2)
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
          & v1_funct_2(X3,X0,k1_tarski(X1))
          & v1_funct_1(X3) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f41])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( ? [X3] :
          ( k1_tarski(X3) != k5_partfun1(X0,k1_tarski(X1),X2)
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
          & v1_funct_2(X3,X0,k1_tarski(X1))
          & v1_funct_1(X3) )
     => ( k1_tarski(sK10) != k5_partfun1(X0,k1_tarski(X1),X2)
        & m1_subset_1(sK10,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
        & v1_funct_2(sK10,X0,k1_tarski(X1))
        & v1_funct_1(sK10) ) ) ),
    introduced(choice_axiom,[])).

fof(f61,plain,
    ( ? [X0,X1,X2] :
        ( ? [X3] :
            ( k1_tarski(X3) != k5_partfun1(X0,k1_tarski(X1),X2)
            & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
            & v1_funct_2(X3,X0,k1_tarski(X1))
            & v1_funct_1(X3) )
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
        & v1_funct_1(X2) )
   => ( ? [X3] :
          ( k1_tarski(X3) != k5_partfun1(sK7,k1_tarski(sK8),sK9)
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK7,k1_tarski(sK8))))
          & v1_funct_2(X3,sK7,k1_tarski(sK8))
          & v1_funct_1(X3) )
      & m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(sK7,k1_tarski(sK8))))
      & v1_funct_1(sK9) ) ),
    introduced(choice_axiom,[])).

fof(f63,plain,
    ( k1_tarski(sK10) != k5_partfun1(sK7,k1_tarski(sK8),sK9)
    & m1_subset_1(sK10,k1_zfmisc_1(k2_zfmisc_1(sK7,k1_tarski(sK8))))
    & v1_funct_2(sK10,sK7,k1_tarski(sK8))
    & v1_funct_1(sK10)
    & m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(sK7,k1_tarski(sK8))))
    & v1_funct_1(sK9) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7,sK8,sK9,sK10])],[f42,f62,f61])).

fof(f103,plain,(
    m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(sK7,k1_tarski(sK8)))) ),
    inference(cnf_transformation,[],[f63])).

fof(f44,plain,(
    ! [X1,X0,X2] :
      ( ! [X3] :
          ( k5_partfun1(X0,X1,X2) = X3
        <=> sP0(X2,X0,X1,X3) )
      | ~ sP1(X1,X0,X2) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f50,plain,(
    ! [X1,X0,X2] :
      ( ! [X3] :
          ( ( k5_partfun1(X0,X1,X2) = X3
            | ~ sP0(X2,X0,X1,X3) )
          & ( sP0(X2,X0,X1,X3)
            | k5_partfun1(X0,X1,X2) != X3 ) )
      | ~ sP1(X1,X0,X2) ) ),
    inference(nnf_transformation,[],[f44])).

fof(f51,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( ( k5_partfun1(X1,X0,X2) = X3
            | ~ sP0(X2,X1,X0,X3) )
          & ( sP0(X2,X1,X0,X3)
            | k5_partfun1(X1,X0,X2) != X3 ) )
      | ~ sP1(X0,X1,X2) ) ),
    inference(rectify,[],[f50])).

fof(f71,plain,(
    ! [X2,X0,X3,X1] :
      ( sP0(X2,X1,X0,X3)
      | k5_partfun1(X1,X0,X2) != X3
      | ~ sP1(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f111,plain,(
    ! [X2,X0,X1] :
      ( sP0(X2,X1,X0,k5_partfun1(X1,X0,X2))
      | ~ sP1(X0,X1,X2) ) ),
    inference(equality_resolution,[],[f71])).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
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

fof(f24,plain,(
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
    inference(flattening,[],[f23])).

fof(f43,plain,(
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

fof(f45,plain,(
    ! [X0,X1,X2] :
      ( sP1(X1,X0,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(definition_folding,[],[f24,f44,f43])).

fof(f85,plain,(
    ! [X2,X0,X1] :
      ( sP1(X1,X0,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f106,plain,(
    m1_subset_1(sK10,k1_zfmisc_1(k2_zfmisc_1(sK7,k1_tarski(sK8)))) ),
    inference(cnf_transformation,[],[f63])).

fof(f52,plain,(
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
    inference(nnf_transformation,[],[f43])).

fof(f53,plain,(
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
    inference(rectify,[],[f52])).

fof(f56,plain,(
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

fof(f55,plain,(
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

fof(f54,plain,(
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

fof(f57,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5])],[f53,f56,f55,f54])).

fof(f78,plain,(
    ! [X2,X0,X8,X7,X3,X1] :
      ( r2_hidden(X7,X3)
      | ~ r1_partfun1(X0,X8)
      | ~ v1_partfun1(X8,X1)
      | X7 != X8
      | ~ m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ v1_funct_1(X8)
      | ~ sP0(X0,X1,X2,X3) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f113,plain,(
    ! [X2,X0,X8,X3,X1] :
      ( r2_hidden(X8,X3)
      | ~ r1_partfun1(X0,X8)
      | ~ v1_partfun1(X8,X1)
      | ~ m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ v1_funct_1(X8)
      | ~ sP0(X0,X1,X2,X3) ) ),
    inference(equality_resolution,[],[f78])).

fof(f104,plain,(
    v1_funct_1(sK10) ),
    inference(cnf_transformation,[],[f63])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
        & v1_funct_1(X2) )
     => ! [X3] :
          ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
            & v1_funct_1(X3) )
         => r1_partfun1(X2,X3) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( r1_partfun1(X2,X3)
          | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
          | ~ v1_funct_1(X3) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( r1_partfun1(X2,X3)
          | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
          | ~ v1_funct_1(X3) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f29])).

fof(f92,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_partfun1(X2,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f102,plain,(
    v1_funct_1(sK9) ),
    inference(cnf_transformation,[],[f63])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
         => ( ( v1_funct_2(X2,X0,X1)
              & v1_funct_1(X2) )
           => ( v1_partfun1(X2,X0)
              & v1_funct_1(X2) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( v1_partfun1(X2,X0)
            & v1_funct_1(X2) )
          | ~ v1_funct_2(X2,X0,X1)
          | ~ v1_funct_1(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | v1_xboole_0(X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( v1_partfun1(X2,X0)
            & v1_funct_1(X2) )
          | ~ v1_funct_2(X2,X0,X1)
          | ~ v1_funct_1(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | v1_xboole_0(X1) ) ),
    inference(flattening,[],[f21])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( v1_partfun1(X2,X0)
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f105,plain,(
    v1_funct_2(sK10,sK7,k1_tarski(sK8)) ),
    inference(cnf_transformation,[],[f63])).

fof(f93,plain,(
    ! [X2,X0,X3,X1] :
      ( v1_funct_1(X3)
      | ~ r2_hidden(X3,k5_partfun1(X0,X1,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f46,plain,(
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

fof(f47,plain,(
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
    inference(rectify,[],[f46])).

fof(f48,plain,(
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

fof(f49,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f47,f48])).

fof(f69,plain,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
      | sK2(X0,X1) = X0
      | r2_hidden(sK2(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f70,plain,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
      | sK2(X0,X1) != X0
      | ~ r2_hidden(sK2(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f107,plain,(
    k1_tarski(sK10) != k5_partfun1(sK7,k1_tarski(sK8),sK9) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_26,plain,
    ( ~ r2_relset_1(X0,X1,X2,X3)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | X3 = X2 ),
    inference(cnf_transformation,[],[f89])).

cnf(c_34,plain,
    ( r2_relset_1(X0,k1_tarski(X1),X2,X3)
    | ~ v1_funct_2(X3,X0,k1_tarski(X1))
    | ~ v1_funct_2(X2,X0,k1_tarski(X1))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
    | ~ v1_funct_1(X2)
    | ~ v1_funct_1(X3) ),
    inference(cnf_transformation,[],[f98])).

cnf(c_518,plain,
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
    inference(resolution_lifted,[status(thm)],[c_26,c_34])).

cnf(c_519,plain,
    ( ~ v1_funct_2(X0,X1,k1_tarski(X2))
    | ~ v1_funct_2(X3,X1,k1_tarski(X2))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k1_tarski(X2))))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,k1_tarski(X2))))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3)
    | X3 = X0 ),
    inference(unflattening,[status(thm)],[c_518])).

cnf(c_9881,plain,
    ( ~ v1_funct_2(sK2(sK10,k5_partfun1(sK7,k1_tarski(sK8),sK9)),X0,k1_tarski(X1))
    | ~ v1_funct_2(sK10,X0,k1_tarski(X1))
    | ~ m1_subset_1(sK2(sK10,k5_partfun1(sK7,k1_tarski(sK8),sK9)),k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
    | ~ m1_subset_1(sK10,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
    | ~ v1_funct_1(sK2(sK10,k5_partfun1(sK7,k1_tarski(sK8),sK9)))
    | ~ v1_funct_1(sK10)
    | sK2(sK10,k5_partfun1(sK7,k1_tarski(sK8),sK9)) = sK10 ),
    inference(instantiation,[status(thm)],[c_519])).

cnf(c_34281,plain,
    ( ~ v1_funct_2(sK2(sK10,k5_partfun1(sK7,k1_tarski(sK8),sK9)),sK7,k1_tarski(sK8))
    | ~ v1_funct_2(sK10,sK7,k1_tarski(sK8))
    | ~ m1_subset_1(sK2(sK10,k5_partfun1(sK7,k1_tarski(sK8),sK9)),k1_zfmisc_1(k2_zfmisc_1(sK7,k1_tarski(sK8))))
    | ~ m1_subset_1(sK10,k1_zfmisc_1(k2_zfmisc_1(sK7,k1_tarski(sK8))))
    | ~ v1_funct_1(sK2(sK10,k5_partfun1(sK7,k1_tarski(sK8),sK9)))
    | ~ v1_funct_1(sK10)
    | sK2(sK10,k5_partfun1(sK7,k1_tarski(sK8),sK9)) = sK10 ),
    inference(instantiation,[status(thm)],[c_9881])).

cnf(c_30,plain,
    ( v1_funct_2(X0,X1,X2)
    | ~ r2_hidden(X0,k5_partfun1(X1,X2,X3))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X3) ),
    inference(cnf_transformation,[],[f94])).

cnf(c_14035,plain,
    ( v1_funct_2(X0,sK7,k1_tarski(sK8))
    | ~ r2_hidden(X0,k5_partfun1(sK7,k1_tarski(sK8),sK9))
    | ~ m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(sK7,k1_tarski(sK8))))
    | ~ v1_funct_1(sK9) ),
    inference(instantiation,[status(thm)],[c_30])).

cnf(c_25620,plain,
    ( v1_funct_2(sK2(sK10,k5_partfun1(sK7,k1_tarski(sK8),sK9)),sK7,k1_tarski(sK8))
    | ~ r2_hidden(sK2(sK10,k5_partfun1(sK7,k1_tarski(sK8),sK9)),k5_partfun1(sK7,k1_tarski(sK8),sK9))
    | ~ m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(sK7,k1_tarski(sK8))))
    | ~ v1_funct_1(sK9) ),
    inference(instantiation,[status(thm)],[c_14035])).

cnf(c_29,plain,
    ( ~ r2_hidden(X0,k5_partfun1(X1,X2,X3))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X3) ),
    inference(cnf_transformation,[],[f95])).

cnf(c_11139,plain,
    ( ~ r2_hidden(X0,k5_partfun1(sK7,k1_tarski(sK8),sK9))
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK7,k1_tarski(sK8))))
    | ~ m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(sK7,k1_tarski(sK8))))
    | ~ v1_funct_1(sK9) ),
    inference(instantiation,[status(thm)],[c_29])).

cnf(c_23163,plain,
    ( ~ r2_hidden(sK2(sK10,k5_partfun1(sK7,k1_tarski(sK8),sK9)),k5_partfun1(sK7,k1_tarski(sK8),sK9))
    | m1_subset_1(sK2(sK10,k5_partfun1(sK7,k1_tarski(sK8),sK9)),k1_zfmisc_1(k2_zfmisc_1(sK7,k1_tarski(sK8))))
    | ~ m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(sK7,k1_tarski(sK8))))
    | ~ v1_funct_1(sK9) ),
    inference(instantiation,[status(thm)],[c_11139])).

cnf(c_24,plain,
    ( ~ v1_xboole_0(k1_tarski(X0)) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_19670,plain,
    ( ~ v1_xboole_0(k1_tarski(sK8)) ),
    inference(instantiation,[status(thm)],[c_24])).

cnf(c_19671,plain,
    ( v1_xboole_0(k1_tarski(sK8)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19670])).

cnf(c_42,negated_conjecture,
    ( m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(sK7,k1_tarski(sK8)))) ),
    inference(cnf_transformation,[],[f103])).

cnf(c_9776,plain,
    ( m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(sK7,k1_tarski(sK8)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_42])).

cnf(c_8,plain,
    ( sP0(X0,X1,X2,k5_partfun1(X1,X2,X0))
    | ~ sP1(X2,X1,X0) ),
    inference(cnf_transformation,[],[f111])).

cnf(c_21,plain,
    ( sP1(X0,X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
    | ~ v1_funct_1(X2) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_474,plain,
    ( sP0(X0,X1,X2,k5_partfun1(X1,X2,X0))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
    | ~ v1_funct_1(X3)
    | X5 != X2
    | X4 != X1
    | X3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_8,c_21])).

cnf(c_475,plain,
    ( sP0(X0,X1,X2,k5_partfun1(X1,X2,X0))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0) ),
    inference(unflattening,[status(thm)],[c_474])).

cnf(c_9774,plain,
    ( sP0(X0,X1,X2,k5_partfun1(X1,X2,X0)) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_475])).

cnf(c_39,negated_conjecture,
    ( m1_subset_1(sK10,k1_zfmisc_1(k2_zfmisc_1(sK7,k1_tarski(sK8)))) ),
    inference(cnf_transformation,[],[f106])).

cnf(c_9779,plain,
    ( m1_subset_1(sK10,k1_zfmisc_1(k2_zfmisc_1(sK7,k1_tarski(sK8)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_39])).

cnf(c_15,plain,
    ( ~ sP0(X0,X1,X2,X3)
    | ~ r1_partfun1(X0,X4)
    | r2_hidden(X4,X3)
    | ~ v1_partfun1(X4,X1)
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X4) ),
    inference(cnf_transformation,[],[f113])).

cnf(c_9800,plain,
    ( sP0(X0,X1,X2,X3) != iProver_top
    | r1_partfun1(X0,X4) != iProver_top
    | r2_hidden(X4,X3) = iProver_top
    | v1_partfun1(X4,X1) != iProver_top
    | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | v1_funct_1(X4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_13073,plain,
    ( sP0(X0,sK7,k1_tarski(sK8),X1) != iProver_top
    | r1_partfun1(X0,sK10) != iProver_top
    | r2_hidden(sK10,X1) = iProver_top
    | v1_partfun1(sK10,sK7) != iProver_top
    | v1_funct_1(sK10) != iProver_top ),
    inference(superposition,[status(thm)],[c_9779,c_9800])).

cnf(c_41,negated_conjecture,
    ( v1_funct_1(sK10) ),
    inference(cnf_transformation,[],[f104])).

cnf(c_46,plain,
    ( v1_funct_1(sK10) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_41])).

cnf(c_13704,plain,
    ( v1_partfun1(sK10,sK7) != iProver_top
    | r2_hidden(sK10,X1) = iProver_top
    | r1_partfun1(X0,sK10) != iProver_top
    | sP0(X0,sK7,k1_tarski(sK8),X1) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_13073,c_46])).

cnf(c_13705,plain,
    ( sP0(X0,sK7,k1_tarski(sK8),X1) != iProver_top
    | r1_partfun1(X0,sK10) != iProver_top
    | r2_hidden(sK10,X1) = iProver_top
    | v1_partfun1(sK10,sK7) != iProver_top ),
    inference(renaming,[status(thm)],[c_13704])).

cnf(c_13710,plain,
    ( r1_partfun1(X0,sK10) != iProver_top
    | r2_hidden(sK10,k5_partfun1(sK7,k1_tarski(sK8),X0)) = iProver_top
    | v1_partfun1(sK10,sK7) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK7,k1_tarski(sK8)))) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_9774,c_13705])).

cnf(c_28,plain,
    ( r1_partfun1(X0,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,k1_tarski(X3))))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,k1_tarski(X3))))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X1) ),
    inference(cnf_transformation,[],[f92])).

cnf(c_9788,plain,
    ( r1_partfun1(X0,X1) = iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,k1_tarski(X3)))) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,k1_tarski(X3)))) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_12882,plain,
    ( r1_partfun1(X0,sK10) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK7,k1_tarski(sK8)))) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(sK10) != iProver_top ),
    inference(superposition,[status(thm)],[c_9779,c_9788])).

cnf(c_14547,plain,
    ( r2_hidden(sK10,k5_partfun1(sK7,k1_tarski(sK8),X0)) = iProver_top
    | v1_partfun1(sK10,sK7) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK7,k1_tarski(sK8)))) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_13710,c_46,c_12882])).

cnf(c_14556,plain,
    ( r2_hidden(sK10,k5_partfun1(sK7,k1_tarski(sK8),sK9)) = iProver_top
    | v1_partfun1(sK10,sK7) != iProver_top
    | v1_funct_1(sK9) != iProver_top ),
    inference(superposition,[status(thm)],[c_9776,c_14547])).

cnf(c_43,negated_conjecture,
    ( v1_funct_1(sK9) ),
    inference(cnf_transformation,[],[f102])).

cnf(c_44,plain,
    ( v1_funct_1(sK9) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_43])).

cnf(c_14626,plain,
    ( v1_partfun1(sK10,sK7) != iProver_top
    | r2_hidden(sK10,k5_partfun1(sK7,k1_tarski(sK8),sK9)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_14556,c_44])).

cnf(c_14627,plain,
    ( r2_hidden(sK10,k5_partfun1(sK7,k1_tarski(sK8),sK9)) = iProver_top
    | v1_partfun1(sK10,sK7) != iProver_top ),
    inference(renaming,[status(thm)],[c_14626])).

cnf(c_1,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | v1_partfun1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_xboole_0(X2)
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_9811,plain,
    ( v1_funct_2(X0,X1,X2) != iProver_top
    | v1_partfun1(X0,X1) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | v1_xboole_0(X2) = iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_13062,plain,
    ( v1_funct_2(sK10,sK7,k1_tarski(sK8)) != iProver_top
    | v1_partfun1(sK10,sK7) = iProver_top
    | v1_xboole_0(k1_tarski(sK8)) = iProver_top
    | v1_funct_1(sK10) != iProver_top ),
    inference(superposition,[status(thm)],[c_9779,c_9811])).

cnf(c_40,negated_conjecture,
    ( v1_funct_2(sK10,sK7,k1_tarski(sK8)) ),
    inference(cnf_transformation,[],[f105])).

cnf(c_47,plain,
    ( v1_funct_2(sK10,sK7,k1_tarski(sK8)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_40])).

cnf(c_14415,plain,
    ( v1_xboole_0(k1_tarski(sK8)) = iProver_top
    | v1_partfun1(sK10,sK7) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_13062,c_46,c_47])).

cnf(c_14416,plain,
    ( v1_partfun1(sK10,sK7) = iProver_top
    | v1_xboole_0(k1_tarski(sK8)) = iProver_top ),
    inference(renaming,[status(thm)],[c_14415])).

cnf(c_31,plain,
    ( ~ r2_hidden(X0,k5_partfun1(X1,X2,X3))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X3)
    | v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f93])).

cnf(c_10198,plain,
    ( ~ r2_hidden(sK2(sK10,k5_partfun1(sK7,k1_tarski(sK8),sK9)),k5_partfun1(X0,X1,X2))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_funct_1(X2)
    | v1_funct_1(sK2(sK10,k5_partfun1(sK7,k1_tarski(sK8),sK9))) ),
    inference(instantiation,[status(thm)],[c_31])).

cnf(c_10767,plain,
    ( ~ r2_hidden(sK2(sK10,k5_partfun1(sK7,k1_tarski(sK8),sK9)),k5_partfun1(sK7,k1_tarski(sK8),sK9))
    | ~ m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(sK7,k1_tarski(sK8))))
    | v1_funct_1(sK2(sK10,k5_partfun1(sK7,k1_tarski(sK8),sK9)))
    | ~ v1_funct_1(sK9) ),
    inference(instantiation,[status(thm)],[c_10198])).

cnf(c_9107,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_10455,plain,
    ( k5_partfun1(sK7,k1_tarski(sK8),sK9) = k5_partfun1(sK7,k1_tarski(sK8),sK9) ),
    inference(instantiation,[status(thm)],[c_9107])).

cnf(c_9117,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_9952,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(sK2(sK10,k5_partfun1(sK7,k1_tarski(sK8),sK9)),k5_partfun1(sK7,k1_tarski(sK8),sK9))
    | k5_partfun1(sK7,k1_tarski(sK8),sK9) != X1
    | sK2(sK10,k5_partfun1(sK7,k1_tarski(sK8),sK9)) != X0 ),
    inference(instantiation,[status(thm)],[c_9117])).

cnf(c_10089,plain,
    ( ~ r2_hidden(X0,k5_partfun1(sK7,k1_tarski(sK8),sK9))
    | r2_hidden(sK2(sK10,k5_partfun1(sK7,k1_tarski(sK8),sK9)),k5_partfun1(sK7,k1_tarski(sK8),sK9))
    | k5_partfun1(sK7,k1_tarski(sK8),sK9) != k5_partfun1(sK7,k1_tarski(sK8),sK9)
    | sK2(sK10,k5_partfun1(sK7,k1_tarski(sK8),sK9)) != X0 ),
    inference(instantiation,[status(thm)],[c_9952])).

cnf(c_10090,plain,
    ( k5_partfun1(sK7,k1_tarski(sK8),sK9) != k5_partfun1(sK7,k1_tarski(sK8),sK9)
    | sK2(sK10,k5_partfun1(sK7,k1_tarski(sK8),sK9)) != X0
    | r2_hidden(X0,k5_partfun1(sK7,k1_tarski(sK8),sK9)) != iProver_top
    | r2_hidden(sK2(sK10,k5_partfun1(sK7,k1_tarski(sK8),sK9)),k5_partfun1(sK7,k1_tarski(sK8),sK9)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10089])).

cnf(c_10092,plain,
    ( k5_partfun1(sK7,k1_tarski(sK8),sK9) != k5_partfun1(sK7,k1_tarski(sK8),sK9)
    | sK2(sK10,k5_partfun1(sK7,k1_tarski(sK8),sK9)) != sK10
    | r2_hidden(sK2(sK10,k5_partfun1(sK7,k1_tarski(sK8),sK9)),k5_partfun1(sK7,k1_tarski(sK8),sK9)) = iProver_top
    | r2_hidden(sK10,k5_partfun1(sK7,k1_tarski(sK8),sK9)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_10090])).

cnf(c_4,plain,
    ( r2_hidden(sK2(X0,X1),X1)
    | sK2(X0,X1) = X0
    | k1_tarski(X0) = X1 ),
    inference(cnf_transformation,[],[f69])).

cnf(c_9875,plain,
    ( r2_hidden(sK2(sK10,k5_partfun1(sK7,k1_tarski(sK8),sK9)),k5_partfun1(sK7,k1_tarski(sK8),sK9))
    | sK2(sK10,k5_partfun1(sK7,k1_tarski(sK8),sK9)) = sK10
    | k1_tarski(sK10) = k5_partfun1(sK7,k1_tarski(sK8),sK9) ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_3,plain,
    ( ~ r2_hidden(sK2(X0,X1),X1)
    | sK2(X0,X1) != X0
    | k1_tarski(X0) = X1 ),
    inference(cnf_transformation,[],[f70])).

cnf(c_9859,plain,
    ( ~ r2_hidden(sK2(sK10,k5_partfun1(sK7,k1_tarski(sK8),sK9)),k5_partfun1(sK7,k1_tarski(sK8),sK9))
    | sK2(sK10,k5_partfun1(sK7,k1_tarski(sK8),sK9)) != sK10
    | k1_tarski(sK10) = k5_partfun1(sK7,k1_tarski(sK8),sK9) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_9860,plain,
    ( sK2(sK10,k5_partfun1(sK7,k1_tarski(sK8),sK9)) != sK10
    | k1_tarski(sK10) = k5_partfun1(sK7,k1_tarski(sK8),sK9)
    | r2_hidden(sK2(sK10,k5_partfun1(sK7,k1_tarski(sK8),sK9)),k5_partfun1(sK7,k1_tarski(sK8),sK9)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9859])).

cnf(c_38,negated_conjecture,
    ( k1_tarski(sK10) != k5_partfun1(sK7,k1_tarski(sK8),sK9) ),
    inference(cnf_transformation,[],[f107])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_34281,c_25620,c_23163,c_19671,c_14627,c_14416,c_10767,c_10455,c_10092,c_9875,c_9860,c_38,c_39,c_40,c_41,c_42,c_43])).


%------------------------------------------------------------------------------
