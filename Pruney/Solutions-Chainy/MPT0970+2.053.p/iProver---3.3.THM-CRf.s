%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:00:56 EST 2020

% Result     : Theorem 11.53s
% Output     : CNFRefutation 11.53s
% Verified   : 
% Statistics : Number of formulae       :  213 (17617 expanded)
%              Number of clauses        :  145 (5821 expanded)
%              Number of leaves         :   20 (4580 expanded)
%              Depth                    :   35
%              Number of atoms          :  740 (94240 expanded)
%              Number of equality atoms :  381 (33132 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal clause size      :   16 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f6,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( k2_relat_1(X0) = X1
        <=> ! [X2] :
              ( r2_hidden(X2,X1)
            <=> ? [X3] :
                  ( k1_funct_1(X0,X3) = X2
                  & r2_hidden(X3,k1_relat_1(X0)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_relat_1(X0) = X1
        <=> ! [X2] :
              ( r2_hidden(X2,X1)
            <=> ? [X3] :
                  ( k1_funct_1(X0,X3) = X2
                  & r2_hidden(X3,k1_relat_1(X0)) ) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_relat_1(X0) = X1
        <=> ! [X2] :
              ( r2_hidden(X2,X1)
            <=> ? [X3] :
                  ( k1_funct_1(X0,X3) = X2
                  & r2_hidden(X3,k1_relat_1(X0)) ) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f18])).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( k2_relat_1(X0) = X1
            | ? [X2] :
                ( ( ! [X3] :
                      ( k1_funct_1(X0,X3) != X2
                      | ~ r2_hidden(X3,k1_relat_1(X0)) )
                  | ~ r2_hidden(X2,X1) )
                & ( ? [X3] :
                      ( k1_funct_1(X0,X3) = X2
                      & r2_hidden(X3,k1_relat_1(X0)) )
                  | r2_hidden(X2,X1) ) ) )
          & ( ! [X2] :
                ( ( r2_hidden(X2,X1)
                  | ! [X3] :
                      ( k1_funct_1(X0,X3) != X2
                      | ~ r2_hidden(X3,k1_relat_1(X0)) ) )
                & ( ? [X3] :
                      ( k1_funct_1(X0,X3) = X2
                      & r2_hidden(X3,k1_relat_1(X0)) )
                  | ~ r2_hidden(X2,X1) ) )
            | k2_relat_1(X0) != X1 ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f19])).

fof(f34,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( k2_relat_1(X0) = X1
            | ? [X2] :
                ( ( ! [X3] :
                      ( k1_funct_1(X0,X3) != X2
                      | ~ r2_hidden(X3,k1_relat_1(X0)) )
                  | ~ r2_hidden(X2,X1) )
                & ( ? [X4] :
                      ( k1_funct_1(X0,X4) = X2
                      & r2_hidden(X4,k1_relat_1(X0)) )
                  | r2_hidden(X2,X1) ) ) )
          & ( ! [X5] :
                ( ( r2_hidden(X5,X1)
                  | ! [X6] :
                      ( k1_funct_1(X0,X6) != X5
                      | ~ r2_hidden(X6,k1_relat_1(X0)) ) )
                & ( ? [X7] :
                      ( k1_funct_1(X0,X7) = X5
                      & r2_hidden(X7,k1_relat_1(X0)) )
                  | ~ r2_hidden(X5,X1) ) )
            | k2_relat_1(X0) != X1 ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(rectify,[],[f33])).

fof(f37,plain,(
    ! [X5,X0] :
      ( ? [X7] :
          ( k1_funct_1(X0,X7) = X5
          & r2_hidden(X7,k1_relat_1(X0)) )
     => ( k1_funct_1(X0,sK3(X0,X5)) = X5
        & r2_hidden(sK3(X0,X5),k1_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( k1_funct_1(X0,X4) = X2
          & r2_hidden(X4,k1_relat_1(X0)) )
     => ( k1_funct_1(X0,sK2(X0,X1)) = X2
        & r2_hidden(sK2(X0,X1),k1_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ! [X3] :
                ( k1_funct_1(X0,X3) != X2
                | ~ r2_hidden(X3,k1_relat_1(X0)) )
            | ~ r2_hidden(X2,X1) )
          & ( ? [X4] :
                ( k1_funct_1(X0,X4) = X2
                & r2_hidden(X4,k1_relat_1(X0)) )
            | r2_hidden(X2,X1) ) )
     => ( ( ! [X3] :
              ( k1_funct_1(X0,X3) != sK1(X0,X1)
              | ~ r2_hidden(X3,k1_relat_1(X0)) )
          | ~ r2_hidden(sK1(X0,X1),X1) )
        & ( ? [X4] :
              ( k1_funct_1(X0,X4) = sK1(X0,X1)
              & r2_hidden(X4,k1_relat_1(X0)) )
          | r2_hidden(sK1(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f38,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( k2_relat_1(X0) = X1
            | ( ( ! [X3] :
                    ( k1_funct_1(X0,X3) != sK1(X0,X1)
                    | ~ r2_hidden(X3,k1_relat_1(X0)) )
                | ~ r2_hidden(sK1(X0,X1),X1) )
              & ( ( k1_funct_1(X0,sK2(X0,X1)) = sK1(X0,X1)
                  & r2_hidden(sK2(X0,X1),k1_relat_1(X0)) )
                | r2_hidden(sK1(X0,X1),X1) ) ) )
          & ( ! [X5] :
                ( ( r2_hidden(X5,X1)
                  | ! [X6] :
                      ( k1_funct_1(X0,X6) != X5
                      | ~ r2_hidden(X6,k1_relat_1(X0)) ) )
                & ( ( k1_funct_1(X0,sK3(X0,X5)) = X5
                    & r2_hidden(sK3(X0,X5),k1_relat_1(X0)) )
                  | ~ r2_hidden(X5,X1) ) )
            | k2_relat_1(X0) != X1 ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f34,f37,f36,f35])).

fof(f54,plain,(
    ! [X0,X1] :
      ( k2_relat_1(X0) = X1
      | r2_hidden(sK2(X0,X1),k1_relat_1(X0))
      | r2_hidden(sK1(X0,X1),X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f12,conjecture,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( ! [X3] :
            ~ ( ! [X4] :
                  ~ ( k1_funct_1(X2,X4) = X3
                    & r2_hidden(X4,X0) )
              & r2_hidden(X3,X1) )
       => k2_relset_1(X0,X1,X2) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f13,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) )
       => ( ! [X3] :
              ~ ( ! [X4] :
                    ~ ( k1_funct_1(X2,X4) = X3
                      & r2_hidden(X4,X0) )
                & r2_hidden(X3,X1) )
         => k2_relset_1(X0,X1,X2) = X1 ) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f26,plain,(
    ? [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) != X1
      & ! [X3] :
          ( ? [X4] :
              ( k1_funct_1(X2,X4) = X3
              & r2_hidden(X4,X0) )
          | ~ r2_hidden(X3,X1) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f27,plain,(
    ? [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) != X1
      & ! [X3] :
          ( ? [X4] :
              ( k1_funct_1(X2,X4) = X3
              & r2_hidden(X4,X0) )
          | ~ r2_hidden(X3,X1) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f26])).

fof(f41,plain,(
    ! [X2,X0,X3] :
      ( ? [X4] :
          ( k1_funct_1(X2,X4) = X3
          & r2_hidden(X4,X0) )
     => ( k1_funct_1(X2,sK7(X3)) = X3
        & r2_hidden(sK7(X3),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f40,plain,
    ( ? [X0,X1,X2] :
        ( k2_relset_1(X0,X1,X2) != X1
        & ! [X3] :
            ( ? [X4] :
                ( k1_funct_1(X2,X4) = X3
                & r2_hidden(X4,X0) )
            | ~ r2_hidden(X3,X1) )
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
   => ( k2_relset_1(sK4,sK5,sK6) != sK5
      & ! [X3] :
          ( ? [X4] :
              ( k1_funct_1(sK6,X4) = X3
              & r2_hidden(X4,sK4) )
          | ~ r2_hidden(X3,sK5) )
      & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5)))
      & v1_funct_2(sK6,sK4,sK5)
      & v1_funct_1(sK6) ) ),
    introduced(choice_axiom,[])).

fof(f42,plain,
    ( k2_relset_1(sK4,sK5,sK6) != sK5
    & ! [X3] :
        ( ( k1_funct_1(sK6,sK7(X3)) = X3
          & r2_hidden(sK7(X3),sK4) )
        | ~ r2_hidden(X3,sK5) )
    & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5)))
    & v1_funct_2(sK6,sK4,sK5)
    & v1_funct_1(sK6) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6,sK7])],[f27,f41,f40])).

fof(f67,plain,(
    v1_funct_1(sK6) ),
    inference(cnf_transformation,[],[f42])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f47,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f69,plain,(
    m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) ),
    inference(cnf_transformation,[],[f42])).

fof(f5,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f50,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f71,plain,(
    ! [X3] :
      ( k1_funct_1(sK6,sK7(X3)) = X3
      | ~ r2_hidden(X3,sK5) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relat_1(X2) = k2_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f72,plain,(
    k2_relset_1(sK4,sK5,sK6) != sK5 ),
    inference(cnf_transformation,[],[f42])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f15])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f28])).

fof(f30,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK0(X0,X1),X1)
        & r2_hidden(sK0(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK0(X0,X1),X1)
          & r2_hidden(sK0(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f29,f30])).

fof(f43,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v5_relat_1(X2,X1) ) ),
    inference(pure_predicate_removal,[],[f8])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( ( v5_relat_1(X1,X0)
          | ~ r1_tarski(k2_relat_1(X1),X0) )
        & ( r1_tarski(k2_relat_1(X1),X0)
          | ~ v5_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f17])).

fof(f48,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(X1),X0)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f70,plain,(
    ! [X3] :
      ( r2_hidden(sK7(X3),sK4)
      | ~ r2_hidden(X3,sK5) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f55,plain,(
    ! [X0,X1] :
      ( k2_relat_1(X0) = X1
      | k1_funct_1(X0,sK2(X0,X1)) = sK1(X0,X1)
      | r2_hidden(sK1(X0,X1),X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f53,plain,(
    ! [X6,X0,X5,X1] :
      ( r2_hidden(X5,X1)
      | k1_funct_1(X0,X6) != X5
      | ~ r2_hidden(X6,k1_relat_1(X0))
      | k2_relat_1(X0) != X1
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f73,plain,(
    ! [X6,X0,X1] :
      ( r2_hidden(k1_funct_1(X0,X6),X1)
      | ~ r2_hidden(X6,k1_relat_1(X0))
      | k2_relat_1(X0) != X1
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f53])).

fof(f74,plain,(
    ! [X6,X0] :
      ( r2_hidden(k1_funct_1(X0,X6),k2_relat_1(X0))
      | ~ r2_hidden(X6,k1_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f73])).

fof(f7,axiom,(
    ! [X0,X1] :
      ~ ( r1_tarski(X1,X0)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f57,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f56,plain,(
    ! [X0,X3,X1] :
      ( k2_relat_1(X0) = X1
      | k1_funct_1(X0,X3) != sK1(X0,X1)
      | ~ r2_hidden(X3,k1_relat_1(X0))
      | ~ r2_hidden(sK1(X0,X1),X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f2,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f46,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f68,plain,(
    v1_funct_2(sK6,sK4,sK5) ),
    inference(cnf_transformation,[],[f42])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( ( k1_xboole_0 = X1
         => ( ( v1_funct_2(X2,X0,X1)
            <=> k1_xboole_0 = X2 )
            | k1_xboole_0 = X0 ) )
        & ( ( k1_xboole_0 = X1
           => k1_xboole_0 = X0 )
         => ( v1_funct_2(X2,X0,X1)
          <=> k1_relset_1(X0,X1,X2) = X0 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( ( ( ( v1_funct_2(X2,X0,X1)
          <=> k1_xboole_0 = X2 )
          | k1_xboole_0 = X0
          | k1_xboole_0 != X1 )
        & ( ( v1_funct_2(X2,X0,X1)
          <=> k1_relset_1(X0,X1,X2) = X0 )
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 ) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( ( ( ( v1_funct_2(X2,X0,X1)
          <=> k1_xboole_0 = X2 )
          | k1_xboole_0 = X0
          | k1_xboole_0 != X1 )
        & ( ( v1_funct_2(X2,X0,X1)
          <=> k1_relset_1(X0,X1,X2) = X0 )
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 ) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f24])).

fof(f39,plain,(
    ! [X0,X1,X2] :
      ( ( ( ( ( v1_funct_2(X2,X0,X1)
              | k1_xboole_0 != X2 )
            & ( k1_xboole_0 = X2
              | ~ v1_funct_2(X2,X0,X1) ) )
          | k1_xboole_0 = X0
          | k1_xboole_0 != X1 )
        & ( ( ( v1_funct_2(X2,X0,X1)
              | k1_relset_1(X0,X1,X2) != X0 )
            & ( k1_relset_1(X0,X1,X2) = X0
              | ~ v1_funct_2(X2,X0,X1) ) )
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 ) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(nnf_transformation,[],[f25])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f51,plain,(
    ! [X0,X5,X1] :
      ( r2_hidden(sK3(X0,X5),k1_relat_1(X0))
      | ~ r2_hidden(X5,X1)
      | k2_relat_1(X0) != X1
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f76,plain,(
    ! [X0,X5] :
      ( r2_hidden(sK3(X0,X5),k1_relat_1(X0))
      | ~ r2_hidden(X5,k2_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f51])).

fof(f52,plain,(
    ! [X0,X5,X1] :
      ( k1_funct_1(X0,sK3(X0,X5)) = X5
      | ~ r2_hidden(X5,X1)
      | k2_relat_1(X0) != X1
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f75,plain,(
    ! [X0,X5] :
      ( k1_funct_1(X0,sK3(X0,X5)) = X5
      | ~ r2_hidden(X5,k2_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f52])).

cnf(c_10,plain,
    ( r2_hidden(sK2(X0,X1),k1_relat_1(X0))
    | r2_hidden(sK1(X0,X1),X1)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k2_relat_1(X0) = X1 ),
    inference(cnf_transformation,[],[f54])).

cnf(c_29,negated_conjecture,
    ( v1_funct_1(sK6) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_766,plain,
    ( r2_hidden(sK2(X0,X1),k1_relat_1(X0))
    | r2_hidden(sK1(X0,X1),X1)
    | ~ v1_relat_1(X0)
    | k2_relat_1(X0) = X1
    | sK6 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_10,c_29])).

cnf(c_767,plain,
    ( r2_hidden(sK2(sK6,X0),k1_relat_1(sK6))
    | r2_hidden(sK1(sK6,X0),X0)
    | ~ v1_relat_1(sK6)
    | k2_relat_1(sK6) = X0 ),
    inference(unflattening,[status(thm)],[c_766])).

cnf(c_1491,plain,
    ( k2_relat_1(sK6) = X0
    | r2_hidden(sK2(sK6,X0),k1_relat_1(sK6)) = iProver_top
    | r2_hidden(sK1(sK6,X0),X0) = iProver_top
    | v1_relat_1(sK6) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_767])).

cnf(c_768,plain,
    ( k2_relat_1(sK6) = X0
    | r2_hidden(sK2(sK6,X0),k1_relat_1(sK6)) = iProver_top
    | r2_hidden(sK1(sK6,X0),X0) = iProver_top
    | v1_relat_1(sK6) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_767])).

cnf(c_1183,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_1660,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(sK4,sK5)) = k1_zfmisc_1(k2_zfmisc_1(sK4,sK5)) ),
    inference(instantiation,[status(thm)],[c_1183])).

cnf(c_4,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_27,negated_conjecture,
    ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_467,plain,
    ( ~ v1_relat_1(X0)
    | v1_relat_1(X1)
    | k1_zfmisc_1(k2_zfmisc_1(sK4,sK5)) != k1_zfmisc_1(X0)
    | sK6 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_4,c_27])).

cnf(c_468,plain,
    ( ~ v1_relat_1(X0)
    | v1_relat_1(sK6)
    | k1_zfmisc_1(k2_zfmisc_1(sK4,sK5)) != k1_zfmisc_1(X0) ),
    inference(unflattening,[status(thm)],[c_467])).

cnf(c_1655,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(X0,X1))
    | v1_relat_1(sK6)
    | k1_zfmisc_1(k2_zfmisc_1(sK4,sK5)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1)) ),
    inference(instantiation,[status(thm)],[c_468])).

cnf(c_1710,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(sK4,sK5))
    | v1_relat_1(sK6)
    | k1_zfmisc_1(k2_zfmisc_1(sK4,sK5)) != k1_zfmisc_1(k2_zfmisc_1(sK4,sK5)) ),
    inference(instantiation,[status(thm)],[c_1655])).

cnf(c_1711,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(sK4,sK5)) != k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))
    | v1_relat_1(k2_zfmisc_1(sK4,sK5)) != iProver_top
    | v1_relat_1(sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1710])).

cnf(c_7,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_1751,plain,
    ( v1_relat_1(k2_zfmisc_1(sK4,sK5)) ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_1752,plain,
    ( v1_relat_1(k2_zfmisc_1(sK4,sK5)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1751])).

cnf(c_2692,plain,
    ( r2_hidden(sK1(sK6,X0),X0) = iProver_top
    | r2_hidden(sK2(sK6,X0),k1_relat_1(sK6)) = iProver_top
    | k2_relat_1(sK6) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1491,c_768,c_1660,c_1711,c_1752])).

cnf(c_2693,plain,
    ( k2_relat_1(sK6) = X0
    | r2_hidden(sK2(sK6,X0),k1_relat_1(sK6)) = iProver_top
    | r2_hidden(sK1(sK6,X0),X0) = iProver_top ),
    inference(renaming,[status(thm)],[c_2692])).

cnf(c_25,negated_conjecture,
    ( ~ r2_hidden(X0,sK5)
    | k1_funct_1(sK6,sK7(X0)) = X0 ),
    inference(cnf_transformation,[],[f71])).

cnf(c_1495,plain,
    ( k1_funct_1(sK6,sK7(X0)) = X0
    | r2_hidden(X0,sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_2704,plain,
    ( k1_funct_1(sK6,sK7(sK1(sK6,sK5))) = sK1(sK6,sK5)
    | k2_relat_1(sK6) = sK5
    | r2_hidden(sK2(sK6,sK5),k1_relat_1(sK6)) = iProver_top ),
    inference(superposition,[status(thm)],[c_2693,c_1495])).

cnf(c_17,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_533,plain,
    ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
    | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))
    | sK6 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_17,c_27])).

cnf(c_534,plain,
    ( k2_relset_1(X0,X1,sK6) = k2_relat_1(sK6)
    | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK4,sK5)) ),
    inference(unflattening,[status(thm)],[c_533])).

cnf(c_1673,plain,
    ( k2_relset_1(sK4,sK5,sK6) = k2_relat_1(sK6) ),
    inference(equality_resolution,[status(thm)],[c_534])).

cnf(c_24,negated_conjecture,
    ( k2_relset_1(sK4,sK5,sK6) != sK5 ),
    inference(cnf_transformation,[],[f72])).

cnf(c_1697,plain,
    ( k2_relat_1(sK6) != sK5 ),
    inference(demodulation,[status(thm)],[c_1673,c_24])).

cnf(c_2763,plain,
    ( k1_funct_1(sK6,sK7(sK1(sK6,sK5))) = sK1(sK6,sK5)
    | r2_hidden(sK2(sK6,sK5),k1_relat_1(sK6)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2704,c_1697])).

cnf(c_2,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,X2)
    | ~ r1_tarski(X1,X2) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_1499,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,X2) = iProver_top
    | r1_tarski(X1,X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_2769,plain,
    ( k1_funct_1(sK6,sK7(sK1(sK6,sK5))) = sK1(sK6,sK5)
    | r2_hidden(sK2(sK6,sK5),X0) = iProver_top
    | r1_tarski(k1_relat_1(sK6),X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_2763,c_1499])).

cnf(c_8870,plain,
    ( k1_funct_1(sK6,sK7(sK1(sK6,sK5))) = sK1(sK6,sK5)
    | r2_hidden(sK2(sK6,sK5),X0) = iProver_top
    | r1_tarski(X1,X0) != iProver_top
    | r1_tarski(k1_relat_1(sK6),X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_2769,c_1499])).

cnf(c_15,plain,
    ( v5_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_6,plain,
    ( ~ v5_relat_1(X0,X1)
    | r1_tarski(k2_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_328,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | r1_tarski(k2_relat_1(X0),X2)
    | ~ v1_relat_1(X0) ),
    inference(resolution,[status(thm)],[c_15,c_6])).

cnf(c_482,plain,
    ( r1_tarski(k2_relat_1(X0),X1)
    | ~ v1_relat_1(X0)
    | k1_zfmisc_1(k2_zfmisc_1(X2,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))
    | sK6 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_328,c_27])).

cnf(c_483,plain,
    ( r1_tarski(k2_relat_1(sK6),X0)
    | ~ v1_relat_1(sK6)
    | k1_zfmisc_1(k2_zfmisc_1(X1,X0)) != k1_zfmisc_1(k2_zfmisc_1(sK4,sK5)) ),
    inference(unflattening,[status(thm)],[c_482])).

cnf(c_1833,plain,
    ( r1_tarski(k2_relat_1(sK6),sK5)
    | ~ v1_relat_1(sK6)
    | k1_zfmisc_1(k2_zfmisc_1(sK4,sK5)) != k1_zfmisc_1(k2_zfmisc_1(sK4,sK5)) ),
    inference(instantiation,[status(thm)],[c_483])).

cnf(c_2000,plain,
    ( ~ r2_hidden(sK1(sK6,sK5),sK5)
    | k1_funct_1(sK6,sK7(sK1(sK6,sK5))) = sK1(sK6,sK5) ),
    inference(instantiation,[status(thm)],[c_25])).

cnf(c_26,negated_conjecture,
    ( ~ r2_hidden(X0,sK5)
    | r2_hidden(sK7(X0),sK4) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_1494,plain,
    ( r2_hidden(X0,sK5) != iProver_top
    | r2_hidden(sK7(X0),sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_2371,plain,
    ( r2_hidden(X0,sK5) != iProver_top
    | r2_hidden(sK7(X0),X1) = iProver_top
    | r1_tarski(sK4,X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1494,c_1499])).

cnf(c_9,plain,
    ( r2_hidden(sK1(X0,X1),X1)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k1_funct_1(X0,sK2(X0,X1)) = sK1(X0,X1)
    | k2_relat_1(X0) = X1 ),
    inference(cnf_transformation,[],[f55])).

cnf(c_784,plain,
    ( r2_hidden(sK1(X0,X1),X1)
    | ~ v1_relat_1(X0)
    | k1_funct_1(X0,sK2(X0,X1)) = sK1(X0,X1)
    | k2_relat_1(X0) = X1
    | sK6 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_9,c_29])).

cnf(c_785,plain,
    ( r2_hidden(sK1(sK6,X0),X0)
    | ~ v1_relat_1(sK6)
    | k1_funct_1(sK6,sK2(sK6,X0)) = sK1(sK6,X0)
    | k2_relat_1(sK6) = X0 ),
    inference(unflattening,[status(thm)],[c_784])).

cnf(c_1490,plain,
    ( k1_funct_1(sK6,sK2(sK6,X0)) = sK1(sK6,X0)
    | k2_relat_1(sK6) = X0
    | r2_hidden(sK1(sK6,X0),X0) = iProver_top
    | v1_relat_1(sK6) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_785])).

cnf(c_786,plain,
    ( k1_funct_1(sK6,sK2(sK6,X0)) = sK1(sK6,X0)
    | k2_relat_1(sK6) = X0
    | r2_hidden(sK1(sK6,X0),X0) = iProver_top
    | v1_relat_1(sK6) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_785])).

cnf(c_2137,plain,
    ( r2_hidden(sK1(sK6,X0),X0) = iProver_top
    | k2_relat_1(sK6) = X0
    | k1_funct_1(sK6,sK2(sK6,X0)) = sK1(sK6,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1490,c_786,c_1660,c_1711,c_1752])).

cnf(c_2138,plain,
    ( k1_funct_1(sK6,sK2(sK6,X0)) = sK1(sK6,X0)
    | k2_relat_1(sK6) = X0
    | r2_hidden(sK1(sK6,X0),X0) = iProver_top ),
    inference(renaming,[status(thm)],[c_2137])).

cnf(c_2147,plain,
    ( k1_funct_1(sK6,sK2(sK6,sK5)) = sK1(sK6,sK5)
    | k1_funct_1(sK6,sK7(sK1(sK6,sK5))) = sK1(sK6,sK5)
    | k2_relat_1(sK6) = sK5 ),
    inference(superposition,[status(thm)],[c_2138,c_1495])).

cnf(c_2636,plain,
    ( k1_funct_1(sK6,sK7(sK1(sK6,sK5))) = sK1(sK6,sK5)
    | k1_funct_1(sK6,sK2(sK6,sK5)) = sK1(sK6,sK5) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2147,c_1697])).

cnf(c_2637,plain,
    ( k1_funct_1(sK6,sK2(sK6,sK5)) = sK1(sK6,sK5)
    | k1_funct_1(sK6,sK7(sK1(sK6,sK5))) = sK1(sK6,sK5) ),
    inference(renaming,[status(thm)],[c_2636])).

cnf(c_11,plain,
    ( ~ r2_hidden(X0,k1_relat_1(X1))
    | r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_832,plain,
    ( ~ r2_hidden(X0,k1_relat_1(X1))
    | r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1))
    | ~ v1_relat_1(X1)
    | sK6 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_11,c_29])).

cnf(c_833,plain,
    ( ~ r2_hidden(X0,k1_relat_1(sK6))
    | r2_hidden(k1_funct_1(sK6,X0),k2_relat_1(sK6))
    | ~ v1_relat_1(sK6) ),
    inference(unflattening,[status(thm)],[c_832])).

cnf(c_1487,plain,
    ( r2_hidden(X0,k1_relat_1(sK6)) != iProver_top
    | r2_hidden(k1_funct_1(sK6,X0),k2_relat_1(sK6)) = iProver_top
    | v1_relat_1(sK6) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_833])).

cnf(c_834,plain,
    ( r2_hidden(X0,k1_relat_1(sK6)) != iProver_top
    | r2_hidden(k1_funct_1(sK6,X0),k2_relat_1(sK6)) = iProver_top
    | v1_relat_1(sK6) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_833])).

cnf(c_1963,plain,
    ( r2_hidden(k1_funct_1(sK6,X0),k2_relat_1(sK6)) = iProver_top
    | r2_hidden(X0,k1_relat_1(sK6)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1487,c_834,c_1660,c_1711,c_1752])).

cnf(c_1964,plain,
    ( r2_hidden(X0,k1_relat_1(sK6)) != iProver_top
    | r2_hidden(k1_funct_1(sK6,X0),k2_relat_1(sK6)) = iProver_top ),
    inference(renaming,[status(thm)],[c_1963])).

cnf(c_2374,plain,
    ( r2_hidden(X0,k1_relat_1(sK6)) != iProver_top
    | r2_hidden(k1_funct_1(sK6,X0),X1) = iProver_top
    | r1_tarski(k2_relat_1(sK6),X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1964,c_1499])).

cnf(c_14,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r1_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_1496,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_3687,plain,
    ( r2_hidden(X0,k1_relat_1(sK6)) != iProver_top
    | r1_tarski(X1,k1_funct_1(sK6,X0)) != iProver_top
    | r1_tarski(k2_relat_1(sK6),X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_2374,c_1496])).

cnf(c_8737,plain,
    ( k1_funct_1(sK6,sK2(sK6,sK5)) = sK1(sK6,sK5)
    | r2_hidden(sK7(sK1(sK6,sK5)),k1_relat_1(sK6)) != iProver_top
    | r1_tarski(X0,sK1(sK6,sK5)) != iProver_top
    | r1_tarski(k2_relat_1(sK6),X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_2637,c_3687])).

cnf(c_2307,plain,
    ( r2_hidden(sK1(sK6,sK5),sK5)
    | ~ v1_relat_1(sK6)
    | k1_funct_1(sK6,sK2(sK6,sK5)) = sK1(sK6,sK5)
    | k2_relat_1(sK6) = sK5 ),
    inference(instantiation,[status(thm)],[c_785])).

cnf(c_2309,plain,
    ( k1_funct_1(sK6,sK2(sK6,sK5)) = sK1(sK6,sK5)
    | k2_relat_1(sK6) = sK5
    | r2_hidden(sK1(sK6,sK5),sK5) = iProver_top
    | v1_relat_1(sK6) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2307])).

cnf(c_8,plain,
    ( ~ r2_hidden(X0,k1_relat_1(X1))
    | ~ r2_hidden(sK1(X1,X2),X2)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1)
    | sK1(X1,X2) != k1_funct_1(X1,X0)
    | k2_relat_1(X1) = X2 ),
    inference(cnf_transformation,[],[f56])).

cnf(c_847,plain,
    ( ~ r2_hidden(X0,k1_relat_1(X1))
    | ~ r2_hidden(sK1(X1,X2),X2)
    | ~ v1_relat_1(X1)
    | sK1(X1,X2) != k1_funct_1(X1,X0)
    | k2_relat_1(X1) = X2
    | sK6 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_8,c_29])).

cnf(c_848,plain,
    ( ~ r2_hidden(X0,k1_relat_1(sK6))
    | ~ r2_hidden(sK1(sK6,X1),X1)
    | ~ v1_relat_1(sK6)
    | sK1(sK6,X1) != k1_funct_1(sK6,X0)
    | k2_relat_1(sK6) = X1 ),
    inference(unflattening,[status(thm)],[c_847])).

cnf(c_1486,plain,
    ( sK1(sK6,X0) != k1_funct_1(sK6,X1)
    | k2_relat_1(sK6) = X0
    | r2_hidden(X1,k1_relat_1(sK6)) != iProver_top
    | r2_hidden(sK1(sK6,X0),X0) != iProver_top
    | v1_relat_1(sK6) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_848])).

cnf(c_849,plain,
    ( sK1(sK6,X0) != k1_funct_1(sK6,X1)
    | k2_relat_1(sK6) = X0
    | r2_hidden(X1,k1_relat_1(sK6)) != iProver_top
    | r2_hidden(sK1(sK6,X0),X0) != iProver_top
    | v1_relat_1(sK6) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_848])).

cnf(c_2126,plain,
    ( r2_hidden(sK1(sK6,X0),X0) != iProver_top
    | r2_hidden(X1,k1_relat_1(sK6)) != iProver_top
    | k2_relat_1(sK6) = X0
    | sK1(sK6,X0) != k1_funct_1(sK6,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1486,c_849,c_1660,c_1711,c_1752])).

cnf(c_2127,plain,
    ( sK1(sK6,X0) != k1_funct_1(sK6,X1)
    | k2_relat_1(sK6) = X0
    | r2_hidden(X1,k1_relat_1(sK6)) != iProver_top
    | r2_hidden(sK1(sK6,X0),X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_2126])).

cnf(c_2641,plain,
    ( sK1(sK6,X0) != sK1(sK6,sK5)
    | k1_funct_1(sK6,sK2(sK6,sK5)) = sK1(sK6,sK5)
    | k2_relat_1(sK6) = X0
    | r2_hidden(sK1(sK6,X0),X0) != iProver_top
    | r2_hidden(sK7(sK1(sK6,sK5)),k1_relat_1(sK6)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2637,c_2127])).

cnf(c_10210,plain,
    ( k1_funct_1(sK6,sK2(sK6,sK5)) = sK1(sK6,sK5)
    | k2_relat_1(sK6) = sK5
    | r2_hidden(sK1(sK6,sK5),sK5) != iProver_top
    | r2_hidden(sK7(sK1(sK6,sK5)),k1_relat_1(sK6)) != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_2641])).

cnf(c_15781,plain,
    ( k1_funct_1(sK6,sK2(sK6,sK5)) = sK1(sK6,sK5)
    | r2_hidden(sK7(sK1(sK6,sK5)),k1_relat_1(sK6)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_8737,c_1660,c_1697,c_1711,c_1752,c_2309,c_10210])).

cnf(c_15787,plain,
    ( k1_funct_1(sK6,sK2(sK6,sK5)) = sK1(sK6,sK5)
    | r2_hidden(sK1(sK6,sK5),sK5) != iProver_top
    | r1_tarski(sK4,k1_relat_1(sK6)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2371,c_15781])).

cnf(c_1989,plain,
    ( ~ r2_hidden(sK1(sK6,sK5),sK5)
    | ~ r1_tarski(sK5,sK1(sK6,sK5)) ),
    inference(instantiation,[status(thm)],[c_14])).

cnf(c_2001,plain,
    ( ~ r2_hidden(sK1(sK6,sK5),sK5)
    | r2_hidden(sK7(sK1(sK6,sK5)),sK4) ),
    inference(instantiation,[status(thm)],[c_26])).

cnf(c_1185,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,X1)
    | X2 != X0 ),
    theory(equality)).

cnf(c_2668,plain,
    ( ~ r1_tarski(X0,sK1(sK6,sK5))
    | r1_tarski(sK5,sK1(sK6,sK5))
    | sK5 != X0 ),
    inference(instantiation,[status(thm)],[c_1185])).

cnf(c_2670,plain,
    ( r1_tarski(sK5,sK1(sK6,sK5))
    | ~ r1_tarski(k1_xboole_0,sK1(sK6,sK5))
    | sK5 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_2668])).

cnf(c_3,plain,
    ( r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_6302,plain,
    ( r1_tarski(k1_xboole_0,sK1(sK6,sK5)) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_28,negated_conjecture,
    ( v1_funct_2(sK6,sK4,sK5) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_23,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f61])).

cnf(c_497,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | k1_relset_1(X1,X2,X0) = X1
    | k1_zfmisc_1(k2_zfmisc_1(X1,X2)) != k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))
    | sK6 != X0
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_23,c_27])).

cnf(c_498,plain,
    ( ~ v1_funct_2(sK6,X0,X1)
    | k1_relset_1(X0,X1,sK6) = X0
    | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))
    | k1_xboole_0 = X1 ),
    inference(unflattening,[status(thm)],[c_497])).

cnf(c_904,plain,
    ( k1_relset_1(X0,X1,sK6) = X0
    | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))
    | sK6 != sK6
    | sK5 != X1
    | sK4 != X0
    | k1_xboole_0 = X1 ),
    inference(resolution_lifted,[status(thm)],[c_28,c_498])).

cnf(c_905,plain,
    ( k1_relset_1(sK4,sK5,sK6) = sK4
    | k1_zfmisc_1(k2_zfmisc_1(sK4,sK5)) != k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))
    | k1_xboole_0 = sK5 ),
    inference(unflattening,[status(thm)],[c_904])).

cnf(c_974,plain,
    ( k1_relset_1(sK4,sK5,sK6) = sK4
    | k1_xboole_0 = sK5 ),
    inference(equality_resolution_simp,[status(thm)],[c_905])).

cnf(c_16,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_542,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))
    | sK6 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_16,c_27])).

cnf(c_543,plain,
    ( k1_relset_1(X0,X1,sK6) = k1_relat_1(sK6)
    | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK4,sK5)) ),
    inference(unflattening,[status(thm)],[c_542])).

cnf(c_1684,plain,
    ( k1_relset_1(sK4,sK5,sK6) = k1_relat_1(sK6) ),
    inference(equality_resolution,[status(thm)],[c_543])).

cnf(c_1821,plain,
    ( k1_relat_1(sK6) = sK4
    | sK5 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_974,c_1684])).

cnf(c_15788,plain,
    ( k1_funct_1(sK6,sK2(sK6,sK5)) = sK1(sK6,sK5)
    | sK5 = k1_xboole_0
    | r2_hidden(sK7(sK1(sK6,sK5)),sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_1821,c_15781])).

cnf(c_15802,plain,
    ( ~ r2_hidden(sK7(sK1(sK6,sK5)),sK4)
    | k1_funct_1(sK6,sK2(sK6,sK5)) = sK1(sK6,sK5)
    | sK5 = k1_xboole_0 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_15788])).

cnf(c_15925,plain,
    ( k1_funct_1(sK6,sK2(sK6,sK5)) = sK1(sK6,sK5) ),
    inference(global_propositional_subsumption,[status(thm)],[c_15787,c_1660,c_1697,c_1710,c_1751,c_1989,c_2001,c_2307,c_2670,c_6302,c_15802])).

cnf(c_15933,plain,
    ( r2_hidden(sK2(sK6,sK5),k1_relat_1(sK6)) != iProver_top
    | r2_hidden(sK1(sK6,sK5),k2_relat_1(sK6)) = iProver_top ),
    inference(superposition,[status(thm)],[c_15925,c_1964])).

cnf(c_15982,plain,
    ( k1_funct_1(sK6,sK7(sK1(sK6,sK5))) = sK1(sK6,sK5)
    | r2_hidden(sK1(sK6,sK5),k2_relat_1(sK6)) = iProver_top ),
    inference(superposition,[status(thm)],[c_2763,c_15933])).

cnf(c_16042,plain,
    ( r2_hidden(sK1(sK6,sK5),k2_relat_1(sK6))
    | k1_funct_1(sK6,sK7(sK1(sK6,sK5))) = sK1(sK6,sK5) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_15982])).

cnf(c_2842,plain,
    ( ~ r2_hidden(sK1(sK6,sK5),X0)
    | r2_hidden(sK1(sK6,sK5),X1)
    | ~ r1_tarski(X0,X1) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_6613,plain,
    ( ~ r2_hidden(sK1(sK6,sK5),X0)
    | r2_hidden(sK1(sK6,sK5),sK5)
    | ~ r1_tarski(X0,sK5) ),
    inference(instantiation,[status(thm)],[c_2842])).

cnf(c_33837,plain,
    ( ~ r2_hidden(sK1(sK6,sK5),k2_relat_1(sK6))
    | r2_hidden(sK1(sK6,sK5),sK5)
    | ~ r1_tarski(k2_relat_1(sK6),sK5) ),
    inference(instantiation,[status(thm)],[c_6613])).

cnf(c_41922,plain,
    ( k1_funct_1(sK6,sK7(sK1(sK6,sK5))) = sK1(sK6,sK5) ),
    inference(global_propositional_subsumption,[status(thm)],[c_8870,c_1660,c_1710,c_1751,c_1833,c_2000,c_16042,c_33837])).

cnf(c_41931,plain,
    ( sK1(sK6,X0) != sK1(sK6,sK5)
    | k2_relat_1(sK6) = X0
    | r2_hidden(sK1(sK6,X0),X0) != iProver_top
    | r2_hidden(sK7(sK1(sK6,sK5)),k1_relat_1(sK6)) != iProver_top ),
    inference(superposition,[status(thm)],[c_41922,c_2127])).

cnf(c_13,plain,
    ( ~ r2_hidden(X0,k2_relat_1(X1))
    | r2_hidden(sK3(X1,X0),k1_relat_1(X1))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_802,plain,
    ( ~ r2_hidden(X0,k2_relat_1(X1))
    | r2_hidden(sK3(X1,X0),k1_relat_1(X1))
    | ~ v1_relat_1(X1)
    | sK6 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_13,c_29])).

cnf(c_803,plain,
    ( ~ r2_hidden(X0,k2_relat_1(sK6))
    | r2_hidden(sK3(sK6,X0),k1_relat_1(sK6))
    | ~ v1_relat_1(sK6) ),
    inference(unflattening,[status(thm)],[c_802])).

cnf(c_2857,plain,
    ( r2_hidden(sK3(sK6,sK1(sK6,sK5)),k1_relat_1(sK6))
    | ~ r2_hidden(sK1(sK6,sK5),k2_relat_1(sK6))
    | ~ v1_relat_1(sK6) ),
    inference(instantiation,[status(thm)],[c_803])).

cnf(c_2860,plain,
    ( r2_hidden(sK3(sK6,sK1(sK6,sK5)),k1_relat_1(sK6)) = iProver_top
    | r2_hidden(sK1(sK6,sK5),k2_relat_1(sK6)) != iProver_top
    | v1_relat_1(sK6) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2857])).

cnf(c_41930,plain,
    ( r2_hidden(sK1(sK6,sK5),k2_relat_1(sK6)) = iProver_top
    | r2_hidden(sK7(sK1(sK6,sK5)),k1_relat_1(sK6)) != iProver_top ),
    inference(superposition,[status(thm)],[c_41922,c_1964])).

cnf(c_42820,plain,
    ( r2_hidden(sK1(sK6,sK5),k2_relat_1(sK6)) = iProver_top
    | r2_hidden(sK1(sK6,sK5),sK5) != iProver_top
    | r1_tarski(sK4,k1_relat_1(sK6)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2371,c_41930])).

cnf(c_97,plain,
    ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_99,plain,
    ( r1_tarski(k1_xboole_0,k1_xboole_0) = iProver_top ),
    inference(instantiation,[status(thm)],[c_97])).

cnf(c_2002,plain,
    ( r2_hidden(sK1(sK6,sK5),sK5) != iProver_top
    | r2_hidden(sK7(sK1(sK6,sK5)),sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2001])).

cnf(c_9566,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(sK5,X1)
    | sK5 != X0 ),
    inference(instantiation,[status(thm)],[c_1185])).

cnf(c_9567,plain,
    ( sK5 != X0
    | r1_tarski(X0,X1) != iProver_top
    | r1_tarski(sK5,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9566])).

cnf(c_9569,plain,
    ( sK5 != k1_xboole_0
    | r1_tarski(sK5,k1_xboole_0) = iProver_top
    | r1_tarski(k1_xboole_0,k1_xboole_0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_9567])).

cnf(c_1498,plain,
    ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_2701,plain,
    ( k2_relat_1(sK6) = X0
    | r2_hidden(sK2(sK6,X0),k1_relat_1(sK6)) = iProver_top
    | r2_hidden(sK1(sK6,X0),X1) = iProver_top
    | r1_tarski(X0,X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_2693,c_1499])).

cnf(c_11369,plain,
    ( k2_relat_1(sK6) = X0
    | r2_hidden(sK2(sK6,X0),k1_relat_1(sK6)) = iProver_top
    | r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X1,sK1(sK6,X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2701,c_1496])).

cnf(c_15308,plain,
    ( k2_relat_1(sK6) = X0
    | r2_hidden(sK2(sK6,X0),k1_relat_1(sK6)) = iProver_top
    | r1_tarski(X0,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1498,c_11369])).

cnf(c_15977,plain,
    ( k2_relat_1(sK6) = sK5
    | r2_hidden(sK1(sK6,sK5),k2_relat_1(sK6)) = iProver_top
    | r1_tarski(sK5,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_15308,c_15933])).

cnf(c_15980,plain,
    ( k2_relat_1(sK6) = sK5
    | r2_hidden(sK1(sK6,sK5),k2_relat_1(sK6)) = iProver_top
    | r2_hidden(sK1(sK6,sK5),sK5) = iProver_top ),
    inference(superposition,[status(thm)],[c_2693,c_15933])).

cnf(c_42821,plain,
    ( sK5 = k1_xboole_0
    | r2_hidden(sK1(sK6,sK5),k2_relat_1(sK6)) = iProver_top
    | r2_hidden(sK7(sK1(sK6,sK5)),sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_1821,c_41930])).

cnf(c_42837,plain,
    ( r2_hidden(sK1(sK6,sK5),k2_relat_1(sK6)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_42820,c_99,c_1697,c_2002,c_9569,c_15977,c_15980,c_42821])).

cnf(c_12,plain,
    ( ~ r2_hidden(X0,k2_relat_1(X1))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1)
    | k1_funct_1(X1,sK3(X1,X0)) = X0 ),
    inference(cnf_transformation,[],[f75])).

cnf(c_817,plain,
    ( ~ r2_hidden(X0,k2_relat_1(X1))
    | ~ v1_relat_1(X1)
    | k1_funct_1(X1,sK3(X1,X0)) = X0
    | sK6 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_12,c_29])).

cnf(c_818,plain,
    ( ~ r2_hidden(X0,k2_relat_1(sK6))
    | ~ v1_relat_1(sK6)
    | k1_funct_1(sK6,sK3(sK6,X0)) = X0 ),
    inference(unflattening,[status(thm)],[c_817])).

cnf(c_1488,plain,
    ( k1_funct_1(sK6,sK3(sK6,X0)) = X0
    | r2_hidden(X0,k2_relat_1(sK6)) != iProver_top
    | v1_relat_1(sK6) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_818])).

cnf(c_819,plain,
    ( k1_funct_1(sK6,sK3(sK6,X0)) = X0
    | r2_hidden(X0,k2_relat_1(sK6)) != iProver_top
    | v1_relat_1(sK6) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_818])).

cnf(c_1954,plain,
    ( r2_hidden(X0,k2_relat_1(sK6)) != iProver_top
    | k1_funct_1(sK6,sK3(sK6,X0)) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1488,c_819,c_1660,c_1711,c_1752])).

cnf(c_1955,plain,
    ( k1_funct_1(sK6,sK3(sK6,X0)) = X0
    | r2_hidden(X0,k2_relat_1(sK6)) != iProver_top ),
    inference(renaming,[status(thm)],[c_1954])).

cnf(c_42873,plain,
    ( k1_funct_1(sK6,sK3(sK6,sK1(sK6,sK5))) = sK1(sK6,sK5) ),
    inference(superposition,[status(thm)],[c_42837,c_1955])).

cnf(c_43051,plain,
    ( sK1(sK6,X0) != sK1(sK6,sK5)
    | k2_relat_1(sK6) = X0
    | r2_hidden(sK3(sK6,sK1(sK6,sK5)),k1_relat_1(sK6)) != iProver_top
    | r2_hidden(sK1(sK6,X0),X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_42873,c_2127])).

cnf(c_43252,plain,
    ( r2_hidden(sK1(sK6,X0),X0) != iProver_top
    | k2_relat_1(sK6) = X0
    | sK1(sK6,X0) != sK1(sK6,sK5) ),
    inference(global_propositional_subsumption,[status(thm)],[c_41931,c_99,c_1660,c_1697,c_1711,c_1752,c_2002,c_2860,c_9569,c_15977,c_15980,c_42821,c_43051])).

cnf(c_43253,plain,
    ( sK1(sK6,X0) != sK1(sK6,sK5)
    | k2_relat_1(sK6) = X0
    | r2_hidden(sK1(sK6,X0),X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_43252])).

cnf(c_43261,plain,
    ( k2_relat_1(sK6) = sK5
    | r2_hidden(sK1(sK6,sK5),sK5) != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_43253])).

cnf(c_33839,plain,
    ( r2_hidden(sK1(sK6,sK5),k2_relat_1(sK6)) != iProver_top
    | r2_hidden(sK1(sK6,sK5),sK5) = iProver_top
    | r1_tarski(k2_relat_1(sK6),sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33837])).

cnf(c_1834,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(sK4,sK5)) != k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))
    | r1_tarski(k2_relat_1(sK6),sK5) = iProver_top
    | v1_relat_1(sK6) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1833])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_43261,c_42837,c_33839,c_1834,c_1752,c_1711,c_1697,c_1660])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : iproveropt_run.sh %d %s
% 0.11/0.34  % Computer   : n007.cluster.edu
% 0.11/0.34  % Model      : x86_64 x86_64
% 0.11/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.11/0.34  % Memory     : 8042.1875MB
% 0.11/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.11/0.34  % CPULimit   : 60
% 0.11/0.34  % WCLimit    : 600
% 0.11/0.34  % DateTime   : Tue Dec  1 10:44:36 EST 2020
% 0.11/0.34  % CPUTime    : 
% 0.11/0.34  % Running in FOF mode
% 11.53/1.99  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 11.53/1.99  
% 11.53/1.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 11.53/1.99  
% 11.53/1.99  ------  iProver source info
% 11.53/1.99  
% 11.53/1.99  git: date: 2020-06-30 10:37:57 +0100
% 11.53/1.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 11.53/1.99  git: non_committed_changes: false
% 11.53/1.99  git: last_make_outside_of_git: false
% 11.53/1.99  
% 11.53/1.99  ------ 
% 11.53/1.99  
% 11.53/1.99  ------ Input Options
% 11.53/1.99  
% 11.53/1.99  --out_options                           all
% 11.53/1.99  --tptp_safe_out                         true
% 11.53/1.99  --problem_path                          ""
% 11.53/1.99  --include_path                          ""
% 11.53/1.99  --clausifier                            res/vclausify_rel
% 11.53/1.99  --clausifier_options                    --mode clausify
% 11.53/1.99  --stdin                                 false
% 11.53/1.99  --stats_out                             all
% 11.53/1.99  
% 11.53/1.99  ------ General Options
% 11.53/1.99  
% 11.53/1.99  --fof                                   false
% 11.53/1.99  --time_out_real                         305.
% 11.53/1.99  --time_out_virtual                      -1.
% 11.53/1.99  --symbol_type_check                     false
% 11.53/1.99  --clausify_out                          false
% 11.53/1.99  --sig_cnt_out                           false
% 11.53/1.99  --trig_cnt_out                          false
% 11.53/1.99  --trig_cnt_out_tolerance                1.
% 11.53/1.99  --trig_cnt_out_sk_spl                   false
% 11.53/1.99  --abstr_cl_out                          false
% 11.53/1.99  
% 11.53/1.99  ------ Global Options
% 11.53/1.99  
% 11.53/1.99  --schedule                              default
% 11.53/1.99  --add_important_lit                     false
% 11.53/1.99  --prop_solver_per_cl                    1000
% 11.53/1.99  --min_unsat_core                        false
% 11.53/1.99  --soft_assumptions                      false
% 11.53/1.99  --soft_lemma_size                       3
% 11.53/1.99  --prop_impl_unit_size                   0
% 11.53/1.99  --prop_impl_unit                        []
% 11.53/1.99  --share_sel_clauses                     true
% 11.53/1.99  --reset_solvers                         false
% 11.53/1.99  --bc_imp_inh                            [conj_cone]
% 11.53/1.99  --conj_cone_tolerance                   3.
% 11.53/1.99  --extra_neg_conj                        none
% 11.53/1.99  --large_theory_mode                     true
% 11.53/1.99  --prolific_symb_bound                   200
% 11.53/1.99  --lt_threshold                          2000
% 11.53/1.99  --clause_weak_htbl                      true
% 11.53/1.99  --gc_record_bc_elim                     false
% 11.53/1.99  
% 11.53/1.99  ------ Preprocessing Options
% 11.53/1.99  
% 11.53/1.99  --preprocessing_flag                    true
% 11.53/1.99  --time_out_prep_mult                    0.1
% 11.53/1.99  --splitting_mode                        input
% 11.53/1.99  --splitting_grd                         true
% 11.53/1.99  --splitting_cvd                         false
% 11.53/1.99  --splitting_cvd_svl                     false
% 11.53/1.99  --splitting_nvd                         32
% 11.53/1.99  --sub_typing                            true
% 11.53/1.99  --prep_gs_sim                           true
% 11.53/1.99  --prep_unflatten                        true
% 11.53/1.99  --prep_res_sim                          true
% 11.53/1.99  --prep_upred                            true
% 11.53/1.99  --prep_sem_filter                       exhaustive
% 11.53/1.99  --prep_sem_filter_out                   false
% 11.53/1.99  --pred_elim                             true
% 11.53/1.99  --res_sim_input                         true
% 11.53/1.99  --eq_ax_congr_red                       true
% 11.53/1.99  --pure_diseq_elim                       true
% 11.53/1.99  --brand_transform                       false
% 11.53/1.99  --non_eq_to_eq                          false
% 11.53/1.99  --prep_def_merge                        true
% 11.53/1.99  --prep_def_merge_prop_impl              false
% 11.53/1.99  --prep_def_merge_mbd                    true
% 11.53/1.99  --prep_def_merge_tr_red                 false
% 11.53/1.99  --prep_def_merge_tr_cl                  false
% 11.53/1.99  --smt_preprocessing                     true
% 11.53/1.99  --smt_ac_axioms                         fast
% 11.53/1.99  --preprocessed_out                      false
% 11.53/1.99  --preprocessed_stats                    false
% 11.53/1.99  
% 11.53/1.99  ------ Abstraction refinement Options
% 11.53/1.99  
% 11.53/1.99  --abstr_ref                             []
% 11.53/1.99  --abstr_ref_prep                        false
% 11.53/1.99  --abstr_ref_until_sat                   false
% 11.53/1.99  --abstr_ref_sig_restrict                funpre
% 11.53/1.99  --abstr_ref_af_restrict_to_split_sk     false
% 11.53/1.99  --abstr_ref_under                       []
% 11.53/1.99  
% 11.53/1.99  ------ SAT Options
% 11.53/1.99  
% 11.53/1.99  --sat_mode                              false
% 11.53/1.99  --sat_fm_restart_options                ""
% 11.53/1.99  --sat_gr_def                            false
% 11.53/1.99  --sat_epr_types                         true
% 11.53/1.99  --sat_non_cyclic_types                  false
% 11.53/1.99  --sat_finite_models                     false
% 11.53/1.99  --sat_fm_lemmas                         false
% 11.53/1.99  --sat_fm_prep                           false
% 11.53/1.99  --sat_fm_uc_incr                        true
% 11.53/1.99  --sat_out_model                         small
% 11.53/1.99  --sat_out_clauses                       false
% 11.53/1.99  
% 11.53/1.99  ------ QBF Options
% 11.53/1.99  
% 11.53/1.99  --qbf_mode                              false
% 11.53/1.99  --qbf_elim_univ                         false
% 11.53/1.99  --qbf_dom_inst                          none
% 11.53/1.99  --qbf_dom_pre_inst                      false
% 11.53/1.99  --qbf_sk_in                             false
% 11.53/1.99  --qbf_pred_elim                         true
% 11.53/1.99  --qbf_split                             512
% 11.53/1.99  
% 11.53/1.99  ------ BMC1 Options
% 11.53/1.99  
% 11.53/1.99  --bmc1_incremental                      false
% 11.53/1.99  --bmc1_axioms                           reachable_all
% 11.53/1.99  --bmc1_min_bound                        0
% 11.53/1.99  --bmc1_max_bound                        -1
% 11.53/1.99  --bmc1_max_bound_default                -1
% 11.53/1.99  --bmc1_symbol_reachability              true
% 11.53/1.99  --bmc1_property_lemmas                  false
% 11.53/1.99  --bmc1_k_induction                      false
% 11.53/1.99  --bmc1_non_equiv_states                 false
% 11.53/1.99  --bmc1_deadlock                         false
% 11.53/1.99  --bmc1_ucm                              false
% 11.53/1.99  --bmc1_add_unsat_core                   none
% 11.53/1.99  --bmc1_unsat_core_children              false
% 11.53/1.99  --bmc1_unsat_core_extrapolate_axioms    false
% 11.53/1.99  --bmc1_out_stat                         full
% 11.53/1.99  --bmc1_ground_init                      false
% 11.53/1.99  --bmc1_pre_inst_next_state              false
% 11.53/1.99  --bmc1_pre_inst_state                   false
% 11.53/1.99  --bmc1_pre_inst_reach_state             false
% 11.53/1.99  --bmc1_out_unsat_core                   false
% 11.53/1.99  --bmc1_aig_witness_out                  false
% 11.53/1.99  --bmc1_verbose                          false
% 11.53/1.99  --bmc1_dump_clauses_tptp                false
% 11.53/1.99  --bmc1_dump_unsat_core_tptp             false
% 11.53/1.99  --bmc1_dump_file                        -
% 11.53/1.99  --bmc1_ucm_expand_uc_limit              128
% 11.53/1.99  --bmc1_ucm_n_expand_iterations          6
% 11.53/1.99  --bmc1_ucm_extend_mode                  1
% 11.53/1.99  --bmc1_ucm_init_mode                    2
% 11.53/1.99  --bmc1_ucm_cone_mode                    none
% 11.53/1.99  --bmc1_ucm_reduced_relation_type        0
% 11.53/1.99  --bmc1_ucm_relax_model                  4
% 11.53/1.99  --bmc1_ucm_full_tr_after_sat            true
% 11.53/1.99  --bmc1_ucm_expand_neg_assumptions       false
% 11.53/1.99  --bmc1_ucm_layered_model                none
% 11.53/1.99  --bmc1_ucm_max_lemma_size               10
% 11.53/1.99  
% 11.53/1.99  ------ AIG Options
% 11.53/1.99  
% 11.53/1.99  --aig_mode                              false
% 11.53/1.99  
% 11.53/1.99  ------ Instantiation Options
% 11.53/1.99  
% 11.53/1.99  --instantiation_flag                    true
% 11.53/1.99  --inst_sos_flag                         false
% 11.53/1.99  --inst_sos_phase                        true
% 11.53/1.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 11.53/1.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 11.53/1.99  --inst_lit_sel_side                     num_symb
% 11.53/1.99  --inst_solver_per_active                1400
% 11.53/1.99  --inst_solver_calls_frac                1.
% 11.53/1.99  --inst_passive_queue_type               priority_queues
% 11.53/1.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 11.53/1.99  --inst_passive_queues_freq              [25;2]
% 11.53/1.99  --inst_dismatching                      true
% 11.53/1.99  --inst_eager_unprocessed_to_passive     true
% 11.53/1.99  --inst_prop_sim_given                   true
% 11.53/1.99  --inst_prop_sim_new                     false
% 11.53/1.99  --inst_subs_new                         false
% 11.53/1.99  --inst_eq_res_simp                      false
% 11.53/1.99  --inst_subs_given                       false
% 11.53/1.99  --inst_orphan_elimination               true
% 11.53/1.99  --inst_learning_loop_flag               true
% 11.53/1.99  --inst_learning_start                   3000
% 11.53/1.99  --inst_learning_factor                  2
% 11.53/1.99  --inst_start_prop_sim_after_learn       3
% 11.53/1.99  --inst_sel_renew                        solver
% 11.53/1.99  --inst_lit_activity_flag                true
% 11.53/1.99  --inst_restr_to_given                   false
% 11.53/1.99  --inst_activity_threshold               500
% 11.53/1.99  --inst_out_proof                        true
% 11.53/1.99  
% 11.53/1.99  ------ Resolution Options
% 11.53/1.99  
% 11.53/1.99  --resolution_flag                       true
% 11.53/1.99  --res_lit_sel                           adaptive
% 11.53/1.99  --res_lit_sel_side                      none
% 11.53/1.99  --res_ordering                          kbo
% 11.53/1.99  --res_to_prop_solver                    active
% 11.53/1.99  --res_prop_simpl_new                    false
% 11.53/1.99  --res_prop_simpl_given                  true
% 11.53/1.99  --res_passive_queue_type                priority_queues
% 11.53/1.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 11.53/1.99  --res_passive_queues_freq               [15;5]
% 11.53/1.99  --res_forward_subs                      full
% 11.53/1.99  --res_backward_subs                     full
% 11.53/1.99  --res_forward_subs_resolution           true
% 11.53/1.99  --res_backward_subs_resolution          true
% 11.53/1.99  --res_orphan_elimination                true
% 11.53/1.99  --res_time_limit                        2.
% 11.53/1.99  --res_out_proof                         true
% 11.53/1.99  
% 11.53/1.99  ------ Superposition Options
% 11.53/1.99  
% 11.53/1.99  --superposition_flag                    true
% 11.53/1.99  --sup_passive_queue_type                priority_queues
% 11.53/1.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 11.53/1.99  --sup_passive_queues_freq               [8;1;4]
% 11.53/1.99  --demod_completeness_check              fast
% 11.53/1.99  --demod_use_ground                      true
% 11.53/1.99  --sup_to_prop_solver                    passive
% 11.53/1.99  --sup_prop_simpl_new                    true
% 11.53/1.99  --sup_prop_simpl_given                  true
% 11.53/1.99  --sup_fun_splitting                     false
% 11.53/1.99  --sup_smt_interval                      50000
% 11.53/1.99  
% 11.53/1.99  ------ Superposition Simplification Setup
% 11.53/1.99  
% 11.53/1.99  --sup_indices_passive                   []
% 11.53/1.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 11.53/1.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 11.53/1.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 11.53/1.99  --sup_full_triv                         [TrivRules;PropSubs]
% 11.53/1.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 11.53/1.99  --sup_full_bw                           [BwDemod]
% 11.53/1.99  --sup_immed_triv                        [TrivRules]
% 11.53/1.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 11.53/1.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 11.53/1.99  --sup_immed_bw_main                     []
% 11.53/1.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 11.53/1.99  --sup_input_triv                        [Unflattening;TrivRules]
% 11.53/1.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 11.53/1.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 11.53/1.99  
% 11.53/1.99  ------ Combination Options
% 11.53/1.99  
% 11.53/1.99  --comb_res_mult                         3
% 11.53/1.99  --comb_sup_mult                         2
% 11.53/1.99  --comb_inst_mult                        10
% 11.53/1.99  
% 11.53/1.99  ------ Debug Options
% 11.53/1.99  
% 11.53/1.99  --dbg_backtrace                         false
% 11.53/1.99  --dbg_dump_prop_clauses                 false
% 11.53/1.99  --dbg_dump_prop_clauses_file            -
% 11.53/1.99  --dbg_out_stat                          false
% 11.53/1.99  ------ Parsing...
% 11.53/1.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 11.53/1.99  
% 11.53/1.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 4 0s  sf_e  pe_s  pe_e 
% 11.53/1.99  
% 11.53/1.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 11.53/1.99  
% 11.53/1.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 11.53/1.99  ------ Proving...
% 11.53/1.99  ------ Problem Properties 
% 11.53/1.99  
% 11.53/1.99  
% 11.53/1.99  clauses                                 22
% 11.53/1.99  conjectures                             3
% 11.53/1.99  EPR                                     3
% 11.53/1.99  Horn                                    17
% 11.53/1.99  unary                                   3
% 11.53/1.99  binary                                  8
% 11.53/1.99  lits                                    57
% 11.53/1.99  lits eq                                 23
% 11.53/1.99  fd_pure                                 0
% 11.53/1.99  fd_pseudo                               0
% 11.53/1.99  fd_cond                                 3
% 11.53/1.99  fd_pseudo_cond                          0
% 11.53/1.99  AC symbols                              0
% 11.53/1.99  
% 11.53/1.99  ------ Schedule dynamic 5 is on 
% 11.53/1.99  
% 11.53/1.99  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 11.53/1.99  
% 11.53/1.99  
% 11.53/1.99  ------ 
% 11.53/1.99  Current options:
% 11.53/1.99  ------ 
% 11.53/1.99  
% 11.53/1.99  ------ Input Options
% 11.53/1.99  
% 11.53/1.99  --out_options                           all
% 11.53/1.99  --tptp_safe_out                         true
% 11.53/1.99  --problem_path                          ""
% 11.53/1.99  --include_path                          ""
% 11.53/1.99  --clausifier                            res/vclausify_rel
% 11.53/1.99  --clausifier_options                    --mode clausify
% 11.53/1.99  --stdin                                 false
% 11.53/1.99  --stats_out                             all
% 11.53/1.99  
% 11.53/1.99  ------ General Options
% 11.53/1.99  
% 11.53/1.99  --fof                                   false
% 11.53/1.99  --time_out_real                         305.
% 11.53/1.99  --time_out_virtual                      -1.
% 11.53/1.99  --symbol_type_check                     false
% 11.53/1.99  --clausify_out                          false
% 11.53/1.99  --sig_cnt_out                           false
% 11.53/1.99  --trig_cnt_out                          false
% 11.53/1.99  --trig_cnt_out_tolerance                1.
% 11.53/1.99  --trig_cnt_out_sk_spl                   false
% 11.53/1.99  --abstr_cl_out                          false
% 11.53/1.99  
% 11.53/1.99  ------ Global Options
% 11.53/1.99  
% 11.53/1.99  --schedule                              default
% 11.53/1.99  --add_important_lit                     false
% 11.53/1.99  --prop_solver_per_cl                    1000
% 11.53/1.99  --min_unsat_core                        false
% 11.53/1.99  --soft_assumptions                      false
% 11.53/1.99  --soft_lemma_size                       3
% 11.53/1.99  --prop_impl_unit_size                   0
% 11.53/1.99  --prop_impl_unit                        []
% 11.53/1.99  --share_sel_clauses                     true
% 11.53/1.99  --reset_solvers                         false
% 11.53/1.99  --bc_imp_inh                            [conj_cone]
% 11.53/1.99  --conj_cone_tolerance                   3.
% 11.53/1.99  --extra_neg_conj                        none
% 11.53/1.99  --large_theory_mode                     true
% 11.53/1.99  --prolific_symb_bound                   200
% 11.53/1.99  --lt_threshold                          2000
% 11.53/1.99  --clause_weak_htbl                      true
% 11.53/1.99  --gc_record_bc_elim                     false
% 11.53/1.99  
% 11.53/1.99  ------ Preprocessing Options
% 11.53/1.99  
% 11.53/1.99  --preprocessing_flag                    true
% 11.53/1.99  --time_out_prep_mult                    0.1
% 11.53/1.99  --splitting_mode                        input
% 11.53/1.99  --splitting_grd                         true
% 11.53/1.99  --splitting_cvd                         false
% 11.53/1.99  --splitting_cvd_svl                     false
% 11.53/1.99  --splitting_nvd                         32
% 11.53/1.99  --sub_typing                            true
% 11.53/1.99  --prep_gs_sim                           true
% 11.53/1.99  --prep_unflatten                        true
% 11.53/1.99  --prep_res_sim                          true
% 11.53/1.99  --prep_upred                            true
% 11.53/1.99  --prep_sem_filter                       exhaustive
% 11.53/1.99  --prep_sem_filter_out                   false
% 11.53/1.99  --pred_elim                             true
% 11.53/1.99  --res_sim_input                         true
% 11.53/1.99  --eq_ax_congr_red                       true
% 11.53/1.99  --pure_diseq_elim                       true
% 11.53/1.99  --brand_transform                       false
% 11.53/1.99  --non_eq_to_eq                          false
% 11.53/1.99  --prep_def_merge                        true
% 11.53/1.99  --prep_def_merge_prop_impl              false
% 11.53/1.99  --prep_def_merge_mbd                    true
% 11.53/1.99  --prep_def_merge_tr_red                 false
% 11.53/1.99  --prep_def_merge_tr_cl                  false
% 11.53/1.99  --smt_preprocessing                     true
% 11.53/1.99  --smt_ac_axioms                         fast
% 11.53/1.99  --preprocessed_out                      false
% 11.53/1.99  --preprocessed_stats                    false
% 11.53/1.99  
% 11.53/1.99  ------ Abstraction refinement Options
% 11.53/1.99  
% 11.53/1.99  --abstr_ref                             []
% 11.53/1.99  --abstr_ref_prep                        false
% 11.53/1.99  --abstr_ref_until_sat                   false
% 11.53/1.99  --abstr_ref_sig_restrict                funpre
% 11.53/1.99  --abstr_ref_af_restrict_to_split_sk     false
% 11.53/1.99  --abstr_ref_under                       []
% 11.53/1.99  
% 11.53/1.99  ------ SAT Options
% 11.53/1.99  
% 11.53/1.99  --sat_mode                              false
% 11.53/1.99  --sat_fm_restart_options                ""
% 11.53/1.99  --sat_gr_def                            false
% 11.53/1.99  --sat_epr_types                         true
% 11.53/1.99  --sat_non_cyclic_types                  false
% 11.53/1.99  --sat_finite_models                     false
% 11.53/1.99  --sat_fm_lemmas                         false
% 11.53/1.99  --sat_fm_prep                           false
% 11.53/1.99  --sat_fm_uc_incr                        true
% 11.53/1.99  --sat_out_model                         small
% 11.53/1.99  --sat_out_clauses                       false
% 11.53/1.99  
% 11.53/1.99  ------ QBF Options
% 11.53/1.99  
% 11.53/1.99  --qbf_mode                              false
% 11.53/1.99  --qbf_elim_univ                         false
% 11.53/1.99  --qbf_dom_inst                          none
% 11.53/1.99  --qbf_dom_pre_inst                      false
% 11.53/1.99  --qbf_sk_in                             false
% 11.53/1.99  --qbf_pred_elim                         true
% 11.53/1.99  --qbf_split                             512
% 11.53/1.99  
% 11.53/1.99  ------ BMC1 Options
% 11.53/1.99  
% 11.53/1.99  --bmc1_incremental                      false
% 11.53/1.99  --bmc1_axioms                           reachable_all
% 11.53/1.99  --bmc1_min_bound                        0
% 11.53/1.99  --bmc1_max_bound                        -1
% 11.53/1.99  --bmc1_max_bound_default                -1
% 11.53/1.99  --bmc1_symbol_reachability              true
% 11.53/1.99  --bmc1_property_lemmas                  false
% 11.53/1.99  --bmc1_k_induction                      false
% 11.53/1.99  --bmc1_non_equiv_states                 false
% 11.53/1.99  --bmc1_deadlock                         false
% 11.53/1.99  --bmc1_ucm                              false
% 11.53/1.99  --bmc1_add_unsat_core                   none
% 11.53/1.99  --bmc1_unsat_core_children              false
% 11.53/1.99  --bmc1_unsat_core_extrapolate_axioms    false
% 11.53/1.99  --bmc1_out_stat                         full
% 11.53/1.99  --bmc1_ground_init                      false
% 11.53/1.99  --bmc1_pre_inst_next_state              false
% 11.53/1.99  --bmc1_pre_inst_state                   false
% 11.53/1.99  --bmc1_pre_inst_reach_state             false
% 11.53/1.99  --bmc1_out_unsat_core                   false
% 11.53/1.99  --bmc1_aig_witness_out                  false
% 11.53/1.99  --bmc1_verbose                          false
% 11.53/1.99  --bmc1_dump_clauses_tptp                false
% 11.53/1.99  --bmc1_dump_unsat_core_tptp             false
% 11.53/1.99  --bmc1_dump_file                        -
% 11.53/1.99  --bmc1_ucm_expand_uc_limit              128
% 11.53/1.99  --bmc1_ucm_n_expand_iterations          6
% 11.53/1.99  --bmc1_ucm_extend_mode                  1
% 11.53/1.99  --bmc1_ucm_init_mode                    2
% 11.53/1.99  --bmc1_ucm_cone_mode                    none
% 11.53/1.99  --bmc1_ucm_reduced_relation_type        0
% 11.53/1.99  --bmc1_ucm_relax_model                  4
% 11.53/1.99  --bmc1_ucm_full_tr_after_sat            true
% 11.53/1.99  --bmc1_ucm_expand_neg_assumptions       false
% 11.53/1.99  --bmc1_ucm_layered_model                none
% 11.53/1.99  --bmc1_ucm_max_lemma_size               10
% 11.53/1.99  
% 11.53/1.99  ------ AIG Options
% 11.53/1.99  
% 11.53/1.99  --aig_mode                              false
% 11.53/1.99  
% 11.53/1.99  ------ Instantiation Options
% 11.53/1.99  
% 11.53/1.99  --instantiation_flag                    true
% 11.53/1.99  --inst_sos_flag                         false
% 11.53/1.99  --inst_sos_phase                        true
% 11.53/1.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 11.53/1.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 11.53/1.99  --inst_lit_sel_side                     none
% 11.53/1.99  --inst_solver_per_active                1400
% 11.53/1.99  --inst_solver_calls_frac                1.
% 11.53/1.99  --inst_passive_queue_type               priority_queues
% 11.53/1.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 11.53/1.99  --inst_passive_queues_freq              [25;2]
% 11.53/1.99  --inst_dismatching                      true
% 11.53/1.99  --inst_eager_unprocessed_to_passive     true
% 11.53/1.99  --inst_prop_sim_given                   true
% 11.53/1.99  --inst_prop_sim_new                     false
% 11.53/1.99  --inst_subs_new                         false
% 11.53/1.99  --inst_eq_res_simp                      false
% 11.53/1.99  --inst_subs_given                       false
% 11.53/1.99  --inst_orphan_elimination               true
% 11.53/1.99  --inst_learning_loop_flag               true
% 11.53/1.99  --inst_learning_start                   3000
% 11.53/1.99  --inst_learning_factor                  2
% 11.53/1.99  --inst_start_prop_sim_after_learn       3
% 11.53/1.99  --inst_sel_renew                        solver
% 11.53/1.99  --inst_lit_activity_flag                true
% 11.53/1.99  --inst_restr_to_given                   false
% 11.53/1.99  --inst_activity_threshold               500
% 11.53/1.99  --inst_out_proof                        true
% 11.53/1.99  
% 11.53/1.99  ------ Resolution Options
% 11.53/1.99  
% 11.53/1.99  --resolution_flag                       false
% 11.53/1.99  --res_lit_sel                           adaptive
% 11.53/1.99  --res_lit_sel_side                      none
% 11.53/1.99  --res_ordering                          kbo
% 11.53/1.99  --res_to_prop_solver                    active
% 11.53/1.99  --res_prop_simpl_new                    false
% 11.53/1.99  --res_prop_simpl_given                  true
% 11.53/1.99  --res_passive_queue_type                priority_queues
% 11.53/1.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 11.53/1.99  --res_passive_queues_freq               [15;5]
% 11.53/1.99  --res_forward_subs                      full
% 11.53/1.99  --res_backward_subs                     full
% 11.53/1.99  --res_forward_subs_resolution           true
% 11.53/1.99  --res_backward_subs_resolution          true
% 11.53/1.99  --res_orphan_elimination                true
% 11.53/1.99  --res_time_limit                        2.
% 11.53/1.99  --res_out_proof                         true
% 11.53/1.99  
% 11.53/1.99  ------ Superposition Options
% 11.53/1.99  
% 11.53/1.99  --superposition_flag                    true
% 11.53/1.99  --sup_passive_queue_type                priority_queues
% 11.53/1.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 11.53/1.99  --sup_passive_queues_freq               [8;1;4]
% 11.53/1.99  --demod_completeness_check              fast
% 11.53/1.99  --demod_use_ground                      true
% 11.53/1.99  --sup_to_prop_solver                    passive
% 11.53/1.99  --sup_prop_simpl_new                    true
% 11.53/1.99  --sup_prop_simpl_given                  true
% 11.53/1.99  --sup_fun_splitting                     false
% 11.53/1.99  --sup_smt_interval                      50000
% 11.53/1.99  
% 11.53/1.99  ------ Superposition Simplification Setup
% 11.53/1.99  
% 11.53/1.99  --sup_indices_passive                   []
% 11.53/1.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 11.53/1.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 11.53/1.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 11.53/1.99  --sup_full_triv                         [TrivRules;PropSubs]
% 11.53/1.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 11.53/1.99  --sup_full_bw                           [BwDemod]
% 11.53/1.99  --sup_immed_triv                        [TrivRules]
% 11.53/1.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 11.53/1.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 11.53/1.99  --sup_immed_bw_main                     []
% 11.53/1.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 11.53/1.99  --sup_input_triv                        [Unflattening;TrivRules]
% 11.53/1.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 11.53/1.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 11.53/1.99  
% 11.53/1.99  ------ Combination Options
% 11.53/1.99  
% 11.53/1.99  --comb_res_mult                         3
% 11.53/1.99  --comb_sup_mult                         2
% 11.53/1.99  --comb_inst_mult                        10
% 11.53/1.99  
% 11.53/1.99  ------ Debug Options
% 11.53/1.99  
% 11.53/1.99  --dbg_backtrace                         false
% 11.53/1.99  --dbg_dump_prop_clauses                 false
% 11.53/1.99  --dbg_dump_prop_clauses_file            -
% 11.53/1.99  --dbg_out_stat                          false
% 11.53/1.99  
% 11.53/1.99  
% 11.53/1.99  
% 11.53/1.99  
% 11.53/1.99  ------ Proving...
% 11.53/1.99  
% 11.53/1.99  
% 11.53/1.99  % SZS status Theorem for theBenchmark.p
% 11.53/1.99  
% 11.53/1.99  % SZS output start CNFRefutation for theBenchmark.p
% 11.53/1.99  
% 11.53/1.99  fof(f6,axiom,(
% 11.53/1.99    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))))),
% 11.53/1.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.53/1.99  
% 11.53/1.99  fof(f18,plain,(
% 11.53/1.99    ! [X0] : (! [X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 11.53/1.99    inference(ennf_transformation,[],[f6])).
% 11.53/1.99  
% 11.53/1.99  fof(f19,plain,(
% 11.53/1.99    ! [X0] : (! [X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 11.53/1.99    inference(flattening,[],[f18])).
% 11.53/1.99  
% 11.53/1.99  fof(f33,plain,(
% 11.53/1.99    ! [X0] : (! [X1] : ((k2_relat_1(X0) = X1 | ? [X2] : ((! [X3] : (k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(X2,X1)) & (? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ! [X3] : (k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0)))) & (? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(X2,X1))) | k2_relat_1(X0) != X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 11.53/1.99    inference(nnf_transformation,[],[f19])).
% 11.53/1.99  
% 11.53/1.99  fof(f34,plain,(
% 11.53/1.99    ! [X0] : (! [X1] : ((k2_relat_1(X0) = X1 | ? [X2] : ((! [X3] : (k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(X2,X1)) & (? [X4] : (k1_funct_1(X0,X4) = X2 & r2_hidden(X4,k1_relat_1(X0))) | r2_hidden(X2,X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : (k1_funct_1(X0,X6) != X5 | ~r2_hidden(X6,k1_relat_1(X0)))) & (? [X7] : (k1_funct_1(X0,X7) = X5 & r2_hidden(X7,k1_relat_1(X0))) | ~r2_hidden(X5,X1))) | k2_relat_1(X0) != X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 11.53/1.99    inference(rectify,[],[f33])).
% 11.53/1.99  
% 11.53/1.99  fof(f37,plain,(
% 11.53/1.99    ! [X5,X0] : (? [X7] : (k1_funct_1(X0,X7) = X5 & r2_hidden(X7,k1_relat_1(X0))) => (k1_funct_1(X0,sK3(X0,X5)) = X5 & r2_hidden(sK3(X0,X5),k1_relat_1(X0))))),
% 11.53/1.99    introduced(choice_axiom,[])).
% 11.53/1.99  
% 11.53/1.99  fof(f36,plain,(
% 11.53/1.99    ( ! [X2] : (! [X1,X0] : (? [X4] : (k1_funct_1(X0,X4) = X2 & r2_hidden(X4,k1_relat_1(X0))) => (k1_funct_1(X0,sK2(X0,X1)) = X2 & r2_hidden(sK2(X0,X1),k1_relat_1(X0))))) )),
% 11.53/1.99    introduced(choice_axiom,[])).
% 11.53/1.99  
% 11.53/1.99  fof(f35,plain,(
% 11.53/1.99    ! [X1,X0] : (? [X2] : ((! [X3] : (k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(X2,X1)) & (? [X4] : (k1_funct_1(X0,X4) = X2 & r2_hidden(X4,k1_relat_1(X0))) | r2_hidden(X2,X1))) => ((! [X3] : (k1_funct_1(X0,X3) != sK1(X0,X1) | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(sK1(X0,X1),X1)) & (? [X4] : (k1_funct_1(X0,X4) = sK1(X0,X1) & r2_hidden(X4,k1_relat_1(X0))) | r2_hidden(sK1(X0,X1),X1))))),
% 11.53/1.99    introduced(choice_axiom,[])).
% 11.53/1.99  
% 11.53/1.99  fof(f38,plain,(
% 11.53/1.99    ! [X0] : (! [X1] : ((k2_relat_1(X0) = X1 | ((! [X3] : (k1_funct_1(X0,X3) != sK1(X0,X1) | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(sK1(X0,X1),X1)) & ((k1_funct_1(X0,sK2(X0,X1)) = sK1(X0,X1) & r2_hidden(sK2(X0,X1),k1_relat_1(X0))) | r2_hidden(sK1(X0,X1),X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : (k1_funct_1(X0,X6) != X5 | ~r2_hidden(X6,k1_relat_1(X0)))) & ((k1_funct_1(X0,sK3(X0,X5)) = X5 & r2_hidden(sK3(X0,X5),k1_relat_1(X0))) | ~r2_hidden(X5,X1))) | k2_relat_1(X0) != X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 11.53/1.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f34,f37,f36,f35])).
% 11.53/1.99  
% 11.53/1.99  fof(f54,plain,(
% 11.53/1.99    ( ! [X0,X1] : (k2_relat_1(X0) = X1 | r2_hidden(sK2(X0,X1),k1_relat_1(X0)) | r2_hidden(sK1(X0,X1),X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 11.53/1.99    inference(cnf_transformation,[],[f38])).
% 11.53/1.99  
% 11.53/1.99  fof(f12,conjecture,(
% 11.53/1.99    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (! [X3] : ~(! [X4] : ~(k1_funct_1(X2,X4) = X3 & r2_hidden(X4,X0)) & r2_hidden(X3,X1)) => k2_relset_1(X0,X1,X2) = X1))),
% 11.53/1.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.53/1.99  
% 11.53/1.99  fof(f13,negated_conjecture,(
% 11.53/1.99    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (! [X3] : ~(! [X4] : ~(k1_funct_1(X2,X4) = X3 & r2_hidden(X4,X0)) & r2_hidden(X3,X1)) => k2_relset_1(X0,X1,X2) = X1))),
% 11.53/1.99    inference(negated_conjecture,[],[f12])).
% 11.53/1.99  
% 11.53/1.99  fof(f26,plain,(
% 11.53/1.99    ? [X0,X1,X2] : ((k2_relset_1(X0,X1,X2) != X1 & ! [X3] : (? [X4] : (k1_funct_1(X2,X4) = X3 & r2_hidden(X4,X0)) | ~r2_hidden(X3,X1))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 11.53/1.99    inference(ennf_transformation,[],[f13])).
% 11.53/1.99  
% 11.53/1.99  fof(f27,plain,(
% 11.53/1.99    ? [X0,X1,X2] : (k2_relset_1(X0,X1,X2) != X1 & ! [X3] : (? [X4] : (k1_funct_1(X2,X4) = X3 & r2_hidden(X4,X0)) | ~r2_hidden(X3,X1)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 11.53/1.99    inference(flattening,[],[f26])).
% 11.53/1.99  
% 11.53/1.99  fof(f41,plain,(
% 11.53/1.99    ( ! [X2,X0] : (! [X3] : (? [X4] : (k1_funct_1(X2,X4) = X3 & r2_hidden(X4,X0)) => (k1_funct_1(X2,sK7(X3)) = X3 & r2_hidden(sK7(X3),X0)))) )),
% 11.53/1.99    introduced(choice_axiom,[])).
% 11.53/1.99  
% 11.53/1.99  fof(f40,plain,(
% 11.53/1.99    ? [X0,X1,X2] : (k2_relset_1(X0,X1,X2) != X1 & ! [X3] : (? [X4] : (k1_funct_1(X2,X4) = X3 & r2_hidden(X4,X0)) | ~r2_hidden(X3,X1)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (k2_relset_1(sK4,sK5,sK6) != sK5 & ! [X3] : (? [X4] : (k1_funct_1(sK6,X4) = X3 & r2_hidden(X4,sK4)) | ~r2_hidden(X3,sK5)) & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) & v1_funct_2(sK6,sK4,sK5) & v1_funct_1(sK6))),
% 11.53/1.99    introduced(choice_axiom,[])).
% 11.53/1.99  
% 11.53/1.99  fof(f42,plain,(
% 11.53/1.99    k2_relset_1(sK4,sK5,sK6) != sK5 & ! [X3] : ((k1_funct_1(sK6,sK7(X3)) = X3 & r2_hidden(sK7(X3),sK4)) | ~r2_hidden(X3,sK5)) & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) & v1_funct_2(sK6,sK4,sK5) & v1_funct_1(sK6)),
% 11.53/1.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6,sK7])],[f27,f41,f40])).
% 11.53/1.99  
% 11.53/1.99  fof(f67,plain,(
% 11.53/1.99    v1_funct_1(sK6)),
% 11.53/1.99    inference(cnf_transformation,[],[f42])).
% 11.53/1.99  
% 11.53/1.99  fof(f3,axiom,(
% 11.53/1.99    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 11.53/1.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.53/1.99  
% 11.53/1.99  fof(f16,plain,(
% 11.53/1.99    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 11.53/1.99    inference(ennf_transformation,[],[f3])).
% 11.53/1.99  
% 11.53/1.99  fof(f47,plain,(
% 11.53/1.99    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 11.53/1.99    inference(cnf_transformation,[],[f16])).
% 11.53/1.99  
% 11.53/1.99  fof(f69,plain,(
% 11.53/1.99    m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5)))),
% 11.53/1.99    inference(cnf_transformation,[],[f42])).
% 11.53/1.99  
% 11.53/1.99  fof(f5,axiom,(
% 11.53/1.99    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 11.53/1.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.53/1.99  
% 11.53/1.99  fof(f50,plain,(
% 11.53/1.99    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 11.53/1.99    inference(cnf_transformation,[],[f5])).
% 11.53/1.99  
% 11.53/1.99  fof(f71,plain,(
% 11.53/1.99    ( ! [X3] : (k1_funct_1(sK6,sK7(X3)) = X3 | ~r2_hidden(X3,sK5)) )),
% 11.53/1.99    inference(cnf_transformation,[],[f42])).
% 11.53/1.99  
% 11.53/1.99  fof(f10,axiom,(
% 11.53/1.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relat_1(X2) = k2_relset_1(X0,X1,X2))),
% 11.53/1.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.53/1.99  
% 11.53/1.99  fof(f23,plain,(
% 11.53/1.99    ! [X0,X1,X2] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 11.53/1.99    inference(ennf_transformation,[],[f10])).
% 11.53/1.99  
% 11.53/1.99  fof(f60,plain,(
% 11.53/1.99    ( ! [X2,X0,X1] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 11.53/1.99    inference(cnf_transformation,[],[f23])).
% 11.53/1.99  
% 11.53/1.99  fof(f72,plain,(
% 11.53/1.99    k2_relset_1(sK4,sK5,sK6) != sK5),
% 11.53/1.99    inference(cnf_transformation,[],[f42])).
% 11.53/1.99  
% 11.53/1.99  fof(f1,axiom,(
% 11.53/1.99    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 11.53/1.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.53/1.99  
% 11.53/1.99  fof(f15,plain,(
% 11.53/1.99    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 11.53/1.99    inference(ennf_transformation,[],[f1])).
% 11.53/1.99  
% 11.53/1.99  fof(f28,plain,(
% 11.53/1.99    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 11.53/1.99    inference(nnf_transformation,[],[f15])).
% 11.53/1.99  
% 11.53/1.99  fof(f29,plain,(
% 11.53/1.99    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 11.53/1.99    inference(rectify,[],[f28])).
% 11.53/1.99  
% 11.53/1.99  fof(f30,plain,(
% 11.53/1.99    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)))),
% 11.53/1.99    introduced(choice_axiom,[])).
% 11.53/1.99  
% 11.53/1.99  fof(f31,plain,(
% 11.53/1.99    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 11.53/1.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f29,f30])).
% 11.53/1.99  
% 11.53/1.99  fof(f43,plain,(
% 11.53/1.99    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r1_tarski(X0,X1)) )),
% 11.53/1.99    inference(cnf_transformation,[],[f31])).
% 11.53/1.99  
% 11.53/1.99  fof(f8,axiom,(
% 11.53/1.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 11.53/1.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.53/1.99  
% 11.53/1.99  fof(f14,plain,(
% 11.53/1.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v5_relat_1(X2,X1))),
% 11.53/1.99    inference(pure_predicate_removal,[],[f8])).
% 11.53/1.99  
% 11.53/1.99  fof(f21,plain,(
% 11.53/1.99    ! [X0,X1,X2] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 11.53/1.99    inference(ennf_transformation,[],[f14])).
% 11.53/1.99  
% 11.53/1.99  fof(f58,plain,(
% 11.53/1.99    ( ! [X2,X0,X1] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 11.53/1.99    inference(cnf_transformation,[],[f21])).
% 11.53/1.99  
% 11.53/1.99  fof(f4,axiom,(
% 11.53/1.99    ! [X0,X1] : (v1_relat_1(X1) => (v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)))),
% 11.53/1.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.53/1.99  
% 11.53/1.99  fof(f17,plain,(
% 11.53/1.99    ! [X0,X1] : ((v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 11.53/1.99    inference(ennf_transformation,[],[f4])).
% 11.53/1.99  
% 11.53/1.99  fof(f32,plain,(
% 11.53/1.99    ! [X0,X1] : (((v5_relat_1(X1,X0) | ~r1_tarski(k2_relat_1(X1),X0)) & (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 11.53/1.99    inference(nnf_transformation,[],[f17])).
% 11.53/1.99  
% 11.53/1.99  fof(f48,plain,(
% 11.53/1.99    ( ! [X0,X1] : (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 11.53/1.99    inference(cnf_transformation,[],[f32])).
% 11.53/1.99  
% 11.53/1.99  fof(f70,plain,(
% 11.53/1.99    ( ! [X3] : (r2_hidden(sK7(X3),sK4) | ~r2_hidden(X3,sK5)) )),
% 11.53/1.99    inference(cnf_transformation,[],[f42])).
% 11.53/1.99  
% 11.53/1.99  fof(f55,plain,(
% 11.53/1.99    ( ! [X0,X1] : (k2_relat_1(X0) = X1 | k1_funct_1(X0,sK2(X0,X1)) = sK1(X0,X1) | r2_hidden(sK1(X0,X1),X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 11.53/1.99    inference(cnf_transformation,[],[f38])).
% 11.53/1.99  
% 11.53/1.99  fof(f53,plain,(
% 11.53/1.99    ( ! [X6,X0,X5,X1] : (r2_hidden(X5,X1) | k1_funct_1(X0,X6) != X5 | ~r2_hidden(X6,k1_relat_1(X0)) | k2_relat_1(X0) != X1 | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 11.53/1.99    inference(cnf_transformation,[],[f38])).
% 11.53/1.99  
% 11.53/1.99  fof(f73,plain,(
% 11.53/1.99    ( ! [X6,X0,X1] : (r2_hidden(k1_funct_1(X0,X6),X1) | ~r2_hidden(X6,k1_relat_1(X0)) | k2_relat_1(X0) != X1 | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 11.53/1.99    inference(equality_resolution,[],[f53])).
% 11.53/1.99  
% 11.53/1.99  fof(f74,plain,(
% 11.53/1.99    ( ! [X6,X0] : (r2_hidden(k1_funct_1(X0,X6),k2_relat_1(X0)) | ~r2_hidden(X6,k1_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 11.53/1.99    inference(equality_resolution,[],[f73])).
% 11.53/1.99  
% 11.53/1.99  fof(f7,axiom,(
% 11.53/1.99    ! [X0,X1] : ~(r1_tarski(X1,X0) & r2_hidden(X0,X1))),
% 11.53/1.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.53/1.99  
% 11.53/1.99  fof(f20,plain,(
% 11.53/1.99    ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1))),
% 11.53/1.99    inference(ennf_transformation,[],[f7])).
% 11.53/1.99  
% 11.53/1.99  fof(f57,plain,(
% 11.53/1.99    ( ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1)) )),
% 11.53/1.99    inference(cnf_transformation,[],[f20])).
% 11.53/1.99  
% 11.53/1.99  fof(f56,plain,(
% 11.53/1.99    ( ! [X0,X3,X1] : (k2_relat_1(X0) = X1 | k1_funct_1(X0,X3) != sK1(X0,X1) | ~r2_hidden(X3,k1_relat_1(X0)) | ~r2_hidden(sK1(X0,X1),X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 11.53/1.99    inference(cnf_transformation,[],[f38])).
% 11.53/1.99  
% 11.53/1.99  fof(f2,axiom,(
% 11.53/1.99    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 11.53/1.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.53/1.99  
% 11.53/1.99  fof(f46,plain,(
% 11.53/1.99    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 11.53/1.99    inference(cnf_transformation,[],[f2])).
% 11.53/1.99  
% 11.53/1.99  fof(f68,plain,(
% 11.53/1.99    v1_funct_2(sK6,sK4,sK5)),
% 11.53/1.99    inference(cnf_transformation,[],[f42])).
% 11.53/1.99  
% 11.53/1.99  fof(f11,axiom,(
% 11.53/1.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 11.53/1.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.53/1.99  
% 11.53/1.99  fof(f24,plain,(
% 11.53/1.99    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 11.53/1.99    inference(ennf_transformation,[],[f11])).
% 11.53/1.99  
% 11.53/1.99  fof(f25,plain,(
% 11.53/1.99    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 11.53/1.99    inference(flattening,[],[f24])).
% 11.53/1.99  
% 11.53/1.99  fof(f39,plain,(
% 11.53/1.99    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 11.53/1.99    inference(nnf_transformation,[],[f25])).
% 11.53/1.99  
% 11.53/1.99  fof(f61,plain,(
% 11.53/1.99    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 11.53/1.99    inference(cnf_transformation,[],[f39])).
% 11.53/1.99  
% 11.53/1.99  fof(f9,axiom,(
% 11.53/1.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 11.53/1.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.53/1.99  
% 11.53/1.99  fof(f22,plain,(
% 11.53/1.99    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 11.53/1.99    inference(ennf_transformation,[],[f9])).
% 11.53/1.99  
% 11.53/1.99  fof(f59,plain,(
% 11.53/1.99    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 11.53/1.99    inference(cnf_transformation,[],[f22])).
% 11.53/1.99  
% 11.53/1.99  fof(f51,plain,(
% 11.53/1.99    ( ! [X0,X5,X1] : (r2_hidden(sK3(X0,X5),k1_relat_1(X0)) | ~r2_hidden(X5,X1) | k2_relat_1(X0) != X1 | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 11.53/1.99    inference(cnf_transformation,[],[f38])).
% 11.53/1.99  
% 11.53/1.99  fof(f76,plain,(
% 11.53/1.99    ( ! [X0,X5] : (r2_hidden(sK3(X0,X5),k1_relat_1(X0)) | ~r2_hidden(X5,k2_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 11.53/1.99    inference(equality_resolution,[],[f51])).
% 11.53/1.99  
% 11.53/1.99  fof(f52,plain,(
% 11.53/1.99    ( ! [X0,X5,X1] : (k1_funct_1(X0,sK3(X0,X5)) = X5 | ~r2_hidden(X5,X1) | k2_relat_1(X0) != X1 | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 11.53/1.99    inference(cnf_transformation,[],[f38])).
% 11.53/1.99  
% 11.53/1.99  fof(f75,plain,(
% 11.53/1.99    ( ! [X0,X5] : (k1_funct_1(X0,sK3(X0,X5)) = X5 | ~r2_hidden(X5,k2_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 11.53/1.99    inference(equality_resolution,[],[f52])).
% 11.53/1.99  
% 11.53/1.99  cnf(c_10,plain,
% 11.53/1.99      ( r2_hidden(sK2(X0,X1),k1_relat_1(X0))
% 11.53/1.99      | r2_hidden(sK1(X0,X1),X1)
% 11.53/1.99      | ~ v1_funct_1(X0)
% 11.53/1.99      | ~ v1_relat_1(X0)
% 11.53/1.99      | k2_relat_1(X0) = X1 ),
% 11.53/1.99      inference(cnf_transformation,[],[f54]) ).
% 11.53/1.99  
% 11.53/1.99  cnf(c_29,negated_conjecture,
% 11.53/1.99      ( v1_funct_1(sK6) ),
% 11.53/1.99      inference(cnf_transformation,[],[f67]) ).
% 11.53/1.99  
% 11.53/1.99  cnf(c_766,plain,
% 11.53/1.99      ( r2_hidden(sK2(X0,X1),k1_relat_1(X0))
% 11.53/1.99      | r2_hidden(sK1(X0,X1),X1)
% 11.53/1.99      | ~ v1_relat_1(X0)
% 11.53/1.99      | k2_relat_1(X0) = X1
% 11.53/1.99      | sK6 != X0 ),
% 11.53/1.99      inference(resolution_lifted,[status(thm)],[c_10,c_29]) ).
% 11.53/1.99  
% 11.53/1.99  cnf(c_767,plain,
% 11.53/1.99      ( r2_hidden(sK2(sK6,X0),k1_relat_1(sK6))
% 11.53/1.99      | r2_hidden(sK1(sK6,X0),X0)
% 11.53/1.99      | ~ v1_relat_1(sK6)
% 11.53/1.99      | k2_relat_1(sK6) = X0 ),
% 11.53/1.99      inference(unflattening,[status(thm)],[c_766]) ).
% 11.53/1.99  
% 11.53/1.99  cnf(c_1491,plain,
% 11.53/1.99      ( k2_relat_1(sK6) = X0
% 11.53/1.99      | r2_hidden(sK2(sK6,X0),k1_relat_1(sK6)) = iProver_top
% 11.53/1.99      | r2_hidden(sK1(sK6,X0),X0) = iProver_top
% 11.53/1.99      | v1_relat_1(sK6) != iProver_top ),
% 11.53/1.99      inference(predicate_to_equality,[status(thm)],[c_767]) ).
% 11.53/1.99  
% 11.53/1.99  cnf(c_768,plain,
% 11.53/1.99      ( k2_relat_1(sK6) = X0
% 11.53/1.99      | r2_hidden(sK2(sK6,X0),k1_relat_1(sK6)) = iProver_top
% 11.53/1.99      | r2_hidden(sK1(sK6,X0),X0) = iProver_top
% 11.53/1.99      | v1_relat_1(sK6) != iProver_top ),
% 11.53/1.99      inference(predicate_to_equality,[status(thm)],[c_767]) ).
% 11.53/1.99  
% 11.53/1.99  cnf(c_1183,plain,( X0 = X0 ),theory(equality) ).
% 11.53/1.99  
% 11.53/1.99  cnf(c_1660,plain,
% 11.53/1.99      ( k1_zfmisc_1(k2_zfmisc_1(sK4,sK5)) = k1_zfmisc_1(k2_zfmisc_1(sK4,sK5)) ),
% 11.53/1.99      inference(instantiation,[status(thm)],[c_1183]) ).
% 11.53/1.99  
% 11.53/1.99  cnf(c_4,plain,
% 11.53/1.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 11.53/1.99      | ~ v1_relat_1(X1)
% 11.53/1.99      | v1_relat_1(X0) ),
% 11.53/1.99      inference(cnf_transformation,[],[f47]) ).
% 11.53/1.99  
% 11.53/1.99  cnf(c_27,negated_conjecture,
% 11.53/1.99      ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) ),
% 11.53/1.99      inference(cnf_transformation,[],[f69]) ).
% 11.53/1.99  
% 11.53/1.99  cnf(c_467,plain,
% 11.53/1.99      ( ~ v1_relat_1(X0)
% 11.53/1.99      | v1_relat_1(X1)
% 11.53/1.99      | k1_zfmisc_1(k2_zfmisc_1(sK4,sK5)) != k1_zfmisc_1(X0)
% 11.53/1.99      | sK6 != X1 ),
% 11.53/1.99      inference(resolution_lifted,[status(thm)],[c_4,c_27]) ).
% 11.53/1.99  
% 11.53/1.99  cnf(c_468,plain,
% 11.53/1.99      ( ~ v1_relat_1(X0)
% 11.53/1.99      | v1_relat_1(sK6)
% 11.53/1.99      | k1_zfmisc_1(k2_zfmisc_1(sK4,sK5)) != k1_zfmisc_1(X0) ),
% 11.53/1.99      inference(unflattening,[status(thm)],[c_467]) ).
% 11.53/1.99  
% 11.53/1.99  cnf(c_1655,plain,
% 11.53/1.99      ( ~ v1_relat_1(k2_zfmisc_1(X0,X1))
% 11.53/1.99      | v1_relat_1(sK6)
% 11.53/1.99      | k1_zfmisc_1(k2_zfmisc_1(sK4,sK5)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1)) ),
% 11.53/1.99      inference(instantiation,[status(thm)],[c_468]) ).
% 11.53/1.99  
% 11.53/1.99  cnf(c_1710,plain,
% 11.53/1.99      ( ~ v1_relat_1(k2_zfmisc_1(sK4,sK5))
% 11.53/1.99      | v1_relat_1(sK6)
% 11.53/1.99      | k1_zfmisc_1(k2_zfmisc_1(sK4,sK5)) != k1_zfmisc_1(k2_zfmisc_1(sK4,sK5)) ),
% 11.53/1.99      inference(instantiation,[status(thm)],[c_1655]) ).
% 11.53/1.99  
% 11.53/1.99  cnf(c_1711,plain,
% 11.53/1.99      ( k1_zfmisc_1(k2_zfmisc_1(sK4,sK5)) != k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))
% 11.53/1.99      | v1_relat_1(k2_zfmisc_1(sK4,sK5)) != iProver_top
% 11.53/1.99      | v1_relat_1(sK6) = iProver_top ),
% 11.53/1.99      inference(predicate_to_equality,[status(thm)],[c_1710]) ).
% 11.53/1.99  
% 11.53/1.99  cnf(c_7,plain,
% 11.53/1.99      ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
% 11.53/1.99      inference(cnf_transformation,[],[f50]) ).
% 11.53/1.99  
% 11.53/1.99  cnf(c_1751,plain,
% 11.53/1.99      ( v1_relat_1(k2_zfmisc_1(sK4,sK5)) ),
% 11.53/1.99      inference(instantiation,[status(thm)],[c_7]) ).
% 11.53/1.99  
% 11.53/1.99  cnf(c_1752,plain,
% 11.53/1.99      ( v1_relat_1(k2_zfmisc_1(sK4,sK5)) = iProver_top ),
% 11.53/1.99      inference(predicate_to_equality,[status(thm)],[c_1751]) ).
% 11.53/1.99  
% 11.53/1.99  cnf(c_2692,plain,
% 11.53/1.99      ( r2_hidden(sK1(sK6,X0),X0) = iProver_top
% 11.53/1.99      | r2_hidden(sK2(sK6,X0),k1_relat_1(sK6)) = iProver_top
% 11.53/1.99      | k2_relat_1(sK6) = X0 ),
% 11.53/1.99      inference(global_propositional_subsumption,
% 11.53/1.99                [status(thm)],
% 11.53/1.99                [c_1491,c_768,c_1660,c_1711,c_1752]) ).
% 11.53/1.99  
% 11.53/1.99  cnf(c_2693,plain,
% 11.53/1.99      ( k2_relat_1(sK6) = X0
% 11.53/1.99      | r2_hidden(sK2(sK6,X0),k1_relat_1(sK6)) = iProver_top
% 11.53/1.99      | r2_hidden(sK1(sK6,X0),X0) = iProver_top ),
% 11.53/1.99      inference(renaming,[status(thm)],[c_2692]) ).
% 11.53/1.99  
% 11.53/1.99  cnf(c_25,negated_conjecture,
% 11.53/1.99      ( ~ r2_hidden(X0,sK5) | k1_funct_1(sK6,sK7(X0)) = X0 ),
% 11.53/1.99      inference(cnf_transformation,[],[f71]) ).
% 11.53/1.99  
% 11.53/1.99  cnf(c_1495,plain,
% 11.53/1.99      ( k1_funct_1(sK6,sK7(X0)) = X0 | r2_hidden(X0,sK5) != iProver_top ),
% 11.53/1.99      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 11.53/1.99  
% 11.53/1.99  cnf(c_2704,plain,
% 11.53/1.99      ( k1_funct_1(sK6,sK7(sK1(sK6,sK5))) = sK1(sK6,sK5)
% 11.53/1.99      | k2_relat_1(sK6) = sK5
% 11.53/1.99      | r2_hidden(sK2(sK6,sK5),k1_relat_1(sK6)) = iProver_top ),
% 11.53/1.99      inference(superposition,[status(thm)],[c_2693,c_1495]) ).
% 11.53/1.99  
% 11.53/1.99  cnf(c_17,plain,
% 11.53/1.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 11.53/1.99      | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
% 11.53/1.99      inference(cnf_transformation,[],[f60]) ).
% 11.53/1.99  
% 11.53/1.99  cnf(c_533,plain,
% 11.53/1.99      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
% 11.53/1.99      | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))
% 11.53/1.99      | sK6 != X2 ),
% 11.53/1.99      inference(resolution_lifted,[status(thm)],[c_17,c_27]) ).
% 11.53/1.99  
% 11.53/1.99  cnf(c_534,plain,
% 11.53/1.99      ( k2_relset_1(X0,X1,sK6) = k2_relat_1(sK6)
% 11.53/1.99      | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK4,sK5)) ),
% 11.53/1.99      inference(unflattening,[status(thm)],[c_533]) ).
% 11.53/1.99  
% 11.53/1.99  cnf(c_1673,plain,
% 11.53/1.99      ( k2_relset_1(sK4,sK5,sK6) = k2_relat_1(sK6) ),
% 11.53/1.99      inference(equality_resolution,[status(thm)],[c_534]) ).
% 11.53/1.99  
% 11.53/1.99  cnf(c_24,negated_conjecture,
% 11.53/1.99      ( k2_relset_1(sK4,sK5,sK6) != sK5 ),
% 11.53/1.99      inference(cnf_transformation,[],[f72]) ).
% 11.53/1.99  
% 11.53/1.99  cnf(c_1697,plain,
% 11.53/1.99      ( k2_relat_1(sK6) != sK5 ),
% 11.53/1.99      inference(demodulation,[status(thm)],[c_1673,c_24]) ).
% 11.53/1.99  
% 11.53/1.99  cnf(c_2763,plain,
% 11.53/1.99      ( k1_funct_1(sK6,sK7(sK1(sK6,sK5))) = sK1(sK6,sK5)
% 11.53/1.99      | r2_hidden(sK2(sK6,sK5),k1_relat_1(sK6)) = iProver_top ),
% 11.53/1.99      inference(global_propositional_subsumption,
% 11.53/1.99                [status(thm)],
% 11.53/1.99                [c_2704,c_1697]) ).
% 11.53/1.99  
% 11.53/1.99  cnf(c_2,plain,
% 11.53/1.99      ( ~ r2_hidden(X0,X1) | r2_hidden(X0,X2) | ~ r1_tarski(X1,X2) ),
% 11.53/1.99      inference(cnf_transformation,[],[f43]) ).
% 11.53/1.99  
% 11.53/1.99  cnf(c_1499,plain,
% 11.53/1.99      ( r2_hidden(X0,X1) != iProver_top
% 11.53/1.99      | r2_hidden(X0,X2) = iProver_top
% 11.53/1.99      | r1_tarski(X1,X2) != iProver_top ),
% 11.53/1.99      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 11.53/1.99  
% 11.53/1.99  cnf(c_2769,plain,
% 11.53/1.99      ( k1_funct_1(sK6,sK7(sK1(sK6,sK5))) = sK1(sK6,sK5)
% 11.53/1.99      | r2_hidden(sK2(sK6,sK5),X0) = iProver_top
% 11.53/1.99      | r1_tarski(k1_relat_1(sK6),X0) != iProver_top ),
% 11.53/1.99      inference(superposition,[status(thm)],[c_2763,c_1499]) ).
% 11.53/1.99  
% 11.53/1.99  cnf(c_8870,plain,
% 11.53/1.99      ( k1_funct_1(sK6,sK7(sK1(sK6,sK5))) = sK1(sK6,sK5)
% 11.53/1.99      | r2_hidden(sK2(sK6,sK5),X0) = iProver_top
% 11.53/1.99      | r1_tarski(X1,X0) != iProver_top
% 11.53/1.99      | r1_tarski(k1_relat_1(sK6),X1) != iProver_top ),
% 11.53/1.99      inference(superposition,[status(thm)],[c_2769,c_1499]) ).
% 11.53/1.99  
% 11.53/1.99  cnf(c_15,plain,
% 11.53/1.99      ( v5_relat_1(X0,X1)
% 11.53/1.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
% 11.53/1.99      inference(cnf_transformation,[],[f58]) ).
% 11.53/1.99  
% 11.53/1.99  cnf(c_6,plain,
% 11.53/1.99      ( ~ v5_relat_1(X0,X1)
% 11.53/1.99      | r1_tarski(k2_relat_1(X0),X1)
% 11.53/1.99      | ~ v1_relat_1(X0) ),
% 11.53/1.99      inference(cnf_transformation,[],[f48]) ).
% 11.53/1.99  
% 11.53/1.99  cnf(c_328,plain,
% 11.53/1.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 11.53/1.99      | r1_tarski(k2_relat_1(X0),X2)
% 11.53/1.99      | ~ v1_relat_1(X0) ),
% 11.53/1.99      inference(resolution,[status(thm)],[c_15,c_6]) ).
% 11.53/1.99  
% 11.53/1.99  cnf(c_482,plain,
% 11.53/1.99      ( r1_tarski(k2_relat_1(X0),X1)
% 11.53/1.99      | ~ v1_relat_1(X0)
% 11.53/1.99      | k1_zfmisc_1(k2_zfmisc_1(X2,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))
% 11.53/1.99      | sK6 != X0 ),
% 11.53/1.99      inference(resolution_lifted,[status(thm)],[c_328,c_27]) ).
% 11.53/1.99  
% 11.53/1.99  cnf(c_483,plain,
% 11.53/1.99      ( r1_tarski(k2_relat_1(sK6),X0)
% 11.53/1.99      | ~ v1_relat_1(sK6)
% 11.53/1.99      | k1_zfmisc_1(k2_zfmisc_1(X1,X0)) != k1_zfmisc_1(k2_zfmisc_1(sK4,sK5)) ),
% 11.53/1.99      inference(unflattening,[status(thm)],[c_482]) ).
% 11.53/1.99  
% 11.53/1.99  cnf(c_1833,plain,
% 11.53/1.99      ( r1_tarski(k2_relat_1(sK6),sK5)
% 11.53/1.99      | ~ v1_relat_1(sK6)
% 11.53/1.99      | k1_zfmisc_1(k2_zfmisc_1(sK4,sK5)) != k1_zfmisc_1(k2_zfmisc_1(sK4,sK5)) ),
% 11.53/1.99      inference(instantiation,[status(thm)],[c_483]) ).
% 11.53/1.99  
% 11.53/1.99  cnf(c_2000,plain,
% 11.53/1.99      ( ~ r2_hidden(sK1(sK6,sK5),sK5)
% 11.53/1.99      | k1_funct_1(sK6,sK7(sK1(sK6,sK5))) = sK1(sK6,sK5) ),
% 11.53/1.99      inference(instantiation,[status(thm)],[c_25]) ).
% 11.53/1.99  
% 11.53/1.99  cnf(c_26,negated_conjecture,
% 11.53/1.99      ( ~ r2_hidden(X0,sK5) | r2_hidden(sK7(X0),sK4) ),
% 11.53/1.99      inference(cnf_transformation,[],[f70]) ).
% 11.53/1.99  
% 11.53/1.99  cnf(c_1494,plain,
% 11.53/1.99      ( r2_hidden(X0,sK5) != iProver_top
% 11.53/1.99      | r2_hidden(sK7(X0),sK4) = iProver_top ),
% 11.53/1.99      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 11.53/1.99  
% 11.53/1.99  cnf(c_2371,plain,
% 11.53/1.99      ( r2_hidden(X0,sK5) != iProver_top
% 11.53/1.99      | r2_hidden(sK7(X0),X1) = iProver_top
% 11.53/1.99      | r1_tarski(sK4,X1) != iProver_top ),
% 11.53/1.99      inference(superposition,[status(thm)],[c_1494,c_1499]) ).
% 11.53/1.99  
% 11.53/1.99  cnf(c_9,plain,
% 11.53/1.99      ( r2_hidden(sK1(X0,X1),X1)
% 11.53/1.99      | ~ v1_funct_1(X0)
% 11.53/1.99      | ~ v1_relat_1(X0)
% 11.53/1.99      | k1_funct_1(X0,sK2(X0,X1)) = sK1(X0,X1)
% 11.53/1.99      | k2_relat_1(X0) = X1 ),
% 11.53/1.99      inference(cnf_transformation,[],[f55]) ).
% 11.53/1.99  
% 11.53/1.99  cnf(c_784,plain,
% 11.53/1.99      ( r2_hidden(sK1(X0,X1),X1)
% 11.53/1.99      | ~ v1_relat_1(X0)
% 11.53/1.99      | k1_funct_1(X0,sK2(X0,X1)) = sK1(X0,X1)
% 11.53/1.99      | k2_relat_1(X0) = X1
% 11.53/1.99      | sK6 != X0 ),
% 11.53/1.99      inference(resolution_lifted,[status(thm)],[c_9,c_29]) ).
% 11.53/1.99  
% 11.53/1.99  cnf(c_785,plain,
% 11.53/1.99      ( r2_hidden(sK1(sK6,X0),X0)
% 11.53/1.99      | ~ v1_relat_1(sK6)
% 11.53/1.99      | k1_funct_1(sK6,sK2(sK6,X0)) = sK1(sK6,X0)
% 11.53/1.99      | k2_relat_1(sK6) = X0 ),
% 11.53/1.99      inference(unflattening,[status(thm)],[c_784]) ).
% 11.53/1.99  
% 11.53/1.99  cnf(c_1490,plain,
% 11.53/1.99      ( k1_funct_1(sK6,sK2(sK6,X0)) = sK1(sK6,X0)
% 11.53/1.99      | k2_relat_1(sK6) = X0
% 11.53/1.99      | r2_hidden(sK1(sK6,X0),X0) = iProver_top
% 11.53/1.99      | v1_relat_1(sK6) != iProver_top ),
% 11.53/1.99      inference(predicate_to_equality,[status(thm)],[c_785]) ).
% 11.53/1.99  
% 11.53/1.99  cnf(c_786,plain,
% 11.53/1.99      ( k1_funct_1(sK6,sK2(sK6,X0)) = sK1(sK6,X0)
% 11.53/1.99      | k2_relat_1(sK6) = X0
% 11.53/1.99      | r2_hidden(sK1(sK6,X0),X0) = iProver_top
% 11.53/1.99      | v1_relat_1(sK6) != iProver_top ),
% 11.53/1.99      inference(predicate_to_equality,[status(thm)],[c_785]) ).
% 11.53/1.99  
% 11.53/1.99  cnf(c_2137,plain,
% 11.53/1.99      ( r2_hidden(sK1(sK6,X0),X0) = iProver_top
% 11.53/1.99      | k2_relat_1(sK6) = X0
% 11.53/1.99      | k1_funct_1(sK6,sK2(sK6,X0)) = sK1(sK6,X0) ),
% 11.53/1.99      inference(global_propositional_subsumption,
% 11.53/1.99                [status(thm)],
% 11.53/1.99                [c_1490,c_786,c_1660,c_1711,c_1752]) ).
% 11.53/1.99  
% 11.53/1.99  cnf(c_2138,plain,
% 11.53/1.99      ( k1_funct_1(sK6,sK2(sK6,X0)) = sK1(sK6,X0)
% 11.53/1.99      | k2_relat_1(sK6) = X0
% 11.53/1.99      | r2_hidden(sK1(sK6,X0),X0) = iProver_top ),
% 11.53/1.99      inference(renaming,[status(thm)],[c_2137]) ).
% 11.53/1.99  
% 11.53/1.99  cnf(c_2147,plain,
% 11.53/1.99      ( k1_funct_1(sK6,sK2(sK6,sK5)) = sK1(sK6,sK5)
% 11.53/1.99      | k1_funct_1(sK6,sK7(sK1(sK6,sK5))) = sK1(sK6,sK5)
% 11.53/1.99      | k2_relat_1(sK6) = sK5 ),
% 11.53/1.99      inference(superposition,[status(thm)],[c_2138,c_1495]) ).
% 11.53/1.99  
% 11.53/1.99  cnf(c_2636,plain,
% 11.53/1.99      ( k1_funct_1(sK6,sK7(sK1(sK6,sK5))) = sK1(sK6,sK5)
% 11.53/1.99      | k1_funct_1(sK6,sK2(sK6,sK5)) = sK1(sK6,sK5) ),
% 11.53/1.99      inference(global_propositional_subsumption,
% 11.53/1.99                [status(thm)],
% 11.53/1.99                [c_2147,c_1697]) ).
% 11.53/1.99  
% 11.53/1.99  cnf(c_2637,plain,
% 11.53/1.99      ( k1_funct_1(sK6,sK2(sK6,sK5)) = sK1(sK6,sK5)
% 11.53/1.99      | k1_funct_1(sK6,sK7(sK1(sK6,sK5))) = sK1(sK6,sK5) ),
% 11.53/1.99      inference(renaming,[status(thm)],[c_2636]) ).
% 11.53/1.99  
% 11.53/1.99  cnf(c_11,plain,
% 11.53/1.99      ( ~ r2_hidden(X0,k1_relat_1(X1))
% 11.53/1.99      | r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1))
% 11.53/1.99      | ~ v1_funct_1(X1)
% 11.53/1.99      | ~ v1_relat_1(X1) ),
% 11.53/1.99      inference(cnf_transformation,[],[f74]) ).
% 11.53/1.99  
% 11.53/1.99  cnf(c_832,plain,
% 11.53/1.99      ( ~ r2_hidden(X0,k1_relat_1(X1))
% 11.53/1.99      | r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1))
% 11.53/1.99      | ~ v1_relat_1(X1)
% 11.53/1.99      | sK6 != X1 ),
% 11.53/1.99      inference(resolution_lifted,[status(thm)],[c_11,c_29]) ).
% 11.53/1.99  
% 11.53/1.99  cnf(c_833,plain,
% 11.53/1.99      ( ~ r2_hidden(X0,k1_relat_1(sK6))
% 11.53/1.99      | r2_hidden(k1_funct_1(sK6,X0),k2_relat_1(sK6))
% 11.53/1.99      | ~ v1_relat_1(sK6) ),
% 11.53/1.99      inference(unflattening,[status(thm)],[c_832]) ).
% 11.53/1.99  
% 11.53/1.99  cnf(c_1487,plain,
% 11.53/1.99      ( r2_hidden(X0,k1_relat_1(sK6)) != iProver_top
% 11.53/1.99      | r2_hidden(k1_funct_1(sK6,X0),k2_relat_1(sK6)) = iProver_top
% 11.53/1.99      | v1_relat_1(sK6) != iProver_top ),
% 11.53/1.99      inference(predicate_to_equality,[status(thm)],[c_833]) ).
% 11.53/1.99  
% 11.53/1.99  cnf(c_834,plain,
% 11.53/1.99      ( r2_hidden(X0,k1_relat_1(sK6)) != iProver_top
% 11.53/1.99      | r2_hidden(k1_funct_1(sK6,X0),k2_relat_1(sK6)) = iProver_top
% 11.53/1.99      | v1_relat_1(sK6) != iProver_top ),
% 11.53/1.99      inference(predicate_to_equality,[status(thm)],[c_833]) ).
% 11.53/1.99  
% 11.53/1.99  cnf(c_1963,plain,
% 11.53/1.99      ( r2_hidden(k1_funct_1(sK6,X0),k2_relat_1(sK6)) = iProver_top
% 11.53/1.99      | r2_hidden(X0,k1_relat_1(sK6)) != iProver_top ),
% 11.53/1.99      inference(global_propositional_subsumption,
% 11.53/1.99                [status(thm)],
% 11.53/1.99                [c_1487,c_834,c_1660,c_1711,c_1752]) ).
% 11.53/1.99  
% 11.53/1.99  cnf(c_1964,plain,
% 11.53/1.99      ( r2_hidden(X0,k1_relat_1(sK6)) != iProver_top
% 11.53/1.99      | r2_hidden(k1_funct_1(sK6,X0),k2_relat_1(sK6)) = iProver_top ),
% 11.53/1.99      inference(renaming,[status(thm)],[c_1963]) ).
% 11.53/1.99  
% 11.53/1.99  cnf(c_2374,plain,
% 11.53/1.99      ( r2_hidden(X0,k1_relat_1(sK6)) != iProver_top
% 11.53/1.99      | r2_hidden(k1_funct_1(sK6,X0),X1) = iProver_top
% 11.53/1.99      | r1_tarski(k2_relat_1(sK6),X1) != iProver_top ),
% 11.53/1.99      inference(superposition,[status(thm)],[c_1964,c_1499]) ).
% 11.53/1.99  
% 11.53/1.99  cnf(c_14,plain,
% 11.53/1.99      ( ~ r2_hidden(X0,X1) | ~ r1_tarski(X1,X0) ),
% 11.53/1.99      inference(cnf_transformation,[],[f57]) ).
% 11.53/1.99  
% 11.53/1.99  cnf(c_1496,plain,
% 11.53/1.99      ( r2_hidden(X0,X1) != iProver_top
% 11.53/1.99      | r1_tarski(X1,X0) != iProver_top ),
% 11.53/1.99      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 11.53/1.99  
% 11.53/1.99  cnf(c_3687,plain,
% 11.53/1.99      ( r2_hidden(X0,k1_relat_1(sK6)) != iProver_top
% 11.53/1.99      | r1_tarski(X1,k1_funct_1(sK6,X0)) != iProver_top
% 11.53/1.99      | r1_tarski(k2_relat_1(sK6),X1) != iProver_top ),
% 11.53/1.99      inference(superposition,[status(thm)],[c_2374,c_1496]) ).
% 11.53/1.99  
% 11.53/1.99  cnf(c_8737,plain,
% 11.53/1.99      ( k1_funct_1(sK6,sK2(sK6,sK5)) = sK1(sK6,sK5)
% 11.53/1.99      | r2_hidden(sK7(sK1(sK6,sK5)),k1_relat_1(sK6)) != iProver_top
% 11.53/1.99      | r1_tarski(X0,sK1(sK6,sK5)) != iProver_top
% 11.53/1.99      | r1_tarski(k2_relat_1(sK6),X0) != iProver_top ),
% 11.53/1.99      inference(superposition,[status(thm)],[c_2637,c_3687]) ).
% 11.53/1.99  
% 11.53/1.99  cnf(c_2307,plain,
% 11.53/1.99      ( r2_hidden(sK1(sK6,sK5),sK5)
% 11.53/1.99      | ~ v1_relat_1(sK6)
% 11.53/1.99      | k1_funct_1(sK6,sK2(sK6,sK5)) = sK1(sK6,sK5)
% 11.53/1.99      | k2_relat_1(sK6) = sK5 ),
% 11.53/1.99      inference(instantiation,[status(thm)],[c_785]) ).
% 11.53/1.99  
% 11.53/1.99  cnf(c_2309,plain,
% 11.53/1.99      ( k1_funct_1(sK6,sK2(sK6,sK5)) = sK1(sK6,sK5)
% 11.53/1.99      | k2_relat_1(sK6) = sK5
% 11.53/1.99      | r2_hidden(sK1(sK6,sK5),sK5) = iProver_top
% 11.53/1.99      | v1_relat_1(sK6) != iProver_top ),
% 11.53/1.99      inference(predicate_to_equality,[status(thm)],[c_2307]) ).
% 11.53/1.99  
% 11.53/1.99  cnf(c_8,plain,
% 11.53/1.99      ( ~ r2_hidden(X0,k1_relat_1(X1))
% 11.53/1.99      | ~ r2_hidden(sK1(X1,X2),X2)
% 11.53/1.99      | ~ v1_funct_1(X1)
% 11.53/1.99      | ~ v1_relat_1(X1)
% 11.53/1.99      | sK1(X1,X2) != k1_funct_1(X1,X0)
% 11.53/1.99      | k2_relat_1(X1) = X2 ),
% 11.53/1.99      inference(cnf_transformation,[],[f56]) ).
% 11.53/1.99  
% 11.53/1.99  cnf(c_847,plain,
% 11.53/1.99      ( ~ r2_hidden(X0,k1_relat_1(X1))
% 11.53/1.99      | ~ r2_hidden(sK1(X1,X2),X2)
% 11.53/1.99      | ~ v1_relat_1(X1)
% 11.53/1.99      | sK1(X1,X2) != k1_funct_1(X1,X0)
% 11.53/1.99      | k2_relat_1(X1) = X2
% 11.53/1.99      | sK6 != X1 ),
% 11.53/1.99      inference(resolution_lifted,[status(thm)],[c_8,c_29]) ).
% 11.53/1.99  
% 11.53/1.99  cnf(c_848,plain,
% 11.53/1.99      ( ~ r2_hidden(X0,k1_relat_1(sK6))
% 11.53/1.99      | ~ r2_hidden(sK1(sK6,X1),X1)
% 11.53/1.99      | ~ v1_relat_1(sK6)
% 11.53/1.99      | sK1(sK6,X1) != k1_funct_1(sK6,X0)
% 11.53/1.99      | k2_relat_1(sK6) = X1 ),
% 11.53/1.99      inference(unflattening,[status(thm)],[c_847]) ).
% 11.53/1.99  
% 11.53/1.99  cnf(c_1486,plain,
% 11.53/1.99      ( sK1(sK6,X0) != k1_funct_1(sK6,X1)
% 11.53/1.99      | k2_relat_1(sK6) = X0
% 11.53/1.99      | r2_hidden(X1,k1_relat_1(sK6)) != iProver_top
% 11.53/1.99      | r2_hidden(sK1(sK6,X0),X0) != iProver_top
% 11.53/1.99      | v1_relat_1(sK6) != iProver_top ),
% 11.53/1.99      inference(predicate_to_equality,[status(thm)],[c_848]) ).
% 11.53/1.99  
% 11.53/1.99  cnf(c_849,plain,
% 11.53/1.99      ( sK1(sK6,X0) != k1_funct_1(sK6,X1)
% 11.53/1.99      | k2_relat_1(sK6) = X0
% 11.53/1.99      | r2_hidden(X1,k1_relat_1(sK6)) != iProver_top
% 11.53/1.99      | r2_hidden(sK1(sK6,X0),X0) != iProver_top
% 11.53/1.99      | v1_relat_1(sK6) != iProver_top ),
% 11.53/1.99      inference(predicate_to_equality,[status(thm)],[c_848]) ).
% 11.53/1.99  
% 11.53/1.99  cnf(c_2126,plain,
% 11.53/1.99      ( r2_hidden(sK1(sK6,X0),X0) != iProver_top
% 11.53/1.99      | r2_hidden(X1,k1_relat_1(sK6)) != iProver_top
% 11.53/1.99      | k2_relat_1(sK6) = X0
% 11.53/1.99      | sK1(sK6,X0) != k1_funct_1(sK6,X1) ),
% 11.53/1.99      inference(global_propositional_subsumption,
% 11.53/1.99                [status(thm)],
% 11.53/1.99                [c_1486,c_849,c_1660,c_1711,c_1752]) ).
% 11.53/1.99  
% 11.53/1.99  cnf(c_2127,plain,
% 11.53/1.99      ( sK1(sK6,X0) != k1_funct_1(sK6,X1)
% 11.53/1.99      | k2_relat_1(sK6) = X0
% 11.53/1.99      | r2_hidden(X1,k1_relat_1(sK6)) != iProver_top
% 11.53/1.99      | r2_hidden(sK1(sK6,X0),X0) != iProver_top ),
% 11.53/1.99      inference(renaming,[status(thm)],[c_2126]) ).
% 11.53/1.99  
% 11.53/1.99  cnf(c_2641,plain,
% 11.53/1.99      ( sK1(sK6,X0) != sK1(sK6,sK5)
% 11.53/1.99      | k1_funct_1(sK6,sK2(sK6,sK5)) = sK1(sK6,sK5)
% 11.53/1.99      | k2_relat_1(sK6) = X0
% 11.53/1.99      | r2_hidden(sK1(sK6,X0),X0) != iProver_top
% 11.53/1.99      | r2_hidden(sK7(sK1(sK6,sK5)),k1_relat_1(sK6)) != iProver_top ),
% 11.53/1.99      inference(superposition,[status(thm)],[c_2637,c_2127]) ).
% 11.53/1.99  
% 11.53/1.99  cnf(c_10210,plain,
% 11.53/1.99      ( k1_funct_1(sK6,sK2(sK6,sK5)) = sK1(sK6,sK5)
% 11.53/1.99      | k2_relat_1(sK6) = sK5
% 11.53/1.99      | r2_hidden(sK1(sK6,sK5),sK5) != iProver_top
% 11.53/1.99      | r2_hidden(sK7(sK1(sK6,sK5)),k1_relat_1(sK6)) != iProver_top ),
% 11.53/1.99      inference(equality_resolution,[status(thm)],[c_2641]) ).
% 11.53/1.99  
% 11.53/1.99  cnf(c_15781,plain,
% 11.53/1.99      ( k1_funct_1(sK6,sK2(sK6,sK5)) = sK1(sK6,sK5)
% 11.53/1.99      | r2_hidden(sK7(sK1(sK6,sK5)),k1_relat_1(sK6)) != iProver_top ),
% 11.53/1.99      inference(global_propositional_subsumption,
% 11.53/1.99                [status(thm)],
% 11.53/1.99                [c_8737,c_1660,c_1697,c_1711,c_1752,c_2309,c_10210]) ).
% 11.53/1.99  
% 11.53/1.99  cnf(c_15787,plain,
% 11.53/1.99      ( k1_funct_1(sK6,sK2(sK6,sK5)) = sK1(sK6,sK5)
% 11.53/1.99      | r2_hidden(sK1(sK6,sK5),sK5) != iProver_top
% 11.53/1.99      | r1_tarski(sK4,k1_relat_1(sK6)) != iProver_top ),
% 11.53/1.99      inference(superposition,[status(thm)],[c_2371,c_15781]) ).
% 11.53/1.99  
% 11.53/1.99  cnf(c_1989,plain,
% 11.53/1.99      ( ~ r2_hidden(sK1(sK6,sK5),sK5) | ~ r1_tarski(sK5,sK1(sK6,sK5)) ),
% 11.53/1.99      inference(instantiation,[status(thm)],[c_14]) ).
% 11.53/1.99  
% 11.53/1.99  cnf(c_2001,plain,
% 11.53/1.99      ( ~ r2_hidden(sK1(sK6,sK5),sK5)
% 11.53/1.99      | r2_hidden(sK7(sK1(sK6,sK5)),sK4) ),
% 11.53/1.99      inference(instantiation,[status(thm)],[c_26]) ).
% 11.53/1.99  
% 11.53/1.99  cnf(c_1185,plain,
% 11.53/1.99      ( ~ r1_tarski(X0,X1) | r1_tarski(X2,X1) | X2 != X0 ),
% 11.53/1.99      theory(equality) ).
% 11.53/1.99  
% 11.53/1.99  cnf(c_2668,plain,
% 11.53/1.99      ( ~ r1_tarski(X0,sK1(sK6,sK5))
% 11.53/1.99      | r1_tarski(sK5,sK1(sK6,sK5))
% 11.53/1.99      | sK5 != X0 ),
% 11.53/1.99      inference(instantiation,[status(thm)],[c_1185]) ).
% 11.53/1.99  
% 11.53/1.99  cnf(c_2670,plain,
% 11.53/1.99      ( r1_tarski(sK5,sK1(sK6,sK5))
% 11.53/1.99      | ~ r1_tarski(k1_xboole_0,sK1(sK6,sK5))
% 11.53/1.99      | sK5 != k1_xboole_0 ),
% 11.53/1.99      inference(instantiation,[status(thm)],[c_2668]) ).
% 11.53/1.99  
% 11.53/1.99  cnf(c_3,plain,
% 11.53/1.99      ( r1_tarski(k1_xboole_0,X0) ),
% 11.53/1.99      inference(cnf_transformation,[],[f46]) ).
% 11.53/1.99  
% 11.53/1.99  cnf(c_6302,plain,
% 11.53/1.99      ( r1_tarski(k1_xboole_0,sK1(sK6,sK5)) ),
% 11.53/1.99      inference(instantiation,[status(thm)],[c_3]) ).
% 11.53/1.99  
% 11.53/1.99  cnf(c_28,negated_conjecture,
% 11.53/1.99      ( v1_funct_2(sK6,sK4,sK5) ),
% 11.53/1.99      inference(cnf_transformation,[],[f68]) ).
% 11.53/1.99  
% 11.53/1.99  cnf(c_23,plain,
% 11.53/1.99      ( ~ v1_funct_2(X0,X1,X2)
% 11.53/1.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 11.53/1.99      | k1_relset_1(X1,X2,X0) = X1
% 11.53/1.99      | k1_xboole_0 = X2 ),
% 11.53/1.99      inference(cnf_transformation,[],[f61]) ).
% 11.53/1.99  
% 11.53/1.99  cnf(c_497,plain,
% 11.53/1.99      ( ~ v1_funct_2(X0,X1,X2)
% 11.53/1.99      | k1_relset_1(X1,X2,X0) = X1
% 11.53/1.99      | k1_zfmisc_1(k2_zfmisc_1(X1,X2)) != k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))
% 11.53/1.99      | sK6 != X0
% 11.53/1.99      | k1_xboole_0 = X2 ),
% 11.53/1.99      inference(resolution_lifted,[status(thm)],[c_23,c_27]) ).
% 11.53/1.99  
% 11.53/1.99  cnf(c_498,plain,
% 11.53/1.99      ( ~ v1_funct_2(sK6,X0,X1)
% 11.53/1.99      | k1_relset_1(X0,X1,sK6) = X0
% 11.53/1.99      | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))
% 11.53/1.99      | k1_xboole_0 = X1 ),
% 11.53/1.99      inference(unflattening,[status(thm)],[c_497]) ).
% 11.53/1.99  
% 11.53/1.99  cnf(c_904,plain,
% 11.53/1.99      ( k1_relset_1(X0,X1,sK6) = X0
% 11.53/1.99      | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))
% 11.53/1.99      | sK6 != sK6
% 11.53/1.99      | sK5 != X1
% 11.53/1.99      | sK4 != X0
% 11.53/1.99      | k1_xboole_0 = X1 ),
% 11.53/1.99      inference(resolution_lifted,[status(thm)],[c_28,c_498]) ).
% 11.53/1.99  
% 11.53/1.99  cnf(c_905,plain,
% 11.53/1.99      ( k1_relset_1(sK4,sK5,sK6) = sK4
% 11.53/1.99      | k1_zfmisc_1(k2_zfmisc_1(sK4,sK5)) != k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))
% 11.53/1.99      | k1_xboole_0 = sK5 ),
% 11.53/1.99      inference(unflattening,[status(thm)],[c_904]) ).
% 11.53/1.99  
% 11.53/1.99  cnf(c_974,plain,
% 11.53/1.99      ( k1_relset_1(sK4,sK5,sK6) = sK4 | k1_xboole_0 = sK5 ),
% 11.53/1.99      inference(equality_resolution_simp,[status(thm)],[c_905]) ).
% 11.53/1.99  
% 11.53/1.99  cnf(c_16,plain,
% 11.53/1.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 11.53/1.99      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 11.53/1.99      inference(cnf_transformation,[],[f59]) ).
% 11.53/1.99  
% 11.53/1.99  cnf(c_542,plain,
% 11.53/1.99      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 11.53/1.99      | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))
% 11.53/1.99      | sK6 != X2 ),
% 11.53/1.99      inference(resolution_lifted,[status(thm)],[c_16,c_27]) ).
% 11.53/1.99  
% 11.53/1.99  cnf(c_543,plain,
% 11.53/1.99      ( k1_relset_1(X0,X1,sK6) = k1_relat_1(sK6)
% 11.53/1.99      | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK4,sK5)) ),
% 11.53/1.99      inference(unflattening,[status(thm)],[c_542]) ).
% 11.53/1.99  
% 11.53/1.99  cnf(c_1684,plain,
% 11.53/1.99      ( k1_relset_1(sK4,sK5,sK6) = k1_relat_1(sK6) ),
% 11.53/1.99      inference(equality_resolution,[status(thm)],[c_543]) ).
% 11.53/1.99  
% 11.53/1.99  cnf(c_1821,plain,
% 11.53/1.99      ( k1_relat_1(sK6) = sK4 | sK5 = k1_xboole_0 ),
% 11.53/1.99      inference(superposition,[status(thm)],[c_974,c_1684]) ).
% 11.53/1.99  
% 11.53/1.99  cnf(c_15788,plain,
% 11.53/1.99      ( k1_funct_1(sK6,sK2(sK6,sK5)) = sK1(sK6,sK5)
% 11.53/1.99      | sK5 = k1_xboole_0
% 11.53/1.99      | r2_hidden(sK7(sK1(sK6,sK5)),sK4) != iProver_top ),
% 11.53/1.99      inference(superposition,[status(thm)],[c_1821,c_15781]) ).
% 11.53/1.99  
% 11.53/1.99  cnf(c_15802,plain,
% 11.53/1.99      ( ~ r2_hidden(sK7(sK1(sK6,sK5)),sK4)
% 11.53/1.99      | k1_funct_1(sK6,sK2(sK6,sK5)) = sK1(sK6,sK5)
% 11.53/1.99      | sK5 = k1_xboole_0 ),
% 11.53/1.99      inference(predicate_to_equality_rev,[status(thm)],[c_15788]) ).
% 11.53/1.99  
% 11.53/1.99  cnf(c_15925,plain,
% 11.53/1.99      ( k1_funct_1(sK6,sK2(sK6,sK5)) = sK1(sK6,sK5) ),
% 11.53/1.99      inference(global_propositional_subsumption,
% 11.53/1.99                [status(thm)],
% 11.53/1.99                [c_15787,c_1660,c_1697,c_1710,c_1751,c_1989,c_2001,
% 11.53/1.99                 c_2307,c_2670,c_6302,c_15802]) ).
% 11.53/1.99  
% 11.53/1.99  cnf(c_15933,plain,
% 11.53/1.99      ( r2_hidden(sK2(sK6,sK5),k1_relat_1(sK6)) != iProver_top
% 11.53/1.99      | r2_hidden(sK1(sK6,sK5),k2_relat_1(sK6)) = iProver_top ),
% 11.53/1.99      inference(superposition,[status(thm)],[c_15925,c_1964]) ).
% 11.53/1.99  
% 11.53/1.99  cnf(c_15982,plain,
% 11.53/1.99      ( k1_funct_1(sK6,sK7(sK1(sK6,sK5))) = sK1(sK6,sK5)
% 11.53/1.99      | r2_hidden(sK1(sK6,sK5),k2_relat_1(sK6)) = iProver_top ),
% 11.53/1.99      inference(superposition,[status(thm)],[c_2763,c_15933]) ).
% 11.53/1.99  
% 11.53/1.99  cnf(c_16042,plain,
% 11.53/1.99      ( r2_hidden(sK1(sK6,sK5),k2_relat_1(sK6))
% 11.53/1.99      | k1_funct_1(sK6,sK7(sK1(sK6,sK5))) = sK1(sK6,sK5) ),
% 11.53/1.99      inference(predicate_to_equality_rev,[status(thm)],[c_15982]) ).
% 11.53/1.99  
% 11.53/1.99  cnf(c_2842,plain,
% 11.53/1.99      ( ~ r2_hidden(sK1(sK6,sK5),X0)
% 11.53/1.99      | r2_hidden(sK1(sK6,sK5),X1)
% 11.53/1.99      | ~ r1_tarski(X0,X1) ),
% 11.53/1.99      inference(instantiation,[status(thm)],[c_2]) ).
% 11.53/1.99  
% 11.53/1.99  cnf(c_6613,plain,
% 11.53/1.99      ( ~ r2_hidden(sK1(sK6,sK5),X0)
% 11.53/1.99      | r2_hidden(sK1(sK6,sK5),sK5)
% 11.53/1.99      | ~ r1_tarski(X0,sK5) ),
% 11.53/1.99      inference(instantiation,[status(thm)],[c_2842]) ).
% 11.53/1.99  
% 11.53/1.99  cnf(c_33837,plain,
% 11.53/1.99      ( ~ r2_hidden(sK1(sK6,sK5),k2_relat_1(sK6))
% 11.53/1.99      | r2_hidden(sK1(sK6,sK5),sK5)
% 11.53/1.99      | ~ r1_tarski(k2_relat_1(sK6),sK5) ),
% 11.53/1.99      inference(instantiation,[status(thm)],[c_6613]) ).
% 11.53/1.99  
% 11.53/1.99  cnf(c_41922,plain,
% 11.53/1.99      ( k1_funct_1(sK6,sK7(sK1(sK6,sK5))) = sK1(sK6,sK5) ),
% 11.53/1.99      inference(global_propositional_subsumption,
% 11.53/1.99                [status(thm)],
% 11.53/1.99                [c_8870,c_1660,c_1710,c_1751,c_1833,c_2000,c_16042,
% 11.53/1.99                 c_33837]) ).
% 11.53/1.99  
% 11.53/1.99  cnf(c_41931,plain,
% 11.53/1.99      ( sK1(sK6,X0) != sK1(sK6,sK5)
% 11.53/1.99      | k2_relat_1(sK6) = X0
% 11.53/1.99      | r2_hidden(sK1(sK6,X0),X0) != iProver_top
% 11.53/1.99      | r2_hidden(sK7(sK1(sK6,sK5)),k1_relat_1(sK6)) != iProver_top ),
% 11.53/1.99      inference(superposition,[status(thm)],[c_41922,c_2127]) ).
% 11.53/1.99  
% 11.53/1.99  cnf(c_13,plain,
% 11.53/1.99      ( ~ r2_hidden(X0,k2_relat_1(X1))
% 11.53/1.99      | r2_hidden(sK3(X1,X0),k1_relat_1(X1))
% 11.53/1.99      | ~ v1_funct_1(X1)
% 11.53/1.99      | ~ v1_relat_1(X1) ),
% 11.53/1.99      inference(cnf_transformation,[],[f76]) ).
% 11.53/1.99  
% 11.53/1.99  cnf(c_802,plain,
% 11.53/1.99      ( ~ r2_hidden(X0,k2_relat_1(X1))
% 11.53/1.99      | r2_hidden(sK3(X1,X0),k1_relat_1(X1))
% 11.53/1.99      | ~ v1_relat_1(X1)
% 11.53/1.99      | sK6 != X1 ),
% 11.53/1.99      inference(resolution_lifted,[status(thm)],[c_13,c_29]) ).
% 11.53/1.99  
% 11.53/1.99  cnf(c_803,plain,
% 11.53/1.99      ( ~ r2_hidden(X0,k2_relat_1(sK6))
% 11.53/1.99      | r2_hidden(sK3(sK6,X0),k1_relat_1(sK6))
% 11.53/1.99      | ~ v1_relat_1(sK6) ),
% 11.53/1.99      inference(unflattening,[status(thm)],[c_802]) ).
% 11.53/1.99  
% 11.53/1.99  cnf(c_2857,plain,
% 11.53/1.99      ( r2_hidden(sK3(sK6,sK1(sK6,sK5)),k1_relat_1(sK6))
% 11.53/1.99      | ~ r2_hidden(sK1(sK6,sK5),k2_relat_1(sK6))
% 11.53/1.99      | ~ v1_relat_1(sK6) ),
% 11.53/1.99      inference(instantiation,[status(thm)],[c_803]) ).
% 11.53/1.99  
% 11.53/1.99  cnf(c_2860,plain,
% 11.53/1.99      ( r2_hidden(sK3(sK6,sK1(sK6,sK5)),k1_relat_1(sK6)) = iProver_top
% 11.53/1.99      | r2_hidden(sK1(sK6,sK5),k2_relat_1(sK6)) != iProver_top
% 11.53/1.99      | v1_relat_1(sK6) != iProver_top ),
% 11.53/1.99      inference(predicate_to_equality,[status(thm)],[c_2857]) ).
% 11.53/1.99  
% 11.53/1.99  cnf(c_41930,plain,
% 11.53/1.99      ( r2_hidden(sK1(sK6,sK5),k2_relat_1(sK6)) = iProver_top
% 11.53/1.99      | r2_hidden(sK7(sK1(sK6,sK5)),k1_relat_1(sK6)) != iProver_top ),
% 11.53/1.99      inference(superposition,[status(thm)],[c_41922,c_1964]) ).
% 11.53/1.99  
% 11.53/1.99  cnf(c_42820,plain,
% 11.53/1.99      ( r2_hidden(sK1(sK6,sK5),k2_relat_1(sK6)) = iProver_top
% 11.53/1.99      | r2_hidden(sK1(sK6,sK5),sK5) != iProver_top
% 11.53/1.99      | r1_tarski(sK4,k1_relat_1(sK6)) != iProver_top ),
% 11.53/1.99      inference(superposition,[status(thm)],[c_2371,c_41930]) ).
% 11.53/1.99  
% 11.53/1.99  cnf(c_97,plain,
% 11.53/1.99      ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
% 11.53/1.99      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 11.53/1.99  
% 11.53/1.99  cnf(c_99,plain,
% 11.53/1.99      ( r1_tarski(k1_xboole_0,k1_xboole_0) = iProver_top ),
% 11.53/1.99      inference(instantiation,[status(thm)],[c_97]) ).
% 11.53/1.99  
% 11.53/1.99  cnf(c_2002,plain,
% 11.53/1.99      ( r2_hidden(sK1(sK6,sK5),sK5) != iProver_top
% 11.53/1.99      | r2_hidden(sK7(sK1(sK6,sK5)),sK4) = iProver_top ),
% 11.53/1.99      inference(predicate_to_equality,[status(thm)],[c_2001]) ).
% 11.53/1.99  
% 11.53/1.99  cnf(c_9566,plain,
% 11.53/1.99      ( ~ r1_tarski(X0,X1) | r1_tarski(sK5,X1) | sK5 != X0 ),
% 11.53/1.99      inference(instantiation,[status(thm)],[c_1185]) ).
% 11.53/1.99  
% 11.53/1.99  cnf(c_9567,plain,
% 11.53/1.99      ( sK5 != X0
% 11.53/1.99      | r1_tarski(X0,X1) != iProver_top
% 11.53/1.99      | r1_tarski(sK5,X1) = iProver_top ),
% 11.53/1.99      inference(predicate_to_equality,[status(thm)],[c_9566]) ).
% 11.53/1.99  
% 11.53/1.99  cnf(c_9569,plain,
% 11.53/1.99      ( sK5 != k1_xboole_0
% 11.53/1.99      | r1_tarski(sK5,k1_xboole_0) = iProver_top
% 11.53/1.99      | r1_tarski(k1_xboole_0,k1_xboole_0) != iProver_top ),
% 11.53/1.99      inference(instantiation,[status(thm)],[c_9567]) ).
% 11.53/1.99  
% 11.53/1.99  cnf(c_1498,plain,
% 11.53/1.99      ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
% 11.53/1.99      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 11.53/1.99  
% 11.53/1.99  cnf(c_2701,plain,
% 11.53/1.99      ( k2_relat_1(sK6) = X0
% 11.53/1.99      | r2_hidden(sK2(sK6,X0),k1_relat_1(sK6)) = iProver_top
% 11.53/1.99      | r2_hidden(sK1(sK6,X0),X1) = iProver_top
% 11.53/1.99      | r1_tarski(X0,X1) != iProver_top ),
% 11.53/1.99      inference(superposition,[status(thm)],[c_2693,c_1499]) ).
% 11.53/1.99  
% 11.53/1.99  cnf(c_11369,plain,
% 11.53/1.99      ( k2_relat_1(sK6) = X0
% 11.53/1.99      | r2_hidden(sK2(sK6,X0),k1_relat_1(sK6)) = iProver_top
% 11.53/1.99      | r1_tarski(X0,X1) != iProver_top
% 11.53/1.99      | r1_tarski(X1,sK1(sK6,X0)) != iProver_top ),
% 11.53/1.99      inference(superposition,[status(thm)],[c_2701,c_1496]) ).
% 11.53/1.99  
% 11.53/1.99  cnf(c_15308,plain,
% 11.53/1.99      ( k2_relat_1(sK6) = X0
% 11.53/1.99      | r2_hidden(sK2(sK6,X0),k1_relat_1(sK6)) = iProver_top
% 11.53/1.99      | r1_tarski(X0,k1_xboole_0) != iProver_top ),
% 11.53/1.99      inference(superposition,[status(thm)],[c_1498,c_11369]) ).
% 11.53/1.99  
% 11.53/1.99  cnf(c_15977,plain,
% 11.53/1.99      ( k2_relat_1(sK6) = sK5
% 11.53/1.99      | r2_hidden(sK1(sK6,sK5),k2_relat_1(sK6)) = iProver_top
% 11.53/1.99      | r1_tarski(sK5,k1_xboole_0) != iProver_top ),
% 11.53/1.99      inference(superposition,[status(thm)],[c_15308,c_15933]) ).
% 11.53/1.99  
% 11.53/1.99  cnf(c_15980,plain,
% 11.53/1.99      ( k2_relat_1(sK6) = sK5
% 11.53/1.99      | r2_hidden(sK1(sK6,sK5),k2_relat_1(sK6)) = iProver_top
% 11.53/1.99      | r2_hidden(sK1(sK6,sK5),sK5) = iProver_top ),
% 11.53/1.99      inference(superposition,[status(thm)],[c_2693,c_15933]) ).
% 11.53/1.99  
% 11.53/1.99  cnf(c_42821,plain,
% 11.53/1.99      ( sK5 = k1_xboole_0
% 11.53/1.99      | r2_hidden(sK1(sK6,sK5),k2_relat_1(sK6)) = iProver_top
% 11.53/1.99      | r2_hidden(sK7(sK1(sK6,sK5)),sK4) != iProver_top ),
% 11.53/1.99      inference(superposition,[status(thm)],[c_1821,c_41930]) ).
% 11.53/1.99  
% 11.53/1.99  cnf(c_42837,plain,
% 11.53/1.99      ( r2_hidden(sK1(sK6,sK5),k2_relat_1(sK6)) = iProver_top ),
% 11.53/1.99      inference(global_propositional_subsumption,
% 11.53/1.99                [status(thm)],
% 11.53/1.99                [c_42820,c_99,c_1697,c_2002,c_9569,c_15977,c_15980,
% 11.53/1.99                 c_42821]) ).
% 11.53/1.99  
% 11.53/1.99  cnf(c_12,plain,
% 11.53/1.99      ( ~ r2_hidden(X0,k2_relat_1(X1))
% 11.53/1.99      | ~ v1_funct_1(X1)
% 11.53/1.99      | ~ v1_relat_1(X1)
% 11.53/1.99      | k1_funct_1(X1,sK3(X1,X0)) = X0 ),
% 11.53/1.99      inference(cnf_transformation,[],[f75]) ).
% 11.53/1.99  
% 11.53/1.99  cnf(c_817,plain,
% 11.53/1.99      ( ~ r2_hidden(X0,k2_relat_1(X1))
% 11.53/1.99      | ~ v1_relat_1(X1)
% 11.53/1.99      | k1_funct_1(X1,sK3(X1,X0)) = X0
% 11.53/1.99      | sK6 != X1 ),
% 11.53/1.99      inference(resolution_lifted,[status(thm)],[c_12,c_29]) ).
% 11.53/1.99  
% 11.53/1.99  cnf(c_818,plain,
% 11.53/1.99      ( ~ r2_hidden(X0,k2_relat_1(sK6))
% 11.53/1.99      | ~ v1_relat_1(sK6)
% 11.53/1.99      | k1_funct_1(sK6,sK3(sK6,X0)) = X0 ),
% 11.53/1.99      inference(unflattening,[status(thm)],[c_817]) ).
% 11.53/1.99  
% 11.53/1.99  cnf(c_1488,plain,
% 11.53/1.99      ( k1_funct_1(sK6,sK3(sK6,X0)) = X0
% 11.53/1.99      | r2_hidden(X0,k2_relat_1(sK6)) != iProver_top
% 11.53/1.99      | v1_relat_1(sK6) != iProver_top ),
% 11.53/1.99      inference(predicate_to_equality,[status(thm)],[c_818]) ).
% 11.53/1.99  
% 11.53/1.99  cnf(c_819,plain,
% 11.53/1.99      ( k1_funct_1(sK6,sK3(sK6,X0)) = X0
% 11.53/1.99      | r2_hidden(X0,k2_relat_1(sK6)) != iProver_top
% 11.53/1.99      | v1_relat_1(sK6) != iProver_top ),
% 11.53/1.99      inference(predicate_to_equality,[status(thm)],[c_818]) ).
% 11.53/1.99  
% 11.53/1.99  cnf(c_1954,plain,
% 11.53/1.99      ( r2_hidden(X0,k2_relat_1(sK6)) != iProver_top
% 11.53/1.99      | k1_funct_1(sK6,sK3(sK6,X0)) = X0 ),
% 11.53/1.99      inference(global_propositional_subsumption,
% 11.53/1.99                [status(thm)],
% 11.53/1.99                [c_1488,c_819,c_1660,c_1711,c_1752]) ).
% 11.53/1.99  
% 11.53/1.99  cnf(c_1955,plain,
% 11.53/1.99      ( k1_funct_1(sK6,sK3(sK6,X0)) = X0
% 11.53/1.99      | r2_hidden(X0,k2_relat_1(sK6)) != iProver_top ),
% 11.53/1.99      inference(renaming,[status(thm)],[c_1954]) ).
% 11.53/1.99  
% 11.53/1.99  cnf(c_42873,plain,
% 11.53/1.99      ( k1_funct_1(sK6,sK3(sK6,sK1(sK6,sK5))) = sK1(sK6,sK5) ),
% 11.53/1.99      inference(superposition,[status(thm)],[c_42837,c_1955]) ).
% 11.53/1.99  
% 11.53/1.99  cnf(c_43051,plain,
% 11.53/1.99      ( sK1(sK6,X0) != sK1(sK6,sK5)
% 11.53/1.99      | k2_relat_1(sK6) = X0
% 11.53/1.99      | r2_hidden(sK3(sK6,sK1(sK6,sK5)),k1_relat_1(sK6)) != iProver_top
% 11.53/1.99      | r2_hidden(sK1(sK6,X0),X0) != iProver_top ),
% 11.53/1.99      inference(superposition,[status(thm)],[c_42873,c_2127]) ).
% 11.53/1.99  
% 11.53/1.99  cnf(c_43252,plain,
% 11.53/1.99      ( r2_hidden(sK1(sK6,X0),X0) != iProver_top
% 11.53/1.99      | k2_relat_1(sK6) = X0
% 11.53/1.99      | sK1(sK6,X0) != sK1(sK6,sK5) ),
% 11.53/1.99      inference(global_propositional_subsumption,
% 11.53/1.99                [status(thm)],
% 11.53/1.99                [c_41931,c_99,c_1660,c_1697,c_1711,c_1752,c_2002,c_2860,
% 11.53/1.99                 c_9569,c_15977,c_15980,c_42821,c_43051]) ).
% 11.53/1.99  
% 11.53/1.99  cnf(c_43253,plain,
% 11.53/1.99      ( sK1(sK6,X0) != sK1(sK6,sK5)
% 11.53/1.99      | k2_relat_1(sK6) = X0
% 11.53/1.99      | r2_hidden(sK1(sK6,X0),X0) != iProver_top ),
% 11.53/1.99      inference(renaming,[status(thm)],[c_43252]) ).
% 11.53/1.99  
% 11.53/1.99  cnf(c_43261,plain,
% 11.53/1.99      ( k2_relat_1(sK6) = sK5
% 11.53/1.99      | r2_hidden(sK1(sK6,sK5),sK5) != iProver_top ),
% 11.53/1.99      inference(equality_resolution,[status(thm)],[c_43253]) ).
% 11.53/1.99  
% 11.53/1.99  cnf(c_33839,plain,
% 11.53/1.99      ( r2_hidden(sK1(sK6,sK5),k2_relat_1(sK6)) != iProver_top
% 11.53/1.99      | r2_hidden(sK1(sK6,sK5),sK5) = iProver_top
% 11.53/1.99      | r1_tarski(k2_relat_1(sK6),sK5) != iProver_top ),
% 11.53/1.99      inference(predicate_to_equality,[status(thm)],[c_33837]) ).
% 11.53/1.99  
% 11.53/1.99  cnf(c_1834,plain,
% 11.53/1.99      ( k1_zfmisc_1(k2_zfmisc_1(sK4,sK5)) != k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))
% 11.53/1.99      | r1_tarski(k2_relat_1(sK6),sK5) = iProver_top
% 11.53/1.99      | v1_relat_1(sK6) != iProver_top ),
% 11.53/1.99      inference(predicate_to_equality,[status(thm)],[c_1833]) ).
% 11.53/1.99  
% 11.53/1.99  cnf(contradiction,plain,
% 11.53/1.99      ( $false ),
% 11.53/1.99      inference(minisat,
% 11.53/1.99                [status(thm)],
% 11.53/1.99                [c_43261,c_42837,c_33839,c_1834,c_1752,c_1711,c_1697,
% 11.53/1.99                 c_1660]) ).
% 11.53/1.99  
% 11.53/1.99  
% 11.53/1.99  % SZS output end CNFRefutation for theBenchmark.p
% 11.53/1.99  
% 11.53/1.99  ------                               Statistics
% 11.53/1.99  
% 11.53/1.99  ------ General
% 11.53/1.99  
% 11.53/1.99  abstr_ref_over_cycles:                  0
% 11.53/1.99  abstr_ref_under_cycles:                 0
% 11.53/1.99  gc_basic_clause_elim:                   0
% 11.53/1.99  forced_gc_time:                         0
% 11.53/1.99  parsing_time:                           0.012
% 11.53/1.99  unif_index_cands_time:                  0.
% 11.53/1.99  unif_index_add_time:                    0.
% 11.53/1.99  orderings_time:                         0.
% 11.53/1.99  out_proof_time:                         0.016
% 11.53/1.99  total_time:                             1.063
% 11.53/1.99  num_of_symbols:                         54
% 11.53/1.99  num_of_terms:                           16560
% 11.53/1.99  
% 11.53/1.99  ------ Preprocessing
% 11.53/1.99  
% 11.53/1.99  num_of_splits:                          0
% 11.53/1.99  num_of_split_atoms:                     0
% 11.53/1.99  num_of_reused_defs:                     0
% 11.53/1.99  num_eq_ax_congr_red:                    30
% 11.53/1.99  num_of_sem_filtered_clauses:            1
% 11.53/1.99  num_of_subtypes:                        0
% 11.53/1.99  monotx_restored_types:                  0
% 11.53/1.99  sat_num_of_epr_types:                   0
% 11.53/1.99  sat_num_of_non_cyclic_types:            0
% 11.53/1.99  sat_guarded_non_collapsed_types:        0
% 11.53/1.99  num_pure_diseq_elim:                    0
% 11.53/1.99  simp_replaced_by:                       0
% 11.53/1.99  res_preprocessed:                       127
% 11.53/1.99  prep_upred:                             0
% 11.53/1.99  prep_unflattend:                        80
% 11.53/1.99  smt_new_axioms:                         0
% 11.53/1.99  pred_elim_cands:                        3
% 11.53/1.99  pred_elim:                              4
% 11.53/1.99  pred_elim_cl:                           8
% 11.53/1.99  pred_elim_cycles:                       8
% 11.53/1.99  merged_defs:                            0
% 11.53/1.99  merged_defs_ncl:                        0
% 11.53/1.99  bin_hyper_res:                          0
% 11.53/1.99  prep_cycles:                            4
% 11.53/1.99  pred_elim_time:                         0.013
% 11.53/1.99  splitting_time:                         0.
% 11.53/1.99  sem_filter_time:                        0.
% 11.53/1.99  monotx_time:                            0.013
% 11.53/1.99  subtype_inf_time:                       0.
% 11.53/1.99  
% 11.53/1.99  ------ Problem properties
% 11.53/1.99  
% 11.53/1.99  clauses:                                22
% 11.53/1.99  conjectures:                            3
% 11.53/1.99  epr:                                    3
% 11.53/1.99  horn:                                   17
% 11.53/1.99  ground:                                 4
% 11.53/1.99  unary:                                  3
% 11.53/1.99  binary:                                 8
% 11.53/1.99  lits:                                   57
% 11.53/1.99  lits_eq:                                23
% 11.53/1.99  fd_pure:                                0
% 11.53/1.99  fd_pseudo:                              0
% 11.53/1.99  fd_cond:                                3
% 11.53/1.99  fd_pseudo_cond:                         0
% 11.53/1.99  ac_symbols:                             0
% 11.53/1.99  
% 11.53/1.99  ------ Propositional Solver
% 11.53/1.99  
% 11.53/1.99  prop_solver_calls:                      34
% 11.53/1.99  prop_fast_solver_calls:                 1687
% 11.53/1.99  smt_solver_calls:                       0
% 11.53/1.99  smt_fast_solver_calls:                  0
% 11.53/1.99  prop_num_of_clauses:                    11958
% 11.53/1.99  prop_preprocess_simplified:             11664
% 11.53/1.99  prop_fo_subsumed:                       37
% 11.53/1.99  prop_solver_time:                       0.
% 11.53/1.99  smt_solver_time:                        0.
% 11.53/1.99  smt_fast_solver_time:                   0.
% 11.53/1.99  prop_fast_solver_time:                  0.
% 11.53/1.99  prop_unsat_core_time:                   0.001
% 11.53/1.99  
% 11.53/1.99  ------ QBF
% 11.53/1.99  
% 11.53/1.99  qbf_q_res:                              0
% 11.53/1.99  qbf_num_tautologies:                    0
% 11.53/1.99  qbf_prep_cycles:                        0
% 11.53/1.99  
% 11.53/1.99  ------ BMC1
% 11.53/1.99  
% 11.53/1.99  bmc1_current_bound:                     -1
% 11.53/1.99  bmc1_last_solved_bound:                 -1
% 11.53/1.99  bmc1_unsat_core_size:                   -1
% 11.53/1.99  bmc1_unsat_core_parents_size:           -1
% 11.53/1.99  bmc1_merge_next_fun:                    0
% 11.53/1.99  bmc1_unsat_core_clauses_time:           0.
% 11.53/1.99  
% 11.53/1.99  ------ Instantiation
% 11.53/1.99  
% 11.53/1.99  inst_num_of_clauses:                    1811
% 11.53/1.99  inst_num_in_passive:                    411
% 11.53/1.99  inst_num_in_active:                     911
% 11.53/1.99  inst_num_in_unprocessed:                489
% 11.53/1.99  inst_num_of_loops:                      1390
% 11.53/1.99  inst_num_of_learning_restarts:          0
% 11.53/1.99  inst_num_moves_active_passive:          471
% 11.53/1.99  inst_lit_activity:                      0
% 11.53/1.99  inst_lit_activity_moves:                0
% 11.53/1.99  inst_num_tautologies:                   0
% 11.53/1.99  inst_num_prop_implied:                  0
% 11.53/1.99  inst_num_existing_simplified:           0
% 11.53/1.99  inst_num_eq_res_simplified:             0
% 11.53/1.99  inst_num_child_elim:                    0
% 11.53/1.99  inst_num_of_dismatching_blockings:      681
% 11.53/1.99  inst_num_of_non_proper_insts:           1884
% 11.53/1.99  inst_num_of_duplicates:                 0
% 11.53/1.99  inst_inst_num_from_inst_to_res:         0
% 11.53/1.99  inst_dismatching_checking_time:         0.
% 11.53/1.99  
% 11.53/1.99  ------ Resolution
% 11.53/1.99  
% 11.53/1.99  res_num_of_clauses:                     0
% 11.53/1.99  res_num_in_passive:                     0
% 11.53/1.99  res_num_in_active:                      0
% 11.53/1.99  res_num_of_loops:                       131
% 11.53/1.99  res_forward_subset_subsumed:            135
% 11.53/1.99  res_backward_subset_subsumed:           0
% 11.53/1.99  res_forward_subsumed:                   0
% 11.53/1.99  res_backward_subsumed:                  1
% 11.53/1.99  res_forward_subsumption_resolution:     0
% 11.53/1.99  res_backward_subsumption_resolution:    0
% 11.53/1.99  res_clause_to_clause_subsumption:       9340
% 11.53/1.99  res_orphan_elimination:                 0
% 11.53/1.99  res_tautology_del:                      317
% 11.53/1.99  res_num_eq_res_simplified:              1
% 11.53/1.99  res_num_sel_changes:                    0
% 11.53/1.99  res_moves_from_active_to_pass:          0
% 11.53/1.99  
% 11.53/1.99  ------ Superposition
% 11.53/1.99  
% 11.53/1.99  sup_time_total:                         0.
% 11.53/1.99  sup_time_generating:                    0.
% 11.53/1.99  sup_time_sim_full:                      0.
% 11.53/1.99  sup_time_sim_immed:                     0.
% 11.53/1.99  
% 11.53/1.99  sup_num_of_clauses:                     2351
% 11.53/1.99  sup_num_in_active:                      258
% 11.53/1.99  sup_num_in_passive:                     2093
% 11.53/1.99  sup_num_of_loops:                       276
% 11.53/1.99  sup_fw_superposition:                   1895
% 11.53/1.99  sup_bw_superposition:                   1320
% 11.53/1.99  sup_immediate_simplified:               473
% 11.53/1.99  sup_given_eliminated:                   0
% 11.53/1.99  comparisons_done:                       0
% 11.53/1.99  comparisons_avoided:                    66
% 11.53/1.99  
% 11.53/1.99  ------ Simplifications
% 11.53/1.99  
% 11.53/1.99  
% 11.53/1.99  sim_fw_subset_subsumed:                 118
% 11.53/1.99  sim_bw_subset_subsumed:                 298
% 11.53/1.99  sim_fw_subsumed:                        47
% 11.53/1.99  sim_bw_subsumed:                        91
% 11.53/1.99  sim_fw_subsumption_res:                 1
% 11.53/1.99  sim_bw_subsumption_res:                 0
% 11.53/1.99  sim_tautology_del:                      1
% 11.53/1.99  sim_eq_tautology_del:                   276
% 11.53/1.99  sim_eq_res_simp:                        0
% 11.53/1.99  sim_fw_demodulated:                     0
% 11.53/1.99  sim_bw_demodulated:                     3
% 11.53/1.99  sim_light_normalised:                   92
% 11.53/1.99  sim_joinable_taut:                      0
% 11.53/1.99  sim_joinable_simp:                      0
% 11.53/1.99  sim_ac_normalised:                      0
% 11.53/1.99  sim_smt_subsumption:                    0
% 11.53/1.99  
%------------------------------------------------------------------------------
