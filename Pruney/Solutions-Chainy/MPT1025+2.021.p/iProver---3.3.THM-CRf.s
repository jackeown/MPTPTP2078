%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:08:04 EST 2020

% Result     : Theorem 3.27s
% Output     : CNFRefutation 3.27s
% Verified   : 
% Statistics : Number of formulae       :  186 ( 989 expanded)
%              Number of clauses        :  109 ( 306 expanded)
%              Number of leaves         :   19 ( 231 expanded)
%              Depth                    :   23
%              Number of atoms          :  668 (5161 expanded)
%              Number of equality atoms :  248 (1148 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal clause size      :   16 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(X0,k9_relat_1(X2,X1))
      <=> ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(k4_tarski(X3,X0),X2)
            & r2_hidden(X3,k1_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k9_relat_1(X2,X1))
      <=> ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(k4_tarski(X3,X0),X2)
            & r2_hidden(X3,k1_relat_1(X2)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,k9_relat_1(X2,X1))
          | ! [X3] :
              ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(k4_tarski(X3,X0),X2)
              | ~ r2_hidden(X3,k1_relat_1(X2)) ) )
        & ( ? [X3] :
              ( r2_hidden(X3,X1)
              & r2_hidden(k4_tarski(X3,X0),X2)
              & r2_hidden(X3,k1_relat_1(X2)) )
          | ~ r2_hidden(X0,k9_relat_1(X2,X1)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(nnf_transformation,[],[f19])).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,k9_relat_1(X2,X1))
          | ! [X3] :
              ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(k4_tarski(X3,X0),X2)
              | ~ r2_hidden(X3,k1_relat_1(X2)) ) )
        & ( ? [X4] :
              ( r2_hidden(X4,X1)
              & r2_hidden(k4_tarski(X4,X0),X2)
              & r2_hidden(X4,k1_relat_1(X2)) )
          | ~ r2_hidden(X0,k9_relat_1(X2,X1)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(rectify,[],[f34])).

fof(f36,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( r2_hidden(X4,X1)
          & r2_hidden(k4_tarski(X4,X0),X2)
          & r2_hidden(X4,k1_relat_1(X2)) )
     => ( r2_hidden(sK0(X0,X1,X2),X1)
        & r2_hidden(k4_tarski(sK0(X0,X1,X2),X0),X2)
        & r2_hidden(sK0(X0,X1,X2),k1_relat_1(X2)) ) ) ),
    introduced(choice_axiom,[])).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,k9_relat_1(X2,X1))
          | ! [X3] :
              ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(k4_tarski(X3,X0),X2)
              | ~ r2_hidden(X3,k1_relat_1(X2)) ) )
        & ( ( r2_hidden(sK0(X0,X1,X2),X1)
            & r2_hidden(k4_tarski(sK0(X0,X1,X2),X0),X2)
            & r2_hidden(sK0(X0,X1,X2),k1_relat_1(X2)) )
          | ~ r2_hidden(X0,k9_relat_1(X2,X1)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f35,f36])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK0(X0,X1,X2),k1_relat_1(X2))
      | ~ r2_hidden(X0,k9_relat_1(X2,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f13,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
     => ! [X4] :
          ~ ( ! [X5] :
                ( m1_subset_1(X5,X0)
               => ~ ( k1_funct_1(X3,X5) = X4
                    & r2_hidden(X5,X2) ) )
            & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f14,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X3,X0,X1)
          & v1_funct_1(X3) )
       => ! [X4] :
            ~ ( ! [X5] :
                  ( m1_subset_1(X5,X0)
                 => ~ ( k1_funct_1(X3,X5) = X4
                      & r2_hidden(X5,X2) ) )
              & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2)) ) ) ),
    inference(negated_conjecture,[],[f13])).

fof(f32,plain,(
    ? [X0,X1,X2,X3] :
      ( ? [X4] :
          ( ! [X5] :
              ( k1_funct_1(X3,X5) != X4
              | ~ r2_hidden(X5,X2)
              | ~ m1_subset_1(X5,X0) )
          & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2)) )
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X3,X0,X1)
      & v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f33,plain,(
    ? [X0,X1,X2,X3] :
      ( ? [X4] :
          ( ! [X5] :
              ( k1_funct_1(X3,X5) != X4
              | ~ r2_hidden(X5,X2)
              | ~ m1_subset_1(X5,X0) )
          & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2)) )
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X3,X0,X1)
      & v1_funct_1(X3) ) ),
    inference(flattening,[],[f32])).

fof(f48,plain,(
    ! [X2,X0,X3,X1] :
      ( ? [X4] :
          ( ! [X5] :
              ( k1_funct_1(X3,X5) != X4
              | ~ r2_hidden(X5,X2)
              | ~ m1_subset_1(X5,X0) )
          & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2)) )
     => ( ! [X5] :
            ( k1_funct_1(X3,X5) != sK8
            | ~ r2_hidden(X5,X2)
            | ~ m1_subset_1(X5,X0) )
        & r2_hidden(sK8,k7_relset_1(X0,X1,X3,X2)) ) ) ),
    introduced(choice_axiom,[])).

fof(f47,plain,
    ( ? [X0,X1,X2,X3] :
        ( ? [X4] :
            ( ! [X5] :
                ( k1_funct_1(X3,X5) != X4
                | ~ r2_hidden(X5,X2)
                | ~ m1_subset_1(X5,X0) )
            & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2)) )
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
   => ( ? [X4] :
          ( ! [X5] :
              ( k1_funct_1(sK7,X5) != X4
              | ~ r2_hidden(X5,sK6)
              | ~ m1_subset_1(X5,sK4) )
          & r2_hidden(X4,k7_relset_1(sK4,sK5,sK7,sK6)) )
      & m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5)))
      & v1_funct_2(sK7,sK4,sK5)
      & v1_funct_1(sK7) ) ),
    introduced(choice_axiom,[])).

fof(f49,plain,
    ( ! [X5] :
        ( k1_funct_1(sK7,X5) != sK8
        | ~ r2_hidden(X5,sK6)
        | ~ m1_subset_1(X5,sK4) )
    & r2_hidden(sK8,k7_relset_1(sK4,sK5,sK7,sK6))
    & m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5)))
    & v1_funct_2(sK7,sK4,sK5)
    & v1_funct_1(sK7) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6,sK7,sK8])],[f33,f48,f47])).

fof(f79,plain,(
    m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) ),
    inference(cnf_transformation,[],[f49])).

fof(f11,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1,X2,X3] :
      ( k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f70,plain,(
    ! [X2,X0,X3,X1] :
      ( k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f80,plain,(
    r2_hidden(sK8,k7_relset_1(sK4,sK5,sK7,sK6)) ),
    inference(cnf_transformation,[],[f49])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k4_tarski(sK0(X0,X1,X2),X0),X2)
      | ~ r2_hidden(X0,k9_relat_1(X2,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f24])).

fof(f44,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(k4_tarski(X0,X1),X2)
          | k1_funct_1(X2,X0) != X1
          | ~ r2_hidden(X0,k1_relat_1(X2)) )
        & ( ( k1_funct_1(X2,X0) = X1
            & r2_hidden(X0,k1_relat_1(X2)) )
          | ~ r2_hidden(k4_tarski(X0,X1),X2) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(nnf_transformation,[],[f25])).

fof(f45,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(k4_tarski(X0,X1),X2)
          | k1_funct_1(X2,X0) != X1
          | ~ r2_hidden(X0,k1_relat_1(X2)) )
        & ( ( k1_funct_1(X2,X0) = X1
            & r2_hidden(X0,k1_relat_1(X2)) )
          | ~ r2_hidden(k4_tarski(X0,X1),X2) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f44])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( k1_funct_1(X2,X0) = X1
      | ~ r2_hidden(k4_tarski(X0,X1),X2)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f77,plain,(
    v1_funct_1(sK7) ),
    inference(cnf_transformation,[],[f49])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f5,axiom,(
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

fof(f20,plain,(
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
    inference(ennf_transformation,[],[f5])).

fof(f21,plain,(
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
    inference(flattening,[],[f20])).

fof(f38,plain,(
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
    inference(nnf_transformation,[],[f21])).

fof(f39,plain,(
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
    inference(rectify,[],[f38])).

fof(f42,plain,(
    ! [X5,X0] :
      ( ? [X7] :
          ( k1_funct_1(X0,X7) = X5
          & r2_hidden(X7,k1_relat_1(X0)) )
     => ( k1_funct_1(X0,sK3(X0,X5)) = X5
        & r2_hidden(sK3(X0,X5),k1_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f41,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( k1_funct_1(X0,X4) = X2
          & r2_hidden(X4,k1_relat_1(X0)) )
     => ( k1_funct_1(X0,sK2(X0,X1)) = X2
        & r2_hidden(sK2(X0,X1),k1_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f40,plain,(
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

fof(f43,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f39,f42,f41,f40])).

fof(f59,plain,(
    ! [X6,X0,X5,X1] :
      ( r2_hidden(X5,X1)
      | k1_funct_1(X0,X6) != X5
      | ~ r2_hidden(X6,k1_relat_1(X0))
      | k2_relat_1(X0) != X1
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f82,plain,(
    ! [X6,X0,X1] :
      ( r2_hidden(k1_funct_1(X0,X6),X1)
      | ~ r2_hidden(X6,k1_relat_1(X0))
      | k2_relat_1(X0) != X1
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f59])).

fof(f83,plain,(
    ! [X6,X0] :
      ( r2_hidden(k1_funct_1(X0,X6),k2_relat_1(X0))
      | ~ r2_hidden(X6,k1_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f82])).

fof(f58,plain,(
    ! [X0,X5,X1] :
      ( k1_funct_1(X0,sK3(X0,X5)) = X5
      | ~ r2_hidden(X5,X1)
      | k2_relat_1(X0) != X1
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f84,plain,(
    ! [X0,X5] :
      ( k1_funct_1(X0,sK3(X0,X5)) = X5
      | ~ r2_hidden(X5,k2_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f58])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k4_tarski(X0,X1),X2)
      | k1_funct_1(X2,X0) != X1
      | ~ r2_hidden(X0,k1_relat_1(X2))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f86,plain,(
    ! [X2,X0] :
      ( r2_hidden(k4_tarski(X0,k1_funct_1(X2,X0)),X2)
      | ~ r2_hidden(X0,k1_relat_1(X2))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(equality_resolution,[],[f66])).

fof(f57,plain,(
    ! [X0,X5,X1] :
      ( r2_hidden(sK3(X0,X5),k1_relat_1(X0))
      | ~ r2_hidden(X5,X1)
      | k2_relat_1(X0) != X1
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f85,plain,(
    ! [X0,X5] :
      ( r2_hidden(sK3(X0,X5),k1_relat_1(X0))
      | ~ r2_hidden(X5,k2_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f57])).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,k1_relat_1(X2))
      | ~ r2_hidden(k4_tarski(X0,X1),X2)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f12,axiom,(
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

fof(f30,plain,(
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
    inference(ennf_transformation,[],[f12])).

fof(f31,plain,(
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
    inference(flattening,[],[f30])).

fof(f46,plain,(
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
    inference(nnf_transformation,[],[f31])).

fof(f71,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f78,plain,(
    v1_funct_2(sK7,sK4,sK5) ),
    inference(cnf_transformation,[],[f49])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f52,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f81,plain,(
    ! [X5] :
      ( k1_funct_1(sK7,X5) != sK8
      | ~ r2_hidden(X5,sK6)
      | ~ m1_subset_1(X5,sK4) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK0(X0,X1,X2),X1)
      | ~ r2_hidden(X0,k9_relat_1(X2,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v5_relat_1(X2,X1) ) ),
    inference(pure_predicate_removal,[],[f9])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v5_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ! [X2] :
          ( r2_hidden(X2,k1_relat_1(X1))
         => r2_hidden(k1_funct_1(X1,X2),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(k1_funct_1(X1,X2),X0)
          | ~ r2_hidden(X2,k1_relat_1(X1)) )
      | ~ v1_funct_1(X1)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(k1_funct_1(X1,X2),X0)
          | ~ r2_hidden(X2,k1_relat_1(X1)) )
      | ~ v1_funct_1(X1)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f22])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k1_funct_1(X1,X2),X0)
      | ~ r2_hidden(X2,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => ! [X1] : ~ r2_hidden(X1,X0) ) ),
    inference(unused_predicate_definition_removal,[],[f1])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] : ~ r2_hidden(X1,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f50,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f2,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f51,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f2])).

cnf(c_6,plain,
    ( ~ r2_hidden(X0,k9_relat_1(X1,X2))
    | r2_hidden(sK0(X0,X2,X1),k1_relat_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_2196,plain,
    ( r2_hidden(X0,k9_relat_1(X1,X2)) != iProver_top
    | r2_hidden(sK0(X0,X2,X1),k1_relat_1(X1)) = iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_29,negated_conjecture,
    ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_2190,plain,
    ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_20,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k7_relset_1(X1,X2,X0,X3) = k9_relat_1(X0,X3) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_2193,plain,
    ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_2667,plain,
    ( k7_relset_1(sK4,sK5,sK7,X0) = k9_relat_1(sK7,X0) ),
    inference(superposition,[status(thm)],[c_2190,c_2193])).

cnf(c_28,negated_conjecture,
    ( r2_hidden(sK8,k7_relset_1(sK4,sK5,sK7,sK6)) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_2191,plain,
    ( r2_hidden(sK8,k7_relset_1(sK4,sK5,sK7,sK6)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_2750,plain,
    ( r2_hidden(sK8,k9_relat_1(sK7,sK6)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_2667,c_2191])).

cnf(c_5,plain,
    ( ~ r2_hidden(X0,k9_relat_1(X1,X2))
    | r2_hidden(k4_tarski(sK0(X0,X2,X1),X0),X1)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_2197,plain,
    ( r2_hidden(X0,k9_relat_1(X1,X2)) != iProver_top
    | r2_hidden(k4_tarski(sK0(X0,X2,X1),X0),X1) = iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_15,plain,
    ( ~ r2_hidden(k4_tarski(X0,X1),X2)
    | ~ v1_funct_1(X2)
    | ~ v1_relat_1(X2)
    | k1_funct_1(X2,X0) = X1 ),
    inference(cnf_transformation,[],[f65])).

cnf(c_31,negated_conjecture,
    ( v1_funct_1(sK7) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_548,plain,
    ( ~ r2_hidden(k4_tarski(X0,X1),X2)
    | ~ v1_relat_1(X2)
    | k1_funct_1(X2,X0) = X1
    | sK7 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_15,c_31])).

cnf(c_549,plain,
    ( ~ r2_hidden(k4_tarski(X0,X1),sK7)
    | ~ v1_relat_1(sK7)
    | k1_funct_1(sK7,X0) = X1 ),
    inference(unflattening,[status(thm)],[c_548])).

cnf(c_2179,plain,
    ( k1_funct_1(sK7,X0) = X1
    | r2_hidden(k4_tarski(X0,X1),sK7) != iProver_top
    | v1_relat_1(sK7) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_549])).

cnf(c_34,plain,
    ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_550,plain,
    ( k1_funct_1(sK7,X0) = X1
    | r2_hidden(k4_tarski(X0,X1),sK7) != iProver_top
    | v1_relat_1(sK7) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_549])).

cnf(c_17,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_2401,plain,
    ( ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5)))
    | v1_relat_1(sK7) ),
    inference(instantiation,[status(thm)],[c_17])).

cnf(c_2402,plain,
    ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) != iProver_top
    | v1_relat_1(sK7) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2401])).

cnf(c_2416,plain,
    ( r2_hidden(k4_tarski(X0,X1),sK7) != iProver_top
    | k1_funct_1(sK7,X0) = X1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2179,c_34,c_550,c_2402])).

cnf(c_2417,plain,
    ( k1_funct_1(sK7,X0) = X1
    | r2_hidden(k4_tarski(X0,X1),sK7) != iProver_top ),
    inference(renaming,[status(thm)],[c_2416])).

cnf(c_3141,plain,
    ( k1_funct_1(sK7,sK0(X0,X1,sK7)) = X0
    | r2_hidden(X0,k9_relat_1(sK7,X1)) != iProver_top
    | v1_relat_1(sK7) != iProver_top ),
    inference(superposition,[status(thm)],[c_2197,c_2417])).

cnf(c_3892,plain,
    ( r2_hidden(X0,k9_relat_1(sK7,X1)) != iProver_top
    | k1_funct_1(sK7,sK0(X0,X1,sK7)) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3141,c_34,c_2402])).

cnf(c_3893,plain,
    ( k1_funct_1(sK7,sK0(X0,X1,sK7)) = X0
    | r2_hidden(X0,k9_relat_1(sK7,X1)) != iProver_top ),
    inference(renaming,[status(thm)],[c_3892])).

cnf(c_3904,plain,
    ( k1_funct_1(sK7,sK0(sK8,sK6,sK7)) = sK8 ),
    inference(superposition,[status(thm)],[c_2750,c_3893])).

cnf(c_10,plain,
    ( ~ r2_hidden(X0,k1_relat_1(X1))
    | r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_461,plain,
    ( ~ r2_hidden(X0,k1_relat_1(X1))
    | r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1))
    | ~ v1_relat_1(X1)
    | sK7 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_10,c_31])).

cnf(c_462,plain,
    ( ~ r2_hidden(X0,k1_relat_1(sK7))
    | r2_hidden(k1_funct_1(sK7,X0),k2_relat_1(sK7))
    | ~ v1_relat_1(sK7) ),
    inference(unflattening,[status(thm)],[c_461])).

cnf(c_2184,plain,
    ( r2_hidden(X0,k1_relat_1(sK7)) != iProver_top
    | r2_hidden(k1_funct_1(sK7,X0),k2_relat_1(sK7)) = iProver_top
    | v1_relat_1(sK7) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_462])).

cnf(c_463,plain,
    ( r2_hidden(X0,k1_relat_1(sK7)) != iProver_top
    | r2_hidden(k1_funct_1(sK7,X0),k2_relat_1(sK7)) = iProver_top
    | v1_relat_1(sK7) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_462])).

cnf(c_2827,plain,
    ( r2_hidden(k1_funct_1(sK7,X0),k2_relat_1(sK7)) = iProver_top
    | r2_hidden(X0,k1_relat_1(sK7)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2184,c_34,c_463,c_2402])).

cnf(c_2828,plain,
    ( r2_hidden(X0,k1_relat_1(sK7)) != iProver_top
    | r2_hidden(k1_funct_1(sK7,X0),k2_relat_1(sK7)) = iProver_top ),
    inference(renaming,[status(thm)],[c_2827])).

cnf(c_3947,plain,
    ( r2_hidden(sK0(sK8,sK6,sK7),k1_relat_1(sK7)) != iProver_top
    | r2_hidden(sK8,k2_relat_1(sK7)) = iProver_top ),
    inference(superposition,[status(thm)],[c_3904,c_2828])).

cnf(c_4165,plain,
    ( r2_hidden(sK8,k9_relat_1(sK7,sK6)) != iProver_top
    | r2_hidden(sK8,k2_relat_1(sK7)) = iProver_top
    | v1_relat_1(sK7) != iProver_top ),
    inference(superposition,[status(thm)],[c_2196,c_3947])).

cnf(c_5567,plain,
    ( r2_hidden(sK8,k2_relat_1(sK7)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4165,c_34,c_2402,c_2750])).

cnf(c_11,plain,
    ( ~ r2_hidden(X0,k2_relat_1(X1))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1)
    | k1_funct_1(X1,sK3(X1,X0)) = X0 ),
    inference(cnf_transformation,[],[f84])).

cnf(c_446,plain,
    ( ~ r2_hidden(X0,k2_relat_1(X1))
    | ~ v1_relat_1(X1)
    | k1_funct_1(X1,sK3(X1,X0)) = X0
    | sK7 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_11,c_31])).

cnf(c_447,plain,
    ( ~ r2_hidden(X0,k2_relat_1(sK7))
    | ~ v1_relat_1(sK7)
    | k1_funct_1(sK7,sK3(sK7,X0)) = X0 ),
    inference(unflattening,[status(thm)],[c_446])).

cnf(c_2185,plain,
    ( k1_funct_1(sK7,sK3(sK7,X0)) = X0
    | r2_hidden(X0,k2_relat_1(sK7)) != iProver_top
    | v1_relat_1(sK7) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_447])).

cnf(c_448,plain,
    ( k1_funct_1(sK7,sK3(sK7,X0)) = X0
    | r2_hidden(X0,k2_relat_1(sK7)) != iProver_top
    | v1_relat_1(sK7) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_447])).

cnf(c_2444,plain,
    ( r2_hidden(X0,k2_relat_1(sK7)) != iProver_top
    | k1_funct_1(sK7,sK3(sK7,X0)) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2185,c_34,c_448,c_2402])).

cnf(c_2445,plain,
    ( k1_funct_1(sK7,sK3(sK7,X0)) = X0
    | r2_hidden(X0,k2_relat_1(sK7)) != iProver_top ),
    inference(renaming,[status(thm)],[c_2444])).

cnf(c_5576,plain,
    ( k1_funct_1(sK7,sK3(sK7,sK8)) = sK8 ),
    inference(superposition,[status(thm)],[c_5567,c_2445])).

cnf(c_14,plain,
    ( ~ r2_hidden(X0,k1_relat_1(X1))
    | r2_hidden(k4_tarski(X0,k1_funct_1(X1,X0)),X1)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_416,plain,
    ( ~ r2_hidden(X0,k1_relat_1(X1))
    | r2_hidden(k4_tarski(X0,k1_funct_1(X1,X0)),X1)
    | ~ v1_relat_1(X1)
    | sK7 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_14,c_31])).

cnf(c_417,plain,
    ( ~ r2_hidden(X0,k1_relat_1(sK7))
    | r2_hidden(k4_tarski(X0,k1_funct_1(sK7,X0)),sK7)
    | ~ v1_relat_1(sK7) ),
    inference(unflattening,[status(thm)],[c_416])).

cnf(c_2187,plain,
    ( r2_hidden(X0,k1_relat_1(sK7)) != iProver_top
    | r2_hidden(k4_tarski(X0,k1_funct_1(sK7,X0)),sK7) = iProver_top
    | v1_relat_1(sK7) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_417])).

cnf(c_418,plain,
    ( r2_hidden(X0,k1_relat_1(sK7)) != iProver_top
    | r2_hidden(k4_tarski(X0,k1_funct_1(sK7,X0)),sK7) = iProver_top
    | v1_relat_1(sK7) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_417])).

cnf(c_2940,plain,
    ( r2_hidden(k4_tarski(X0,k1_funct_1(sK7,X0)),sK7) = iProver_top
    | r2_hidden(X0,k1_relat_1(sK7)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2187,c_34,c_418,c_2402])).

cnf(c_2941,plain,
    ( r2_hidden(X0,k1_relat_1(sK7)) != iProver_top
    | r2_hidden(k4_tarski(X0,k1_funct_1(sK7,X0)),sK7) = iProver_top ),
    inference(renaming,[status(thm)],[c_2940])).

cnf(c_5793,plain,
    ( r2_hidden(sK3(sK7,sK8),k1_relat_1(sK7)) != iProver_top
    | r2_hidden(k4_tarski(sK3(sK7,sK8),sK8),sK7) = iProver_top ),
    inference(superposition,[status(thm)],[c_5576,c_2941])).

cnf(c_12,plain,
    ( ~ r2_hidden(X0,k2_relat_1(X1))
    | r2_hidden(sK3(X1,X0),k1_relat_1(X1))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_431,plain,
    ( ~ r2_hidden(X0,k2_relat_1(X1))
    | r2_hidden(sK3(X1,X0),k1_relat_1(X1))
    | ~ v1_relat_1(X1)
    | sK7 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_12,c_31])).

cnf(c_432,plain,
    ( ~ r2_hidden(X0,k2_relat_1(sK7))
    | r2_hidden(sK3(sK7,X0),k1_relat_1(sK7))
    | ~ v1_relat_1(sK7) ),
    inference(unflattening,[status(thm)],[c_431])).

cnf(c_3024,plain,
    ( r2_hidden(sK3(sK7,sK8),k1_relat_1(sK7))
    | ~ r2_hidden(sK8,k2_relat_1(sK7))
    | ~ v1_relat_1(sK7) ),
    inference(instantiation,[status(thm)],[c_432])).

cnf(c_3025,plain,
    ( r2_hidden(sK3(sK7,sK8),k1_relat_1(sK7)) = iProver_top
    | r2_hidden(sK8,k2_relat_1(sK7)) != iProver_top
    | v1_relat_1(sK7) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3024])).

cnf(c_5834,plain,
    ( r2_hidden(k4_tarski(sK3(sK7,sK8),sK8),sK7) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5793,c_34,c_2402,c_2750,c_3025,c_4165])).

cnf(c_16,plain,
    ( r2_hidden(X0,k1_relat_1(X1))
    | ~ r2_hidden(k4_tarski(X0,X2),X1)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_401,plain,
    ( r2_hidden(X0,k1_relat_1(X1))
    | ~ r2_hidden(k4_tarski(X0,X2),X1)
    | ~ v1_relat_1(X1)
    | sK7 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_16,c_31])).

cnf(c_402,plain,
    ( r2_hidden(X0,k1_relat_1(sK7))
    | ~ r2_hidden(k4_tarski(X0,X1),sK7)
    | ~ v1_relat_1(sK7) ),
    inference(unflattening,[status(thm)],[c_401])).

cnf(c_2188,plain,
    ( r2_hidden(X0,k1_relat_1(sK7)) = iProver_top
    | r2_hidden(k4_tarski(X0,X1),sK7) != iProver_top
    | v1_relat_1(sK7) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_402])).

cnf(c_403,plain,
    ( r2_hidden(X0,k1_relat_1(sK7)) = iProver_top
    | r2_hidden(k4_tarski(X0,X1),sK7) != iProver_top
    | v1_relat_1(sK7) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_402])).

cnf(c_2453,plain,
    ( r2_hidden(k4_tarski(X0,X1),sK7) != iProver_top
    | r2_hidden(X0,k1_relat_1(sK7)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2188,c_34,c_403,c_2402])).

cnf(c_2454,plain,
    ( r2_hidden(X0,k1_relat_1(sK7)) = iProver_top
    | r2_hidden(k4_tarski(X0,X1),sK7) != iProver_top ),
    inference(renaming,[status(thm)],[c_2453])).

cnf(c_5841,plain,
    ( r2_hidden(sK3(sK7,sK8),k1_relat_1(sK7)) = iProver_top ),
    inference(superposition,[status(thm)],[c_5834,c_2454])).

cnf(c_26,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f71])).

cnf(c_30,negated_conjecture,
    ( v1_funct_2(sK7,sK4,sK5) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_908,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | sK5 != X2
    | sK4 != X1
    | sK7 != X0
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_26,c_30])).

cnf(c_909,plain,
    ( ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5)))
    | k1_relset_1(sK4,sK5,sK7) = sK4
    | k1_xboole_0 = sK5 ),
    inference(unflattening,[status(thm)],[c_908])).

cnf(c_911,plain,
    ( k1_relset_1(sK4,sK5,sK7) = sK4
    | k1_xboole_0 = sK5 ),
    inference(global_propositional_subsumption,[status(thm)],[c_909,c_29])).

cnf(c_19,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_2194,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_2553,plain,
    ( k1_relset_1(sK4,sK5,sK7) = k1_relat_1(sK7) ),
    inference(superposition,[status(thm)],[c_2190,c_2194])).

cnf(c_2727,plain,
    ( k1_relat_1(sK7) = sK4
    | sK5 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_911,c_2553])).

cnf(c_3372,plain,
    ( sK5 = k1_xboole_0
    | r2_hidden(X0,k9_relat_1(sK7,X1)) != iProver_top
    | r2_hidden(sK0(X0,X1,sK7),sK4) = iProver_top
    | v1_relat_1(sK7) != iProver_top ),
    inference(superposition,[status(thm)],[c_2727,c_2196])).

cnf(c_7350,plain,
    ( r2_hidden(sK0(X0,X1,sK7),sK4) = iProver_top
    | r2_hidden(X0,k9_relat_1(sK7,X1)) != iProver_top
    | sK5 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3372,c_34,c_2402])).

cnf(c_7351,plain,
    ( sK5 = k1_xboole_0
    | r2_hidden(X0,k9_relat_1(sK7,X1)) != iProver_top
    | r2_hidden(sK0(X0,X1,sK7),sK4) = iProver_top ),
    inference(renaming,[status(thm)],[c_7350])).

cnf(c_2,plain,
    ( m1_subset_1(X0,X1)
    | ~ r2_hidden(X0,X1) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_2200,plain,
    ( m1_subset_1(X0,X1) = iProver_top
    | r2_hidden(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_7359,plain,
    ( sK5 = k1_xboole_0
    | m1_subset_1(sK0(X0,X1,sK7),sK4) = iProver_top
    | r2_hidden(X0,k9_relat_1(sK7,X1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_7351,c_2200])).

cnf(c_27,negated_conjecture,
    ( ~ m1_subset_1(X0,sK4)
    | ~ r2_hidden(X0,sK6)
    | k1_funct_1(sK7,X0) != sK8 ),
    inference(cnf_transformation,[],[f81])).

cnf(c_2192,plain,
    ( k1_funct_1(sK7,X0) != sK8
    | m1_subset_1(X0,sK4) != iProver_top
    | r2_hidden(X0,sK6) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_3948,plain,
    ( m1_subset_1(sK0(sK8,sK6,sK7),sK4) != iProver_top
    | r2_hidden(sK0(sK8,sK6,sK7),sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_3904,c_2192])).

cnf(c_7381,plain,
    ( sK5 = k1_xboole_0
    | r2_hidden(sK0(sK8,sK6,sK7),sK6) != iProver_top
    | r2_hidden(sK8,k9_relat_1(sK7,sK6)) != iProver_top ),
    inference(superposition,[status(thm)],[c_7359,c_3948])).

cnf(c_4,plain,
    ( ~ r2_hidden(X0,k9_relat_1(X1,X2))
    | r2_hidden(sK0(X0,X2,X1),X2)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_2471,plain,
    ( ~ r2_hidden(X0,k9_relat_1(sK7,X1))
    | r2_hidden(sK0(X0,X1,sK7),X1)
    | ~ v1_relat_1(sK7) ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_5104,plain,
    ( r2_hidden(sK0(sK8,sK6,sK7),sK6)
    | ~ r2_hidden(sK8,k9_relat_1(sK7,sK6))
    | ~ v1_relat_1(sK7) ),
    inference(instantiation,[status(thm)],[c_2471])).

cnf(c_5111,plain,
    ( r2_hidden(sK0(sK8,sK6,sK7),sK6) = iProver_top
    | r2_hidden(sK8,k9_relat_1(sK7,sK6)) != iProver_top
    | v1_relat_1(sK7) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5104])).

cnf(c_7384,plain,
    ( sK5 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_7381,c_34,c_2402,c_2750,c_5111])).

cnf(c_18,plain,
    ( v5_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_13,plain,
    ( ~ v5_relat_1(X0,X1)
    | ~ r2_hidden(X2,k1_relat_1(X0))
    | r2_hidden(k1_funct_1(X0,X2),X1)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_373,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ r2_hidden(X3,k1_relat_1(X0))
    | r2_hidden(k1_funct_1(X0,X3),X2)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0) ),
    inference(resolution,[status(thm)],[c_18,c_13])).

cnf(c_377,plain,
    ( ~ v1_funct_1(X0)
    | r2_hidden(k1_funct_1(X0,X3),X2)
    | ~ r2_hidden(X3,k1_relat_1(X0))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_373,c_17])).

cnf(c_378,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ r2_hidden(X3,k1_relat_1(X0))
    | r2_hidden(k1_funct_1(X0,X3),X2)
    | ~ v1_funct_1(X0) ),
    inference(renaming,[status(thm)],[c_377])).

cnf(c_497,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ r2_hidden(X3,k1_relat_1(X0))
    | r2_hidden(k1_funct_1(X0,X3),X2)
    | sK7 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_378,c_31])).

cnf(c_498,plain,
    ( ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ r2_hidden(X2,k1_relat_1(sK7))
    | r2_hidden(k1_funct_1(sK7,X2),X1) ),
    inference(unflattening,[status(thm)],[c_497])).

cnf(c_2182,plain,
    ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | r2_hidden(X2,k1_relat_1(sK7)) != iProver_top
    | r2_hidden(k1_funct_1(sK7,X2),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_498])).

cnf(c_3332,plain,
    ( r2_hidden(X0,k1_relat_1(sK7)) != iProver_top
    | r2_hidden(k1_funct_1(sK7,X0),sK5) = iProver_top ),
    inference(superposition,[status(thm)],[c_2190,c_2182])).

cnf(c_7391,plain,
    ( r2_hidden(X0,k1_relat_1(sK7)) != iProver_top
    | r2_hidden(k1_funct_1(sK7,X0),k1_xboole_0) = iProver_top ),
    inference(demodulation,[status(thm)],[c_7384,c_3332])).

cnf(c_0,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_1,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_362,plain,
    ( ~ r2_hidden(X0,X1)
    | k1_xboole_0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_1])).

cnf(c_363,plain,
    ( ~ r2_hidden(X0,k1_xboole_0) ),
    inference(unflattening,[status(thm)],[c_362])).

cnf(c_2189,plain,
    ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_363])).

cnf(c_7534,plain,
    ( r2_hidden(X0,k1_relat_1(sK7)) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_7391,c_2189])).

cnf(c_7547,plain,
    ( $false ),
    inference(superposition,[status(thm)],[c_5841,c_7534])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.35  % Computer   : n010.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 10:02:44 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running in FOF mode
% 3.27/1.02  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.27/1.02  
% 3.27/1.02  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.27/1.02  
% 3.27/1.02  ------  iProver source info
% 3.27/1.02  
% 3.27/1.02  git: date: 2020-06-30 10:37:57 +0100
% 3.27/1.02  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.27/1.02  git: non_committed_changes: false
% 3.27/1.02  git: last_make_outside_of_git: false
% 3.27/1.02  
% 3.27/1.02  ------ 
% 3.27/1.02  
% 3.27/1.02  ------ Input Options
% 3.27/1.02  
% 3.27/1.02  --out_options                           all
% 3.27/1.02  --tptp_safe_out                         true
% 3.27/1.02  --problem_path                          ""
% 3.27/1.02  --include_path                          ""
% 3.27/1.02  --clausifier                            res/vclausify_rel
% 3.27/1.02  --clausifier_options                    --mode clausify
% 3.27/1.02  --stdin                                 false
% 3.27/1.02  --stats_out                             all
% 3.27/1.02  
% 3.27/1.02  ------ General Options
% 3.27/1.02  
% 3.27/1.02  --fof                                   false
% 3.27/1.02  --time_out_real                         305.
% 3.27/1.02  --time_out_virtual                      -1.
% 3.27/1.02  --symbol_type_check                     false
% 3.27/1.02  --clausify_out                          false
% 3.27/1.02  --sig_cnt_out                           false
% 3.27/1.02  --trig_cnt_out                          false
% 3.27/1.02  --trig_cnt_out_tolerance                1.
% 3.27/1.02  --trig_cnt_out_sk_spl                   false
% 3.27/1.02  --abstr_cl_out                          false
% 3.27/1.02  
% 3.27/1.02  ------ Global Options
% 3.27/1.02  
% 3.27/1.02  --schedule                              default
% 3.27/1.02  --add_important_lit                     false
% 3.27/1.02  --prop_solver_per_cl                    1000
% 3.27/1.02  --min_unsat_core                        false
% 3.27/1.02  --soft_assumptions                      false
% 3.27/1.02  --soft_lemma_size                       3
% 3.27/1.02  --prop_impl_unit_size                   0
% 3.27/1.02  --prop_impl_unit                        []
% 3.27/1.02  --share_sel_clauses                     true
% 3.27/1.02  --reset_solvers                         false
% 3.27/1.02  --bc_imp_inh                            [conj_cone]
% 3.27/1.02  --conj_cone_tolerance                   3.
% 3.27/1.02  --extra_neg_conj                        none
% 3.27/1.02  --large_theory_mode                     true
% 3.27/1.02  --prolific_symb_bound                   200
% 3.27/1.02  --lt_threshold                          2000
% 3.27/1.02  --clause_weak_htbl                      true
% 3.27/1.02  --gc_record_bc_elim                     false
% 3.27/1.02  
% 3.27/1.02  ------ Preprocessing Options
% 3.27/1.02  
% 3.27/1.02  --preprocessing_flag                    true
% 3.27/1.02  --time_out_prep_mult                    0.1
% 3.27/1.02  --splitting_mode                        input
% 3.27/1.02  --splitting_grd                         true
% 3.27/1.02  --splitting_cvd                         false
% 3.27/1.02  --splitting_cvd_svl                     false
% 3.27/1.02  --splitting_nvd                         32
% 3.27/1.02  --sub_typing                            true
% 3.27/1.02  --prep_gs_sim                           true
% 3.27/1.02  --prep_unflatten                        true
% 3.27/1.02  --prep_res_sim                          true
% 3.27/1.02  --prep_upred                            true
% 3.27/1.02  --prep_sem_filter                       exhaustive
% 3.27/1.02  --prep_sem_filter_out                   false
% 3.27/1.02  --pred_elim                             true
% 3.27/1.02  --res_sim_input                         true
% 3.27/1.02  --eq_ax_congr_red                       true
% 3.27/1.02  --pure_diseq_elim                       true
% 3.27/1.02  --brand_transform                       false
% 3.27/1.02  --non_eq_to_eq                          false
% 3.27/1.02  --prep_def_merge                        true
% 3.27/1.02  --prep_def_merge_prop_impl              false
% 3.27/1.02  --prep_def_merge_mbd                    true
% 3.27/1.02  --prep_def_merge_tr_red                 false
% 3.27/1.02  --prep_def_merge_tr_cl                  false
% 3.27/1.02  --smt_preprocessing                     true
% 3.27/1.02  --smt_ac_axioms                         fast
% 3.27/1.02  --preprocessed_out                      false
% 3.27/1.02  --preprocessed_stats                    false
% 3.27/1.02  
% 3.27/1.02  ------ Abstraction refinement Options
% 3.27/1.02  
% 3.27/1.02  --abstr_ref                             []
% 3.27/1.02  --abstr_ref_prep                        false
% 3.27/1.02  --abstr_ref_until_sat                   false
% 3.27/1.02  --abstr_ref_sig_restrict                funpre
% 3.27/1.02  --abstr_ref_af_restrict_to_split_sk     false
% 3.27/1.02  --abstr_ref_under                       []
% 3.27/1.02  
% 3.27/1.02  ------ SAT Options
% 3.27/1.02  
% 3.27/1.02  --sat_mode                              false
% 3.27/1.02  --sat_fm_restart_options                ""
% 3.27/1.02  --sat_gr_def                            false
% 3.27/1.02  --sat_epr_types                         true
% 3.27/1.02  --sat_non_cyclic_types                  false
% 3.27/1.02  --sat_finite_models                     false
% 3.27/1.02  --sat_fm_lemmas                         false
% 3.27/1.02  --sat_fm_prep                           false
% 3.27/1.02  --sat_fm_uc_incr                        true
% 3.27/1.02  --sat_out_model                         small
% 3.27/1.02  --sat_out_clauses                       false
% 3.27/1.02  
% 3.27/1.02  ------ QBF Options
% 3.27/1.02  
% 3.27/1.02  --qbf_mode                              false
% 3.27/1.02  --qbf_elim_univ                         false
% 3.27/1.02  --qbf_dom_inst                          none
% 3.27/1.02  --qbf_dom_pre_inst                      false
% 3.27/1.02  --qbf_sk_in                             false
% 3.27/1.02  --qbf_pred_elim                         true
% 3.27/1.02  --qbf_split                             512
% 3.27/1.02  
% 3.27/1.02  ------ BMC1 Options
% 3.27/1.02  
% 3.27/1.02  --bmc1_incremental                      false
% 3.27/1.02  --bmc1_axioms                           reachable_all
% 3.27/1.02  --bmc1_min_bound                        0
% 3.27/1.02  --bmc1_max_bound                        -1
% 3.27/1.02  --bmc1_max_bound_default                -1
% 3.27/1.02  --bmc1_symbol_reachability              true
% 3.27/1.02  --bmc1_property_lemmas                  false
% 3.27/1.02  --bmc1_k_induction                      false
% 3.27/1.02  --bmc1_non_equiv_states                 false
% 3.27/1.02  --bmc1_deadlock                         false
% 3.27/1.02  --bmc1_ucm                              false
% 3.27/1.02  --bmc1_add_unsat_core                   none
% 3.27/1.02  --bmc1_unsat_core_children              false
% 3.27/1.02  --bmc1_unsat_core_extrapolate_axioms    false
% 3.27/1.02  --bmc1_out_stat                         full
% 3.27/1.02  --bmc1_ground_init                      false
% 3.27/1.02  --bmc1_pre_inst_next_state              false
% 3.27/1.02  --bmc1_pre_inst_state                   false
% 3.27/1.02  --bmc1_pre_inst_reach_state             false
% 3.27/1.02  --bmc1_out_unsat_core                   false
% 3.27/1.02  --bmc1_aig_witness_out                  false
% 3.27/1.02  --bmc1_verbose                          false
% 3.27/1.02  --bmc1_dump_clauses_tptp                false
% 3.27/1.02  --bmc1_dump_unsat_core_tptp             false
% 3.27/1.02  --bmc1_dump_file                        -
% 3.27/1.02  --bmc1_ucm_expand_uc_limit              128
% 3.27/1.02  --bmc1_ucm_n_expand_iterations          6
% 3.27/1.02  --bmc1_ucm_extend_mode                  1
% 3.27/1.02  --bmc1_ucm_init_mode                    2
% 3.27/1.02  --bmc1_ucm_cone_mode                    none
% 3.27/1.02  --bmc1_ucm_reduced_relation_type        0
% 3.27/1.02  --bmc1_ucm_relax_model                  4
% 3.27/1.02  --bmc1_ucm_full_tr_after_sat            true
% 3.27/1.02  --bmc1_ucm_expand_neg_assumptions       false
% 3.27/1.02  --bmc1_ucm_layered_model                none
% 3.27/1.02  --bmc1_ucm_max_lemma_size               10
% 3.27/1.02  
% 3.27/1.02  ------ AIG Options
% 3.27/1.02  
% 3.27/1.02  --aig_mode                              false
% 3.27/1.02  
% 3.27/1.02  ------ Instantiation Options
% 3.27/1.02  
% 3.27/1.02  --instantiation_flag                    true
% 3.27/1.02  --inst_sos_flag                         false
% 3.27/1.02  --inst_sos_phase                        true
% 3.27/1.02  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.27/1.02  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.27/1.02  --inst_lit_sel_side                     num_symb
% 3.27/1.02  --inst_solver_per_active                1400
% 3.27/1.02  --inst_solver_calls_frac                1.
% 3.27/1.02  --inst_passive_queue_type               priority_queues
% 3.27/1.02  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.27/1.02  --inst_passive_queues_freq              [25;2]
% 3.27/1.02  --inst_dismatching                      true
% 3.27/1.02  --inst_eager_unprocessed_to_passive     true
% 3.27/1.02  --inst_prop_sim_given                   true
% 3.27/1.02  --inst_prop_sim_new                     false
% 3.27/1.02  --inst_subs_new                         false
% 3.27/1.02  --inst_eq_res_simp                      false
% 3.27/1.02  --inst_subs_given                       false
% 3.27/1.02  --inst_orphan_elimination               true
% 3.27/1.02  --inst_learning_loop_flag               true
% 3.27/1.02  --inst_learning_start                   3000
% 3.27/1.02  --inst_learning_factor                  2
% 3.27/1.02  --inst_start_prop_sim_after_learn       3
% 3.27/1.02  --inst_sel_renew                        solver
% 3.27/1.02  --inst_lit_activity_flag                true
% 3.27/1.02  --inst_restr_to_given                   false
% 3.27/1.02  --inst_activity_threshold               500
% 3.27/1.02  --inst_out_proof                        true
% 3.27/1.02  
% 3.27/1.02  ------ Resolution Options
% 3.27/1.02  
% 3.27/1.02  --resolution_flag                       true
% 3.27/1.02  --res_lit_sel                           adaptive
% 3.27/1.02  --res_lit_sel_side                      none
% 3.27/1.02  --res_ordering                          kbo
% 3.27/1.02  --res_to_prop_solver                    active
% 3.27/1.02  --res_prop_simpl_new                    false
% 3.27/1.02  --res_prop_simpl_given                  true
% 3.27/1.02  --res_passive_queue_type                priority_queues
% 3.27/1.02  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.27/1.02  --res_passive_queues_freq               [15;5]
% 3.27/1.02  --res_forward_subs                      full
% 3.27/1.02  --res_backward_subs                     full
% 3.27/1.02  --res_forward_subs_resolution           true
% 3.27/1.02  --res_backward_subs_resolution          true
% 3.27/1.02  --res_orphan_elimination                true
% 3.27/1.02  --res_time_limit                        2.
% 3.27/1.02  --res_out_proof                         true
% 3.27/1.02  
% 3.27/1.02  ------ Superposition Options
% 3.27/1.02  
% 3.27/1.02  --superposition_flag                    true
% 3.27/1.02  --sup_passive_queue_type                priority_queues
% 3.27/1.02  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.27/1.02  --sup_passive_queues_freq               [8;1;4]
% 3.27/1.02  --demod_completeness_check              fast
% 3.27/1.02  --demod_use_ground                      true
% 3.27/1.02  --sup_to_prop_solver                    passive
% 3.27/1.02  --sup_prop_simpl_new                    true
% 3.27/1.02  --sup_prop_simpl_given                  true
% 3.27/1.02  --sup_fun_splitting                     false
% 3.27/1.02  --sup_smt_interval                      50000
% 3.27/1.02  
% 3.27/1.02  ------ Superposition Simplification Setup
% 3.27/1.02  
% 3.27/1.02  --sup_indices_passive                   []
% 3.27/1.02  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.27/1.02  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.27/1.02  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.27/1.02  --sup_full_triv                         [TrivRules;PropSubs]
% 3.27/1.02  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.27/1.02  --sup_full_bw                           [BwDemod]
% 3.27/1.02  --sup_immed_triv                        [TrivRules]
% 3.27/1.02  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.27/1.02  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.27/1.02  --sup_immed_bw_main                     []
% 3.27/1.02  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.27/1.02  --sup_input_triv                        [Unflattening;TrivRules]
% 3.27/1.02  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.27/1.02  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.27/1.02  
% 3.27/1.02  ------ Combination Options
% 3.27/1.02  
% 3.27/1.02  --comb_res_mult                         3
% 3.27/1.02  --comb_sup_mult                         2
% 3.27/1.02  --comb_inst_mult                        10
% 3.27/1.02  
% 3.27/1.02  ------ Debug Options
% 3.27/1.02  
% 3.27/1.02  --dbg_backtrace                         false
% 3.27/1.02  --dbg_dump_prop_clauses                 false
% 3.27/1.02  --dbg_dump_prop_clauses_file            -
% 3.27/1.02  --dbg_out_stat                          false
% 3.27/1.02  ------ Parsing...
% 3.27/1.02  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.27/1.02  
% 3.27/1.02  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 4 0s  sf_e  pe_s  pe_e 
% 3.27/1.02  
% 3.27/1.02  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.27/1.02  
% 3.27/1.02  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.27/1.02  ------ Proving...
% 3.27/1.02  ------ Problem Properties 
% 3.27/1.02  
% 3.27/1.02  
% 3.27/1.02  clauses                                 25
% 3.27/1.02  conjectures                             3
% 3.27/1.02  EPR                                     2
% 3.27/1.02  Horn                                    21
% 3.27/1.02  unary                                   3
% 3.27/1.02  binary                                  5
% 3.27/1.02  lits                                    71
% 3.27/1.02  lits eq                                 17
% 3.27/1.02  fd_pure                                 0
% 3.27/1.02  fd_pseudo                               0
% 3.27/1.02  fd_cond                                 3
% 3.27/1.02  fd_pseudo_cond                          1
% 3.27/1.02  AC symbols                              0
% 3.27/1.02  
% 3.27/1.02  ------ Schedule dynamic 5 is on 
% 3.27/1.02  
% 3.27/1.02  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.27/1.02  
% 3.27/1.02  
% 3.27/1.02  ------ 
% 3.27/1.02  Current options:
% 3.27/1.02  ------ 
% 3.27/1.02  
% 3.27/1.02  ------ Input Options
% 3.27/1.02  
% 3.27/1.02  --out_options                           all
% 3.27/1.02  --tptp_safe_out                         true
% 3.27/1.02  --problem_path                          ""
% 3.27/1.02  --include_path                          ""
% 3.27/1.02  --clausifier                            res/vclausify_rel
% 3.27/1.02  --clausifier_options                    --mode clausify
% 3.27/1.02  --stdin                                 false
% 3.27/1.02  --stats_out                             all
% 3.27/1.02  
% 3.27/1.02  ------ General Options
% 3.27/1.02  
% 3.27/1.02  --fof                                   false
% 3.27/1.02  --time_out_real                         305.
% 3.27/1.02  --time_out_virtual                      -1.
% 3.27/1.02  --symbol_type_check                     false
% 3.27/1.02  --clausify_out                          false
% 3.27/1.02  --sig_cnt_out                           false
% 3.27/1.02  --trig_cnt_out                          false
% 3.27/1.02  --trig_cnt_out_tolerance                1.
% 3.27/1.02  --trig_cnt_out_sk_spl                   false
% 3.27/1.02  --abstr_cl_out                          false
% 3.27/1.02  
% 3.27/1.02  ------ Global Options
% 3.27/1.02  
% 3.27/1.02  --schedule                              default
% 3.27/1.02  --add_important_lit                     false
% 3.27/1.02  --prop_solver_per_cl                    1000
% 3.27/1.02  --min_unsat_core                        false
% 3.27/1.02  --soft_assumptions                      false
% 3.27/1.02  --soft_lemma_size                       3
% 3.27/1.02  --prop_impl_unit_size                   0
% 3.27/1.02  --prop_impl_unit                        []
% 3.27/1.02  --share_sel_clauses                     true
% 3.27/1.02  --reset_solvers                         false
% 3.27/1.02  --bc_imp_inh                            [conj_cone]
% 3.27/1.02  --conj_cone_tolerance                   3.
% 3.27/1.02  --extra_neg_conj                        none
% 3.27/1.02  --large_theory_mode                     true
% 3.27/1.02  --prolific_symb_bound                   200
% 3.27/1.02  --lt_threshold                          2000
% 3.27/1.02  --clause_weak_htbl                      true
% 3.27/1.02  --gc_record_bc_elim                     false
% 3.27/1.02  
% 3.27/1.02  ------ Preprocessing Options
% 3.27/1.02  
% 3.27/1.02  --preprocessing_flag                    true
% 3.27/1.02  --time_out_prep_mult                    0.1
% 3.27/1.02  --splitting_mode                        input
% 3.27/1.02  --splitting_grd                         true
% 3.27/1.02  --splitting_cvd                         false
% 3.27/1.02  --splitting_cvd_svl                     false
% 3.27/1.02  --splitting_nvd                         32
% 3.27/1.02  --sub_typing                            true
% 3.27/1.02  --prep_gs_sim                           true
% 3.27/1.02  --prep_unflatten                        true
% 3.27/1.02  --prep_res_sim                          true
% 3.27/1.02  --prep_upred                            true
% 3.27/1.02  --prep_sem_filter                       exhaustive
% 3.27/1.02  --prep_sem_filter_out                   false
% 3.27/1.02  --pred_elim                             true
% 3.27/1.02  --res_sim_input                         true
% 3.27/1.02  --eq_ax_congr_red                       true
% 3.27/1.02  --pure_diseq_elim                       true
% 3.27/1.02  --brand_transform                       false
% 3.27/1.02  --non_eq_to_eq                          false
% 3.27/1.02  --prep_def_merge                        true
% 3.27/1.02  --prep_def_merge_prop_impl              false
% 3.27/1.02  --prep_def_merge_mbd                    true
% 3.27/1.02  --prep_def_merge_tr_red                 false
% 3.27/1.02  --prep_def_merge_tr_cl                  false
% 3.27/1.02  --smt_preprocessing                     true
% 3.27/1.02  --smt_ac_axioms                         fast
% 3.27/1.02  --preprocessed_out                      false
% 3.27/1.02  --preprocessed_stats                    false
% 3.27/1.02  
% 3.27/1.02  ------ Abstraction refinement Options
% 3.27/1.02  
% 3.27/1.02  --abstr_ref                             []
% 3.27/1.02  --abstr_ref_prep                        false
% 3.27/1.02  --abstr_ref_until_sat                   false
% 3.27/1.02  --abstr_ref_sig_restrict                funpre
% 3.27/1.02  --abstr_ref_af_restrict_to_split_sk     false
% 3.27/1.02  --abstr_ref_under                       []
% 3.27/1.02  
% 3.27/1.02  ------ SAT Options
% 3.27/1.02  
% 3.27/1.02  --sat_mode                              false
% 3.27/1.02  --sat_fm_restart_options                ""
% 3.27/1.02  --sat_gr_def                            false
% 3.27/1.02  --sat_epr_types                         true
% 3.27/1.02  --sat_non_cyclic_types                  false
% 3.27/1.02  --sat_finite_models                     false
% 3.27/1.02  --sat_fm_lemmas                         false
% 3.27/1.02  --sat_fm_prep                           false
% 3.27/1.02  --sat_fm_uc_incr                        true
% 3.27/1.02  --sat_out_model                         small
% 3.27/1.02  --sat_out_clauses                       false
% 3.27/1.02  
% 3.27/1.02  ------ QBF Options
% 3.27/1.02  
% 3.27/1.02  --qbf_mode                              false
% 3.27/1.02  --qbf_elim_univ                         false
% 3.27/1.02  --qbf_dom_inst                          none
% 3.27/1.02  --qbf_dom_pre_inst                      false
% 3.27/1.02  --qbf_sk_in                             false
% 3.27/1.02  --qbf_pred_elim                         true
% 3.27/1.02  --qbf_split                             512
% 3.27/1.02  
% 3.27/1.02  ------ BMC1 Options
% 3.27/1.02  
% 3.27/1.02  --bmc1_incremental                      false
% 3.27/1.02  --bmc1_axioms                           reachable_all
% 3.27/1.02  --bmc1_min_bound                        0
% 3.27/1.02  --bmc1_max_bound                        -1
% 3.27/1.02  --bmc1_max_bound_default                -1
% 3.27/1.02  --bmc1_symbol_reachability              true
% 3.27/1.02  --bmc1_property_lemmas                  false
% 3.27/1.02  --bmc1_k_induction                      false
% 3.27/1.02  --bmc1_non_equiv_states                 false
% 3.27/1.02  --bmc1_deadlock                         false
% 3.27/1.02  --bmc1_ucm                              false
% 3.27/1.02  --bmc1_add_unsat_core                   none
% 3.27/1.02  --bmc1_unsat_core_children              false
% 3.27/1.02  --bmc1_unsat_core_extrapolate_axioms    false
% 3.27/1.02  --bmc1_out_stat                         full
% 3.27/1.02  --bmc1_ground_init                      false
% 3.27/1.02  --bmc1_pre_inst_next_state              false
% 3.27/1.02  --bmc1_pre_inst_state                   false
% 3.27/1.02  --bmc1_pre_inst_reach_state             false
% 3.27/1.02  --bmc1_out_unsat_core                   false
% 3.27/1.02  --bmc1_aig_witness_out                  false
% 3.27/1.02  --bmc1_verbose                          false
% 3.27/1.02  --bmc1_dump_clauses_tptp                false
% 3.27/1.02  --bmc1_dump_unsat_core_tptp             false
% 3.27/1.02  --bmc1_dump_file                        -
% 3.27/1.02  --bmc1_ucm_expand_uc_limit              128
% 3.27/1.02  --bmc1_ucm_n_expand_iterations          6
% 3.27/1.02  --bmc1_ucm_extend_mode                  1
% 3.27/1.02  --bmc1_ucm_init_mode                    2
% 3.27/1.02  --bmc1_ucm_cone_mode                    none
% 3.27/1.02  --bmc1_ucm_reduced_relation_type        0
% 3.27/1.02  --bmc1_ucm_relax_model                  4
% 3.27/1.02  --bmc1_ucm_full_tr_after_sat            true
% 3.27/1.02  --bmc1_ucm_expand_neg_assumptions       false
% 3.27/1.02  --bmc1_ucm_layered_model                none
% 3.27/1.02  --bmc1_ucm_max_lemma_size               10
% 3.27/1.02  
% 3.27/1.02  ------ AIG Options
% 3.27/1.02  
% 3.27/1.02  --aig_mode                              false
% 3.27/1.02  
% 3.27/1.02  ------ Instantiation Options
% 3.27/1.02  
% 3.27/1.02  --instantiation_flag                    true
% 3.27/1.02  --inst_sos_flag                         false
% 3.27/1.02  --inst_sos_phase                        true
% 3.27/1.02  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.27/1.02  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.27/1.02  --inst_lit_sel_side                     none
% 3.27/1.02  --inst_solver_per_active                1400
% 3.27/1.02  --inst_solver_calls_frac                1.
% 3.27/1.02  --inst_passive_queue_type               priority_queues
% 3.27/1.02  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.27/1.02  --inst_passive_queues_freq              [25;2]
% 3.27/1.02  --inst_dismatching                      true
% 3.27/1.02  --inst_eager_unprocessed_to_passive     true
% 3.27/1.02  --inst_prop_sim_given                   true
% 3.27/1.02  --inst_prop_sim_new                     false
% 3.27/1.02  --inst_subs_new                         false
% 3.27/1.02  --inst_eq_res_simp                      false
% 3.27/1.02  --inst_subs_given                       false
% 3.27/1.02  --inst_orphan_elimination               true
% 3.27/1.02  --inst_learning_loop_flag               true
% 3.27/1.02  --inst_learning_start                   3000
% 3.27/1.02  --inst_learning_factor                  2
% 3.27/1.02  --inst_start_prop_sim_after_learn       3
% 3.27/1.02  --inst_sel_renew                        solver
% 3.27/1.02  --inst_lit_activity_flag                true
% 3.27/1.02  --inst_restr_to_given                   false
% 3.27/1.02  --inst_activity_threshold               500
% 3.27/1.02  --inst_out_proof                        true
% 3.27/1.02  
% 3.27/1.02  ------ Resolution Options
% 3.27/1.02  
% 3.27/1.02  --resolution_flag                       false
% 3.27/1.02  --res_lit_sel                           adaptive
% 3.27/1.02  --res_lit_sel_side                      none
% 3.27/1.02  --res_ordering                          kbo
% 3.27/1.02  --res_to_prop_solver                    active
% 3.27/1.02  --res_prop_simpl_new                    false
% 3.27/1.02  --res_prop_simpl_given                  true
% 3.27/1.02  --res_passive_queue_type                priority_queues
% 3.27/1.02  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.27/1.02  --res_passive_queues_freq               [15;5]
% 3.27/1.02  --res_forward_subs                      full
% 3.27/1.02  --res_backward_subs                     full
% 3.27/1.02  --res_forward_subs_resolution           true
% 3.27/1.02  --res_backward_subs_resolution          true
% 3.27/1.02  --res_orphan_elimination                true
% 3.27/1.02  --res_time_limit                        2.
% 3.27/1.02  --res_out_proof                         true
% 3.27/1.02  
% 3.27/1.02  ------ Superposition Options
% 3.27/1.02  
% 3.27/1.02  --superposition_flag                    true
% 3.27/1.02  --sup_passive_queue_type                priority_queues
% 3.27/1.02  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.27/1.02  --sup_passive_queues_freq               [8;1;4]
% 3.27/1.02  --demod_completeness_check              fast
% 3.27/1.02  --demod_use_ground                      true
% 3.27/1.02  --sup_to_prop_solver                    passive
% 3.27/1.02  --sup_prop_simpl_new                    true
% 3.27/1.02  --sup_prop_simpl_given                  true
% 3.27/1.02  --sup_fun_splitting                     false
% 3.27/1.02  --sup_smt_interval                      50000
% 3.27/1.02  
% 3.27/1.02  ------ Superposition Simplification Setup
% 3.27/1.02  
% 3.27/1.02  --sup_indices_passive                   []
% 3.27/1.02  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.27/1.02  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.27/1.02  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.27/1.02  --sup_full_triv                         [TrivRules;PropSubs]
% 3.27/1.02  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.27/1.02  --sup_full_bw                           [BwDemod]
% 3.27/1.02  --sup_immed_triv                        [TrivRules]
% 3.27/1.02  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.27/1.02  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.27/1.02  --sup_immed_bw_main                     []
% 3.27/1.02  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.27/1.02  --sup_input_triv                        [Unflattening;TrivRules]
% 3.27/1.02  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.27/1.02  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.27/1.02  
% 3.27/1.02  ------ Combination Options
% 3.27/1.02  
% 3.27/1.02  --comb_res_mult                         3
% 3.27/1.02  --comb_sup_mult                         2
% 3.27/1.02  --comb_inst_mult                        10
% 3.27/1.02  
% 3.27/1.02  ------ Debug Options
% 3.27/1.02  
% 3.27/1.02  --dbg_backtrace                         false
% 3.27/1.02  --dbg_dump_prop_clauses                 false
% 3.27/1.02  --dbg_dump_prop_clauses_file            -
% 3.27/1.02  --dbg_out_stat                          false
% 3.27/1.02  
% 3.27/1.02  
% 3.27/1.02  
% 3.27/1.02  
% 3.27/1.02  ------ Proving...
% 3.27/1.02  
% 3.27/1.02  
% 3.27/1.02  % SZS status Theorem for theBenchmark.p
% 3.27/1.02  
% 3.27/1.02   Resolution empty clause
% 3.27/1.02  
% 3.27/1.02  % SZS output start CNFRefutation for theBenchmark.p
% 3.27/1.02  
% 3.27/1.02  fof(f4,axiom,(
% 3.27/1.02    ! [X0,X1,X2] : (v1_relat_1(X2) => (r2_hidden(X0,k9_relat_1(X2,X1)) <=> ? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X3,X0),X2) & r2_hidden(X3,k1_relat_1(X2)))))),
% 3.27/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.27/1.02  
% 3.27/1.02  fof(f19,plain,(
% 3.27/1.02    ! [X0,X1,X2] : ((r2_hidden(X0,k9_relat_1(X2,X1)) <=> ? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X3,X0),X2) & r2_hidden(X3,k1_relat_1(X2)))) | ~v1_relat_1(X2))),
% 3.27/1.02    inference(ennf_transformation,[],[f4])).
% 3.27/1.02  
% 3.27/1.02  fof(f34,plain,(
% 3.27/1.02    ! [X0,X1,X2] : (((r2_hidden(X0,k9_relat_1(X2,X1)) | ! [X3] : (~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X3,X0),X2) | ~r2_hidden(X3,k1_relat_1(X2)))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X3,X0),X2) & r2_hidden(X3,k1_relat_1(X2))) | ~r2_hidden(X0,k9_relat_1(X2,X1)))) | ~v1_relat_1(X2))),
% 3.27/1.02    inference(nnf_transformation,[],[f19])).
% 3.27/1.02  
% 3.27/1.02  fof(f35,plain,(
% 3.27/1.02    ! [X0,X1,X2] : (((r2_hidden(X0,k9_relat_1(X2,X1)) | ! [X3] : (~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X3,X0),X2) | ~r2_hidden(X3,k1_relat_1(X2)))) & (? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X4,X0),X2) & r2_hidden(X4,k1_relat_1(X2))) | ~r2_hidden(X0,k9_relat_1(X2,X1)))) | ~v1_relat_1(X2))),
% 3.27/1.02    inference(rectify,[],[f34])).
% 3.27/1.02  
% 3.27/1.02  fof(f36,plain,(
% 3.27/1.02    ! [X2,X1,X0] : (? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X4,X0),X2) & r2_hidden(X4,k1_relat_1(X2))) => (r2_hidden(sK0(X0,X1,X2),X1) & r2_hidden(k4_tarski(sK0(X0,X1,X2),X0),X2) & r2_hidden(sK0(X0,X1,X2),k1_relat_1(X2))))),
% 3.27/1.02    introduced(choice_axiom,[])).
% 3.27/1.02  
% 3.27/1.02  fof(f37,plain,(
% 3.27/1.02    ! [X0,X1,X2] : (((r2_hidden(X0,k9_relat_1(X2,X1)) | ! [X3] : (~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X3,X0),X2) | ~r2_hidden(X3,k1_relat_1(X2)))) & ((r2_hidden(sK0(X0,X1,X2),X1) & r2_hidden(k4_tarski(sK0(X0,X1,X2),X0),X2) & r2_hidden(sK0(X0,X1,X2),k1_relat_1(X2))) | ~r2_hidden(X0,k9_relat_1(X2,X1)))) | ~v1_relat_1(X2))),
% 3.27/1.02    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f35,f36])).
% 3.27/1.02  
% 3.27/1.02  fof(f53,plain,(
% 3.27/1.02    ( ! [X2,X0,X1] : (r2_hidden(sK0(X0,X1,X2),k1_relat_1(X2)) | ~r2_hidden(X0,k9_relat_1(X2,X1)) | ~v1_relat_1(X2)) )),
% 3.27/1.02    inference(cnf_transformation,[],[f37])).
% 3.27/1.02  
% 3.27/1.02  fof(f13,conjecture,(
% 3.27/1.02    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ! [X4] : ~(! [X5] : (m1_subset_1(X5,X0) => ~(k1_funct_1(X3,X5) = X4 & r2_hidden(X5,X2))) & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2))))),
% 3.27/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.27/1.02  
% 3.27/1.02  fof(f14,negated_conjecture,(
% 3.27/1.02    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ! [X4] : ~(! [X5] : (m1_subset_1(X5,X0) => ~(k1_funct_1(X3,X5) = X4 & r2_hidden(X5,X2))) & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2))))),
% 3.27/1.02    inference(negated_conjecture,[],[f13])).
% 3.27/1.02  
% 3.27/1.02  fof(f32,plain,(
% 3.27/1.02    ? [X0,X1,X2,X3] : (? [X4] : (! [X5] : ((k1_funct_1(X3,X5) != X4 | ~r2_hidden(X5,X2)) | ~m1_subset_1(X5,X0)) & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2))) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)))),
% 3.27/1.02    inference(ennf_transformation,[],[f14])).
% 3.27/1.02  
% 3.27/1.02  fof(f33,plain,(
% 3.27/1.02    ? [X0,X1,X2,X3] : (? [X4] : (! [X5] : (k1_funct_1(X3,X5) != X4 | ~r2_hidden(X5,X2) | ~m1_subset_1(X5,X0)) & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2))) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3))),
% 3.27/1.02    inference(flattening,[],[f32])).
% 3.27/1.02  
% 3.27/1.02  fof(f48,plain,(
% 3.27/1.02    ( ! [X2,X0,X3,X1] : (? [X4] : (! [X5] : (k1_funct_1(X3,X5) != X4 | ~r2_hidden(X5,X2) | ~m1_subset_1(X5,X0)) & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2))) => (! [X5] : (k1_funct_1(X3,X5) != sK8 | ~r2_hidden(X5,X2) | ~m1_subset_1(X5,X0)) & r2_hidden(sK8,k7_relset_1(X0,X1,X3,X2)))) )),
% 3.27/1.02    introduced(choice_axiom,[])).
% 3.27/1.02  
% 3.27/1.02  fof(f47,plain,(
% 3.27/1.02    ? [X0,X1,X2,X3] : (? [X4] : (! [X5] : (k1_funct_1(X3,X5) != X4 | ~r2_hidden(X5,X2) | ~m1_subset_1(X5,X0)) & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2))) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (? [X4] : (! [X5] : (k1_funct_1(sK7,X5) != X4 | ~r2_hidden(X5,sK6) | ~m1_subset_1(X5,sK4)) & r2_hidden(X4,k7_relset_1(sK4,sK5,sK7,sK6))) & m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) & v1_funct_2(sK7,sK4,sK5) & v1_funct_1(sK7))),
% 3.27/1.02    introduced(choice_axiom,[])).
% 3.27/1.02  
% 3.27/1.02  fof(f49,plain,(
% 3.27/1.02    (! [X5] : (k1_funct_1(sK7,X5) != sK8 | ~r2_hidden(X5,sK6) | ~m1_subset_1(X5,sK4)) & r2_hidden(sK8,k7_relset_1(sK4,sK5,sK7,sK6))) & m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) & v1_funct_2(sK7,sK4,sK5) & v1_funct_1(sK7)),
% 3.27/1.02    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6,sK7,sK8])],[f33,f48,f47])).
% 3.27/1.02  
% 3.27/1.02  fof(f79,plain,(
% 3.27/1.02    m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5)))),
% 3.27/1.02    inference(cnf_transformation,[],[f49])).
% 3.27/1.02  
% 3.27/1.02  fof(f11,axiom,(
% 3.27/1.02    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3))),
% 3.27/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.27/1.02  
% 3.27/1.02  fof(f29,plain,(
% 3.27/1.02    ! [X0,X1,X2,X3] : (k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.27/1.02    inference(ennf_transformation,[],[f11])).
% 3.27/1.02  
% 3.27/1.02  fof(f70,plain,(
% 3.27/1.02    ( ! [X2,X0,X3,X1] : (k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.27/1.02    inference(cnf_transformation,[],[f29])).
% 3.27/1.02  
% 3.27/1.02  fof(f80,plain,(
% 3.27/1.02    r2_hidden(sK8,k7_relset_1(sK4,sK5,sK7,sK6))),
% 3.27/1.02    inference(cnf_transformation,[],[f49])).
% 3.27/1.02  
% 3.27/1.02  fof(f54,plain,(
% 3.27/1.02    ( ! [X2,X0,X1] : (r2_hidden(k4_tarski(sK0(X0,X1,X2),X0),X2) | ~r2_hidden(X0,k9_relat_1(X2,X1)) | ~v1_relat_1(X2)) )),
% 3.27/1.02    inference(cnf_transformation,[],[f37])).
% 3.27/1.02  
% 3.27/1.02  fof(f7,axiom,(
% 3.27/1.02    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (r2_hidden(k4_tarski(X0,X1),X2) <=> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2)))))),
% 3.27/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.27/1.02  
% 3.27/1.02  fof(f24,plain,(
% 3.27/1.02    ! [X0,X1,X2] : ((r2_hidden(k4_tarski(X0,X1),X2) <=> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2)))) | (~v1_funct_1(X2) | ~v1_relat_1(X2)))),
% 3.27/1.02    inference(ennf_transformation,[],[f7])).
% 3.27/1.02  
% 3.27/1.02  fof(f25,plain,(
% 3.27/1.02    ! [X0,X1,X2] : ((r2_hidden(k4_tarski(X0,X1),X2) <=> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2)))) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 3.27/1.02    inference(flattening,[],[f24])).
% 3.27/1.02  
% 3.27/1.02  fof(f44,plain,(
% 3.27/1.02    ! [X0,X1,X2] : (((r2_hidden(k4_tarski(X0,X1),X2) | (k1_funct_1(X2,X0) != X1 | ~r2_hidden(X0,k1_relat_1(X2)))) & ((k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2))) | ~r2_hidden(k4_tarski(X0,X1),X2))) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 3.27/1.02    inference(nnf_transformation,[],[f25])).
% 3.27/1.02  
% 3.27/1.02  fof(f45,plain,(
% 3.27/1.02    ! [X0,X1,X2] : (((r2_hidden(k4_tarski(X0,X1),X2) | k1_funct_1(X2,X0) != X1 | ~r2_hidden(X0,k1_relat_1(X2))) & ((k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2))) | ~r2_hidden(k4_tarski(X0,X1),X2))) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 3.27/1.02    inference(flattening,[],[f44])).
% 3.27/1.02  
% 3.27/1.02  fof(f65,plain,(
% 3.27/1.02    ( ! [X2,X0,X1] : (k1_funct_1(X2,X0) = X1 | ~r2_hidden(k4_tarski(X0,X1),X2) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 3.27/1.02    inference(cnf_transformation,[],[f45])).
% 3.27/1.02  
% 3.27/1.02  fof(f77,plain,(
% 3.27/1.02    v1_funct_1(sK7)),
% 3.27/1.02    inference(cnf_transformation,[],[f49])).
% 3.27/1.02  
% 3.27/1.02  fof(f8,axiom,(
% 3.27/1.02    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 3.27/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.27/1.02  
% 3.27/1.02  fof(f26,plain,(
% 3.27/1.02    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.27/1.02    inference(ennf_transformation,[],[f8])).
% 3.27/1.02  
% 3.27/1.02  fof(f67,plain,(
% 3.27/1.02    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.27/1.02    inference(cnf_transformation,[],[f26])).
% 3.27/1.02  
% 3.27/1.02  fof(f5,axiom,(
% 3.27/1.02    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))))),
% 3.27/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.27/1.02  
% 3.27/1.02  fof(f20,plain,(
% 3.27/1.02    ! [X0] : (! [X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 3.27/1.02    inference(ennf_transformation,[],[f5])).
% 3.27/1.02  
% 3.27/1.02  fof(f21,plain,(
% 3.27/1.02    ! [X0] : (! [X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.27/1.02    inference(flattening,[],[f20])).
% 3.27/1.02  
% 3.27/1.02  fof(f38,plain,(
% 3.27/1.02    ! [X0] : (! [X1] : ((k2_relat_1(X0) = X1 | ? [X2] : ((! [X3] : (k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(X2,X1)) & (? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ! [X3] : (k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0)))) & (? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(X2,X1))) | k2_relat_1(X0) != X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.27/1.02    inference(nnf_transformation,[],[f21])).
% 3.27/1.02  
% 3.27/1.02  fof(f39,plain,(
% 3.27/1.02    ! [X0] : (! [X1] : ((k2_relat_1(X0) = X1 | ? [X2] : ((! [X3] : (k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(X2,X1)) & (? [X4] : (k1_funct_1(X0,X4) = X2 & r2_hidden(X4,k1_relat_1(X0))) | r2_hidden(X2,X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : (k1_funct_1(X0,X6) != X5 | ~r2_hidden(X6,k1_relat_1(X0)))) & (? [X7] : (k1_funct_1(X0,X7) = X5 & r2_hidden(X7,k1_relat_1(X0))) | ~r2_hidden(X5,X1))) | k2_relat_1(X0) != X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.27/1.02    inference(rectify,[],[f38])).
% 3.27/1.02  
% 3.27/1.02  fof(f42,plain,(
% 3.27/1.02    ! [X5,X0] : (? [X7] : (k1_funct_1(X0,X7) = X5 & r2_hidden(X7,k1_relat_1(X0))) => (k1_funct_1(X0,sK3(X0,X5)) = X5 & r2_hidden(sK3(X0,X5),k1_relat_1(X0))))),
% 3.27/1.02    introduced(choice_axiom,[])).
% 3.27/1.02  
% 3.27/1.02  fof(f41,plain,(
% 3.27/1.02    ( ! [X2] : (! [X1,X0] : (? [X4] : (k1_funct_1(X0,X4) = X2 & r2_hidden(X4,k1_relat_1(X0))) => (k1_funct_1(X0,sK2(X0,X1)) = X2 & r2_hidden(sK2(X0,X1),k1_relat_1(X0))))) )),
% 3.27/1.02    introduced(choice_axiom,[])).
% 3.27/1.02  
% 3.27/1.02  fof(f40,plain,(
% 3.27/1.02    ! [X1,X0] : (? [X2] : ((! [X3] : (k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(X2,X1)) & (? [X4] : (k1_funct_1(X0,X4) = X2 & r2_hidden(X4,k1_relat_1(X0))) | r2_hidden(X2,X1))) => ((! [X3] : (k1_funct_1(X0,X3) != sK1(X0,X1) | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(sK1(X0,X1),X1)) & (? [X4] : (k1_funct_1(X0,X4) = sK1(X0,X1) & r2_hidden(X4,k1_relat_1(X0))) | r2_hidden(sK1(X0,X1),X1))))),
% 3.27/1.02    introduced(choice_axiom,[])).
% 3.27/1.02  
% 3.27/1.02  fof(f43,plain,(
% 3.27/1.02    ! [X0] : (! [X1] : ((k2_relat_1(X0) = X1 | ((! [X3] : (k1_funct_1(X0,X3) != sK1(X0,X1) | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(sK1(X0,X1),X1)) & ((k1_funct_1(X0,sK2(X0,X1)) = sK1(X0,X1) & r2_hidden(sK2(X0,X1),k1_relat_1(X0))) | r2_hidden(sK1(X0,X1),X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : (k1_funct_1(X0,X6) != X5 | ~r2_hidden(X6,k1_relat_1(X0)))) & ((k1_funct_1(X0,sK3(X0,X5)) = X5 & r2_hidden(sK3(X0,X5),k1_relat_1(X0))) | ~r2_hidden(X5,X1))) | k2_relat_1(X0) != X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.27/1.02    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f39,f42,f41,f40])).
% 3.27/1.02  
% 3.27/1.02  fof(f59,plain,(
% 3.27/1.02    ( ! [X6,X0,X5,X1] : (r2_hidden(X5,X1) | k1_funct_1(X0,X6) != X5 | ~r2_hidden(X6,k1_relat_1(X0)) | k2_relat_1(X0) != X1 | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.27/1.02    inference(cnf_transformation,[],[f43])).
% 3.27/1.02  
% 3.27/1.02  fof(f82,plain,(
% 3.27/1.02    ( ! [X6,X0,X1] : (r2_hidden(k1_funct_1(X0,X6),X1) | ~r2_hidden(X6,k1_relat_1(X0)) | k2_relat_1(X0) != X1 | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.27/1.02    inference(equality_resolution,[],[f59])).
% 3.27/1.02  
% 3.27/1.02  fof(f83,plain,(
% 3.27/1.02    ( ! [X6,X0] : (r2_hidden(k1_funct_1(X0,X6),k2_relat_1(X0)) | ~r2_hidden(X6,k1_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.27/1.02    inference(equality_resolution,[],[f82])).
% 3.27/1.02  
% 3.27/1.02  fof(f58,plain,(
% 3.27/1.02    ( ! [X0,X5,X1] : (k1_funct_1(X0,sK3(X0,X5)) = X5 | ~r2_hidden(X5,X1) | k2_relat_1(X0) != X1 | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.27/1.02    inference(cnf_transformation,[],[f43])).
% 3.27/1.02  
% 3.27/1.02  fof(f84,plain,(
% 3.27/1.02    ( ! [X0,X5] : (k1_funct_1(X0,sK3(X0,X5)) = X5 | ~r2_hidden(X5,k2_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.27/1.02    inference(equality_resolution,[],[f58])).
% 3.27/1.02  
% 3.27/1.02  fof(f66,plain,(
% 3.27/1.02    ( ! [X2,X0,X1] : (r2_hidden(k4_tarski(X0,X1),X2) | k1_funct_1(X2,X0) != X1 | ~r2_hidden(X0,k1_relat_1(X2)) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 3.27/1.02    inference(cnf_transformation,[],[f45])).
% 3.27/1.02  
% 3.27/1.02  fof(f86,plain,(
% 3.27/1.02    ( ! [X2,X0] : (r2_hidden(k4_tarski(X0,k1_funct_1(X2,X0)),X2) | ~r2_hidden(X0,k1_relat_1(X2)) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 3.27/1.02    inference(equality_resolution,[],[f66])).
% 3.27/1.02  
% 3.27/1.02  fof(f57,plain,(
% 3.27/1.02    ( ! [X0,X5,X1] : (r2_hidden(sK3(X0,X5),k1_relat_1(X0)) | ~r2_hidden(X5,X1) | k2_relat_1(X0) != X1 | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.27/1.02    inference(cnf_transformation,[],[f43])).
% 3.27/1.02  
% 3.27/1.02  fof(f85,plain,(
% 3.27/1.02    ( ! [X0,X5] : (r2_hidden(sK3(X0,X5),k1_relat_1(X0)) | ~r2_hidden(X5,k2_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.27/1.02    inference(equality_resolution,[],[f57])).
% 3.27/1.02  
% 3.27/1.02  fof(f64,plain,(
% 3.27/1.02    ( ! [X2,X0,X1] : (r2_hidden(X0,k1_relat_1(X2)) | ~r2_hidden(k4_tarski(X0,X1),X2) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 3.27/1.02    inference(cnf_transformation,[],[f45])).
% 3.27/1.02  
% 3.27/1.02  fof(f12,axiom,(
% 3.27/1.02    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 3.27/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.27/1.02  
% 3.27/1.02  fof(f30,plain,(
% 3.27/1.02    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.27/1.02    inference(ennf_transformation,[],[f12])).
% 3.27/1.02  
% 3.27/1.02  fof(f31,plain,(
% 3.27/1.02    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.27/1.02    inference(flattening,[],[f30])).
% 3.27/1.02  
% 3.27/1.02  fof(f46,plain,(
% 3.27/1.02    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.27/1.02    inference(nnf_transformation,[],[f31])).
% 3.27/1.02  
% 3.27/1.02  fof(f71,plain,(
% 3.27/1.02    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.27/1.02    inference(cnf_transformation,[],[f46])).
% 3.27/1.02  
% 3.27/1.02  fof(f78,plain,(
% 3.27/1.02    v1_funct_2(sK7,sK4,sK5)),
% 3.27/1.02    inference(cnf_transformation,[],[f49])).
% 3.27/1.02  
% 3.27/1.02  fof(f10,axiom,(
% 3.27/1.02    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 3.27/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.27/1.02  
% 3.27/1.02  fof(f28,plain,(
% 3.27/1.02    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.27/1.02    inference(ennf_transformation,[],[f10])).
% 3.27/1.02  
% 3.27/1.02  fof(f69,plain,(
% 3.27/1.02    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.27/1.02    inference(cnf_transformation,[],[f28])).
% 3.27/1.02  
% 3.27/1.02  fof(f3,axiom,(
% 3.27/1.02    ! [X0,X1] : (r2_hidden(X0,X1) => m1_subset_1(X0,X1))),
% 3.27/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.27/1.02  
% 3.27/1.02  fof(f18,plain,(
% 3.27/1.02    ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1))),
% 3.27/1.02    inference(ennf_transformation,[],[f3])).
% 3.27/1.02  
% 3.27/1.02  fof(f52,plain,(
% 3.27/1.02    ( ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1)) )),
% 3.27/1.02    inference(cnf_transformation,[],[f18])).
% 3.27/1.02  
% 3.27/1.02  fof(f81,plain,(
% 3.27/1.02    ( ! [X5] : (k1_funct_1(sK7,X5) != sK8 | ~r2_hidden(X5,sK6) | ~m1_subset_1(X5,sK4)) )),
% 3.27/1.02    inference(cnf_transformation,[],[f49])).
% 3.27/1.02  
% 3.27/1.02  fof(f55,plain,(
% 3.27/1.02    ( ! [X2,X0,X1] : (r2_hidden(sK0(X0,X1,X2),X1) | ~r2_hidden(X0,k9_relat_1(X2,X1)) | ~v1_relat_1(X2)) )),
% 3.27/1.02    inference(cnf_transformation,[],[f37])).
% 3.27/1.02  
% 3.27/1.02  fof(f9,axiom,(
% 3.27/1.02    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 3.27/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.27/1.02  
% 3.27/1.02  fof(f16,plain,(
% 3.27/1.02    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v5_relat_1(X2,X1))),
% 3.27/1.02    inference(pure_predicate_removal,[],[f9])).
% 3.27/1.02  
% 3.27/1.02  fof(f27,plain,(
% 3.27/1.02    ! [X0,X1,X2] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.27/1.02    inference(ennf_transformation,[],[f16])).
% 3.27/1.02  
% 3.27/1.02  fof(f68,plain,(
% 3.27/1.02    ( ! [X2,X0,X1] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.27/1.02    inference(cnf_transformation,[],[f27])).
% 3.27/1.02  
% 3.27/1.02  fof(f6,axiom,(
% 3.27/1.02    ! [X0,X1] : ((v1_funct_1(X1) & v5_relat_1(X1,X0) & v1_relat_1(X1)) => ! [X2] : (r2_hidden(X2,k1_relat_1(X1)) => r2_hidden(k1_funct_1(X1,X2),X0)))),
% 3.27/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.27/1.02  
% 3.27/1.02  fof(f22,plain,(
% 3.27/1.02    ! [X0,X1] : (! [X2] : (r2_hidden(k1_funct_1(X1,X2),X0) | ~r2_hidden(X2,k1_relat_1(X1))) | (~v1_funct_1(X1) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 3.27/1.02    inference(ennf_transformation,[],[f6])).
% 3.27/1.02  
% 3.27/1.02  fof(f23,plain,(
% 3.27/1.02    ! [X0,X1] : (! [X2] : (r2_hidden(k1_funct_1(X1,X2),X0) | ~r2_hidden(X2,k1_relat_1(X1))) | ~v1_funct_1(X1) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 3.27/1.02    inference(flattening,[],[f22])).
% 3.27/1.02  
% 3.27/1.02  fof(f63,plain,(
% 3.27/1.02    ( ! [X2,X0,X1] : (r2_hidden(k1_funct_1(X1,X2),X0) | ~r2_hidden(X2,k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 3.27/1.02    inference(cnf_transformation,[],[f23])).
% 3.27/1.02  
% 3.27/1.02  fof(f1,axiom,(
% 3.27/1.02    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 3.27/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.27/1.02  
% 3.27/1.02  fof(f15,plain,(
% 3.27/1.02    ! [X0] : (v1_xboole_0(X0) => ! [X1] : ~r2_hidden(X1,X0))),
% 3.27/1.02    inference(unused_predicate_definition_removal,[],[f1])).
% 3.27/1.02  
% 3.27/1.02  fof(f17,plain,(
% 3.27/1.02    ! [X0] : (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0))),
% 3.27/1.02    inference(ennf_transformation,[],[f15])).
% 3.27/1.02  
% 3.27/1.02  fof(f50,plain,(
% 3.27/1.02    ( ! [X0,X1] : (~r2_hidden(X1,X0) | ~v1_xboole_0(X0)) )),
% 3.27/1.02    inference(cnf_transformation,[],[f17])).
% 3.27/1.02  
% 3.27/1.02  fof(f2,axiom,(
% 3.27/1.02    v1_xboole_0(k1_xboole_0)),
% 3.27/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.27/1.02  
% 3.27/1.02  fof(f51,plain,(
% 3.27/1.02    v1_xboole_0(k1_xboole_0)),
% 3.27/1.02    inference(cnf_transformation,[],[f2])).
% 3.27/1.02  
% 3.27/1.02  cnf(c_6,plain,
% 3.27/1.02      ( ~ r2_hidden(X0,k9_relat_1(X1,X2))
% 3.27/1.02      | r2_hidden(sK0(X0,X2,X1),k1_relat_1(X1))
% 3.27/1.02      | ~ v1_relat_1(X1) ),
% 3.27/1.02      inference(cnf_transformation,[],[f53]) ).
% 3.27/1.02  
% 3.27/1.02  cnf(c_2196,plain,
% 3.27/1.02      ( r2_hidden(X0,k9_relat_1(X1,X2)) != iProver_top
% 3.27/1.02      | r2_hidden(sK0(X0,X2,X1),k1_relat_1(X1)) = iProver_top
% 3.27/1.02      | v1_relat_1(X1) != iProver_top ),
% 3.27/1.02      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 3.27/1.02  
% 3.27/1.02  cnf(c_29,negated_conjecture,
% 3.27/1.02      ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) ),
% 3.27/1.02      inference(cnf_transformation,[],[f79]) ).
% 3.27/1.02  
% 3.27/1.02  cnf(c_2190,plain,
% 3.27/1.02      ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) = iProver_top ),
% 3.27/1.02      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 3.27/1.02  
% 3.27/1.02  cnf(c_20,plain,
% 3.27/1.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.27/1.02      | k7_relset_1(X1,X2,X0,X3) = k9_relat_1(X0,X3) ),
% 3.27/1.02      inference(cnf_transformation,[],[f70]) ).
% 3.27/1.02  
% 3.27/1.02  cnf(c_2193,plain,
% 3.27/1.02      ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
% 3.27/1.02      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 3.27/1.02      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 3.27/1.02  
% 3.27/1.02  cnf(c_2667,plain,
% 3.27/1.02      ( k7_relset_1(sK4,sK5,sK7,X0) = k9_relat_1(sK7,X0) ),
% 3.27/1.02      inference(superposition,[status(thm)],[c_2190,c_2193]) ).
% 3.27/1.02  
% 3.27/1.02  cnf(c_28,negated_conjecture,
% 3.27/1.02      ( r2_hidden(sK8,k7_relset_1(sK4,sK5,sK7,sK6)) ),
% 3.27/1.02      inference(cnf_transformation,[],[f80]) ).
% 3.27/1.02  
% 3.27/1.02  cnf(c_2191,plain,
% 3.27/1.02      ( r2_hidden(sK8,k7_relset_1(sK4,sK5,sK7,sK6)) = iProver_top ),
% 3.27/1.02      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 3.27/1.02  
% 3.27/1.02  cnf(c_2750,plain,
% 3.27/1.02      ( r2_hidden(sK8,k9_relat_1(sK7,sK6)) = iProver_top ),
% 3.27/1.02      inference(demodulation,[status(thm)],[c_2667,c_2191]) ).
% 3.27/1.02  
% 3.27/1.02  cnf(c_5,plain,
% 3.27/1.02      ( ~ r2_hidden(X0,k9_relat_1(X1,X2))
% 3.27/1.02      | r2_hidden(k4_tarski(sK0(X0,X2,X1),X0),X1)
% 3.27/1.02      | ~ v1_relat_1(X1) ),
% 3.27/1.02      inference(cnf_transformation,[],[f54]) ).
% 3.27/1.02  
% 3.27/1.02  cnf(c_2197,plain,
% 3.27/1.02      ( r2_hidden(X0,k9_relat_1(X1,X2)) != iProver_top
% 3.27/1.02      | r2_hidden(k4_tarski(sK0(X0,X2,X1),X0),X1) = iProver_top
% 3.27/1.02      | v1_relat_1(X1) != iProver_top ),
% 3.27/1.02      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 3.27/1.02  
% 3.27/1.02  cnf(c_15,plain,
% 3.27/1.02      ( ~ r2_hidden(k4_tarski(X0,X1),X2)
% 3.27/1.02      | ~ v1_funct_1(X2)
% 3.27/1.02      | ~ v1_relat_1(X2)
% 3.27/1.02      | k1_funct_1(X2,X0) = X1 ),
% 3.27/1.02      inference(cnf_transformation,[],[f65]) ).
% 3.27/1.02  
% 3.27/1.02  cnf(c_31,negated_conjecture,
% 3.27/1.02      ( v1_funct_1(sK7) ),
% 3.27/1.02      inference(cnf_transformation,[],[f77]) ).
% 3.27/1.02  
% 3.27/1.02  cnf(c_548,plain,
% 3.27/1.02      ( ~ r2_hidden(k4_tarski(X0,X1),X2)
% 3.27/1.02      | ~ v1_relat_1(X2)
% 3.27/1.02      | k1_funct_1(X2,X0) = X1
% 3.27/1.02      | sK7 != X2 ),
% 3.27/1.02      inference(resolution_lifted,[status(thm)],[c_15,c_31]) ).
% 3.27/1.02  
% 3.27/1.02  cnf(c_549,plain,
% 3.27/1.02      ( ~ r2_hidden(k4_tarski(X0,X1),sK7)
% 3.27/1.02      | ~ v1_relat_1(sK7)
% 3.27/1.02      | k1_funct_1(sK7,X0) = X1 ),
% 3.27/1.02      inference(unflattening,[status(thm)],[c_548]) ).
% 3.27/1.02  
% 3.27/1.02  cnf(c_2179,plain,
% 3.27/1.02      ( k1_funct_1(sK7,X0) = X1
% 3.27/1.02      | r2_hidden(k4_tarski(X0,X1),sK7) != iProver_top
% 3.27/1.02      | v1_relat_1(sK7) != iProver_top ),
% 3.27/1.02      inference(predicate_to_equality,[status(thm)],[c_549]) ).
% 3.27/1.02  
% 3.27/1.02  cnf(c_34,plain,
% 3.27/1.02      ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) = iProver_top ),
% 3.27/1.02      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 3.27/1.02  
% 3.27/1.02  cnf(c_550,plain,
% 3.27/1.02      ( k1_funct_1(sK7,X0) = X1
% 3.27/1.02      | r2_hidden(k4_tarski(X0,X1),sK7) != iProver_top
% 3.27/1.02      | v1_relat_1(sK7) != iProver_top ),
% 3.27/1.02      inference(predicate_to_equality,[status(thm)],[c_549]) ).
% 3.27/1.02  
% 3.27/1.02  cnf(c_17,plain,
% 3.27/1.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | v1_relat_1(X0) ),
% 3.27/1.02      inference(cnf_transformation,[],[f67]) ).
% 3.27/1.02  
% 3.27/1.02  cnf(c_2401,plain,
% 3.27/1.02      ( ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5)))
% 3.27/1.02      | v1_relat_1(sK7) ),
% 3.27/1.02      inference(instantiation,[status(thm)],[c_17]) ).
% 3.27/1.02  
% 3.27/1.02  cnf(c_2402,plain,
% 3.27/1.02      ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) != iProver_top
% 3.27/1.02      | v1_relat_1(sK7) = iProver_top ),
% 3.27/1.02      inference(predicate_to_equality,[status(thm)],[c_2401]) ).
% 3.27/1.02  
% 3.27/1.02  cnf(c_2416,plain,
% 3.27/1.02      ( r2_hidden(k4_tarski(X0,X1),sK7) != iProver_top
% 3.27/1.02      | k1_funct_1(sK7,X0) = X1 ),
% 3.27/1.02      inference(global_propositional_subsumption,
% 3.27/1.02                [status(thm)],
% 3.27/1.02                [c_2179,c_34,c_550,c_2402]) ).
% 3.27/1.02  
% 3.27/1.02  cnf(c_2417,plain,
% 3.27/1.02      ( k1_funct_1(sK7,X0) = X1
% 3.27/1.02      | r2_hidden(k4_tarski(X0,X1),sK7) != iProver_top ),
% 3.27/1.02      inference(renaming,[status(thm)],[c_2416]) ).
% 3.27/1.02  
% 3.27/1.02  cnf(c_3141,plain,
% 3.27/1.02      ( k1_funct_1(sK7,sK0(X0,X1,sK7)) = X0
% 3.27/1.02      | r2_hidden(X0,k9_relat_1(sK7,X1)) != iProver_top
% 3.27/1.02      | v1_relat_1(sK7) != iProver_top ),
% 3.27/1.02      inference(superposition,[status(thm)],[c_2197,c_2417]) ).
% 3.27/1.02  
% 3.27/1.02  cnf(c_3892,plain,
% 3.27/1.02      ( r2_hidden(X0,k9_relat_1(sK7,X1)) != iProver_top
% 3.27/1.02      | k1_funct_1(sK7,sK0(X0,X1,sK7)) = X0 ),
% 3.27/1.02      inference(global_propositional_subsumption,
% 3.27/1.02                [status(thm)],
% 3.27/1.02                [c_3141,c_34,c_2402]) ).
% 3.27/1.02  
% 3.27/1.02  cnf(c_3893,plain,
% 3.27/1.02      ( k1_funct_1(sK7,sK0(X0,X1,sK7)) = X0
% 3.27/1.02      | r2_hidden(X0,k9_relat_1(sK7,X1)) != iProver_top ),
% 3.27/1.02      inference(renaming,[status(thm)],[c_3892]) ).
% 3.27/1.02  
% 3.27/1.02  cnf(c_3904,plain,
% 3.27/1.02      ( k1_funct_1(sK7,sK0(sK8,sK6,sK7)) = sK8 ),
% 3.27/1.02      inference(superposition,[status(thm)],[c_2750,c_3893]) ).
% 3.27/1.02  
% 3.27/1.02  cnf(c_10,plain,
% 3.27/1.02      ( ~ r2_hidden(X0,k1_relat_1(X1))
% 3.27/1.02      | r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1))
% 3.27/1.02      | ~ v1_funct_1(X1)
% 3.27/1.02      | ~ v1_relat_1(X1) ),
% 3.27/1.02      inference(cnf_transformation,[],[f83]) ).
% 3.27/1.02  
% 3.27/1.02  cnf(c_461,plain,
% 3.27/1.02      ( ~ r2_hidden(X0,k1_relat_1(X1))
% 3.27/1.02      | r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1))
% 3.27/1.02      | ~ v1_relat_1(X1)
% 3.27/1.02      | sK7 != X1 ),
% 3.27/1.02      inference(resolution_lifted,[status(thm)],[c_10,c_31]) ).
% 3.27/1.02  
% 3.27/1.02  cnf(c_462,plain,
% 3.27/1.02      ( ~ r2_hidden(X0,k1_relat_1(sK7))
% 3.27/1.02      | r2_hidden(k1_funct_1(sK7,X0),k2_relat_1(sK7))
% 3.27/1.02      | ~ v1_relat_1(sK7) ),
% 3.27/1.02      inference(unflattening,[status(thm)],[c_461]) ).
% 3.27/1.02  
% 3.27/1.02  cnf(c_2184,plain,
% 3.27/1.02      ( r2_hidden(X0,k1_relat_1(sK7)) != iProver_top
% 3.27/1.02      | r2_hidden(k1_funct_1(sK7,X0),k2_relat_1(sK7)) = iProver_top
% 3.27/1.02      | v1_relat_1(sK7) != iProver_top ),
% 3.27/1.02      inference(predicate_to_equality,[status(thm)],[c_462]) ).
% 3.27/1.02  
% 3.27/1.02  cnf(c_463,plain,
% 3.27/1.02      ( r2_hidden(X0,k1_relat_1(sK7)) != iProver_top
% 3.27/1.02      | r2_hidden(k1_funct_1(sK7,X0),k2_relat_1(sK7)) = iProver_top
% 3.27/1.02      | v1_relat_1(sK7) != iProver_top ),
% 3.27/1.02      inference(predicate_to_equality,[status(thm)],[c_462]) ).
% 3.27/1.02  
% 3.27/1.02  cnf(c_2827,plain,
% 3.27/1.02      ( r2_hidden(k1_funct_1(sK7,X0),k2_relat_1(sK7)) = iProver_top
% 3.27/1.02      | r2_hidden(X0,k1_relat_1(sK7)) != iProver_top ),
% 3.27/1.02      inference(global_propositional_subsumption,
% 3.27/1.02                [status(thm)],
% 3.27/1.02                [c_2184,c_34,c_463,c_2402]) ).
% 3.27/1.02  
% 3.27/1.02  cnf(c_2828,plain,
% 3.27/1.02      ( r2_hidden(X0,k1_relat_1(sK7)) != iProver_top
% 3.27/1.02      | r2_hidden(k1_funct_1(sK7,X0),k2_relat_1(sK7)) = iProver_top ),
% 3.27/1.02      inference(renaming,[status(thm)],[c_2827]) ).
% 3.27/1.02  
% 3.27/1.02  cnf(c_3947,plain,
% 3.27/1.02      ( r2_hidden(sK0(sK8,sK6,sK7),k1_relat_1(sK7)) != iProver_top
% 3.27/1.02      | r2_hidden(sK8,k2_relat_1(sK7)) = iProver_top ),
% 3.27/1.02      inference(superposition,[status(thm)],[c_3904,c_2828]) ).
% 3.27/1.02  
% 3.27/1.02  cnf(c_4165,plain,
% 3.27/1.02      ( r2_hidden(sK8,k9_relat_1(sK7,sK6)) != iProver_top
% 3.27/1.02      | r2_hidden(sK8,k2_relat_1(sK7)) = iProver_top
% 3.27/1.02      | v1_relat_1(sK7) != iProver_top ),
% 3.27/1.02      inference(superposition,[status(thm)],[c_2196,c_3947]) ).
% 3.27/1.02  
% 3.27/1.02  cnf(c_5567,plain,
% 3.27/1.02      ( r2_hidden(sK8,k2_relat_1(sK7)) = iProver_top ),
% 3.27/1.02      inference(global_propositional_subsumption,
% 3.27/1.02                [status(thm)],
% 3.27/1.02                [c_4165,c_34,c_2402,c_2750]) ).
% 3.27/1.02  
% 3.27/1.02  cnf(c_11,plain,
% 3.27/1.02      ( ~ r2_hidden(X0,k2_relat_1(X1))
% 3.27/1.02      | ~ v1_funct_1(X1)
% 3.27/1.02      | ~ v1_relat_1(X1)
% 3.27/1.02      | k1_funct_1(X1,sK3(X1,X0)) = X0 ),
% 3.27/1.02      inference(cnf_transformation,[],[f84]) ).
% 3.27/1.02  
% 3.27/1.02  cnf(c_446,plain,
% 3.27/1.02      ( ~ r2_hidden(X0,k2_relat_1(X1))
% 3.27/1.02      | ~ v1_relat_1(X1)
% 3.27/1.02      | k1_funct_1(X1,sK3(X1,X0)) = X0
% 3.27/1.02      | sK7 != X1 ),
% 3.27/1.02      inference(resolution_lifted,[status(thm)],[c_11,c_31]) ).
% 3.27/1.02  
% 3.27/1.02  cnf(c_447,plain,
% 3.27/1.02      ( ~ r2_hidden(X0,k2_relat_1(sK7))
% 3.27/1.02      | ~ v1_relat_1(sK7)
% 3.27/1.02      | k1_funct_1(sK7,sK3(sK7,X0)) = X0 ),
% 3.27/1.02      inference(unflattening,[status(thm)],[c_446]) ).
% 3.27/1.02  
% 3.27/1.02  cnf(c_2185,plain,
% 3.27/1.02      ( k1_funct_1(sK7,sK3(sK7,X0)) = X0
% 3.27/1.02      | r2_hidden(X0,k2_relat_1(sK7)) != iProver_top
% 3.27/1.02      | v1_relat_1(sK7) != iProver_top ),
% 3.27/1.02      inference(predicate_to_equality,[status(thm)],[c_447]) ).
% 3.27/1.02  
% 3.27/1.02  cnf(c_448,plain,
% 3.27/1.02      ( k1_funct_1(sK7,sK3(sK7,X0)) = X0
% 3.27/1.02      | r2_hidden(X0,k2_relat_1(sK7)) != iProver_top
% 3.27/1.02      | v1_relat_1(sK7) != iProver_top ),
% 3.27/1.02      inference(predicate_to_equality,[status(thm)],[c_447]) ).
% 3.27/1.02  
% 3.27/1.02  cnf(c_2444,plain,
% 3.27/1.02      ( r2_hidden(X0,k2_relat_1(sK7)) != iProver_top
% 3.27/1.02      | k1_funct_1(sK7,sK3(sK7,X0)) = X0 ),
% 3.27/1.02      inference(global_propositional_subsumption,
% 3.27/1.02                [status(thm)],
% 3.27/1.02                [c_2185,c_34,c_448,c_2402]) ).
% 3.27/1.02  
% 3.27/1.02  cnf(c_2445,plain,
% 3.27/1.02      ( k1_funct_1(sK7,sK3(sK7,X0)) = X0
% 3.27/1.02      | r2_hidden(X0,k2_relat_1(sK7)) != iProver_top ),
% 3.27/1.02      inference(renaming,[status(thm)],[c_2444]) ).
% 3.27/1.02  
% 3.27/1.02  cnf(c_5576,plain,
% 3.27/1.02      ( k1_funct_1(sK7,sK3(sK7,sK8)) = sK8 ),
% 3.27/1.02      inference(superposition,[status(thm)],[c_5567,c_2445]) ).
% 3.27/1.02  
% 3.27/1.02  cnf(c_14,plain,
% 3.27/1.02      ( ~ r2_hidden(X0,k1_relat_1(X1))
% 3.27/1.02      | r2_hidden(k4_tarski(X0,k1_funct_1(X1,X0)),X1)
% 3.27/1.02      | ~ v1_funct_1(X1)
% 3.27/1.02      | ~ v1_relat_1(X1) ),
% 3.27/1.02      inference(cnf_transformation,[],[f86]) ).
% 3.27/1.02  
% 3.27/1.02  cnf(c_416,plain,
% 3.27/1.02      ( ~ r2_hidden(X0,k1_relat_1(X1))
% 3.27/1.02      | r2_hidden(k4_tarski(X0,k1_funct_1(X1,X0)),X1)
% 3.27/1.02      | ~ v1_relat_1(X1)
% 3.27/1.02      | sK7 != X1 ),
% 3.27/1.02      inference(resolution_lifted,[status(thm)],[c_14,c_31]) ).
% 3.27/1.02  
% 3.27/1.02  cnf(c_417,plain,
% 3.27/1.02      ( ~ r2_hidden(X0,k1_relat_1(sK7))
% 3.27/1.02      | r2_hidden(k4_tarski(X0,k1_funct_1(sK7,X0)),sK7)
% 3.27/1.02      | ~ v1_relat_1(sK7) ),
% 3.27/1.02      inference(unflattening,[status(thm)],[c_416]) ).
% 3.27/1.02  
% 3.27/1.02  cnf(c_2187,plain,
% 3.27/1.02      ( r2_hidden(X0,k1_relat_1(sK7)) != iProver_top
% 3.27/1.02      | r2_hidden(k4_tarski(X0,k1_funct_1(sK7,X0)),sK7) = iProver_top
% 3.27/1.02      | v1_relat_1(sK7) != iProver_top ),
% 3.27/1.02      inference(predicate_to_equality,[status(thm)],[c_417]) ).
% 3.27/1.02  
% 3.27/1.02  cnf(c_418,plain,
% 3.27/1.02      ( r2_hidden(X0,k1_relat_1(sK7)) != iProver_top
% 3.27/1.02      | r2_hidden(k4_tarski(X0,k1_funct_1(sK7,X0)),sK7) = iProver_top
% 3.27/1.02      | v1_relat_1(sK7) != iProver_top ),
% 3.27/1.02      inference(predicate_to_equality,[status(thm)],[c_417]) ).
% 3.27/1.02  
% 3.27/1.02  cnf(c_2940,plain,
% 3.27/1.02      ( r2_hidden(k4_tarski(X0,k1_funct_1(sK7,X0)),sK7) = iProver_top
% 3.27/1.02      | r2_hidden(X0,k1_relat_1(sK7)) != iProver_top ),
% 3.27/1.02      inference(global_propositional_subsumption,
% 3.27/1.02                [status(thm)],
% 3.27/1.02                [c_2187,c_34,c_418,c_2402]) ).
% 3.27/1.02  
% 3.27/1.02  cnf(c_2941,plain,
% 3.27/1.02      ( r2_hidden(X0,k1_relat_1(sK7)) != iProver_top
% 3.27/1.02      | r2_hidden(k4_tarski(X0,k1_funct_1(sK7,X0)),sK7) = iProver_top ),
% 3.27/1.02      inference(renaming,[status(thm)],[c_2940]) ).
% 3.27/1.02  
% 3.27/1.02  cnf(c_5793,plain,
% 3.27/1.02      ( r2_hidden(sK3(sK7,sK8),k1_relat_1(sK7)) != iProver_top
% 3.27/1.02      | r2_hidden(k4_tarski(sK3(sK7,sK8),sK8),sK7) = iProver_top ),
% 3.27/1.02      inference(superposition,[status(thm)],[c_5576,c_2941]) ).
% 3.27/1.02  
% 3.27/1.02  cnf(c_12,plain,
% 3.27/1.02      ( ~ r2_hidden(X0,k2_relat_1(X1))
% 3.27/1.02      | r2_hidden(sK3(X1,X0),k1_relat_1(X1))
% 3.27/1.02      | ~ v1_funct_1(X1)
% 3.27/1.02      | ~ v1_relat_1(X1) ),
% 3.27/1.02      inference(cnf_transformation,[],[f85]) ).
% 3.27/1.02  
% 3.27/1.02  cnf(c_431,plain,
% 3.27/1.02      ( ~ r2_hidden(X0,k2_relat_1(X1))
% 3.27/1.02      | r2_hidden(sK3(X1,X0),k1_relat_1(X1))
% 3.27/1.02      | ~ v1_relat_1(X1)
% 3.27/1.02      | sK7 != X1 ),
% 3.27/1.02      inference(resolution_lifted,[status(thm)],[c_12,c_31]) ).
% 3.27/1.02  
% 3.27/1.02  cnf(c_432,plain,
% 3.27/1.02      ( ~ r2_hidden(X0,k2_relat_1(sK7))
% 3.27/1.02      | r2_hidden(sK3(sK7,X0),k1_relat_1(sK7))
% 3.27/1.02      | ~ v1_relat_1(sK7) ),
% 3.27/1.02      inference(unflattening,[status(thm)],[c_431]) ).
% 3.27/1.02  
% 3.27/1.02  cnf(c_3024,plain,
% 3.27/1.02      ( r2_hidden(sK3(sK7,sK8),k1_relat_1(sK7))
% 3.27/1.02      | ~ r2_hidden(sK8,k2_relat_1(sK7))
% 3.27/1.02      | ~ v1_relat_1(sK7) ),
% 3.27/1.02      inference(instantiation,[status(thm)],[c_432]) ).
% 3.27/1.02  
% 3.27/1.02  cnf(c_3025,plain,
% 3.27/1.02      ( r2_hidden(sK3(sK7,sK8),k1_relat_1(sK7)) = iProver_top
% 3.27/1.02      | r2_hidden(sK8,k2_relat_1(sK7)) != iProver_top
% 3.27/1.02      | v1_relat_1(sK7) != iProver_top ),
% 3.27/1.02      inference(predicate_to_equality,[status(thm)],[c_3024]) ).
% 3.27/1.02  
% 3.27/1.02  cnf(c_5834,plain,
% 3.27/1.02      ( r2_hidden(k4_tarski(sK3(sK7,sK8),sK8),sK7) = iProver_top ),
% 3.27/1.02      inference(global_propositional_subsumption,
% 3.27/1.02                [status(thm)],
% 3.27/1.02                [c_5793,c_34,c_2402,c_2750,c_3025,c_4165]) ).
% 3.27/1.02  
% 3.27/1.02  cnf(c_16,plain,
% 3.27/1.02      ( r2_hidden(X0,k1_relat_1(X1))
% 3.27/1.02      | ~ r2_hidden(k4_tarski(X0,X2),X1)
% 3.27/1.02      | ~ v1_funct_1(X1)
% 3.27/1.02      | ~ v1_relat_1(X1) ),
% 3.27/1.02      inference(cnf_transformation,[],[f64]) ).
% 3.27/1.02  
% 3.27/1.02  cnf(c_401,plain,
% 3.27/1.02      ( r2_hidden(X0,k1_relat_1(X1))
% 3.27/1.02      | ~ r2_hidden(k4_tarski(X0,X2),X1)
% 3.27/1.02      | ~ v1_relat_1(X1)
% 3.27/1.02      | sK7 != X1 ),
% 3.27/1.02      inference(resolution_lifted,[status(thm)],[c_16,c_31]) ).
% 3.27/1.02  
% 3.27/1.02  cnf(c_402,plain,
% 3.27/1.02      ( r2_hidden(X0,k1_relat_1(sK7))
% 3.27/1.02      | ~ r2_hidden(k4_tarski(X0,X1),sK7)
% 3.27/1.02      | ~ v1_relat_1(sK7) ),
% 3.27/1.02      inference(unflattening,[status(thm)],[c_401]) ).
% 3.27/1.02  
% 3.27/1.02  cnf(c_2188,plain,
% 3.27/1.02      ( r2_hidden(X0,k1_relat_1(sK7)) = iProver_top
% 3.27/1.02      | r2_hidden(k4_tarski(X0,X1),sK7) != iProver_top
% 3.27/1.02      | v1_relat_1(sK7) != iProver_top ),
% 3.27/1.02      inference(predicate_to_equality,[status(thm)],[c_402]) ).
% 3.27/1.02  
% 3.27/1.02  cnf(c_403,plain,
% 3.27/1.02      ( r2_hidden(X0,k1_relat_1(sK7)) = iProver_top
% 3.27/1.02      | r2_hidden(k4_tarski(X0,X1),sK7) != iProver_top
% 3.27/1.02      | v1_relat_1(sK7) != iProver_top ),
% 3.27/1.02      inference(predicate_to_equality,[status(thm)],[c_402]) ).
% 3.27/1.02  
% 3.27/1.02  cnf(c_2453,plain,
% 3.27/1.02      ( r2_hidden(k4_tarski(X0,X1),sK7) != iProver_top
% 3.27/1.02      | r2_hidden(X0,k1_relat_1(sK7)) = iProver_top ),
% 3.27/1.02      inference(global_propositional_subsumption,
% 3.27/1.02                [status(thm)],
% 3.27/1.02                [c_2188,c_34,c_403,c_2402]) ).
% 3.27/1.02  
% 3.27/1.02  cnf(c_2454,plain,
% 3.27/1.02      ( r2_hidden(X0,k1_relat_1(sK7)) = iProver_top
% 3.27/1.02      | r2_hidden(k4_tarski(X0,X1),sK7) != iProver_top ),
% 3.27/1.02      inference(renaming,[status(thm)],[c_2453]) ).
% 3.27/1.02  
% 3.27/1.02  cnf(c_5841,plain,
% 3.27/1.02      ( r2_hidden(sK3(sK7,sK8),k1_relat_1(sK7)) = iProver_top ),
% 3.27/1.02      inference(superposition,[status(thm)],[c_5834,c_2454]) ).
% 3.27/1.02  
% 3.27/1.02  cnf(c_26,plain,
% 3.27/1.02      ( ~ v1_funct_2(X0,X1,X2)
% 3.27/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.27/1.02      | k1_relset_1(X1,X2,X0) = X1
% 3.27/1.02      | k1_xboole_0 = X2 ),
% 3.27/1.02      inference(cnf_transformation,[],[f71]) ).
% 3.27/1.02  
% 3.27/1.02  cnf(c_30,negated_conjecture,
% 3.27/1.02      ( v1_funct_2(sK7,sK4,sK5) ),
% 3.27/1.02      inference(cnf_transformation,[],[f78]) ).
% 3.27/1.02  
% 3.27/1.02  cnf(c_908,plain,
% 3.27/1.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.27/1.02      | k1_relset_1(X1,X2,X0) = X1
% 3.27/1.02      | sK5 != X2
% 3.27/1.02      | sK4 != X1
% 3.27/1.02      | sK7 != X0
% 3.27/1.02      | k1_xboole_0 = X2 ),
% 3.27/1.02      inference(resolution_lifted,[status(thm)],[c_26,c_30]) ).
% 3.27/1.02  
% 3.27/1.02  cnf(c_909,plain,
% 3.27/1.02      ( ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5)))
% 3.27/1.02      | k1_relset_1(sK4,sK5,sK7) = sK4
% 3.27/1.02      | k1_xboole_0 = sK5 ),
% 3.27/1.02      inference(unflattening,[status(thm)],[c_908]) ).
% 3.27/1.02  
% 3.27/1.02  cnf(c_911,plain,
% 3.27/1.02      ( k1_relset_1(sK4,sK5,sK7) = sK4 | k1_xboole_0 = sK5 ),
% 3.27/1.02      inference(global_propositional_subsumption,[status(thm)],[c_909,c_29]) ).
% 3.27/1.02  
% 3.27/1.02  cnf(c_19,plain,
% 3.27/1.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.27/1.02      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 3.27/1.02      inference(cnf_transformation,[],[f69]) ).
% 3.27/1.02  
% 3.27/1.02  cnf(c_2194,plain,
% 3.27/1.02      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 3.27/1.02      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 3.27/1.02      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 3.27/1.02  
% 3.27/1.02  cnf(c_2553,plain,
% 3.27/1.02      ( k1_relset_1(sK4,sK5,sK7) = k1_relat_1(sK7) ),
% 3.27/1.02      inference(superposition,[status(thm)],[c_2190,c_2194]) ).
% 3.27/1.02  
% 3.27/1.02  cnf(c_2727,plain,
% 3.27/1.02      ( k1_relat_1(sK7) = sK4 | sK5 = k1_xboole_0 ),
% 3.27/1.02      inference(superposition,[status(thm)],[c_911,c_2553]) ).
% 3.27/1.02  
% 3.27/1.02  cnf(c_3372,plain,
% 3.27/1.02      ( sK5 = k1_xboole_0
% 3.27/1.02      | r2_hidden(X0,k9_relat_1(sK7,X1)) != iProver_top
% 3.27/1.02      | r2_hidden(sK0(X0,X1,sK7),sK4) = iProver_top
% 3.27/1.02      | v1_relat_1(sK7) != iProver_top ),
% 3.27/1.02      inference(superposition,[status(thm)],[c_2727,c_2196]) ).
% 3.27/1.02  
% 3.27/1.02  cnf(c_7350,plain,
% 3.27/1.02      ( r2_hidden(sK0(X0,X1,sK7),sK4) = iProver_top
% 3.27/1.02      | r2_hidden(X0,k9_relat_1(sK7,X1)) != iProver_top
% 3.27/1.02      | sK5 = k1_xboole_0 ),
% 3.27/1.02      inference(global_propositional_subsumption,
% 3.27/1.02                [status(thm)],
% 3.27/1.02                [c_3372,c_34,c_2402]) ).
% 3.27/1.02  
% 3.27/1.02  cnf(c_7351,plain,
% 3.27/1.02      ( sK5 = k1_xboole_0
% 3.27/1.02      | r2_hidden(X0,k9_relat_1(sK7,X1)) != iProver_top
% 3.27/1.02      | r2_hidden(sK0(X0,X1,sK7),sK4) = iProver_top ),
% 3.27/1.02      inference(renaming,[status(thm)],[c_7350]) ).
% 3.27/1.02  
% 3.27/1.02  cnf(c_2,plain,
% 3.27/1.02      ( m1_subset_1(X0,X1) | ~ r2_hidden(X0,X1) ),
% 3.27/1.02      inference(cnf_transformation,[],[f52]) ).
% 3.27/1.02  
% 3.27/1.02  cnf(c_2200,plain,
% 3.27/1.02      ( m1_subset_1(X0,X1) = iProver_top | r2_hidden(X0,X1) != iProver_top ),
% 3.27/1.02      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 3.27/1.02  
% 3.27/1.02  cnf(c_7359,plain,
% 3.27/1.02      ( sK5 = k1_xboole_0
% 3.27/1.02      | m1_subset_1(sK0(X0,X1,sK7),sK4) = iProver_top
% 3.27/1.02      | r2_hidden(X0,k9_relat_1(sK7,X1)) != iProver_top ),
% 3.27/1.02      inference(superposition,[status(thm)],[c_7351,c_2200]) ).
% 3.27/1.02  
% 3.27/1.02  cnf(c_27,negated_conjecture,
% 3.27/1.02      ( ~ m1_subset_1(X0,sK4)
% 3.27/1.02      | ~ r2_hidden(X0,sK6)
% 3.27/1.02      | k1_funct_1(sK7,X0) != sK8 ),
% 3.27/1.02      inference(cnf_transformation,[],[f81]) ).
% 3.27/1.02  
% 3.27/1.02  cnf(c_2192,plain,
% 3.27/1.02      ( k1_funct_1(sK7,X0) != sK8
% 3.27/1.02      | m1_subset_1(X0,sK4) != iProver_top
% 3.27/1.02      | r2_hidden(X0,sK6) != iProver_top ),
% 3.27/1.02      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 3.27/1.02  
% 3.27/1.02  cnf(c_3948,plain,
% 3.27/1.02      ( m1_subset_1(sK0(sK8,sK6,sK7),sK4) != iProver_top
% 3.27/1.02      | r2_hidden(sK0(sK8,sK6,sK7),sK6) != iProver_top ),
% 3.27/1.02      inference(superposition,[status(thm)],[c_3904,c_2192]) ).
% 3.27/1.02  
% 3.27/1.02  cnf(c_7381,plain,
% 3.27/1.02      ( sK5 = k1_xboole_0
% 3.27/1.02      | r2_hidden(sK0(sK8,sK6,sK7),sK6) != iProver_top
% 3.27/1.02      | r2_hidden(sK8,k9_relat_1(sK7,sK6)) != iProver_top ),
% 3.27/1.02      inference(superposition,[status(thm)],[c_7359,c_3948]) ).
% 3.27/1.02  
% 3.27/1.02  cnf(c_4,plain,
% 3.27/1.02      ( ~ r2_hidden(X0,k9_relat_1(X1,X2))
% 3.27/1.02      | r2_hidden(sK0(X0,X2,X1),X2)
% 3.27/1.02      | ~ v1_relat_1(X1) ),
% 3.27/1.02      inference(cnf_transformation,[],[f55]) ).
% 3.27/1.02  
% 3.27/1.02  cnf(c_2471,plain,
% 3.27/1.02      ( ~ r2_hidden(X0,k9_relat_1(sK7,X1))
% 3.27/1.02      | r2_hidden(sK0(X0,X1,sK7),X1)
% 3.27/1.02      | ~ v1_relat_1(sK7) ),
% 3.27/1.02      inference(instantiation,[status(thm)],[c_4]) ).
% 3.27/1.02  
% 3.27/1.02  cnf(c_5104,plain,
% 3.27/1.02      ( r2_hidden(sK0(sK8,sK6,sK7),sK6)
% 3.27/1.02      | ~ r2_hidden(sK8,k9_relat_1(sK7,sK6))
% 3.27/1.02      | ~ v1_relat_1(sK7) ),
% 3.27/1.02      inference(instantiation,[status(thm)],[c_2471]) ).
% 3.27/1.02  
% 3.27/1.02  cnf(c_5111,plain,
% 3.27/1.02      ( r2_hidden(sK0(sK8,sK6,sK7),sK6) = iProver_top
% 3.27/1.02      | r2_hidden(sK8,k9_relat_1(sK7,sK6)) != iProver_top
% 3.27/1.02      | v1_relat_1(sK7) != iProver_top ),
% 3.27/1.02      inference(predicate_to_equality,[status(thm)],[c_5104]) ).
% 3.27/1.02  
% 3.27/1.02  cnf(c_7384,plain,
% 3.27/1.02      ( sK5 = k1_xboole_0 ),
% 3.27/1.02      inference(global_propositional_subsumption,
% 3.27/1.02                [status(thm)],
% 3.27/1.02                [c_7381,c_34,c_2402,c_2750,c_5111]) ).
% 3.27/1.02  
% 3.27/1.02  cnf(c_18,plain,
% 3.27/1.02      ( v5_relat_1(X0,X1) | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
% 3.27/1.02      inference(cnf_transformation,[],[f68]) ).
% 3.27/1.02  
% 3.27/1.02  cnf(c_13,plain,
% 3.27/1.02      ( ~ v5_relat_1(X0,X1)
% 3.27/1.02      | ~ r2_hidden(X2,k1_relat_1(X0))
% 3.27/1.02      | r2_hidden(k1_funct_1(X0,X2),X1)
% 3.27/1.02      | ~ v1_funct_1(X0)
% 3.27/1.02      | ~ v1_relat_1(X0) ),
% 3.27/1.02      inference(cnf_transformation,[],[f63]) ).
% 3.27/1.02  
% 3.27/1.02  cnf(c_373,plain,
% 3.27/1.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.27/1.02      | ~ r2_hidden(X3,k1_relat_1(X0))
% 3.27/1.02      | r2_hidden(k1_funct_1(X0,X3),X2)
% 3.27/1.02      | ~ v1_funct_1(X0)
% 3.27/1.02      | ~ v1_relat_1(X0) ),
% 3.27/1.02      inference(resolution,[status(thm)],[c_18,c_13]) ).
% 3.27/1.02  
% 3.27/1.02  cnf(c_377,plain,
% 3.27/1.02      ( ~ v1_funct_1(X0)
% 3.27/1.02      | r2_hidden(k1_funct_1(X0,X3),X2)
% 3.27/1.02      | ~ r2_hidden(X3,k1_relat_1(X0))
% 3.27/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
% 3.27/1.02      inference(global_propositional_subsumption,[status(thm)],[c_373,c_17]) ).
% 3.27/1.02  
% 3.27/1.02  cnf(c_378,plain,
% 3.27/1.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.27/1.02      | ~ r2_hidden(X3,k1_relat_1(X0))
% 3.27/1.02      | r2_hidden(k1_funct_1(X0,X3),X2)
% 3.27/1.02      | ~ v1_funct_1(X0) ),
% 3.27/1.02      inference(renaming,[status(thm)],[c_377]) ).
% 3.27/1.02  
% 3.27/1.02  cnf(c_497,plain,
% 3.27/1.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.27/1.02      | ~ r2_hidden(X3,k1_relat_1(X0))
% 3.27/1.02      | r2_hidden(k1_funct_1(X0,X3),X2)
% 3.27/1.02      | sK7 != X0 ),
% 3.27/1.02      inference(resolution_lifted,[status(thm)],[c_378,c_31]) ).
% 3.27/1.02  
% 3.27/1.02  cnf(c_498,plain,
% 3.27/1.02      ( ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.27/1.02      | ~ r2_hidden(X2,k1_relat_1(sK7))
% 3.27/1.02      | r2_hidden(k1_funct_1(sK7,X2),X1) ),
% 3.27/1.02      inference(unflattening,[status(thm)],[c_497]) ).
% 3.27/1.02  
% 3.27/1.02  cnf(c_2182,plain,
% 3.27/1.02      ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 3.27/1.02      | r2_hidden(X2,k1_relat_1(sK7)) != iProver_top
% 3.27/1.02      | r2_hidden(k1_funct_1(sK7,X2),X1) = iProver_top ),
% 3.27/1.02      inference(predicate_to_equality,[status(thm)],[c_498]) ).
% 3.27/1.02  
% 3.27/1.02  cnf(c_3332,plain,
% 3.27/1.02      ( r2_hidden(X0,k1_relat_1(sK7)) != iProver_top
% 3.27/1.02      | r2_hidden(k1_funct_1(sK7,X0),sK5) = iProver_top ),
% 3.27/1.02      inference(superposition,[status(thm)],[c_2190,c_2182]) ).
% 3.27/1.02  
% 3.27/1.02  cnf(c_7391,plain,
% 3.27/1.02      ( r2_hidden(X0,k1_relat_1(sK7)) != iProver_top
% 3.27/1.02      | r2_hidden(k1_funct_1(sK7,X0),k1_xboole_0) = iProver_top ),
% 3.27/1.02      inference(demodulation,[status(thm)],[c_7384,c_3332]) ).
% 3.27/1.02  
% 3.27/1.02  cnf(c_0,plain,
% 3.27/1.02      ( ~ r2_hidden(X0,X1) | ~ v1_xboole_0(X1) ),
% 3.27/1.02      inference(cnf_transformation,[],[f50]) ).
% 3.27/1.02  
% 3.27/1.02  cnf(c_1,plain,
% 3.27/1.02      ( v1_xboole_0(k1_xboole_0) ),
% 3.27/1.02      inference(cnf_transformation,[],[f51]) ).
% 3.27/1.02  
% 3.27/1.02  cnf(c_362,plain,
% 3.27/1.02      ( ~ r2_hidden(X0,X1) | k1_xboole_0 != X1 ),
% 3.27/1.02      inference(resolution_lifted,[status(thm)],[c_0,c_1]) ).
% 3.27/1.02  
% 3.27/1.02  cnf(c_363,plain,
% 3.27/1.02      ( ~ r2_hidden(X0,k1_xboole_0) ),
% 3.27/1.02      inference(unflattening,[status(thm)],[c_362]) ).
% 3.27/1.02  
% 3.27/1.02  cnf(c_2189,plain,
% 3.27/1.02      ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
% 3.27/1.02      inference(predicate_to_equality,[status(thm)],[c_363]) ).
% 3.27/1.02  
% 3.27/1.02  cnf(c_7534,plain,
% 3.27/1.02      ( r2_hidden(X0,k1_relat_1(sK7)) != iProver_top ),
% 3.27/1.02      inference(forward_subsumption_resolution,[status(thm)],[c_7391,c_2189]) ).
% 3.27/1.02  
% 3.27/1.02  cnf(c_7547,plain,
% 3.27/1.02      ( $false ),
% 3.27/1.02      inference(superposition,[status(thm)],[c_5841,c_7534]) ).
% 3.27/1.02  
% 3.27/1.02  
% 3.27/1.02  % SZS output end CNFRefutation for theBenchmark.p
% 3.27/1.02  
% 3.27/1.02  ------                               Statistics
% 3.27/1.02  
% 3.27/1.02  ------ General
% 3.27/1.02  
% 3.27/1.02  abstr_ref_over_cycles:                  0
% 3.27/1.02  abstr_ref_under_cycles:                 0
% 3.27/1.02  gc_basic_clause_elim:                   0
% 3.27/1.02  forced_gc_time:                         0
% 3.27/1.02  parsing_time:                           0.012
% 3.27/1.02  unif_index_cands_time:                  0.
% 3.27/1.02  unif_index_add_time:                    0.
% 3.27/1.02  orderings_time:                         0.
% 3.27/1.02  out_proof_time:                         0.012
% 3.27/1.02  total_time:                             0.235
% 3.27/1.02  num_of_symbols:                         57
% 3.27/1.02  num_of_terms:                           5299
% 3.27/1.02  
% 3.27/1.02  ------ Preprocessing
% 3.27/1.02  
% 3.27/1.02  num_of_splits:                          0
% 3.27/1.02  num_of_split_atoms:                     0
% 3.27/1.02  num_of_reused_defs:                     0
% 3.27/1.02  num_eq_ax_congr_red:                    34
% 3.27/1.02  num_of_sem_filtered_clauses:            1
% 3.27/1.02  num_of_subtypes:                        0
% 3.27/1.02  monotx_restored_types:                  0
% 3.27/1.02  sat_num_of_epr_types:                   0
% 3.27/1.02  sat_num_of_non_cyclic_types:            0
% 3.27/1.02  sat_guarded_non_collapsed_types:        0
% 3.27/1.02  num_pure_diseq_elim:                    0
% 3.27/1.02  simp_replaced_by:                       0
% 3.27/1.02  res_preprocessed:                       140
% 3.27/1.02  prep_upred:                             0
% 3.27/1.02  prep_unflattend:                        100
% 3.27/1.02  smt_new_axioms:                         0
% 3.27/1.02  pred_elim_cands:                        3
% 3.27/1.02  pred_elim:                              4
% 3.27/1.02  pred_elim_cl:                           7
% 3.27/1.02  pred_elim_cycles:                       8
% 3.27/1.02  merged_defs:                            0
% 3.27/1.02  merged_defs_ncl:                        0
% 3.27/1.02  bin_hyper_res:                          0
% 3.27/1.02  prep_cycles:                            4
% 3.27/1.02  pred_elim_time:                         0.02
% 3.27/1.02  splitting_time:                         0.
% 3.27/1.02  sem_filter_time:                        0.
% 3.27/1.02  monotx_time:                            0.001
% 3.27/1.02  subtype_inf_time:                       0.
% 3.27/1.02  
% 3.27/1.02  ------ Problem properties
% 3.27/1.02  
% 3.27/1.02  clauses:                                25
% 3.27/1.02  conjectures:                            3
% 3.27/1.02  epr:                                    2
% 3.27/1.02  horn:                                   21
% 3.27/1.02  ground:                                 5
% 3.27/1.02  unary:                                  3
% 3.27/1.02  binary:                                 5
% 3.27/1.02  lits:                                   71
% 3.27/1.02  lits_eq:                                17
% 3.27/1.02  fd_pure:                                0
% 3.27/1.02  fd_pseudo:                              0
% 3.27/1.02  fd_cond:                                3
% 3.27/1.02  fd_pseudo_cond:                         1
% 3.27/1.02  ac_symbols:                             0
% 3.27/1.02  
% 3.27/1.02  ------ Propositional Solver
% 3.27/1.02  
% 3.27/1.02  prop_solver_calls:                      29
% 3.27/1.02  prop_fast_solver_calls:                 1298
% 3.27/1.02  smt_solver_calls:                       0
% 3.27/1.02  smt_fast_solver_calls:                  0
% 3.27/1.02  prop_num_of_clauses:                    2280
% 3.27/1.02  prop_preprocess_simplified:             5924
% 3.27/1.02  prop_fo_subsumed:                       22
% 3.27/1.02  prop_solver_time:                       0.
% 3.27/1.02  smt_solver_time:                        0.
% 3.27/1.02  smt_fast_solver_time:                   0.
% 3.27/1.02  prop_fast_solver_time:                  0.
% 3.27/1.02  prop_unsat_core_time:                   0.
% 3.27/1.02  
% 3.27/1.02  ------ QBF
% 3.27/1.02  
% 3.27/1.02  qbf_q_res:                              0
% 3.27/1.02  qbf_num_tautologies:                    0
% 3.27/1.02  qbf_prep_cycles:                        0
% 3.27/1.02  
% 3.27/1.02  ------ BMC1
% 3.27/1.02  
% 3.27/1.02  bmc1_current_bound:                     -1
% 3.27/1.02  bmc1_last_solved_bound:                 -1
% 3.27/1.02  bmc1_unsat_core_size:                   -1
% 3.27/1.02  bmc1_unsat_core_parents_size:           -1
% 3.27/1.02  bmc1_merge_next_fun:                    0
% 3.27/1.02  bmc1_unsat_core_clauses_time:           0.
% 3.27/1.02  
% 3.27/1.02  ------ Instantiation
% 3.27/1.02  
% 3.27/1.02  inst_num_of_clauses:                    494
% 3.27/1.02  inst_num_in_passive:                    33
% 3.27/1.02  inst_num_in_active:                     349
% 3.27/1.02  inst_num_in_unprocessed:                112
% 3.27/1.02  inst_num_of_loops:                      480
% 3.27/1.02  inst_num_of_learning_restarts:          0
% 3.27/1.02  inst_num_moves_active_passive:          127
% 3.27/1.02  inst_lit_activity:                      0
% 3.27/1.02  inst_lit_activity_moves:                0
% 3.27/1.02  inst_num_tautologies:                   0
% 3.27/1.02  inst_num_prop_implied:                  0
% 3.27/1.02  inst_num_existing_simplified:           0
% 3.27/1.02  inst_num_eq_res_simplified:             0
% 3.27/1.02  inst_num_child_elim:                    0
% 3.27/1.02  inst_num_of_dismatching_blockings:      101
% 3.27/1.02  inst_num_of_non_proper_insts:           442
% 3.27/1.02  inst_num_of_duplicates:                 0
% 3.27/1.02  inst_inst_num_from_inst_to_res:         0
% 3.27/1.02  inst_dismatching_checking_time:         0.
% 3.27/1.02  
% 3.27/1.02  ------ Resolution
% 3.27/1.02  
% 3.27/1.02  res_num_of_clauses:                     0
% 3.27/1.02  res_num_in_passive:                     0
% 3.27/1.02  res_num_in_active:                      0
% 3.27/1.02  res_num_of_loops:                       144
% 3.27/1.02  res_forward_subset_subsumed:            22
% 3.27/1.02  res_backward_subset_subsumed:           0
% 3.27/1.02  res_forward_subsumed:                   0
% 3.27/1.02  res_backward_subsumed:                  0
% 3.27/1.02  res_forward_subsumption_resolution:     0
% 3.27/1.02  res_backward_subsumption_resolution:    0
% 3.27/1.02  res_clause_to_clause_subsumption:       711
% 3.27/1.02  res_orphan_elimination:                 0
% 3.27/1.02  res_tautology_del:                      62
% 3.27/1.02  res_num_eq_res_simplified:              0
% 3.27/1.02  res_num_sel_changes:                    0
% 3.27/1.02  res_moves_from_active_to_pass:          0
% 3.27/1.02  
% 3.27/1.02  ------ Superposition
% 3.27/1.02  
% 3.27/1.02  sup_time_total:                         0.
% 3.27/1.02  sup_time_generating:                    0.
% 3.27/1.02  sup_time_sim_full:                      0.
% 3.27/1.02  sup_time_sim_immed:                     0.
% 3.27/1.02  
% 3.27/1.02  sup_num_of_clauses:                     253
% 3.27/1.02  sup_num_in_active:                      79
% 3.27/1.02  sup_num_in_passive:                     174
% 3.27/1.02  sup_num_of_loops:                       95
% 3.27/1.02  sup_fw_superposition:                   228
% 3.27/1.02  sup_bw_superposition:                   92
% 3.27/1.02  sup_immediate_simplified:               21
% 3.27/1.02  sup_given_eliminated:                   0
% 3.27/1.02  comparisons_done:                       0
% 3.27/1.02  comparisons_avoided:                    7
% 3.27/1.02  
% 3.27/1.02  ------ Simplifications
% 3.27/1.02  
% 3.27/1.02  
% 3.27/1.02  sim_fw_subset_subsumed:                 7
% 3.27/1.02  sim_bw_subset_subsumed:                 15
% 3.27/1.02  sim_fw_subsumed:                        3
% 3.27/1.02  sim_bw_subsumed:                        1
% 3.27/1.02  sim_fw_subsumption_res:                 2
% 3.27/1.02  sim_bw_subsumption_res:                 0
% 3.27/1.02  sim_tautology_del:                      2
% 3.27/1.02  sim_eq_tautology_del:                   38
% 3.27/1.02  sim_eq_res_simp:                        1
% 3.27/1.02  sim_fw_demodulated:                     0
% 3.27/1.02  sim_bw_demodulated:                     13
% 3.27/1.02  sim_light_normalised:                   9
% 3.27/1.02  sim_joinable_taut:                      0
% 3.27/1.02  sim_joinable_simp:                      0
% 3.27/1.02  sim_ac_normalised:                      0
% 3.27/1.02  sim_smt_subsumption:                    0
% 3.27/1.02  
%------------------------------------------------------------------------------
