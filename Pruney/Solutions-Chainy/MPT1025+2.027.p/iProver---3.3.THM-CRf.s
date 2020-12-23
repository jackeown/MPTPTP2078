%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:08:05 EST 2020

% Result     : Theorem 2.23s
% Output     : CNFRefutation 2.23s
% Verified   : 
% Statistics : Number of formulae       :   96 ( 354 expanded)
%              Number of clauses        :   53 (  98 expanded)
%              Number of leaves         :   12 (  87 expanded)
%              Depth                    :   19
%              Number of atoms          :  353 (2028 expanded)
%              Number of equality atoms :  127 ( 496 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal clause size      :   20 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1,X2] :
          ( k9_relat_1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ? [X4] :
                  ( k1_funct_1(X0,X4) = X3
                  & r2_hidden(X4,X1)
                  & r2_hidden(X4,k1_relat_1(X0)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( k9_relat_1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ? [X4] :
                  ( k1_funct_1(X0,X4) = X3
                  & r2_hidden(X4,X1)
                  & r2_hidden(X4,k1_relat_1(X0)) ) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( k9_relat_1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ? [X4] :
                  ( k1_funct_1(X0,X4) = X3
                  & r2_hidden(X4,X1)
                  & r2_hidden(X4,k1_relat_1(X0)) ) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f12])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k9_relat_1(X0,X1) = X2
            | ? [X3] :
                ( ( ! [X4] :
                      ( k1_funct_1(X0,X4) != X3
                      | ~ r2_hidden(X4,X1)
                      | ~ r2_hidden(X4,k1_relat_1(X0)) )
                  | ~ r2_hidden(X3,X2) )
                & ( ? [X4] :
                      ( k1_funct_1(X0,X4) = X3
                      & r2_hidden(X4,X1)
                      & r2_hidden(X4,k1_relat_1(X0)) )
                  | r2_hidden(X3,X2) ) ) )
          & ( ! [X3] :
                ( ( r2_hidden(X3,X2)
                  | ! [X4] :
                      ( k1_funct_1(X0,X4) != X3
                      | ~ r2_hidden(X4,X1)
                      | ~ r2_hidden(X4,k1_relat_1(X0)) ) )
                & ( ? [X4] :
                      ( k1_funct_1(X0,X4) = X3
                      & r2_hidden(X4,X1)
                      & r2_hidden(X4,k1_relat_1(X0)) )
                  | ~ r2_hidden(X3,X2) ) )
            | k9_relat_1(X0,X1) != X2 ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f13])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k9_relat_1(X0,X1) = X2
            | ? [X3] :
                ( ( ! [X4] :
                      ( k1_funct_1(X0,X4) != X3
                      | ~ r2_hidden(X4,X1)
                      | ~ r2_hidden(X4,k1_relat_1(X0)) )
                  | ~ r2_hidden(X3,X2) )
                & ( ? [X5] :
                      ( k1_funct_1(X0,X5) = X3
                      & r2_hidden(X5,X1)
                      & r2_hidden(X5,k1_relat_1(X0)) )
                  | r2_hidden(X3,X2) ) ) )
          & ( ! [X6] :
                ( ( r2_hidden(X6,X2)
                  | ! [X7] :
                      ( k1_funct_1(X0,X7) != X6
                      | ~ r2_hidden(X7,X1)
                      | ~ r2_hidden(X7,k1_relat_1(X0)) ) )
                & ( ? [X8] :
                      ( k1_funct_1(X0,X8) = X6
                      & r2_hidden(X8,X1)
                      & r2_hidden(X8,k1_relat_1(X0)) )
                  | ~ r2_hidden(X6,X2) ) )
            | k9_relat_1(X0,X1) != X2 ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(rectify,[],[f20])).

fof(f24,plain,(
    ! [X6,X1,X0] :
      ( ? [X8] :
          ( k1_funct_1(X0,X8) = X6
          & r2_hidden(X8,X1)
          & r2_hidden(X8,k1_relat_1(X0)) )
     => ( k1_funct_1(X0,sK2(X0,X1,X6)) = X6
        & r2_hidden(sK2(X0,X1,X6),X1)
        & r2_hidden(sK2(X0,X1,X6),k1_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,(
    ! [X3,X2,X1,X0] :
      ( ? [X5] :
          ( k1_funct_1(X0,X5) = X3
          & r2_hidden(X5,X1)
          & r2_hidden(X5,k1_relat_1(X0)) )
     => ( k1_funct_1(X0,sK1(X0,X1,X2)) = X3
        & r2_hidden(sK1(X0,X1,X2),X1)
        & r2_hidden(sK1(X0,X1,X2),k1_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ! [X4] :
                ( k1_funct_1(X0,X4) != X3
                | ~ r2_hidden(X4,X1)
                | ~ r2_hidden(X4,k1_relat_1(X0)) )
            | ~ r2_hidden(X3,X2) )
          & ( ? [X5] :
                ( k1_funct_1(X0,X5) = X3
                & r2_hidden(X5,X1)
                & r2_hidden(X5,k1_relat_1(X0)) )
            | r2_hidden(X3,X2) ) )
     => ( ( ! [X4] :
              ( k1_funct_1(X0,X4) != sK0(X0,X1,X2)
              | ~ r2_hidden(X4,X1)
              | ~ r2_hidden(X4,k1_relat_1(X0)) )
          | ~ r2_hidden(sK0(X0,X1,X2),X2) )
        & ( ? [X5] :
              ( k1_funct_1(X0,X5) = sK0(X0,X1,X2)
              & r2_hidden(X5,X1)
              & r2_hidden(X5,k1_relat_1(X0)) )
          | r2_hidden(sK0(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k9_relat_1(X0,X1) = X2
            | ( ( ! [X4] :
                    ( k1_funct_1(X0,X4) != sK0(X0,X1,X2)
                    | ~ r2_hidden(X4,X1)
                    | ~ r2_hidden(X4,k1_relat_1(X0)) )
                | ~ r2_hidden(sK0(X0,X1,X2),X2) )
              & ( ( k1_funct_1(X0,sK1(X0,X1,X2)) = sK0(X0,X1,X2)
                  & r2_hidden(sK1(X0,X1,X2),X1)
                  & r2_hidden(sK1(X0,X1,X2),k1_relat_1(X0)) )
                | r2_hidden(sK0(X0,X1,X2),X2) ) ) )
          & ( ! [X6] :
                ( ( r2_hidden(X6,X2)
                  | ! [X7] :
                      ( k1_funct_1(X0,X7) != X6
                      | ~ r2_hidden(X7,X1)
                      | ~ r2_hidden(X7,k1_relat_1(X0)) ) )
                & ( ( k1_funct_1(X0,sK2(X0,X1,X6)) = X6
                    & r2_hidden(sK2(X0,X1,X6),X1)
                    & r2_hidden(sK2(X0,X1,X6),k1_relat_1(X0)) )
                  | ~ r2_hidden(X6,X2) ) )
            | k9_relat_1(X0,X1) != X2 ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f21,f24,f23,f22])).

fof(f30,plain,(
    ! [X6,X2,X0,X1] :
      ( r2_hidden(sK2(X0,X1,X6),k1_relat_1(X0))
      | ~ r2_hidden(X6,X2)
      | k9_relat_1(X0,X1) != X2
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f50,plain,(
    ! [X6,X0,X1] :
      ( r2_hidden(sK2(X0,X1,X6),k1_relat_1(X0))
      | ~ r2_hidden(X6,k9_relat_1(X0,X1))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f30])).

fof(f7,conjecture,(
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

fof(f8,negated_conjecture,(
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
    inference(negated_conjecture,[],[f7])).

fof(f9,plain,(
    ~ ! [X0,X1,X2,X3] :
        ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_1(X3) )
       => ! [X4] :
            ~ ( ! [X5] :
                  ( m1_subset_1(X5,X0)
                 => ~ ( k1_funct_1(X3,X5) = X4
                      & r2_hidden(X5,X2) ) )
              & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2)) ) ) ),
    inference(pure_predicate_removal,[],[f8])).

fof(f18,plain,(
    ? [X0,X1,X2,X3] :
      ( ? [X4] :
          ( ! [X5] :
              ( k1_funct_1(X3,X5) != X4
              | ~ r2_hidden(X5,X2)
              | ~ m1_subset_1(X5,X0) )
          & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2)) )
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f19,plain,(
    ? [X0,X1,X2,X3] :
      ( ? [X4] :
          ( ! [X5] :
              ( k1_funct_1(X3,X5) != X4
              | ~ r2_hidden(X5,X2)
              | ~ m1_subset_1(X5,X0) )
          & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2)) )
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_1(X3) ) ),
    inference(flattening,[],[f18])).

fof(f27,plain,(
    ! [X2,X0,X3,X1] :
      ( ? [X4] :
          ( ! [X5] :
              ( k1_funct_1(X3,X5) != X4
              | ~ r2_hidden(X5,X2)
              | ~ m1_subset_1(X5,X0) )
          & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2)) )
     => ( ! [X5] :
            ( k1_funct_1(X3,X5) != sK7
            | ~ r2_hidden(X5,X2)
            | ~ m1_subset_1(X5,X0) )
        & r2_hidden(sK7,k7_relset_1(X0,X1,X3,X2)) ) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,
    ( ? [X0,X1,X2,X3] :
        ( ? [X4] :
            ( ! [X5] :
                ( k1_funct_1(X3,X5) != X4
                | ~ r2_hidden(X5,X2)
                | ~ m1_subset_1(X5,X0) )
            & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2)) )
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X3) )
   => ( ? [X4] :
          ( ! [X5] :
              ( k1_funct_1(sK6,X5) != X4
              | ~ r2_hidden(X5,sK5)
              | ~ m1_subset_1(X5,sK3) )
          & r2_hidden(X4,k7_relset_1(sK3,sK4,sK6,sK5)) )
      & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))
      & v1_funct_1(sK6) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,
    ( ! [X5] :
        ( k1_funct_1(sK6,X5) != sK7
        | ~ r2_hidden(X5,sK5)
        | ~ m1_subset_1(X5,sK3) )
    & r2_hidden(sK7,k7_relset_1(sK3,sK4,sK6,sK5))
    & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))
    & v1_funct_1(sK6) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5,sK6,sK7])],[f19,f27,f26])).

fof(f42,plain,(
    v1_funct_1(sK6) ),
    inference(cnf_transformation,[],[f28])).

fof(f43,plain,(
    m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) ),
    inference(cnf_transformation,[],[f28])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f38,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f40,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f39,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f10,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f11,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f10])).

fof(f29,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f31,plain,(
    ! [X6,X2,X0,X1] :
      ( r2_hidden(sK2(X0,X1,X6),X1)
      | ~ r2_hidden(X6,X2)
      | k9_relat_1(X0,X1) != X2
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f49,plain,(
    ! [X6,X0,X1] :
      ( r2_hidden(sK2(X0,X1,X6),X1)
      | ~ r2_hidden(X6,k9_relat_1(X0,X1))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f31])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1,X2,X3] :
      ( k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f41,plain,(
    ! [X2,X0,X3,X1] :
      ( k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f44,plain,(
    r2_hidden(sK7,k7_relset_1(sK3,sK4,sK6,sK5)) ),
    inference(cnf_transformation,[],[f28])).

fof(f32,plain,(
    ! [X6,X2,X0,X1] :
      ( k1_funct_1(X0,sK2(X0,X1,X6)) = X6
      | ~ r2_hidden(X6,X2)
      | k9_relat_1(X0,X1) != X2
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f48,plain,(
    ! [X6,X0,X1] :
      ( k1_funct_1(X0,sK2(X0,X1,X6)) = X6
      | ~ r2_hidden(X6,k9_relat_1(X0,X1))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f32])).

fof(f45,plain,(
    ! [X5] :
      ( k1_funct_1(sK6,X5) != sK7
      | ~ r2_hidden(X5,sK5)
      | ~ m1_subset_1(X5,sK3) ) ),
    inference(cnf_transformation,[],[f28])).

cnf(c_8,plain,
    ( ~ r2_hidden(X0,k9_relat_1(X1,X2))
    | r2_hidden(sK2(X1,X2,X0),k1_relat_1(X1))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_16,negated_conjecture,
    ( v1_funct_1(sK6) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_291,plain,
    ( ~ r2_hidden(X0,k9_relat_1(X1,X2))
    | r2_hidden(sK2(X1,X2,X0),k1_relat_1(X1))
    | ~ v1_relat_1(X1)
    | sK6 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_8,c_16])).

cnf(c_292,plain,
    ( ~ r2_hidden(X0,k9_relat_1(sK6,X1))
    | r2_hidden(sK2(sK6,X1,X0),k1_relat_1(sK6))
    | ~ v1_relat_1(sK6) ),
    inference(unflattening,[status(thm)],[c_291])).

cnf(c_1120,plain,
    ( r2_hidden(X0,k9_relat_1(sK6,X1)) != iProver_top
    | r2_hidden(sK2(sK6,X1,X0),k1_relat_1(sK6)) = iProver_top
    | v1_relat_1(sK6) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_292])).

cnf(c_15,negated_conjecture,
    ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_18,plain,
    ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_293,plain,
    ( r2_hidden(X0,k9_relat_1(sK6,X1)) != iProver_top
    | r2_hidden(sK2(sK6,X1,X0),k1_relat_1(sK6)) = iProver_top
    | v1_relat_1(sK6) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_292])).

cnf(c_9,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_1267,plain,
    ( ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))
    | v1_relat_1(sK6) ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_1268,plain,
    ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) != iProver_top
    | v1_relat_1(sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1267])).

cnf(c_1323,plain,
    ( r2_hidden(sK2(sK6,X1,X0),k1_relat_1(sK6)) = iProver_top
    | r2_hidden(X0,k9_relat_1(sK6,X1)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1120,c_18,c_293,c_1268])).

cnf(c_1324,plain,
    ( r2_hidden(X0,k9_relat_1(sK6,X1)) != iProver_top
    | r2_hidden(sK2(sK6,X1,X0),k1_relat_1(sK6)) = iProver_top ),
    inference(renaming,[status(thm)],[c_1323])).

cnf(c_1126,plain,
    ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_11,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_1130,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_1536,plain,
    ( k1_relset_1(sK3,sK4,sK6) = k1_relat_1(sK6) ),
    inference(superposition,[status(thm)],[c_1126,c_1130])).

cnf(c_10,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | m1_subset_1(k1_relset_1(X1,X2,X0),k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_1131,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | m1_subset_1(k1_relset_1(X1,X2,X0),k1_zfmisc_1(X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_1717,plain,
    ( m1_subset_1(k1_relat_1(sK6),k1_zfmisc_1(sK3)) = iProver_top
    | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) != iProver_top ),
    inference(superposition,[status(thm)],[c_1536,c_1131])).

cnf(c_2206,plain,
    ( m1_subset_1(k1_relat_1(sK6),k1_zfmisc_1(sK3)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1717,c_18])).

cnf(c_0,plain,
    ( ~ r2_hidden(X0,X1)
    | m1_subset_1(X0,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(cnf_transformation,[],[f29])).

cnf(c_1133,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | m1_subset_1(X0,X2) = iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(X2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_2211,plain,
    ( r2_hidden(X0,k1_relat_1(sK6)) != iProver_top
    | m1_subset_1(X0,sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_2206,c_1133])).

cnf(c_2346,plain,
    ( r2_hidden(X0,k9_relat_1(sK6,X1)) != iProver_top
    | m1_subset_1(sK2(sK6,X1,X0),sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_1324,c_2211])).

cnf(c_7,plain,
    ( ~ r2_hidden(X0,k9_relat_1(X1,X2))
    | r2_hidden(sK2(X1,X2,X0),X2)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_306,plain,
    ( ~ r2_hidden(X0,k9_relat_1(X1,X2))
    | r2_hidden(sK2(X1,X2,X0),X2)
    | ~ v1_relat_1(X1)
    | sK6 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_7,c_16])).

cnf(c_307,plain,
    ( ~ r2_hidden(X0,k9_relat_1(sK6,X1))
    | r2_hidden(sK2(sK6,X1,X0),X1)
    | ~ v1_relat_1(sK6) ),
    inference(unflattening,[status(thm)],[c_306])).

cnf(c_1119,plain,
    ( r2_hidden(X0,k9_relat_1(sK6,X1)) != iProver_top
    | r2_hidden(sK2(sK6,X1,X0),X1) = iProver_top
    | v1_relat_1(sK6) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_307])).

cnf(c_308,plain,
    ( r2_hidden(X0,k9_relat_1(sK6,X1)) != iProver_top
    | r2_hidden(sK2(sK6,X1,X0),X1) = iProver_top
    | v1_relat_1(sK6) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_307])).

cnf(c_1310,plain,
    ( r2_hidden(sK2(sK6,X1,X0),X1) = iProver_top
    | r2_hidden(X0,k9_relat_1(sK6,X1)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1119,c_18,c_308,c_1268])).

cnf(c_1311,plain,
    ( r2_hidden(X0,k9_relat_1(sK6,X1)) != iProver_top
    | r2_hidden(sK2(sK6,X1,X0),X1) = iProver_top ),
    inference(renaming,[status(thm)],[c_1310])).

cnf(c_12,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k7_relset_1(X1,X2,X0,X3) = k9_relat_1(X0,X3) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_1129,plain,
    ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_1540,plain,
    ( k7_relset_1(sK3,sK4,sK6,X0) = k9_relat_1(sK6,X0) ),
    inference(superposition,[status(thm)],[c_1126,c_1129])).

cnf(c_14,negated_conjecture,
    ( r2_hidden(sK7,k7_relset_1(sK3,sK4,sK6,sK5)) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_1127,plain,
    ( r2_hidden(sK7,k7_relset_1(sK3,sK4,sK6,sK5)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_1720,plain,
    ( r2_hidden(sK7,k9_relat_1(sK6,sK5)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_1540,c_1127])).

cnf(c_6,plain,
    ( ~ r2_hidden(X0,k9_relat_1(X1,X2))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1)
    | k1_funct_1(X1,sK2(X1,X2,X0)) = X0 ),
    inference(cnf_transformation,[],[f48])).

cnf(c_321,plain,
    ( ~ r2_hidden(X0,k9_relat_1(X1,X2))
    | ~ v1_relat_1(X1)
    | k1_funct_1(X1,sK2(X1,X2,X0)) = X0
    | sK6 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_6,c_16])).

cnf(c_322,plain,
    ( ~ r2_hidden(X0,k9_relat_1(sK6,X1))
    | ~ v1_relat_1(sK6)
    | k1_funct_1(sK6,sK2(sK6,X1,X0)) = X0 ),
    inference(unflattening,[status(thm)],[c_321])).

cnf(c_1118,plain,
    ( k1_funct_1(sK6,sK2(sK6,X0,X1)) = X1
    | r2_hidden(X1,k9_relat_1(sK6,X0)) != iProver_top
    | v1_relat_1(sK6) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_322])).

cnf(c_323,plain,
    ( k1_funct_1(sK6,sK2(sK6,X0,X1)) = X1
    | r2_hidden(X1,k9_relat_1(sK6,X0)) != iProver_top
    | v1_relat_1(sK6) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_322])).

cnf(c_1283,plain,
    ( r2_hidden(X1,k9_relat_1(sK6,X0)) != iProver_top
    | k1_funct_1(sK6,sK2(sK6,X0,X1)) = X1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1118,c_18,c_323,c_1268])).

cnf(c_1284,plain,
    ( k1_funct_1(sK6,sK2(sK6,X0,X1)) = X1
    | r2_hidden(X1,k9_relat_1(sK6,X0)) != iProver_top ),
    inference(renaming,[status(thm)],[c_1283])).

cnf(c_1794,plain,
    ( k1_funct_1(sK6,sK2(sK6,sK5,sK7)) = sK7 ),
    inference(superposition,[status(thm)],[c_1720,c_1284])).

cnf(c_13,negated_conjecture,
    ( ~ r2_hidden(X0,sK5)
    | ~ m1_subset_1(X0,sK3)
    | k1_funct_1(sK6,X0) != sK7 ),
    inference(cnf_transformation,[],[f45])).

cnf(c_1128,plain,
    ( k1_funct_1(sK6,X0) != sK7
    | r2_hidden(X0,sK5) != iProver_top
    | m1_subset_1(X0,sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_1968,plain,
    ( r2_hidden(sK2(sK6,sK5,sK7),sK5) != iProver_top
    | m1_subset_1(sK2(sK6,sK5,sK7),sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1794,c_1128])).

cnf(c_2067,plain,
    ( r2_hidden(sK7,k9_relat_1(sK6,sK5)) != iProver_top
    | m1_subset_1(sK2(sK6,sK5,sK7),sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1311,c_1968])).

cnf(c_2489,plain,
    ( m1_subset_1(sK2(sK6,sK5,sK7),sK3) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2067,c_1720])).

cnf(c_2494,plain,
    ( r2_hidden(sK7,k9_relat_1(sK6,sK5)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2346,c_2489])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_2494,c_1720])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.10  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.00/0.11  % Command    : iproveropt_run.sh %d %s
% 0.11/0.32  % Computer   : n001.cluster.edu
% 0.11/0.32  % Model      : x86_64 x86_64
% 0.11/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.11/0.32  % Memory     : 8042.1875MB
% 0.11/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.11/0.32  % CPULimit   : 60
% 0.11/0.32  % WCLimit    : 600
% 0.11/0.32  % DateTime   : Tue Dec  1 14:01:30 EST 2020
% 0.11/0.32  % CPUTime    : 
% 0.11/0.32  % Running in FOF mode
% 2.23/0.97  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.23/0.97  
% 2.23/0.97  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.23/0.97  
% 2.23/0.97  ------  iProver source info
% 2.23/0.97  
% 2.23/0.97  git: date: 2020-06-30 10:37:57 +0100
% 2.23/0.97  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.23/0.97  git: non_committed_changes: false
% 2.23/0.97  git: last_make_outside_of_git: false
% 2.23/0.97  
% 2.23/0.97  ------ 
% 2.23/0.97  
% 2.23/0.97  ------ Input Options
% 2.23/0.97  
% 2.23/0.97  --out_options                           all
% 2.23/0.97  --tptp_safe_out                         true
% 2.23/0.97  --problem_path                          ""
% 2.23/0.97  --include_path                          ""
% 2.23/0.97  --clausifier                            res/vclausify_rel
% 2.23/0.97  --clausifier_options                    --mode clausify
% 2.23/0.97  --stdin                                 false
% 2.23/0.97  --stats_out                             all
% 2.23/0.97  
% 2.23/0.97  ------ General Options
% 2.23/0.97  
% 2.23/0.97  --fof                                   false
% 2.23/0.97  --time_out_real                         305.
% 2.23/0.97  --time_out_virtual                      -1.
% 2.23/0.97  --symbol_type_check                     false
% 2.23/0.97  --clausify_out                          false
% 2.23/0.97  --sig_cnt_out                           false
% 2.23/0.97  --trig_cnt_out                          false
% 2.23/0.97  --trig_cnt_out_tolerance                1.
% 2.23/0.97  --trig_cnt_out_sk_spl                   false
% 2.23/0.97  --abstr_cl_out                          false
% 2.23/0.97  
% 2.23/0.97  ------ Global Options
% 2.23/0.97  
% 2.23/0.97  --schedule                              default
% 2.23/0.97  --add_important_lit                     false
% 2.23/0.97  --prop_solver_per_cl                    1000
% 2.23/0.97  --min_unsat_core                        false
% 2.23/0.97  --soft_assumptions                      false
% 2.23/0.97  --soft_lemma_size                       3
% 2.23/0.97  --prop_impl_unit_size                   0
% 2.23/0.97  --prop_impl_unit                        []
% 2.23/0.97  --share_sel_clauses                     true
% 2.23/0.97  --reset_solvers                         false
% 2.23/0.97  --bc_imp_inh                            [conj_cone]
% 2.23/0.97  --conj_cone_tolerance                   3.
% 2.23/0.97  --extra_neg_conj                        none
% 2.23/0.97  --large_theory_mode                     true
% 2.23/0.97  --prolific_symb_bound                   200
% 2.23/0.97  --lt_threshold                          2000
% 2.23/0.97  --clause_weak_htbl                      true
% 2.23/0.97  --gc_record_bc_elim                     false
% 2.23/0.97  
% 2.23/0.97  ------ Preprocessing Options
% 2.23/0.97  
% 2.23/0.97  --preprocessing_flag                    true
% 2.23/0.97  --time_out_prep_mult                    0.1
% 2.23/0.97  --splitting_mode                        input
% 2.23/0.97  --splitting_grd                         true
% 2.23/0.97  --splitting_cvd                         false
% 2.23/0.97  --splitting_cvd_svl                     false
% 2.23/0.97  --splitting_nvd                         32
% 2.23/0.97  --sub_typing                            true
% 2.23/0.97  --prep_gs_sim                           true
% 2.23/0.97  --prep_unflatten                        true
% 2.23/0.97  --prep_res_sim                          true
% 2.23/0.97  --prep_upred                            true
% 2.23/0.97  --prep_sem_filter                       exhaustive
% 2.23/0.97  --prep_sem_filter_out                   false
% 2.23/0.97  --pred_elim                             true
% 2.23/0.97  --res_sim_input                         true
% 2.23/0.97  --eq_ax_congr_red                       true
% 2.23/0.97  --pure_diseq_elim                       true
% 2.23/0.97  --brand_transform                       false
% 2.23/0.97  --non_eq_to_eq                          false
% 2.23/0.97  --prep_def_merge                        true
% 2.23/0.97  --prep_def_merge_prop_impl              false
% 2.23/0.97  --prep_def_merge_mbd                    true
% 2.23/0.97  --prep_def_merge_tr_red                 false
% 2.23/0.97  --prep_def_merge_tr_cl                  false
% 2.23/0.97  --smt_preprocessing                     true
% 2.23/0.97  --smt_ac_axioms                         fast
% 2.23/0.97  --preprocessed_out                      false
% 2.23/0.97  --preprocessed_stats                    false
% 2.23/0.97  
% 2.23/0.97  ------ Abstraction refinement Options
% 2.23/0.97  
% 2.23/0.97  --abstr_ref                             []
% 2.23/0.97  --abstr_ref_prep                        false
% 2.23/0.97  --abstr_ref_until_sat                   false
% 2.23/0.97  --abstr_ref_sig_restrict                funpre
% 2.23/0.97  --abstr_ref_af_restrict_to_split_sk     false
% 2.23/0.97  --abstr_ref_under                       []
% 2.23/0.97  
% 2.23/0.97  ------ SAT Options
% 2.23/0.97  
% 2.23/0.97  --sat_mode                              false
% 2.23/0.97  --sat_fm_restart_options                ""
% 2.23/0.97  --sat_gr_def                            false
% 2.23/0.97  --sat_epr_types                         true
% 2.23/0.97  --sat_non_cyclic_types                  false
% 2.23/0.97  --sat_finite_models                     false
% 2.23/0.97  --sat_fm_lemmas                         false
% 2.23/0.97  --sat_fm_prep                           false
% 2.23/0.97  --sat_fm_uc_incr                        true
% 2.23/0.97  --sat_out_model                         small
% 2.23/0.97  --sat_out_clauses                       false
% 2.23/0.97  
% 2.23/0.97  ------ QBF Options
% 2.23/0.97  
% 2.23/0.97  --qbf_mode                              false
% 2.23/0.97  --qbf_elim_univ                         false
% 2.23/0.97  --qbf_dom_inst                          none
% 2.23/0.97  --qbf_dom_pre_inst                      false
% 2.23/0.97  --qbf_sk_in                             false
% 2.23/0.97  --qbf_pred_elim                         true
% 2.23/0.97  --qbf_split                             512
% 2.23/0.97  
% 2.23/0.97  ------ BMC1 Options
% 2.23/0.97  
% 2.23/0.97  --bmc1_incremental                      false
% 2.23/0.97  --bmc1_axioms                           reachable_all
% 2.23/0.97  --bmc1_min_bound                        0
% 2.23/0.97  --bmc1_max_bound                        -1
% 2.23/0.97  --bmc1_max_bound_default                -1
% 2.23/0.97  --bmc1_symbol_reachability              true
% 2.23/0.97  --bmc1_property_lemmas                  false
% 2.23/0.97  --bmc1_k_induction                      false
% 2.23/0.97  --bmc1_non_equiv_states                 false
% 2.23/0.97  --bmc1_deadlock                         false
% 2.23/0.97  --bmc1_ucm                              false
% 2.23/0.97  --bmc1_add_unsat_core                   none
% 2.23/0.97  --bmc1_unsat_core_children              false
% 2.23/0.97  --bmc1_unsat_core_extrapolate_axioms    false
% 2.23/0.97  --bmc1_out_stat                         full
% 2.23/0.97  --bmc1_ground_init                      false
% 2.23/0.97  --bmc1_pre_inst_next_state              false
% 2.23/0.97  --bmc1_pre_inst_state                   false
% 2.23/0.97  --bmc1_pre_inst_reach_state             false
% 2.23/0.97  --bmc1_out_unsat_core                   false
% 2.23/0.97  --bmc1_aig_witness_out                  false
% 2.23/0.97  --bmc1_verbose                          false
% 2.23/0.97  --bmc1_dump_clauses_tptp                false
% 2.23/0.97  --bmc1_dump_unsat_core_tptp             false
% 2.23/0.97  --bmc1_dump_file                        -
% 2.23/0.97  --bmc1_ucm_expand_uc_limit              128
% 2.23/0.97  --bmc1_ucm_n_expand_iterations          6
% 2.23/0.97  --bmc1_ucm_extend_mode                  1
% 2.23/0.97  --bmc1_ucm_init_mode                    2
% 2.23/0.97  --bmc1_ucm_cone_mode                    none
% 2.23/0.97  --bmc1_ucm_reduced_relation_type        0
% 2.23/0.97  --bmc1_ucm_relax_model                  4
% 2.23/0.97  --bmc1_ucm_full_tr_after_sat            true
% 2.23/0.97  --bmc1_ucm_expand_neg_assumptions       false
% 2.23/0.97  --bmc1_ucm_layered_model                none
% 2.23/0.97  --bmc1_ucm_max_lemma_size               10
% 2.23/0.97  
% 2.23/0.97  ------ AIG Options
% 2.23/0.97  
% 2.23/0.97  --aig_mode                              false
% 2.23/0.97  
% 2.23/0.97  ------ Instantiation Options
% 2.23/0.97  
% 2.23/0.97  --instantiation_flag                    true
% 2.23/0.97  --inst_sos_flag                         false
% 2.23/0.97  --inst_sos_phase                        true
% 2.23/0.97  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.23/0.97  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.23/0.97  --inst_lit_sel_side                     num_symb
% 2.23/0.97  --inst_solver_per_active                1400
% 2.23/0.97  --inst_solver_calls_frac                1.
% 2.23/0.97  --inst_passive_queue_type               priority_queues
% 2.23/0.97  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.23/0.97  --inst_passive_queues_freq              [25;2]
% 2.23/0.97  --inst_dismatching                      true
% 2.23/0.97  --inst_eager_unprocessed_to_passive     true
% 2.23/0.97  --inst_prop_sim_given                   true
% 2.23/0.97  --inst_prop_sim_new                     false
% 2.23/0.97  --inst_subs_new                         false
% 2.23/0.97  --inst_eq_res_simp                      false
% 2.23/0.97  --inst_subs_given                       false
% 2.23/0.97  --inst_orphan_elimination               true
% 2.23/0.97  --inst_learning_loop_flag               true
% 2.23/0.97  --inst_learning_start                   3000
% 2.23/0.97  --inst_learning_factor                  2
% 2.23/0.97  --inst_start_prop_sim_after_learn       3
% 2.23/0.97  --inst_sel_renew                        solver
% 2.23/0.97  --inst_lit_activity_flag                true
% 2.23/0.97  --inst_restr_to_given                   false
% 2.23/0.97  --inst_activity_threshold               500
% 2.23/0.97  --inst_out_proof                        true
% 2.23/0.97  
% 2.23/0.97  ------ Resolution Options
% 2.23/0.97  
% 2.23/0.97  --resolution_flag                       true
% 2.23/0.97  --res_lit_sel                           adaptive
% 2.23/0.97  --res_lit_sel_side                      none
% 2.23/0.97  --res_ordering                          kbo
% 2.23/0.97  --res_to_prop_solver                    active
% 2.23/0.97  --res_prop_simpl_new                    false
% 2.23/0.97  --res_prop_simpl_given                  true
% 2.23/0.97  --res_passive_queue_type                priority_queues
% 2.23/0.97  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.23/0.97  --res_passive_queues_freq               [15;5]
% 2.23/0.97  --res_forward_subs                      full
% 2.23/0.97  --res_backward_subs                     full
% 2.23/0.97  --res_forward_subs_resolution           true
% 2.23/0.97  --res_backward_subs_resolution          true
% 2.23/0.97  --res_orphan_elimination                true
% 2.23/0.97  --res_time_limit                        2.
% 2.23/0.97  --res_out_proof                         true
% 2.23/0.97  
% 2.23/0.97  ------ Superposition Options
% 2.23/0.97  
% 2.23/0.97  --superposition_flag                    true
% 2.23/0.97  --sup_passive_queue_type                priority_queues
% 2.23/0.97  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.23/0.97  --sup_passive_queues_freq               [8;1;4]
% 2.23/0.97  --demod_completeness_check              fast
% 2.23/0.97  --demod_use_ground                      true
% 2.23/0.97  --sup_to_prop_solver                    passive
% 2.23/0.97  --sup_prop_simpl_new                    true
% 2.23/0.97  --sup_prop_simpl_given                  true
% 2.23/0.97  --sup_fun_splitting                     false
% 2.23/0.97  --sup_smt_interval                      50000
% 2.23/0.97  
% 2.23/0.97  ------ Superposition Simplification Setup
% 2.23/0.97  
% 2.23/0.97  --sup_indices_passive                   []
% 2.23/0.97  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.23/0.97  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.23/0.97  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.23/0.97  --sup_full_triv                         [TrivRules;PropSubs]
% 2.23/0.97  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.23/0.97  --sup_full_bw                           [BwDemod]
% 2.23/0.97  --sup_immed_triv                        [TrivRules]
% 2.23/0.97  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.23/0.97  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.23/0.97  --sup_immed_bw_main                     []
% 2.23/0.97  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.23/0.97  --sup_input_triv                        [Unflattening;TrivRules]
% 2.23/0.97  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.23/0.97  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.23/0.97  
% 2.23/0.97  ------ Combination Options
% 2.23/0.97  
% 2.23/0.97  --comb_res_mult                         3
% 2.23/0.97  --comb_sup_mult                         2
% 2.23/0.97  --comb_inst_mult                        10
% 2.23/0.97  
% 2.23/0.97  ------ Debug Options
% 2.23/0.97  
% 2.23/0.97  --dbg_backtrace                         false
% 2.23/0.97  --dbg_dump_prop_clauses                 false
% 2.23/0.97  --dbg_dump_prop_clauses_file            -
% 2.23/0.97  --dbg_out_stat                          false
% 2.23/0.97  ------ Parsing...
% 2.23/0.97  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.23/0.97  
% 2.23/0.97  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 2.23/0.97  
% 2.23/0.97  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.23/0.97  
% 2.23/0.97  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.23/0.97  ------ Proving...
% 2.23/0.97  ------ Problem Properties 
% 2.23/0.97  
% 2.23/0.97  
% 2.23/0.97  clauses                                 16
% 2.23/0.97  conjectures                             3
% 2.23/0.97  EPR                                     0
% 2.23/0.97  Horn                                    13
% 2.23/0.97  unary                                   2
% 2.23/0.97  binary                                  4
% 2.23/0.97  lits                                    47
% 2.23/0.97  lits eq                                 10
% 2.23/0.97  fd_pure                                 0
% 2.23/0.97  fd_pseudo                               0
% 2.23/0.97  fd_cond                                 0
% 2.23/0.97  fd_pseudo_cond                          4
% 2.23/0.97  AC symbols                              0
% 2.23/0.97  
% 2.23/0.97  ------ Schedule dynamic 5 is on 
% 2.23/0.97  
% 2.23/0.97  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.23/0.97  
% 2.23/0.97  
% 2.23/0.97  ------ 
% 2.23/0.97  Current options:
% 2.23/0.97  ------ 
% 2.23/0.97  
% 2.23/0.97  ------ Input Options
% 2.23/0.97  
% 2.23/0.97  --out_options                           all
% 2.23/0.97  --tptp_safe_out                         true
% 2.23/0.97  --problem_path                          ""
% 2.23/0.97  --include_path                          ""
% 2.23/0.97  --clausifier                            res/vclausify_rel
% 2.23/0.97  --clausifier_options                    --mode clausify
% 2.23/0.97  --stdin                                 false
% 2.23/0.97  --stats_out                             all
% 2.23/0.97  
% 2.23/0.97  ------ General Options
% 2.23/0.97  
% 2.23/0.97  --fof                                   false
% 2.23/0.97  --time_out_real                         305.
% 2.23/0.97  --time_out_virtual                      -1.
% 2.23/0.97  --symbol_type_check                     false
% 2.23/0.97  --clausify_out                          false
% 2.23/0.97  --sig_cnt_out                           false
% 2.23/0.97  --trig_cnt_out                          false
% 2.23/0.97  --trig_cnt_out_tolerance                1.
% 2.23/0.97  --trig_cnt_out_sk_spl                   false
% 2.23/0.97  --abstr_cl_out                          false
% 2.23/0.97  
% 2.23/0.97  ------ Global Options
% 2.23/0.97  
% 2.23/0.97  --schedule                              default
% 2.23/0.97  --add_important_lit                     false
% 2.23/0.97  --prop_solver_per_cl                    1000
% 2.23/0.97  --min_unsat_core                        false
% 2.23/0.97  --soft_assumptions                      false
% 2.23/0.97  --soft_lemma_size                       3
% 2.23/0.97  --prop_impl_unit_size                   0
% 2.23/0.97  --prop_impl_unit                        []
% 2.23/0.97  --share_sel_clauses                     true
% 2.23/0.97  --reset_solvers                         false
% 2.23/0.97  --bc_imp_inh                            [conj_cone]
% 2.23/0.97  --conj_cone_tolerance                   3.
% 2.23/0.97  --extra_neg_conj                        none
% 2.23/0.97  --large_theory_mode                     true
% 2.23/0.97  --prolific_symb_bound                   200
% 2.23/0.97  --lt_threshold                          2000
% 2.23/0.97  --clause_weak_htbl                      true
% 2.23/0.97  --gc_record_bc_elim                     false
% 2.23/0.97  
% 2.23/0.97  ------ Preprocessing Options
% 2.23/0.97  
% 2.23/0.97  --preprocessing_flag                    true
% 2.23/0.97  --time_out_prep_mult                    0.1
% 2.23/0.97  --splitting_mode                        input
% 2.23/0.97  --splitting_grd                         true
% 2.23/0.97  --splitting_cvd                         false
% 2.23/0.97  --splitting_cvd_svl                     false
% 2.23/0.97  --splitting_nvd                         32
% 2.23/0.97  --sub_typing                            true
% 2.23/0.97  --prep_gs_sim                           true
% 2.23/0.97  --prep_unflatten                        true
% 2.23/0.97  --prep_res_sim                          true
% 2.23/0.97  --prep_upred                            true
% 2.23/0.97  --prep_sem_filter                       exhaustive
% 2.23/0.97  --prep_sem_filter_out                   false
% 2.23/0.97  --pred_elim                             true
% 2.23/0.97  --res_sim_input                         true
% 2.23/0.97  --eq_ax_congr_red                       true
% 2.23/0.97  --pure_diseq_elim                       true
% 2.23/0.97  --brand_transform                       false
% 2.23/0.97  --non_eq_to_eq                          false
% 2.23/0.97  --prep_def_merge                        true
% 2.23/0.97  --prep_def_merge_prop_impl              false
% 2.23/0.97  --prep_def_merge_mbd                    true
% 2.23/0.97  --prep_def_merge_tr_red                 false
% 2.23/0.97  --prep_def_merge_tr_cl                  false
% 2.23/0.97  --smt_preprocessing                     true
% 2.23/0.97  --smt_ac_axioms                         fast
% 2.23/0.97  --preprocessed_out                      false
% 2.23/0.97  --preprocessed_stats                    false
% 2.23/0.97  
% 2.23/0.97  ------ Abstraction refinement Options
% 2.23/0.97  
% 2.23/0.97  --abstr_ref                             []
% 2.23/0.97  --abstr_ref_prep                        false
% 2.23/0.97  --abstr_ref_until_sat                   false
% 2.23/0.97  --abstr_ref_sig_restrict                funpre
% 2.23/0.97  --abstr_ref_af_restrict_to_split_sk     false
% 2.23/0.97  --abstr_ref_under                       []
% 2.23/0.97  
% 2.23/0.97  ------ SAT Options
% 2.23/0.97  
% 2.23/0.97  --sat_mode                              false
% 2.23/0.97  --sat_fm_restart_options                ""
% 2.23/0.97  --sat_gr_def                            false
% 2.23/0.97  --sat_epr_types                         true
% 2.23/0.97  --sat_non_cyclic_types                  false
% 2.23/0.97  --sat_finite_models                     false
% 2.23/0.97  --sat_fm_lemmas                         false
% 2.23/0.97  --sat_fm_prep                           false
% 2.23/0.97  --sat_fm_uc_incr                        true
% 2.23/0.97  --sat_out_model                         small
% 2.23/0.97  --sat_out_clauses                       false
% 2.23/0.97  
% 2.23/0.97  ------ QBF Options
% 2.23/0.97  
% 2.23/0.97  --qbf_mode                              false
% 2.23/0.97  --qbf_elim_univ                         false
% 2.23/0.97  --qbf_dom_inst                          none
% 2.23/0.97  --qbf_dom_pre_inst                      false
% 2.23/0.97  --qbf_sk_in                             false
% 2.23/0.97  --qbf_pred_elim                         true
% 2.23/0.97  --qbf_split                             512
% 2.23/0.97  
% 2.23/0.97  ------ BMC1 Options
% 2.23/0.97  
% 2.23/0.97  --bmc1_incremental                      false
% 2.23/0.97  --bmc1_axioms                           reachable_all
% 2.23/0.97  --bmc1_min_bound                        0
% 2.23/0.97  --bmc1_max_bound                        -1
% 2.23/0.97  --bmc1_max_bound_default                -1
% 2.23/0.97  --bmc1_symbol_reachability              true
% 2.23/0.98  --bmc1_property_lemmas                  false
% 2.23/0.98  --bmc1_k_induction                      false
% 2.23/0.98  --bmc1_non_equiv_states                 false
% 2.23/0.98  --bmc1_deadlock                         false
% 2.23/0.98  --bmc1_ucm                              false
% 2.23/0.98  --bmc1_add_unsat_core                   none
% 2.23/0.98  --bmc1_unsat_core_children              false
% 2.23/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 2.23/0.98  --bmc1_out_stat                         full
% 2.23/0.98  --bmc1_ground_init                      false
% 2.23/0.98  --bmc1_pre_inst_next_state              false
% 2.23/0.98  --bmc1_pre_inst_state                   false
% 2.23/0.98  --bmc1_pre_inst_reach_state             false
% 2.23/0.98  --bmc1_out_unsat_core                   false
% 2.23/0.98  --bmc1_aig_witness_out                  false
% 2.23/0.98  --bmc1_verbose                          false
% 2.23/0.98  --bmc1_dump_clauses_tptp                false
% 2.23/0.98  --bmc1_dump_unsat_core_tptp             false
% 2.23/0.98  --bmc1_dump_file                        -
% 2.23/0.98  --bmc1_ucm_expand_uc_limit              128
% 2.23/0.98  --bmc1_ucm_n_expand_iterations          6
% 2.23/0.98  --bmc1_ucm_extend_mode                  1
% 2.23/0.98  --bmc1_ucm_init_mode                    2
% 2.23/0.98  --bmc1_ucm_cone_mode                    none
% 2.23/0.98  --bmc1_ucm_reduced_relation_type        0
% 2.23/0.98  --bmc1_ucm_relax_model                  4
% 2.23/0.98  --bmc1_ucm_full_tr_after_sat            true
% 2.23/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 2.23/0.98  --bmc1_ucm_layered_model                none
% 2.23/0.98  --bmc1_ucm_max_lemma_size               10
% 2.23/0.98  
% 2.23/0.98  ------ AIG Options
% 2.23/0.98  
% 2.23/0.98  --aig_mode                              false
% 2.23/0.98  
% 2.23/0.98  ------ Instantiation Options
% 2.23/0.98  
% 2.23/0.98  --instantiation_flag                    true
% 2.23/0.98  --inst_sos_flag                         false
% 2.23/0.98  --inst_sos_phase                        true
% 2.23/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.23/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.23/0.98  --inst_lit_sel_side                     none
% 2.23/0.98  --inst_solver_per_active                1400
% 2.23/0.98  --inst_solver_calls_frac                1.
% 2.23/0.98  --inst_passive_queue_type               priority_queues
% 2.23/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.23/0.98  --inst_passive_queues_freq              [25;2]
% 2.23/0.98  --inst_dismatching                      true
% 2.23/0.98  --inst_eager_unprocessed_to_passive     true
% 2.23/0.98  --inst_prop_sim_given                   true
% 2.23/0.98  --inst_prop_sim_new                     false
% 2.23/0.98  --inst_subs_new                         false
% 2.23/0.98  --inst_eq_res_simp                      false
% 2.23/0.98  --inst_subs_given                       false
% 2.23/0.98  --inst_orphan_elimination               true
% 2.23/0.98  --inst_learning_loop_flag               true
% 2.23/0.98  --inst_learning_start                   3000
% 2.23/0.98  --inst_learning_factor                  2
% 2.23/0.98  --inst_start_prop_sim_after_learn       3
% 2.23/0.98  --inst_sel_renew                        solver
% 2.23/0.98  --inst_lit_activity_flag                true
% 2.23/0.98  --inst_restr_to_given                   false
% 2.23/0.98  --inst_activity_threshold               500
% 2.23/0.98  --inst_out_proof                        true
% 2.23/0.98  
% 2.23/0.98  ------ Resolution Options
% 2.23/0.98  
% 2.23/0.98  --resolution_flag                       false
% 2.23/0.98  --res_lit_sel                           adaptive
% 2.23/0.98  --res_lit_sel_side                      none
% 2.23/0.98  --res_ordering                          kbo
% 2.23/0.98  --res_to_prop_solver                    active
% 2.23/0.98  --res_prop_simpl_new                    false
% 2.23/0.98  --res_prop_simpl_given                  true
% 2.23/0.98  --res_passive_queue_type                priority_queues
% 2.23/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.23/0.98  --res_passive_queues_freq               [15;5]
% 2.23/0.98  --res_forward_subs                      full
% 2.23/0.98  --res_backward_subs                     full
% 2.23/0.98  --res_forward_subs_resolution           true
% 2.23/0.98  --res_backward_subs_resolution          true
% 2.23/0.98  --res_orphan_elimination                true
% 2.23/0.98  --res_time_limit                        2.
% 2.23/0.98  --res_out_proof                         true
% 2.23/0.98  
% 2.23/0.98  ------ Superposition Options
% 2.23/0.98  
% 2.23/0.98  --superposition_flag                    true
% 2.23/0.98  --sup_passive_queue_type                priority_queues
% 2.23/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.23/0.98  --sup_passive_queues_freq               [8;1;4]
% 2.23/0.98  --demod_completeness_check              fast
% 2.23/0.98  --demod_use_ground                      true
% 2.23/0.98  --sup_to_prop_solver                    passive
% 2.23/0.98  --sup_prop_simpl_new                    true
% 2.23/0.98  --sup_prop_simpl_given                  true
% 2.23/0.98  --sup_fun_splitting                     false
% 2.23/0.98  --sup_smt_interval                      50000
% 2.23/0.98  
% 2.23/0.98  ------ Superposition Simplification Setup
% 2.23/0.98  
% 2.23/0.98  --sup_indices_passive                   []
% 2.23/0.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.23/0.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.23/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.23/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 2.23/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.23/0.98  --sup_full_bw                           [BwDemod]
% 2.23/0.98  --sup_immed_triv                        [TrivRules]
% 2.23/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.23/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.23/0.98  --sup_immed_bw_main                     []
% 2.23/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.23/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 2.23/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.23/0.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.23/0.98  
% 2.23/0.98  ------ Combination Options
% 2.23/0.98  
% 2.23/0.98  --comb_res_mult                         3
% 2.23/0.98  --comb_sup_mult                         2
% 2.23/0.98  --comb_inst_mult                        10
% 2.23/0.98  
% 2.23/0.98  ------ Debug Options
% 2.23/0.98  
% 2.23/0.98  --dbg_backtrace                         false
% 2.23/0.98  --dbg_dump_prop_clauses                 false
% 2.23/0.98  --dbg_dump_prop_clauses_file            -
% 2.23/0.98  --dbg_out_stat                          false
% 2.23/0.98  
% 2.23/0.98  
% 2.23/0.98  
% 2.23/0.98  
% 2.23/0.98  ------ Proving...
% 2.23/0.98  
% 2.23/0.98  
% 2.23/0.98  % SZS status Theorem for theBenchmark.p
% 2.23/0.98  
% 2.23/0.98  % SZS output start CNFRefutation for theBenchmark.p
% 2.23/0.98  
% 2.23/0.98  fof(f2,axiom,(
% 2.23/0.98    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1,X2] : (k9_relat_1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> ? [X4] : (k1_funct_1(X0,X4) = X3 & r2_hidden(X4,X1) & r2_hidden(X4,k1_relat_1(X0))))))),
% 2.23/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.23/0.98  
% 2.23/0.98  fof(f12,plain,(
% 2.23/0.98    ! [X0] : (! [X1,X2] : (k9_relat_1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> ? [X4] : (k1_funct_1(X0,X4) = X3 & r2_hidden(X4,X1) & r2_hidden(X4,k1_relat_1(X0))))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 2.23/0.98    inference(ennf_transformation,[],[f2])).
% 2.23/0.98  
% 2.23/0.98  fof(f13,plain,(
% 2.23/0.98    ! [X0] : (! [X1,X2] : (k9_relat_1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> ? [X4] : (k1_funct_1(X0,X4) = X3 & r2_hidden(X4,X1) & r2_hidden(X4,k1_relat_1(X0))))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.23/0.98    inference(flattening,[],[f12])).
% 2.23/0.98  
% 2.23/0.98  fof(f20,plain,(
% 2.23/0.98    ! [X0] : (! [X1,X2] : ((k9_relat_1(X0,X1) = X2 | ? [X3] : ((! [X4] : (k1_funct_1(X0,X4) != X3 | ~r2_hidden(X4,X1) | ~r2_hidden(X4,k1_relat_1(X0))) | ~r2_hidden(X3,X2)) & (? [X4] : (k1_funct_1(X0,X4) = X3 & r2_hidden(X4,X1) & r2_hidden(X4,k1_relat_1(X0))) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | ! [X4] : (k1_funct_1(X0,X4) != X3 | ~r2_hidden(X4,X1) | ~r2_hidden(X4,k1_relat_1(X0)))) & (? [X4] : (k1_funct_1(X0,X4) = X3 & r2_hidden(X4,X1) & r2_hidden(X4,k1_relat_1(X0))) | ~r2_hidden(X3,X2))) | k9_relat_1(X0,X1) != X2)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.23/0.98    inference(nnf_transformation,[],[f13])).
% 2.23/0.98  
% 2.23/0.98  fof(f21,plain,(
% 2.23/0.98    ! [X0] : (! [X1,X2] : ((k9_relat_1(X0,X1) = X2 | ? [X3] : ((! [X4] : (k1_funct_1(X0,X4) != X3 | ~r2_hidden(X4,X1) | ~r2_hidden(X4,k1_relat_1(X0))) | ~r2_hidden(X3,X2)) & (? [X5] : (k1_funct_1(X0,X5) = X3 & r2_hidden(X5,X1) & r2_hidden(X5,k1_relat_1(X0))) | r2_hidden(X3,X2)))) & (! [X6] : ((r2_hidden(X6,X2) | ! [X7] : (k1_funct_1(X0,X7) != X6 | ~r2_hidden(X7,X1) | ~r2_hidden(X7,k1_relat_1(X0)))) & (? [X8] : (k1_funct_1(X0,X8) = X6 & r2_hidden(X8,X1) & r2_hidden(X8,k1_relat_1(X0))) | ~r2_hidden(X6,X2))) | k9_relat_1(X0,X1) != X2)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.23/0.98    inference(rectify,[],[f20])).
% 2.23/0.98  
% 2.23/0.98  fof(f24,plain,(
% 2.23/0.98    ! [X6,X1,X0] : (? [X8] : (k1_funct_1(X0,X8) = X6 & r2_hidden(X8,X1) & r2_hidden(X8,k1_relat_1(X0))) => (k1_funct_1(X0,sK2(X0,X1,X6)) = X6 & r2_hidden(sK2(X0,X1,X6),X1) & r2_hidden(sK2(X0,X1,X6),k1_relat_1(X0))))),
% 2.23/0.98    introduced(choice_axiom,[])).
% 2.23/0.98  
% 2.23/0.98  fof(f23,plain,(
% 2.23/0.98    ( ! [X3] : (! [X2,X1,X0] : (? [X5] : (k1_funct_1(X0,X5) = X3 & r2_hidden(X5,X1) & r2_hidden(X5,k1_relat_1(X0))) => (k1_funct_1(X0,sK1(X0,X1,X2)) = X3 & r2_hidden(sK1(X0,X1,X2),X1) & r2_hidden(sK1(X0,X1,X2),k1_relat_1(X0))))) )),
% 2.23/0.98    introduced(choice_axiom,[])).
% 2.23/0.98  
% 2.23/0.98  fof(f22,plain,(
% 2.23/0.98    ! [X2,X1,X0] : (? [X3] : ((! [X4] : (k1_funct_1(X0,X4) != X3 | ~r2_hidden(X4,X1) | ~r2_hidden(X4,k1_relat_1(X0))) | ~r2_hidden(X3,X2)) & (? [X5] : (k1_funct_1(X0,X5) = X3 & r2_hidden(X5,X1) & r2_hidden(X5,k1_relat_1(X0))) | r2_hidden(X3,X2))) => ((! [X4] : (k1_funct_1(X0,X4) != sK0(X0,X1,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,k1_relat_1(X0))) | ~r2_hidden(sK0(X0,X1,X2),X2)) & (? [X5] : (k1_funct_1(X0,X5) = sK0(X0,X1,X2) & r2_hidden(X5,X1) & r2_hidden(X5,k1_relat_1(X0))) | r2_hidden(sK0(X0,X1,X2),X2))))),
% 2.23/0.98    introduced(choice_axiom,[])).
% 2.23/0.98  
% 2.23/0.98  fof(f25,plain,(
% 2.23/0.98    ! [X0] : (! [X1,X2] : ((k9_relat_1(X0,X1) = X2 | ((! [X4] : (k1_funct_1(X0,X4) != sK0(X0,X1,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,k1_relat_1(X0))) | ~r2_hidden(sK0(X0,X1,X2),X2)) & ((k1_funct_1(X0,sK1(X0,X1,X2)) = sK0(X0,X1,X2) & r2_hidden(sK1(X0,X1,X2),X1) & r2_hidden(sK1(X0,X1,X2),k1_relat_1(X0))) | r2_hidden(sK0(X0,X1,X2),X2)))) & (! [X6] : ((r2_hidden(X6,X2) | ! [X7] : (k1_funct_1(X0,X7) != X6 | ~r2_hidden(X7,X1) | ~r2_hidden(X7,k1_relat_1(X0)))) & ((k1_funct_1(X0,sK2(X0,X1,X6)) = X6 & r2_hidden(sK2(X0,X1,X6),X1) & r2_hidden(sK2(X0,X1,X6),k1_relat_1(X0))) | ~r2_hidden(X6,X2))) | k9_relat_1(X0,X1) != X2)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.23/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f21,f24,f23,f22])).
% 2.23/0.98  
% 2.23/0.98  fof(f30,plain,(
% 2.23/0.98    ( ! [X6,X2,X0,X1] : (r2_hidden(sK2(X0,X1,X6),k1_relat_1(X0)) | ~r2_hidden(X6,X2) | k9_relat_1(X0,X1) != X2 | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.23/0.98    inference(cnf_transformation,[],[f25])).
% 2.23/0.98  
% 2.23/0.98  fof(f50,plain,(
% 2.23/0.98    ( ! [X6,X0,X1] : (r2_hidden(sK2(X0,X1,X6),k1_relat_1(X0)) | ~r2_hidden(X6,k9_relat_1(X0,X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.23/0.98    inference(equality_resolution,[],[f30])).
% 2.23/0.98  
% 2.23/0.98  fof(f7,conjecture,(
% 2.23/0.98    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ! [X4] : ~(! [X5] : (m1_subset_1(X5,X0) => ~(k1_funct_1(X3,X5) = X4 & r2_hidden(X5,X2))) & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2))))),
% 2.23/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.23/0.98  
% 2.23/0.98  fof(f8,negated_conjecture,(
% 2.23/0.98    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ! [X4] : ~(! [X5] : (m1_subset_1(X5,X0) => ~(k1_funct_1(X3,X5) = X4 & r2_hidden(X5,X2))) & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2))))),
% 2.23/0.98    inference(negated_conjecture,[],[f7])).
% 2.23/0.98  
% 2.23/0.98  fof(f9,plain,(
% 2.23/0.98    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X3)) => ! [X4] : ~(! [X5] : (m1_subset_1(X5,X0) => ~(k1_funct_1(X3,X5) = X4 & r2_hidden(X5,X2))) & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2))))),
% 2.23/0.98    inference(pure_predicate_removal,[],[f8])).
% 2.23/0.98  
% 2.23/0.98  fof(f18,plain,(
% 2.23/0.98    ? [X0,X1,X2,X3] : (? [X4] : (! [X5] : ((k1_funct_1(X3,X5) != X4 | ~r2_hidden(X5,X2)) | ~m1_subset_1(X5,X0)) & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2))) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X3)))),
% 2.23/0.98    inference(ennf_transformation,[],[f9])).
% 2.23/0.98  
% 2.23/0.98  fof(f19,plain,(
% 2.23/0.98    ? [X0,X1,X2,X3] : (? [X4] : (! [X5] : (k1_funct_1(X3,X5) != X4 | ~r2_hidden(X5,X2) | ~m1_subset_1(X5,X0)) & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2))) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X3))),
% 2.23/0.98    inference(flattening,[],[f18])).
% 2.23/0.98  
% 2.23/0.98  fof(f27,plain,(
% 2.23/0.98    ( ! [X2,X0,X3,X1] : (? [X4] : (! [X5] : (k1_funct_1(X3,X5) != X4 | ~r2_hidden(X5,X2) | ~m1_subset_1(X5,X0)) & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2))) => (! [X5] : (k1_funct_1(X3,X5) != sK7 | ~r2_hidden(X5,X2) | ~m1_subset_1(X5,X0)) & r2_hidden(sK7,k7_relset_1(X0,X1,X3,X2)))) )),
% 2.23/0.98    introduced(choice_axiom,[])).
% 2.23/0.98  
% 2.23/0.98  fof(f26,plain,(
% 2.23/0.98    ? [X0,X1,X2,X3] : (? [X4] : (! [X5] : (k1_funct_1(X3,X5) != X4 | ~r2_hidden(X5,X2) | ~m1_subset_1(X5,X0)) & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2))) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X3)) => (? [X4] : (! [X5] : (k1_funct_1(sK6,X5) != X4 | ~r2_hidden(X5,sK5) | ~m1_subset_1(X5,sK3)) & r2_hidden(X4,k7_relset_1(sK3,sK4,sK6,sK5))) & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) & v1_funct_1(sK6))),
% 2.23/0.98    introduced(choice_axiom,[])).
% 2.23/0.98  
% 2.23/0.98  fof(f28,plain,(
% 2.23/0.98    (! [X5] : (k1_funct_1(sK6,X5) != sK7 | ~r2_hidden(X5,sK5) | ~m1_subset_1(X5,sK3)) & r2_hidden(sK7,k7_relset_1(sK3,sK4,sK6,sK5))) & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) & v1_funct_1(sK6)),
% 2.23/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5,sK6,sK7])],[f19,f27,f26])).
% 2.23/0.98  
% 2.23/0.98  fof(f42,plain,(
% 2.23/0.98    v1_funct_1(sK6)),
% 2.23/0.98    inference(cnf_transformation,[],[f28])).
% 2.23/0.98  
% 2.23/0.98  fof(f43,plain,(
% 2.23/0.98    m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))),
% 2.23/0.98    inference(cnf_transformation,[],[f28])).
% 2.23/0.98  
% 2.23/0.98  fof(f3,axiom,(
% 2.23/0.98    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 2.23/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.23/0.98  
% 2.23/0.98  fof(f14,plain,(
% 2.23/0.98    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.23/0.98    inference(ennf_transformation,[],[f3])).
% 2.23/0.98  
% 2.23/0.98  fof(f38,plain,(
% 2.23/0.98    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.23/0.98    inference(cnf_transformation,[],[f14])).
% 2.23/0.98  
% 2.23/0.98  fof(f5,axiom,(
% 2.23/0.98    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 2.23/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.23/0.98  
% 2.23/0.98  fof(f16,plain,(
% 2.23/0.98    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.23/0.98    inference(ennf_transformation,[],[f5])).
% 2.23/0.98  
% 2.23/0.98  fof(f40,plain,(
% 2.23/0.98    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.23/0.98    inference(cnf_transformation,[],[f16])).
% 2.23/0.98  
% 2.23/0.98  fof(f4,axiom,(
% 2.23/0.98    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0)))),
% 2.23/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.23/0.98  
% 2.23/0.98  fof(f15,plain,(
% 2.23/0.98    ! [X0,X1,X2] : (m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.23/0.98    inference(ennf_transformation,[],[f4])).
% 2.23/0.98  
% 2.23/0.98  fof(f39,plain,(
% 2.23/0.98    ( ! [X2,X0,X1] : (m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.23/0.98    inference(cnf_transformation,[],[f15])).
% 2.23/0.98  
% 2.23/0.98  fof(f1,axiom,(
% 2.23/0.98    ! [X0,X1,X2] : ((m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1)) => m1_subset_1(X0,X2))),
% 2.23/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.23/0.98  
% 2.23/0.98  fof(f10,plain,(
% 2.23/0.98    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)))),
% 2.23/0.98    inference(ennf_transformation,[],[f1])).
% 2.23/0.98  
% 2.23/0.98  fof(f11,plain,(
% 2.23/0.98    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 2.23/0.98    inference(flattening,[],[f10])).
% 2.23/0.98  
% 2.23/0.98  fof(f29,plain,(
% 2.23/0.98    ( ! [X2,X0,X1] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) )),
% 2.23/0.98    inference(cnf_transformation,[],[f11])).
% 2.23/0.98  
% 2.23/0.98  fof(f31,plain,(
% 2.23/0.98    ( ! [X6,X2,X0,X1] : (r2_hidden(sK2(X0,X1,X6),X1) | ~r2_hidden(X6,X2) | k9_relat_1(X0,X1) != X2 | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.23/0.98    inference(cnf_transformation,[],[f25])).
% 2.23/0.98  
% 2.23/0.98  fof(f49,plain,(
% 2.23/0.98    ( ! [X6,X0,X1] : (r2_hidden(sK2(X0,X1,X6),X1) | ~r2_hidden(X6,k9_relat_1(X0,X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.23/0.98    inference(equality_resolution,[],[f31])).
% 2.23/0.98  
% 2.23/0.98  fof(f6,axiom,(
% 2.23/0.98    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3))),
% 2.23/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.23/0.98  
% 2.23/0.98  fof(f17,plain,(
% 2.23/0.98    ! [X0,X1,X2,X3] : (k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.23/0.98    inference(ennf_transformation,[],[f6])).
% 2.23/0.98  
% 2.23/0.98  fof(f41,plain,(
% 2.23/0.98    ( ! [X2,X0,X3,X1] : (k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.23/0.98    inference(cnf_transformation,[],[f17])).
% 2.23/0.98  
% 2.23/0.98  fof(f44,plain,(
% 2.23/0.98    r2_hidden(sK7,k7_relset_1(sK3,sK4,sK6,sK5))),
% 2.23/0.98    inference(cnf_transformation,[],[f28])).
% 2.23/0.98  
% 2.23/0.98  fof(f32,plain,(
% 2.23/0.98    ( ! [X6,X2,X0,X1] : (k1_funct_1(X0,sK2(X0,X1,X6)) = X6 | ~r2_hidden(X6,X2) | k9_relat_1(X0,X1) != X2 | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.23/0.98    inference(cnf_transformation,[],[f25])).
% 2.23/0.98  
% 2.23/0.98  fof(f48,plain,(
% 2.23/0.98    ( ! [X6,X0,X1] : (k1_funct_1(X0,sK2(X0,X1,X6)) = X6 | ~r2_hidden(X6,k9_relat_1(X0,X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.23/0.98    inference(equality_resolution,[],[f32])).
% 2.23/0.98  
% 2.23/0.98  fof(f45,plain,(
% 2.23/0.98    ( ! [X5] : (k1_funct_1(sK6,X5) != sK7 | ~r2_hidden(X5,sK5) | ~m1_subset_1(X5,sK3)) )),
% 2.23/0.98    inference(cnf_transformation,[],[f28])).
% 2.23/0.98  
% 2.23/0.98  cnf(c_8,plain,
% 2.23/0.98      ( ~ r2_hidden(X0,k9_relat_1(X1,X2))
% 2.23/0.98      | r2_hidden(sK2(X1,X2,X0),k1_relat_1(X1))
% 2.23/0.98      | ~ v1_relat_1(X1)
% 2.23/0.98      | ~ v1_funct_1(X1) ),
% 2.23/0.98      inference(cnf_transformation,[],[f50]) ).
% 2.23/0.98  
% 2.23/0.98  cnf(c_16,negated_conjecture,
% 2.23/0.98      ( v1_funct_1(sK6) ),
% 2.23/0.98      inference(cnf_transformation,[],[f42]) ).
% 2.23/0.98  
% 2.23/0.98  cnf(c_291,plain,
% 2.23/0.98      ( ~ r2_hidden(X0,k9_relat_1(X1,X2))
% 2.23/0.98      | r2_hidden(sK2(X1,X2,X0),k1_relat_1(X1))
% 2.23/0.98      | ~ v1_relat_1(X1)
% 2.23/0.98      | sK6 != X1 ),
% 2.23/0.98      inference(resolution_lifted,[status(thm)],[c_8,c_16]) ).
% 2.23/0.98  
% 2.23/0.98  cnf(c_292,plain,
% 2.23/0.98      ( ~ r2_hidden(X0,k9_relat_1(sK6,X1))
% 2.23/0.98      | r2_hidden(sK2(sK6,X1,X0),k1_relat_1(sK6))
% 2.23/0.98      | ~ v1_relat_1(sK6) ),
% 2.23/0.98      inference(unflattening,[status(thm)],[c_291]) ).
% 2.23/0.98  
% 2.23/0.98  cnf(c_1120,plain,
% 2.23/0.98      ( r2_hidden(X0,k9_relat_1(sK6,X1)) != iProver_top
% 2.23/0.98      | r2_hidden(sK2(sK6,X1,X0),k1_relat_1(sK6)) = iProver_top
% 2.23/0.98      | v1_relat_1(sK6) != iProver_top ),
% 2.23/0.98      inference(predicate_to_equality,[status(thm)],[c_292]) ).
% 2.23/0.98  
% 2.23/0.98  cnf(c_15,negated_conjecture,
% 2.23/0.98      ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) ),
% 2.23/0.98      inference(cnf_transformation,[],[f43]) ).
% 2.23/0.98  
% 2.23/0.98  cnf(c_18,plain,
% 2.23/0.98      ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) = iProver_top ),
% 2.23/0.98      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 2.23/0.98  
% 2.23/0.98  cnf(c_293,plain,
% 2.23/0.98      ( r2_hidden(X0,k9_relat_1(sK6,X1)) != iProver_top
% 2.23/0.98      | r2_hidden(sK2(sK6,X1,X0),k1_relat_1(sK6)) = iProver_top
% 2.23/0.98      | v1_relat_1(sK6) != iProver_top ),
% 2.23/0.98      inference(predicate_to_equality,[status(thm)],[c_292]) ).
% 2.23/0.98  
% 2.23/0.98  cnf(c_9,plain,
% 2.23/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.23/0.98      | v1_relat_1(X0) ),
% 2.23/0.98      inference(cnf_transformation,[],[f38]) ).
% 2.23/0.98  
% 2.23/0.98  cnf(c_1267,plain,
% 2.23/0.98      ( ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))
% 2.23/0.98      | v1_relat_1(sK6) ),
% 2.23/0.98      inference(instantiation,[status(thm)],[c_9]) ).
% 2.23/0.98  
% 2.23/0.98  cnf(c_1268,plain,
% 2.23/0.98      ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) != iProver_top
% 2.23/0.98      | v1_relat_1(sK6) = iProver_top ),
% 2.23/0.98      inference(predicate_to_equality,[status(thm)],[c_1267]) ).
% 2.23/0.98  
% 2.23/0.98  cnf(c_1323,plain,
% 2.23/0.98      ( r2_hidden(sK2(sK6,X1,X0),k1_relat_1(sK6)) = iProver_top
% 2.23/0.98      | r2_hidden(X0,k9_relat_1(sK6,X1)) != iProver_top ),
% 2.23/0.98      inference(global_propositional_subsumption,
% 2.23/0.98                [status(thm)],
% 2.23/0.98                [c_1120,c_18,c_293,c_1268]) ).
% 2.23/0.98  
% 2.23/0.98  cnf(c_1324,plain,
% 2.23/0.98      ( r2_hidden(X0,k9_relat_1(sK6,X1)) != iProver_top
% 2.23/0.98      | r2_hidden(sK2(sK6,X1,X0),k1_relat_1(sK6)) = iProver_top ),
% 2.23/0.98      inference(renaming,[status(thm)],[c_1323]) ).
% 2.23/0.98  
% 2.23/0.98  cnf(c_1126,plain,
% 2.23/0.98      ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) = iProver_top ),
% 2.23/0.98      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 2.23/0.98  
% 2.23/0.98  cnf(c_11,plain,
% 2.23/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.23/0.98      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 2.23/0.98      inference(cnf_transformation,[],[f40]) ).
% 2.23/0.98  
% 2.23/0.98  cnf(c_1130,plain,
% 2.23/0.98      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 2.23/0.98      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 2.23/0.98      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 2.23/0.98  
% 2.23/0.98  cnf(c_1536,plain,
% 2.23/0.98      ( k1_relset_1(sK3,sK4,sK6) = k1_relat_1(sK6) ),
% 2.23/0.98      inference(superposition,[status(thm)],[c_1126,c_1130]) ).
% 2.23/0.98  
% 2.23/0.98  cnf(c_10,plain,
% 2.23/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.23/0.98      | m1_subset_1(k1_relset_1(X1,X2,X0),k1_zfmisc_1(X1)) ),
% 2.23/0.98      inference(cnf_transformation,[],[f39]) ).
% 2.23/0.98  
% 2.23/0.98  cnf(c_1131,plain,
% 2.23/0.98      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 2.23/0.98      | m1_subset_1(k1_relset_1(X1,X2,X0),k1_zfmisc_1(X1)) = iProver_top ),
% 2.23/0.98      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 2.23/0.98  
% 2.23/0.98  cnf(c_1717,plain,
% 2.23/0.98      ( m1_subset_1(k1_relat_1(sK6),k1_zfmisc_1(sK3)) = iProver_top
% 2.23/0.98      | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) != iProver_top ),
% 2.23/0.98      inference(superposition,[status(thm)],[c_1536,c_1131]) ).
% 2.23/0.98  
% 2.23/0.98  cnf(c_2206,plain,
% 2.23/0.98      ( m1_subset_1(k1_relat_1(sK6),k1_zfmisc_1(sK3)) = iProver_top ),
% 2.23/0.98      inference(global_propositional_subsumption,
% 2.23/0.98                [status(thm)],
% 2.23/0.98                [c_1717,c_18]) ).
% 2.23/0.98  
% 2.23/0.98  cnf(c_0,plain,
% 2.23/0.98      ( ~ r2_hidden(X0,X1)
% 2.23/0.98      | m1_subset_1(X0,X2)
% 2.23/0.98      | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
% 2.23/0.98      inference(cnf_transformation,[],[f29]) ).
% 2.23/0.98  
% 2.23/0.98  cnf(c_1133,plain,
% 2.23/0.98      ( r2_hidden(X0,X1) != iProver_top
% 2.23/0.98      | m1_subset_1(X0,X2) = iProver_top
% 2.23/0.98      | m1_subset_1(X1,k1_zfmisc_1(X2)) != iProver_top ),
% 2.23/0.98      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 2.23/0.98  
% 2.23/0.98  cnf(c_2211,plain,
% 2.23/0.98      ( r2_hidden(X0,k1_relat_1(sK6)) != iProver_top
% 2.23/0.98      | m1_subset_1(X0,sK3) = iProver_top ),
% 2.23/0.98      inference(superposition,[status(thm)],[c_2206,c_1133]) ).
% 2.23/0.98  
% 2.23/0.98  cnf(c_2346,plain,
% 2.23/0.98      ( r2_hidden(X0,k9_relat_1(sK6,X1)) != iProver_top
% 2.23/0.98      | m1_subset_1(sK2(sK6,X1,X0),sK3) = iProver_top ),
% 2.23/0.98      inference(superposition,[status(thm)],[c_1324,c_2211]) ).
% 2.23/0.98  
% 2.23/0.98  cnf(c_7,plain,
% 2.23/0.98      ( ~ r2_hidden(X0,k9_relat_1(X1,X2))
% 2.23/0.98      | r2_hidden(sK2(X1,X2,X0),X2)
% 2.23/0.98      | ~ v1_relat_1(X1)
% 2.23/0.98      | ~ v1_funct_1(X1) ),
% 2.23/0.98      inference(cnf_transformation,[],[f49]) ).
% 2.23/0.98  
% 2.23/0.98  cnf(c_306,plain,
% 2.23/0.98      ( ~ r2_hidden(X0,k9_relat_1(X1,X2))
% 2.23/0.98      | r2_hidden(sK2(X1,X2,X0),X2)
% 2.23/0.98      | ~ v1_relat_1(X1)
% 2.23/0.98      | sK6 != X1 ),
% 2.23/0.98      inference(resolution_lifted,[status(thm)],[c_7,c_16]) ).
% 2.23/0.98  
% 2.23/0.98  cnf(c_307,plain,
% 2.23/0.98      ( ~ r2_hidden(X0,k9_relat_1(sK6,X1))
% 2.23/0.98      | r2_hidden(sK2(sK6,X1,X0),X1)
% 2.23/0.98      | ~ v1_relat_1(sK6) ),
% 2.23/0.98      inference(unflattening,[status(thm)],[c_306]) ).
% 2.23/0.98  
% 2.23/0.98  cnf(c_1119,plain,
% 2.23/0.98      ( r2_hidden(X0,k9_relat_1(sK6,X1)) != iProver_top
% 2.23/0.98      | r2_hidden(sK2(sK6,X1,X0),X1) = iProver_top
% 2.23/0.98      | v1_relat_1(sK6) != iProver_top ),
% 2.23/0.98      inference(predicate_to_equality,[status(thm)],[c_307]) ).
% 2.23/0.98  
% 2.23/0.98  cnf(c_308,plain,
% 2.23/0.98      ( r2_hidden(X0,k9_relat_1(sK6,X1)) != iProver_top
% 2.23/0.98      | r2_hidden(sK2(sK6,X1,X0),X1) = iProver_top
% 2.23/0.98      | v1_relat_1(sK6) != iProver_top ),
% 2.23/0.98      inference(predicate_to_equality,[status(thm)],[c_307]) ).
% 2.23/0.98  
% 2.23/0.98  cnf(c_1310,plain,
% 2.23/0.98      ( r2_hidden(sK2(sK6,X1,X0),X1) = iProver_top
% 2.23/0.98      | r2_hidden(X0,k9_relat_1(sK6,X1)) != iProver_top ),
% 2.23/0.98      inference(global_propositional_subsumption,
% 2.23/0.98                [status(thm)],
% 2.23/0.98                [c_1119,c_18,c_308,c_1268]) ).
% 2.23/0.98  
% 2.23/0.98  cnf(c_1311,plain,
% 2.23/0.98      ( r2_hidden(X0,k9_relat_1(sK6,X1)) != iProver_top
% 2.23/0.98      | r2_hidden(sK2(sK6,X1,X0),X1) = iProver_top ),
% 2.23/0.98      inference(renaming,[status(thm)],[c_1310]) ).
% 2.23/0.98  
% 2.23/0.98  cnf(c_12,plain,
% 2.23/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.23/0.98      | k7_relset_1(X1,X2,X0,X3) = k9_relat_1(X0,X3) ),
% 2.23/0.98      inference(cnf_transformation,[],[f41]) ).
% 2.23/0.98  
% 2.23/0.98  cnf(c_1129,plain,
% 2.23/0.98      ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
% 2.23/0.98      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 2.23/0.98      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 2.23/0.98  
% 2.23/0.98  cnf(c_1540,plain,
% 2.23/0.98      ( k7_relset_1(sK3,sK4,sK6,X0) = k9_relat_1(sK6,X0) ),
% 2.23/0.98      inference(superposition,[status(thm)],[c_1126,c_1129]) ).
% 2.23/0.98  
% 2.23/0.98  cnf(c_14,negated_conjecture,
% 2.23/0.98      ( r2_hidden(sK7,k7_relset_1(sK3,sK4,sK6,sK5)) ),
% 2.23/0.98      inference(cnf_transformation,[],[f44]) ).
% 2.23/0.98  
% 2.23/0.98  cnf(c_1127,plain,
% 2.23/0.98      ( r2_hidden(sK7,k7_relset_1(sK3,sK4,sK6,sK5)) = iProver_top ),
% 2.23/0.98      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 2.23/0.98  
% 2.23/0.98  cnf(c_1720,plain,
% 2.23/0.98      ( r2_hidden(sK7,k9_relat_1(sK6,sK5)) = iProver_top ),
% 2.23/0.98      inference(demodulation,[status(thm)],[c_1540,c_1127]) ).
% 2.23/0.98  
% 2.23/0.98  cnf(c_6,plain,
% 2.23/0.98      ( ~ r2_hidden(X0,k9_relat_1(X1,X2))
% 2.23/0.98      | ~ v1_relat_1(X1)
% 2.23/0.98      | ~ v1_funct_1(X1)
% 2.23/0.98      | k1_funct_1(X1,sK2(X1,X2,X0)) = X0 ),
% 2.23/0.98      inference(cnf_transformation,[],[f48]) ).
% 2.23/0.98  
% 2.23/0.98  cnf(c_321,plain,
% 2.23/0.98      ( ~ r2_hidden(X0,k9_relat_1(X1,X2))
% 2.23/0.98      | ~ v1_relat_1(X1)
% 2.23/0.98      | k1_funct_1(X1,sK2(X1,X2,X0)) = X0
% 2.23/0.98      | sK6 != X1 ),
% 2.23/0.98      inference(resolution_lifted,[status(thm)],[c_6,c_16]) ).
% 2.23/0.98  
% 2.23/0.98  cnf(c_322,plain,
% 2.23/0.98      ( ~ r2_hidden(X0,k9_relat_1(sK6,X1))
% 2.23/0.98      | ~ v1_relat_1(sK6)
% 2.23/0.98      | k1_funct_1(sK6,sK2(sK6,X1,X0)) = X0 ),
% 2.23/0.98      inference(unflattening,[status(thm)],[c_321]) ).
% 2.23/0.98  
% 2.23/0.98  cnf(c_1118,plain,
% 2.23/0.98      ( k1_funct_1(sK6,sK2(sK6,X0,X1)) = X1
% 2.23/0.98      | r2_hidden(X1,k9_relat_1(sK6,X0)) != iProver_top
% 2.23/0.98      | v1_relat_1(sK6) != iProver_top ),
% 2.23/0.98      inference(predicate_to_equality,[status(thm)],[c_322]) ).
% 2.23/0.98  
% 2.23/0.98  cnf(c_323,plain,
% 2.23/0.98      ( k1_funct_1(sK6,sK2(sK6,X0,X1)) = X1
% 2.23/0.98      | r2_hidden(X1,k9_relat_1(sK6,X0)) != iProver_top
% 2.23/0.98      | v1_relat_1(sK6) != iProver_top ),
% 2.23/0.98      inference(predicate_to_equality,[status(thm)],[c_322]) ).
% 2.23/0.98  
% 2.23/0.98  cnf(c_1283,plain,
% 2.23/0.98      ( r2_hidden(X1,k9_relat_1(sK6,X0)) != iProver_top
% 2.23/0.98      | k1_funct_1(sK6,sK2(sK6,X0,X1)) = X1 ),
% 2.23/0.98      inference(global_propositional_subsumption,
% 2.23/0.98                [status(thm)],
% 2.23/0.98                [c_1118,c_18,c_323,c_1268]) ).
% 2.23/0.98  
% 2.23/0.98  cnf(c_1284,plain,
% 2.23/0.98      ( k1_funct_1(sK6,sK2(sK6,X0,X1)) = X1
% 2.23/0.98      | r2_hidden(X1,k9_relat_1(sK6,X0)) != iProver_top ),
% 2.23/0.98      inference(renaming,[status(thm)],[c_1283]) ).
% 2.23/0.98  
% 2.23/0.98  cnf(c_1794,plain,
% 2.23/0.98      ( k1_funct_1(sK6,sK2(sK6,sK5,sK7)) = sK7 ),
% 2.23/0.98      inference(superposition,[status(thm)],[c_1720,c_1284]) ).
% 2.23/0.98  
% 2.23/0.98  cnf(c_13,negated_conjecture,
% 2.23/0.98      ( ~ r2_hidden(X0,sK5)
% 2.23/0.98      | ~ m1_subset_1(X0,sK3)
% 2.23/0.98      | k1_funct_1(sK6,X0) != sK7 ),
% 2.23/0.98      inference(cnf_transformation,[],[f45]) ).
% 2.23/0.98  
% 2.23/0.98  cnf(c_1128,plain,
% 2.23/0.98      ( k1_funct_1(sK6,X0) != sK7
% 2.23/0.98      | r2_hidden(X0,sK5) != iProver_top
% 2.23/0.98      | m1_subset_1(X0,sK3) != iProver_top ),
% 2.23/0.98      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 2.23/0.98  
% 2.23/0.98  cnf(c_1968,plain,
% 2.23/0.98      ( r2_hidden(sK2(sK6,sK5,sK7),sK5) != iProver_top
% 2.23/0.98      | m1_subset_1(sK2(sK6,sK5,sK7),sK3) != iProver_top ),
% 2.23/0.98      inference(superposition,[status(thm)],[c_1794,c_1128]) ).
% 2.23/0.98  
% 2.23/0.98  cnf(c_2067,plain,
% 2.23/0.98      ( r2_hidden(sK7,k9_relat_1(sK6,sK5)) != iProver_top
% 2.23/0.98      | m1_subset_1(sK2(sK6,sK5,sK7),sK3) != iProver_top ),
% 2.23/0.98      inference(superposition,[status(thm)],[c_1311,c_1968]) ).
% 2.23/0.98  
% 2.23/0.98  cnf(c_2489,plain,
% 2.23/0.98      ( m1_subset_1(sK2(sK6,sK5,sK7),sK3) != iProver_top ),
% 2.23/0.98      inference(global_propositional_subsumption,
% 2.23/0.98                [status(thm)],
% 2.23/0.98                [c_2067,c_1720]) ).
% 2.23/0.98  
% 2.23/0.98  cnf(c_2494,plain,
% 2.23/0.98      ( r2_hidden(sK7,k9_relat_1(sK6,sK5)) != iProver_top ),
% 2.23/0.98      inference(superposition,[status(thm)],[c_2346,c_2489]) ).
% 2.23/0.98  
% 2.23/0.98  cnf(contradiction,plain,
% 2.23/0.98      ( $false ),
% 2.23/0.98      inference(minisat,[status(thm)],[c_2494,c_1720]) ).
% 2.23/0.98  
% 2.23/0.98  
% 2.23/0.98  % SZS output end CNFRefutation for theBenchmark.p
% 2.23/0.98  
% 2.23/0.98  ------                               Statistics
% 2.23/0.98  
% 2.23/0.98  ------ General
% 2.23/0.98  
% 2.23/0.98  abstr_ref_over_cycles:                  0
% 2.23/0.98  abstr_ref_under_cycles:                 0
% 2.23/0.98  gc_basic_clause_elim:                   0
% 2.23/0.98  forced_gc_time:                         0
% 2.23/0.98  parsing_time:                           0.009
% 2.23/0.98  unif_index_cands_time:                  0.
% 2.23/0.98  unif_index_add_time:                    0.
% 2.23/0.98  orderings_time:                         0.
% 2.23/0.98  out_proof_time:                         0.012
% 2.23/0.98  total_time:                             0.118
% 2.23/0.98  num_of_symbols:                         50
% 2.23/0.98  num_of_terms:                           2469
% 2.23/0.98  
% 2.23/0.98  ------ Preprocessing
% 2.23/0.98  
% 2.23/0.98  num_of_splits:                          0
% 2.23/0.98  num_of_split_atoms:                     0
% 2.23/0.98  num_of_reused_defs:                     0
% 2.23/0.98  num_eq_ax_congr_red:                    36
% 2.23/0.98  num_of_sem_filtered_clauses:            1
% 2.23/0.98  num_of_subtypes:                        0
% 2.23/0.98  monotx_restored_types:                  0
% 2.23/0.98  sat_num_of_epr_types:                   0
% 2.23/0.98  sat_num_of_non_cyclic_types:            0
% 2.23/0.98  sat_guarded_non_collapsed_types:        0
% 2.23/0.98  num_pure_diseq_elim:                    0
% 2.23/0.98  simp_replaced_by:                       0
% 2.23/0.98  res_preprocessed:                       94
% 2.23/0.98  prep_upred:                             0
% 2.23/0.98  prep_unflattend:                        24
% 2.23/0.98  smt_new_axioms:                         0
% 2.23/0.98  pred_elim_cands:                        3
% 2.23/0.98  pred_elim:                              1
% 2.23/0.98  pred_elim_cl:                           1
% 2.23/0.98  pred_elim_cycles:                       3
% 2.23/0.98  merged_defs:                            0
% 2.23/0.98  merged_defs_ncl:                        0
% 2.23/0.98  bin_hyper_res:                          0
% 2.23/0.98  prep_cycles:                            4
% 2.23/0.98  pred_elim_time:                         0.009
% 2.23/0.98  splitting_time:                         0.
% 2.23/0.98  sem_filter_time:                        0.
% 2.23/0.98  monotx_time:                            0.001
% 2.23/0.98  subtype_inf_time:                       0.
% 2.23/0.98  
% 2.23/0.98  ------ Problem properties
% 2.23/0.98  
% 2.23/0.98  clauses:                                16
% 2.23/0.98  conjectures:                            3
% 2.23/0.98  epr:                                    0
% 2.23/0.98  horn:                                   13
% 2.23/0.98  ground:                                 2
% 2.23/0.98  unary:                                  2
% 2.23/0.98  binary:                                 4
% 2.23/0.98  lits:                                   47
% 2.23/0.98  lits_eq:                                10
% 2.23/0.98  fd_pure:                                0
% 2.23/0.98  fd_pseudo:                              0
% 2.23/0.98  fd_cond:                                0
% 2.23/0.98  fd_pseudo_cond:                         4
% 2.23/0.98  ac_symbols:                             0
% 2.23/0.98  
% 2.23/0.98  ------ Propositional Solver
% 2.23/0.98  
% 2.23/0.98  prop_solver_calls:                      25
% 2.23/0.98  prop_fast_solver_calls:                 732
% 2.23/0.98  smt_solver_calls:                       0
% 2.23/0.98  smt_fast_solver_calls:                  0
% 2.23/0.98  prop_num_of_clauses:                    843
% 2.23/0.98  prop_preprocess_simplified:             3429
% 2.23/0.98  prop_fo_subsumed:                       10
% 2.23/0.98  prop_solver_time:                       0.
% 2.23/0.98  smt_solver_time:                        0.
% 2.23/0.98  smt_fast_solver_time:                   0.
% 2.23/0.98  prop_fast_solver_time:                  0.
% 2.23/0.98  prop_unsat_core_time:                   0.
% 2.23/0.98  
% 2.23/0.98  ------ QBF
% 2.23/0.98  
% 2.23/0.98  qbf_q_res:                              0
% 2.23/0.98  qbf_num_tautologies:                    0
% 2.23/0.98  qbf_prep_cycles:                        0
% 2.23/0.98  
% 2.23/0.98  ------ BMC1
% 2.23/0.98  
% 2.23/0.98  bmc1_current_bound:                     -1
% 2.23/0.98  bmc1_last_solved_bound:                 -1
% 2.23/0.98  bmc1_unsat_core_size:                   -1
% 2.23/0.98  bmc1_unsat_core_parents_size:           -1
% 2.23/0.98  bmc1_merge_next_fun:                    0
% 2.23/0.98  bmc1_unsat_core_clauses_time:           0.
% 2.23/0.98  
% 2.23/0.98  ------ Instantiation
% 2.23/0.98  
% 2.23/0.98  inst_num_of_clauses:                    216
% 2.23/0.98  inst_num_in_passive:                    21
% 2.23/0.98  inst_num_in_active:                     116
% 2.23/0.98  inst_num_in_unprocessed:                79
% 2.23/0.98  inst_num_of_loops:                      140
% 2.23/0.98  inst_num_of_learning_restarts:          0
% 2.23/0.98  inst_num_moves_active_passive:          21
% 2.23/0.98  inst_lit_activity:                      0
% 2.23/0.98  inst_lit_activity_moves:                0
% 2.23/0.98  inst_num_tautologies:                   0
% 2.23/0.98  inst_num_prop_implied:                  0
% 2.23/0.98  inst_num_existing_simplified:           0
% 2.23/0.98  inst_num_eq_res_simplified:             0
% 2.23/0.98  inst_num_child_elim:                    0
% 2.23/0.98  inst_num_of_dismatching_blockings:      18
% 2.23/0.98  inst_num_of_non_proper_insts:           124
% 2.23/0.98  inst_num_of_duplicates:                 0
% 2.23/0.98  inst_inst_num_from_inst_to_res:         0
% 2.23/0.98  inst_dismatching_checking_time:         0.
% 2.23/0.98  
% 2.23/0.98  ------ Resolution
% 2.23/0.98  
% 2.23/0.98  res_num_of_clauses:                     0
% 2.23/0.98  res_num_in_passive:                     0
% 2.23/0.98  res_num_in_active:                      0
% 2.23/0.98  res_num_of_loops:                       98
% 2.23/0.98  res_forward_subset_subsumed:            6
% 2.23/0.98  res_backward_subset_subsumed:           0
% 2.23/0.98  res_forward_subsumed:                   0
% 2.23/0.98  res_backward_subsumed:                  0
% 2.23/0.98  res_forward_subsumption_resolution:     0
% 2.23/0.98  res_backward_subsumption_resolution:    0
% 2.23/0.98  res_clause_to_clause_subsumption:       61
% 2.23/0.98  res_orphan_elimination:                 0
% 2.23/0.98  res_tautology_del:                      15
% 2.23/0.98  res_num_eq_res_simplified:              0
% 2.23/0.98  res_num_sel_changes:                    0
% 2.23/0.98  res_moves_from_active_to_pass:          0
% 2.23/0.98  
% 2.23/0.98  ------ Superposition
% 2.23/0.98  
% 2.23/0.98  sup_time_total:                         0.
% 2.23/0.98  sup_time_generating:                    0.
% 2.23/0.98  sup_time_sim_full:                      0.
% 2.23/0.98  sup_time_sim_immed:                     0.
% 2.23/0.98  
% 2.23/0.98  sup_num_of_clauses:                     44
% 2.23/0.98  sup_num_in_active:                      27
% 2.23/0.98  sup_num_in_passive:                     17
% 2.23/0.98  sup_num_of_loops:                       27
% 2.23/0.98  sup_fw_superposition:                   15
% 2.23/0.98  sup_bw_superposition:                   15
% 2.23/0.98  sup_immediate_simplified:               2
% 2.23/0.98  sup_given_eliminated:                   0
% 2.23/0.98  comparisons_done:                       0
% 2.23/0.98  comparisons_avoided:                    2
% 2.23/0.98  
% 2.23/0.98  ------ Simplifications
% 2.23/0.98  
% 2.23/0.98  
% 2.23/0.98  sim_fw_subset_subsumed:                 0
% 2.23/0.98  sim_bw_subset_subsumed:                 0
% 2.23/0.98  sim_fw_subsumed:                        0
% 2.23/0.98  sim_bw_subsumed:                        2
% 2.23/0.98  sim_fw_subsumption_res:                 0
% 2.23/0.98  sim_bw_subsumption_res:                 0
% 2.23/0.98  sim_tautology_del:                      0
% 2.23/0.98  sim_eq_tautology_del:                   0
% 2.23/0.98  sim_eq_res_simp:                        0
% 2.23/0.98  sim_fw_demodulated:                     0
% 2.23/0.98  sim_bw_demodulated:                     1
% 2.23/0.98  sim_light_normalised:                   0
% 2.23/0.98  sim_joinable_taut:                      0
% 2.23/0.98  sim_joinable_simp:                      0
% 2.23/0.98  sim_ac_normalised:                      0
% 2.23/0.98  sim_smt_subsumption:                    0
% 2.23/0.98  
%------------------------------------------------------------------------------
