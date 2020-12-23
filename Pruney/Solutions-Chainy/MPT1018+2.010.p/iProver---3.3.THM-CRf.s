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
% DateTime   : Thu Dec  3 12:07:00 EST 2020

% Result     : Theorem 2.01s
% Output     : CNFRefutation 2.01s
% Verified   : 
% Statistics : Number of formulae       :  107 ( 488 expanded)
%              Number of clauses        :   64 ( 150 expanded)
%              Number of leaves         :   13 ( 116 expanded)
%              Depth                    :   26
%              Number of atoms          :  436 (3396 expanded)
%              Number of equality atoms :  163 (1065 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal clause size      :   19 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f6,conjecture,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v1_funct_2(X1,X0,X0)
        & v1_funct_1(X1) )
     => ( v2_funct_1(X1)
       => ! [X2,X3] :
            ( ( k1_funct_1(X1,X2) = k1_funct_1(X1,X3)
              & r2_hidden(X3,X0)
              & r2_hidden(X2,X0) )
           => X2 = X3 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f7,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
          & v1_funct_2(X1,X0,X0)
          & v1_funct_1(X1) )
       => ( v2_funct_1(X1)
         => ! [X2,X3] :
              ( ( k1_funct_1(X1,X2) = k1_funct_1(X1,X3)
                & r2_hidden(X3,X0)
                & r2_hidden(X2,X0) )
             => X2 = X3 ) ) ) ),
    inference(negated_conjecture,[],[f6])).

fof(f16,plain,(
    ? [X0,X1] :
      ( ? [X2,X3] :
          ( X2 != X3
          & k1_funct_1(X1,X2) = k1_funct_1(X1,X3)
          & r2_hidden(X3,X0)
          & r2_hidden(X2,X0) )
      & v2_funct_1(X1)
      & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v1_funct_2(X1,X0,X0)
      & v1_funct_1(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f17,plain,(
    ? [X0,X1] :
      ( ? [X2,X3] :
          ( X2 != X3
          & k1_funct_1(X1,X2) = k1_funct_1(X1,X3)
          & r2_hidden(X3,X0)
          & r2_hidden(X2,X0) )
      & v2_funct_1(X1)
      & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v1_funct_2(X1,X0,X0)
      & v1_funct_1(X1) ) ),
    inference(flattening,[],[f16])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ? [X2,X3] :
          ( X2 != X3
          & k1_funct_1(X1,X2) = k1_funct_1(X1,X3)
          & r2_hidden(X3,X0)
          & r2_hidden(X2,X0) )
     => ( sK5 != sK6
        & k1_funct_1(X1,sK5) = k1_funct_1(X1,sK6)
        & r2_hidden(sK6,X0)
        & r2_hidden(sK5,X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,
    ( ? [X0,X1] :
        ( ? [X2,X3] :
            ( X2 != X3
            & k1_funct_1(X1,X2) = k1_funct_1(X1,X3)
            & r2_hidden(X3,X0)
            & r2_hidden(X2,X0) )
        & v2_funct_1(X1)
        & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v1_funct_2(X1,X0,X0)
        & v1_funct_1(X1) )
   => ( ? [X3,X2] :
          ( X2 != X3
          & k1_funct_1(sK4,X2) = k1_funct_1(sK4,X3)
          & r2_hidden(X3,sK3)
          & r2_hidden(X2,sK3) )
      & v2_funct_1(sK4)
      & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK3,sK3)))
      & v1_funct_2(sK4,sK3,sK3)
      & v1_funct_1(sK4) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,
    ( sK5 != sK6
    & k1_funct_1(sK4,sK5) = k1_funct_1(sK4,sK6)
    & r2_hidden(sK6,sK3)
    & r2_hidden(sK5,sK3)
    & v2_funct_1(sK4)
    & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK3,sK3)))
    & v1_funct_2(sK4,sK3,sK3)
    & v1_funct_1(sK4) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5,sK6])],[f17,f29,f28])).

fof(f52,plain,(
    r2_hidden(sK5,sK3) ),
    inference(cnf_transformation,[],[f30])).

fof(f2,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ! [X1] :
            ( ( v1_funct_1(X1)
              & v1_relat_1(X1) )
           => ( k2_funct_1(X0) = X1
            <=> ( ! [X2,X3] :
                    ( ( ( k1_funct_1(X0,X3) = X2
                        & r2_hidden(X3,k1_relat_1(X0)) )
                     => ( k1_funct_1(X1,X2) = X3
                        & r2_hidden(X2,k2_relat_1(X0)) ) )
                    & ( ( k1_funct_1(X1,X2) = X3
                        & r2_hidden(X2,k2_relat_1(X0)) )
                     => ( k1_funct_1(X0,X3) = X2
                        & r2_hidden(X3,k1_relat_1(X0)) ) ) )
                & k1_relat_1(X1) = k2_relat_1(X0) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f10,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( k2_funct_1(X0) = X1
          <=> ( ! [X2,X3] :
                  ( ( ( k1_funct_1(X1,X2) = X3
                      & r2_hidden(X2,k2_relat_1(X0)) )
                    | k1_funct_1(X0,X3) != X2
                    | ~ r2_hidden(X3,k1_relat_1(X0)) )
                  & ( ( k1_funct_1(X0,X3) = X2
                      & r2_hidden(X3,k1_relat_1(X0)) )
                    | k1_funct_1(X1,X2) != X3
                    | ~ r2_hidden(X2,k2_relat_1(X0)) ) )
              & k1_relat_1(X1) = k2_relat_1(X0) ) )
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f11,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( k2_funct_1(X0) = X1
          <=> ( ! [X2,X3] :
                  ( ( ( k1_funct_1(X1,X2) = X3
                      & r2_hidden(X2,k2_relat_1(X0)) )
                    | k1_funct_1(X0,X3) != X2
                    | ~ r2_hidden(X3,k1_relat_1(X0)) )
                  & ( ( k1_funct_1(X0,X3) = X2
                      & r2_hidden(X3,k1_relat_1(X0)) )
                    | k1_funct_1(X1,X2) != X3
                    | ~ r2_hidden(X2,k2_relat_1(X0)) ) )
              & k1_relat_1(X1) = k2_relat_1(X0) ) )
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f10])).

fof(f18,plain,(
    ! [X2,X3,X0,X1] :
      ( sP0(X2,X3,X0,X1)
    <=> ( ( k1_funct_1(X0,X3) = X2
          & r2_hidden(X3,k1_relat_1(X0)) )
        | k1_funct_1(X1,X2) != X3
        | ~ r2_hidden(X2,k2_relat_1(X0)) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( k2_funct_1(X0) = X1
          <=> ( ! [X2,X3] :
                  ( ( ( k1_funct_1(X1,X2) = X3
                      & r2_hidden(X2,k2_relat_1(X0)) )
                    | k1_funct_1(X0,X3) != X2
                    | ~ r2_hidden(X3,k1_relat_1(X0)) )
                  & sP0(X2,X3,X0,X1) )
              & k1_relat_1(X1) = k2_relat_1(X0) ) )
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(definition_folding,[],[f11,f18])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( k2_funct_1(X0) = X1
              | ? [X2,X3] :
                  ( ( ( k1_funct_1(X1,X2) != X3
                      | ~ r2_hidden(X2,k2_relat_1(X0)) )
                    & k1_funct_1(X0,X3) = X2
                    & r2_hidden(X3,k1_relat_1(X0)) )
                  | ~ sP0(X2,X3,X0,X1) )
              | k1_relat_1(X1) != k2_relat_1(X0) )
            & ( ( ! [X2,X3] :
                    ( ( ( k1_funct_1(X1,X2) = X3
                        & r2_hidden(X2,k2_relat_1(X0)) )
                      | k1_funct_1(X0,X3) != X2
                      | ~ r2_hidden(X3,k1_relat_1(X0)) )
                    & sP0(X2,X3,X0,X1) )
                & k1_relat_1(X1) = k2_relat_1(X0) )
              | k2_funct_1(X0) != X1 ) )
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f19])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( k2_funct_1(X0) = X1
              | ? [X2,X3] :
                  ( ( ( k1_funct_1(X1,X2) != X3
                      | ~ r2_hidden(X2,k2_relat_1(X0)) )
                    & k1_funct_1(X0,X3) = X2
                    & r2_hidden(X3,k1_relat_1(X0)) )
                  | ~ sP0(X2,X3,X0,X1) )
              | k1_relat_1(X1) != k2_relat_1(X0) )
            & ( ( ! [X2,X3] :
                    ( ( ( k1_funct_1(X1,X2) = X3
                        & r2_hidden(X2,k2_relat_1(X0)) )
                      | k1_funct_1(X0,X3) != X2
                      | ~ r2_hidden(X3,k1_relat_1(X0)) )
                    & sP0(X2,X3,X0,X1) )
                & k1_relat_1(X1) = k2_relat_1(X0) )
              | k2_funct_1(X0) != X1 ) )
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f23])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( k2_funct_1(X0) = X1
              | ? [X2,X3] :
                  ( ( ( k1_funct_1(X1,X2) != X3
                      | ~ r2_hidden(X2,k2_relat_1(X0)) )
                    & k1_funct_1(X0,X3) = X2
                    & r2_hidden(X3,k1_relat_1(X0)) )
                  | ~ sP0(X2,X3,X0,X1) )
              | k1_relat_1(X1) != k2_relat_1(X0) )
            & ( ( ! [X4,X5] :
                    ( ( ( k1_funct_1(X1,X4) = X5
                        & r2_hidden(X4,k2_relat_1(X0)) )
                      | k1_funct_1(X0,X5) != X4
                      | ~ r2_hidden(X5,k1_relat_1(X0)) )
                    & sP0(X4,X5,X0,X1) )
                & k1_relat_1(X1) = k2_relat_1(X0) )
              | k2_funct_1(X0) != X1 ) )
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(rectify,[],[f24])).

fof(f26,plain,(
    ! [X1,X0] :
      ( ? [X2,X3] :
          ( ( ( k1_funct_1(X1,X2) != X3
              | ~ r2_hidden(X2,k2_relat_1(X0)) )
            & k1_funct_1(X0,X3) = X2
            & r2_hidden(X3,k1_relat_1(X0)) )
          | ~ sP0(X2,X3,X0,X1) )
     => ( ( ( k1_funct_1(X1,sK1(X0,X1)) != sK2(X0,X1)
            | ~ r2_hidden(sK1(X0,X1),k2_relat_1(X0)) )
          & k1_funct_1(X0,sK2(X0,X1)) = sK1(X0,X1)
          & r2_hidden(sK2(X0,X1),k1_relat_1(X0)) )
        | ~ sP0(sK1(X0,X1),sK2(X0,X1),X0,X1) ) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( k2_funct_1(X0) = X1
              | ( ( k1_funct_1(X1,sK1(X0,X1)) != sK2(X0,X1)
                  | ~ r2_hidden(sK1(X0,X1),k2_relat_1(X0)) )
                & k1_funct_1(X0,sK2(X0,X1)) = sK1(X0,X1)
                & r2_hidden(sK2(X0,X1),k1_relat_1(X0)) )
              | ~ sP0(sK1(X0,X1),sK2(X0,X1),X0,X1)
              | k1_relat_1(X1) != k2_relat_1(X0) )
            & ( ( ! [X4,X5] :
                    ( ( ( k1_funct_1(X1,X4) = X5
                        & r2_hidden(X4,k2_relat_1(X0)) )
                      | k1_funct_1(X0,X5) != X4
                      | ~ r2_hidden(X5,k1_relat_1(X0)) )
                    & sP0(X4,X5,X0,X1) )
                & k1_relat_1(X1) = k2_relat_1(X0) )
              | k2_funct_1(X0) != X1 ) )
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f25,f26])).

fof(f41,plain,(
    ! [X4,X0,X5,X1] :
      ( k1_funct_1(X1,X4) = X5
      | k1_funct_1(X0,X5) != X4
      | ~ r2_hidden(X5,k1_relat_1(X0))
      | k2_funct_1(X0) != X1
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f59,plain,(
    ! [X0,X5,X1] :
      ( k1_funct_1(X1,k1_funct_1(X0,X5)) = X5
      | ~ r2_hidden(X5,k1_relat_1(X0))
      | k2_funct_1(X0) != X1
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f41])).

fof(f60,plain,(
    ! [X0,X5] :
      ( k1_funct_1(k2_funct_1(X0),k1_funct_1(X0,X5)) = X5
      | ~ r2_hidden(X5,k1_relat_1(X0))
      | ~ v1_funct_1(k2_funct_1(X0))
      | ~ v1_relat_1(k2_funct_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f59])).

fof(f51,plain,(
    v2_funct_1(sK4) ),
    inference(cnf_transformation,[],[f30])).

fof(f48,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f30])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f50,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK3,sK3))) ),
    inference(cnf_transformation,[],[f30])).

fof(f1,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f8,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f9,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f8])).

fof(f32,plain,(
    ! [X0] :
      ( v1_funct_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f31,plain,(
    ! [X0] :
      ( v1_relat_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v1_funct_2(X1,X0,X0)
        & v1_funct_1(X1) )
     => k1_relset_1(X0,X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1] :
      ( k1_relset_1(X0,X0,X1) = X0
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f15,plain,(
    ! [X0,X1] :
      ( k1_relset_1(X0,X0,X1) = X0
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(flattening,[],[f14])).

fof(f47,plain,(
    ! [X0,X1] :
      ( k1_relset_1(X0,X0,X1) = X0
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f49,plain,(
    v1_funct_2(sK4,sK3,sK3) ),
    inference(cnf_transformation,[],[f30])).

fof(f53,plain,(
    r2_hidden(sK6,sK3) ),
    inference(cnf_transformation,[],[f30])).

fof(f54,plain,(
    k1_funct_1(sK4,sK5) = k1_funct_1(sK4,sK6) ),
    inference(cnf_transformation,[],[f30])).

fof(f55,plain,(
    sK5 != sK6 ),
    inference(cnf_transformation,[],[f30])).

cnf(c_20,negated_conjecture,
    ( r2_hidden(sK5,sK3) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_1256,negated_conjecture,
    ( r2_hidden(sK5,sK3) ),
    inference(subtyping,[status(esa)],[c_20])).

cnf(c_1728,plain,
    ( r2_hidden(sK5,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1256])).

cnf(c_10,plain,
    ( ~ r2_hidden(X0,k1_relat_1(X1))
    | ~ v2_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(k2_funct_1(X1))
    | ~ v1_funct_1(X1)
    | ~ v1_funct_1(k2_funct_1(X1))
    | k1_funct_1(k2_funct_1(X1),k1_funct_1(X1,X0)) = X0 ),
    inference(cnf_transformation,[],[f60])).

cnf(c_21,negated_conjecture,
    ( v2_funct_1(sK4) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_446,plain,
    ( ~ r2_hidden(X0,k1_relat_1(X1))
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(k2_funct_1(X1))
    | ~ v1_funct_1(X1)
    | ~ v1_funct_1(k2_funct_1(X1))
    | k1_funct_1(k2_funct_1(X1),k1_funct_1(X1,X0)) = X0
    | sK4 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_10,c_21])).

cnf(c_447,plain,
    ( ~ r2_hidden(X0,k1_relat_1(sK4))
    | ~ v1_relat_1(k2_funct_1(sK4))
    | ~ v1_relat_1(sK4)
    | ~ v1_funct_1(k2_funct_1(sK4))
    | ~ v1_funct_1(sK4)
    | k1_funct_1(k2_funct_1(sK4),k1_funct_1(sK4,X0)) = X0 ),
    inference(unflattening,[status(thm)],[c_446])).

cnf(c_24,negated_conjecture,
    ( v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_451,plain,
    ( ~ v1_funct_1(k2_funct_1(sK4))
    | ~ v1_relat_1(sK4)
    | ~ v1_relat_1(k2_funct_1(sK4))
    | ~ r2_hidden(X0,k1_relat_1(sK4))
    | k1_funct_1(k2_funct_1(sK4),k1_funct_1(sK4,X0)) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_447,c_24])).

cnf(c_452,plain,
    ( ~ r2_hidden(X0,k1_relat_1(sK4))
    | ~ v1_relat_1(k2_funct_1(sK4))
    | ~ v1_relat_1(sK4)
    | ~ v1_funct_1(k2_funct_1(sK4))
    | k1_funct_1(k2_funct_1(sK4),k1_funct_1(sK4,X0)) = X0 ),
    inference(renaming,[status(thm)],[c_451])).

cnf(c_1246,plain,
    ( ~ r2_hidden(X0_48,k1_relat_1(sK4))
    | ~ v1_relat_1(k2_funct_1(sK4))
    | ~ v1_relat_1(sK4)
    | ~ v1_funct_1(k2_funct_1(sK4))
    | k1_funct_1(k2_funct_1(sK4),k1_funct_1(sK4,X0_48)) = X0_48 ),
    inference(subtyping,[status(esa)],[c_452])).

cnf(c_1269,plain,
    ( ~ r2_hidden(X0_48,k1_relat_1(sK4))
    | k1_funct_1(k2_funct_1(sK4),k1_funct_1(sK4,X0_48)) = X0_48
    | ~ sP1_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[sP1_iProver_split])],[c_1246])).

cnf(c_1738,plain,
    ( k1_funct_1(k2_funct_1(sK4),k1_funct_1(sK4,X0_48)) = X0_48
    | r2_hidden(X0_48,k1_relat_1(sK4)) != iProver_top
    | sP1_iProver_split != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1269])).

cnf(c_14,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_22,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK3,sK3))) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_286,plain,
    ( v1_relat_1(X0)
    | k1_zfmisc_1(k2_zfmisc_1(X1,X2)) != k1_zfmisc_1(k2_zfmisc_1(sK3,sK3))
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_14,c_22])).

cnf(c_287,plain,
    ( v1_relat_1(sK4)
    | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK3,sK3)) ),
    inference(unflattening,[status(thm)],[c_286])).

cnf(c_1252,plain,
    ( v1_relat_1(sK4)
    | k1_zfmisc_1(k2_zfmisc_1(X0_50,X1_50)) != k1_zfmisc_1(k2_zfmisc_1(sK3,sK3)) ),
    inference(subtyping,[status(esa)],[c_287])).

cnf(c_1340,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(X0_50,X1_50)) != k1_zfmisc_1(k2_zfmisc_1(sK3,sK3))
    | v1_relat_1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1252])).

cnf(c_1342,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(sK3,sK3)) != k1_zfmisc_1(k2_zfmisc_1(sK3,sK3))
    | v1_relat_1(sK4) = iProver_top ),
    inference(instantiation,[status(thm)],[c_1340])).

cnf(c_1358,plain,
    ( k1_funct_1(k2_funct_1(sK4),k1_funct_1(sK4,X0_48)) = X0_48
    | r2_hidden(X0_48,k1_relat_1(sK4)) != iProver_top
    | sP1_iProver_split != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1269])).

cnf(c_1270,plain,
    ( ~ v1_relat_1(k2_funct_1(sK4))
    | ~ v1_relat_1(sK4)
    | ~ v1_funct_1(k2_funct_1(sK4))
    | sP1_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[])],[c_1246])).

cnf(c_0,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0)
    | v1_funct_1(k2_funct_1(X0)) ),
    inference(cnf_transformation,[],[f32])).

cnf(c_1266,plain,
    ( ~ v1_relat_1(X0_49)
    | ~ v1_funct_1(X0_49)
    | v1_funct_1(k2_funct_1(X0_49)) ),
    inference(subtyping,[status(esa)],[c_0])).

cnf(c_1316,plain,
    ( ~ v1_relat_1(sK4)
    | v1_funct_1(k2_funct_1(sK4))
    | ~ v1_funct_1(sK4) ),
    inference(instantiation,[status(thm)],[c_1266])).

cnf(c_1,plain,
    ( ~ v1_relat_1(X0)
    | v1_relat_1(k2_funct_1(X0))
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f31])).

cnf(c_1265,plain,
    ( ~ v1_relat_1(X0_49)
    | v1_relat_1(k2_funct_1(X0_49))
    | ~ v1_funct_1(X0_49) ),
    inference(subtyping,[status(esa)],[c_1])).

cnf(c_1319,plain,
    ( v1_relat_1(k2_funct_1(sK4))
    | ~ v1_relat_1(sK4)
    | ~ v1_funct_1(sK4) ),
    inference(instantiation,[status(thm)],[c_1265])).

cnf(c_1416,plain,
    ( ~ v1_relat_1(sK4)
    | sP1_iProver_split ),
    inference(global_propositional_subsumption,[status(thm)],[c_1270,c_24,c_1316,c_1319])).

cnf(c_1418,plain,
    ( v1_relat_1(sK4) != iProver_top
    | sP1_iProver_split = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1416])).

cnf(c_1277,plain,
    ( X0_51 = X0_51 ),
    theory(equality)).

cnf(c_1937,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(sK3,sK3)) = k1_zfmisc_1(k2_zfmisc_1(sK3,sK3)) ),
    inference(instantiation,[status(thm)],[c_1277])).

cnf(c_2325,plain,
    ( r2_hidden(X0_48,k1_relat_1(sK4)) != iProver_top
    | k1_funct_1(k2_funct_1(sK4),k1_funct_1(sK4,X0_48)) = X0_48 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1738,c_1342,c_1358,c_1418,c_1937])).

cnf(c_2326,plain,
    ( k1_funct_1(k2_funct_1(sK4),k1_funct_1(sK4,X0_48)) = X0_48
    | r2_hidden(X0_48,k1_relat_1(sK4)) != iProver_top ),
    inference(renaming,[status(thm)],[c_2325])).

cnf(c_15,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_277,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK3,sK3))
    | sK4 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_15,c_22])).

cnf(c_278,plain,
    ( k1_relset_1(X0,X1,sK4) = k1_relat_1(sK4)
    | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK3,sK3)) ),
    inference(unflattening,[status(thm)],[c_277])).

cnf(c_1253,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(X0_50,X1_50)) != k1_zfmisc_1(k2_zfmisc_1(sK3,sK3))
    | k1_relset_1(X0_50,X1_50,sK4) = k1_relat_1(sK4) ),
    inference(subtyping,[status(esa)],[c_278])).

cnf(c_1951,plain,
    ( k1_relset_1(sK3,sK3,sK4) = k1_relat_1(sK4) ),
    inference(equality_resolution,[status(thm)],[c_1253])).

cnf(c_16,plain,
    ( ~ v1_funct_2(X0,X1,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | ~ v1_funct_1(X0)
    | k1_relset_1(X1,X1,X0) = X1 ),
    inference(cnf_transformation,[],[f47])).

cnf(c_23,negated_conjecture,
    ( v1_funct_2(sK4,sK3,sK3) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_268,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | ~ v1_funct_1(X0)
    | k1_relset_1(X1,X1,X0) = X1
    | sK3 != X1
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_16,c_23])).

cnf(c_269,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK3,sK3)))
    | ~ v1_funct_1(sK4)
    | k1_relset_1(sK3,sK3,sK4) = sK3 ),
    inference(unflattening,[status(thm)],[c_268])).

cnf(c_271,plain,
    ( k1_relset_1(sK3,sK3,sK4) = sK3 ),
    inference(global_propositional_subsumption,[status(thm)],[c_269,c_24,c_22])).

cnf(c_1254,plain,
    ( k1_relset_1(sK3,sK3,sK4) = sK3 ),
    inference(subtyping,[status(esa)],[c_271])).

cnf(c_1952,plain,
    ( k1_relat_1(sK4) = sK3 ),
    inference(light_normalisation,[status(thm)],[c_1951,c_1254])).

cnf(c_2331,plain,
    ( k1_funct_1(k2_funct_1(sK4),k1_funct_1(sK4,X0_48)) = X0_48
    | r2_hidden(X0_48,sK3) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2326,c_1952])).

cnf(c_2338,plain,
    ( k1_funct_1(k2_funct_1(sK4),k1_funct_1(sK4,sK5)) = sK5 ),
    inference(superposition,[status(thm)],[c_1728,c_2331])).

cnf(c_19,negated_conjecture,
    ( r2_hidden(sK6,sK3) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_1257,negated_conjecture,
    ( r2_hidden(sK6,sK3) ),
    inference(subtyping,[status(esa)],[c_19])).

cnf(c_1727,plain,
    ( r2_hidden(sK6,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1257])).

cnf(c_2337,plain,
    ( k1_funct_1(k2_funct_1(sK4),k1_funct_1(sK4,sK6)) = sK6 ),
    inference(superposition,[status(thm)],[c_1727,c_2331])).

cnf(c_18,negated_conjecture,
    ( k1_funct_1(sK4,sK5) = k1_funct_1(sK4,sK6) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_1258,negated_conjecture,
    ( k1_funct_1(sK4,sK5) = k1_funct_1(sK4,sK6) ),
    inference(subtyping,[status(esa)],[c_18])).

cnf(c_2342,plain,
    ( k1_funct_1(k2_funct_1(sK4),k1_funct_1(sK4,sK5)) = sK6 ),
    inference(light_normalisation,[status(thm)],[c_2337,c_1258])).

cnf(c_2626,plain,
    ( sK6 = sK5 ),
    inference(demodulation,[status(thm)],[c_2338,c_2342])).

cnf(c_1279,plain,
    ( X0_48 != X1_48
    | X2_48 != X1_48
    | X2_48 = X0_48 ),
    theory(equality)).

cnf(c_1946,plain,
    ( sK6 != X0_48
    | sK5 != X0_48
    | sK5 = sK6 ),
    inference(instantiation,[status(thm)],[c_1279])).

cnf(c_1947,plain,
    ( sK6 != sK5
    | sK5 = sK6
    | sK5 != sK5 ),
    inference(instantiation,[status(thm)],[c_1946])).

cnf(c_17,negated_conjecture,
    ( sK5 != sK6 ),
    inference(cnf_transformation,[],[f55])).

cnf(c_1259,negated_conjecture,
    ( sK5 != sK6 ),
    inference(subtyping,[status(esa)],[c_17])).

cnf(c_1274,plain,
    ( X0_48 = X0_48 ),
    theory(equality)).

cnf(c_1310,plain,
    ( sK5 = sK5 ),
    inference(instantiation,[status(thm)],[c_1274])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_2626,c_1947,c_1259,c_1310])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.33  % Computer   : n001.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 18:54:30 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 2.01/0.99  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.01/0.99  
% 2.01/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.01/0.99  
% 2.01/0.99  ------  iProver source info
% 2.01/0.99  
% 2.01/0.99  git: date: 2020-06-30 10:37:57 +0100
% 2.01/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.01/0.99  git: non_committed_changes: false
% 2.01/0.99  git: last_make_outside_of_git: false
% 2.01/0.99  
% 2.01/0.99  ------ 
% 2.01/0.99  
% 2.01/0.99  ------ Input Options
% 2.01/0.99  
% 2.01/0.99  --out_options                           all
% 2.01/0.99  --tptp_safe_out                         true
% 2.01/0.99  --problem_path                          ""
% 2.01/0.99  --include_path                          ""
% 2.01/0.99  --clausifier                            res/vclausify_rel
% 2.01/0.99  --clausifier_options                    --mode clausify
% 2.01/0.99  --stdin                                 false
% 2.01/0.99  --stats_out                             all
% 2.01/0.99  
% 2.01/0.99  ------ General Options
% 2.01/0.99  
% 2.01/0.99  --fof                                   false
% 2.01/0.99  --time_out_real                         305.
% 2.01/0.99  --time_out_virtual                      -1.
% 2.01/0.99  --symbol_type_check                     false
% 2.01/0.99  --clausify_out                          false
% 2.01/0.99  --sig_cnt_out                           false
% 2.01/0.99  --trig_cnt_out                          false
% 2.01/0.99  --trig_cnt_out_tolerance                1.
% 2.01/0.99  --trig_cnt_out_sk_spl                   false
% 2.01/0.99  --abstr_cl_out                          false
% 2.01/0.99  
% 2.01/0.99  ------ Global Options
% 2.01/0.99  
% 2.01/0.99  --schedule                              default
% 2.01/0.99  --add_important_lit                     false
% 2.01/0.99  --prop_solver_per_cl                    1000
% 2.01/0.99  --min_unsat_core                        false
% 2.01/0.99  --soft_assumptions                      false
% 2.01/0.99  --soft_lemma_size                       3
% 2.01/0.99  --prop_impl_unit_size                   0
% 2.01/0.99  --prop_impl_unit                        []
% 2.01/0.99  --share_sel_clauses                     true
% 2.01/0.99  --reset_solvers                         false
% 2.01/0.99  --bc_imp_inh                            [conj_cone]
% 2.01/0.99  --conj_cone_tolerance                   3.
% 2.01/0.99  --extra_neg_conj                        none
% 2.01/0.99  --large_theory_mode                     true
% 2.01/0.99  --prolific_symb_bound                   200
% 2.01/0.99  --lt_threshold                          2000
% 2.01/0.99  --clause_weak_htbl                      true
% 2.01/0.99  --gc_record_bc_elim                     false
% 2.01/0.99  
% 2.01/0.99  ------ Preprocessing Options
% 2.01/0.99  
% 2.01/0.99  --preprocessing_flag                    true
% 2.01/0.99  --time_out_prep_mult                    0.1
% 2.01/0.99  --splitting_mode                        input
% 2.01/0.99  --splitting_grd                         true
% 2.01/0.99  --splitting_cvd                         false
% 2.01/0.99  --splitting_cvd_svl                     false
% 2.01/0.99  --splitting_nvd                         32
% 2.01/0.99  --sub_typing                            true
% 2.01/0.99  --prep_gs_sim                           true
% 2.01/0.99  --prep_unflatten                        true
% 2.01/0.99  --prep_res_sim                          true
% 2.01/0.99  --prep_upred                            true
% 2.01/0.99  --prep_sem_filter                       exhaustive
% 2.01/0.99  --prep_sem_filter_out                   false
% 2.01/0.99  --pred_elim                             true
% 2.01/0.99  --res_sim_input                         true
% 2.01/0.99  --eq_ax_congr_red                       true
% 2.01/0.99  --pure_diseq_elim                       true
% 2.01/0.99  --brand_transform                       false
% 2.01/0.99  --non_eq_to_eq                          false
% 2.01/0.99  --prep_def_merge                        true
% 2.01/0.99  --prep_def_merge_prop_impl              false
% 2.01/0.99  --prep_def_merge_mbd                    true
% 2.01/0.99  --prep_def_merge_tr_red                 false
% 2.01/0.99  --prep_def_merge_tr_cl                  false
% 2.01/0.99  --smt_preprocessing                     true
% 2.01/0.99  --smt_ac_axioms                         fast
% 2.01/0.99  --preprocessed_out                      false
% 2.01/0.99  --preprocessed_stats                    false
% 2.01/0.99  
% 2.01/0.99  ------ Abstraction refinement Options
% 2.01/0.99  
% 2.01/0.99  --abstr_ref                             []
% 2.01/0.99  --abstr_ref_prep                        false
% 2.01/0.99  --abstr_ref_until_sat                   false
% 2.01/0.99  --abstr_ref_sig_restrict                funpre
% 2.01/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 2.01/0.99  --abstr_ref_under                       []
% 2.01/0.99  
% 2.01/0.99  ------ SAT Options
% 2.01/0.99  
% 2.01/0.99  --sat_mode                              false
% 2.01/0.99  --sat_fm_restart_options                ""
% 2.01/0.99  --sat_gr_def                            false
% 2.01/0.99  --sat_epr_types                         true
% 2.01/0.99  --sat_non_cyclic_types                  false
% 2.01/0.99  --sat_finite_models                     false
% 2.01/0.99  --sat_fm_lemmas                         false
% 2.01/0.99  --sat_fm_prep                           false
% 2.01/0.99  --sat_fm_uc_incr                        true
% 2.01/0.99  --sat_out_model                         small
% 2.01/0.99  --sat_out_clauses                       false
% 2.01/0.99  
% 2.01/0.99  ------ QBF Options
% 2.01/0.99  
% 2.01/0.99  --qbf_mode                              false
% 2.01/0.99  --qbf_elim_univ                         false
% 2.01/0.99  --qbf_dom_inst                          none
% 2.01/0.99  --qbf_dom_pre_inst                      false
% 2.01/0.99  --qbf_sk_in                             false
% 2.01/0.99  --qbf_pred_elim                         true
% 2.01/0.99  --qbf_split                             512
% 2.01/0.99  
% 2.01/0.99  ------ BMC1 Options
% 2.01/0.99  
% 2.01/0.99  --bmc1_incremental                      false
% 2.01/0.99  --bmc1_axioms                           reachable_all
% 2.01/0.99  --bmc1_min_bound                        0
% 2.01/0.99  --bmc1_max_bound                        -1
% 2.01/0.99  --bmc1_max_bound_default                -1
% 2.01/0.99  --bmc1_symbol_reachability              true
% 2.01/0.99  --bmc1_property_lemmas                  false
% 2.01/0.99  --bmc1_k_induction                      false
% 2.01/0.99  --bmc1_non_equiv_states                 false
% 2.01/0.99  --bmc1_deadlock                         false
% 2.01/0.99  --bmc1_ucm                              false
% 2.01/0.99  --bmc1_add_unsat_core                   none
% 2.01/0.99  --bmc1_unsat_core_children              false
% 2.01/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 2.01/0.99  --bmc1_out_stat                         full
% 2.01/0.99  --bmc1_ground_init                      false
% 2.01/0.99  --bmc1_pre_inst_next_state              false
% 2.01/0.99  --bmc1_pre_inst_state                   false
% 2.01/0.99  --bmc1_pre_inst_reach_state             false
% 2.01/0.99  --bmc1_out_unsat_core                   false
% 2.01/0.99  --bmc1_aig_witness_out                  false
% 2.01/0.99  --bmc1_verbose                          false
% 2.01/0.99  --bmc1_dump_clauses_tptp                false
% 2.01/0.99  --bmc1_dump_unsat_core_tptp             false
% 2.01/0.99  --bmc1_dump_file                        -
% 2.01/0.99  --bmc1_ucm_expand_uc_limit              128
% 2.01/0.99  --bmc1_ucm_n_expand_iterations          6
% 2.01/0.99  --bmc1_ucm_extend_mode                  1
% 2.01/0.99  --bmc1_ucm_init_mode                    2
% 2.01/0.99  --bmc1_ucm_cone_mode                    none
% 2.01/0.99  --bmc1_ucm_reduced_relation_type        0
% 2.01/0.99  --bmc1_ucm_relax_model                  4
% 2.01/0.99  --bmc1_ucm_full_tr_after_sat            true
% 2.01/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 2.01/0.99  --bmc1_ucm_layered_model                none
% 2.01/0.99  --bmc1_ucm_max_lemma_size               10
% 2.01/0.99  
% 2.01/0.99  ------ AIG Options
% 2.01/0.99  
% 2.01/0.99  --aig_mode                              false
% 2.01/0.99  
% 2.01/0.99  ------ Instantiation Options
% 2.01/0.99  
% 2.01/0.99  --instantiation_flag                    true
% 2.01/0.99  --inst_sos_flag                         false
% 2.01/0.99  --inst_sos_phase                        true
% 2.01/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.01/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.01/0.99  --inst_lit_sel_side                     num_symb
% 2.01/0.99  --inst_solver_per_active                1400
% 2.01/0.99  --inst_solver_calls_frac                1.
% 2.01/0.99  --inst_passive_queue_type               priority_queues
% 2.01/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.01/0.99  --inst_passive_queues_freq              [25;2]
% 2.01/0.99  --inst_dismatching                      true
% 2.01/0.99  --inst_eager_unprocessed_to_passive     true
% 2.01/0.99  --inst_prop_sim_given                   true
% 2.01/0.99  --inst_prop_sim_new                     false
% 2.01/0.99  --inst_subs_new                         false
% 2.01/0.99  --inst_eq_res_simp                      false
% 2.01/0.99  --inst_subs_given                       false
% 2.01/0.99  --inst_orphan_elimination               true
% 2.01/0.99  --inst_learning_loop_flag               true
% 2.01/0.99  --inst_learning_start                   3000
% 2.01/0.99  --inst_learning_factor                  2
% 2.01/0.99  --inst_start_prop_sim_after_learn       3
% 2.01/0.99  --inst_sel_renew                        solver
% 2.01/0.99  --inst_lit_activity_flag                true
% 2.01/0.99  --inst_restr_to_given                   false
% 2.01/0.99  --inst_activity_threshold               500
% 2.01/0.99  --inst_out_proof                        true
% 2.01/0.99  
% 2.01/0.99  ------ Resolution Options
% 2.01/0.99  
% 2.01/0.99  --resolution_flag                       true
% 2.01/0.99  --res_lit_sel                           adaptive
% 2.01/0.99  --res_lit_sel_side                      none
% 2.01/0.99  --res_ordering                          kbo
% 2.01/0.99  --res_to_prop_solver                    active
% 2.01/0.99  --res_prop_simpl_new                    false
% 2.01/0.99  --res_prop_simpl_given                  true
% 2.01/0.99  --res_passive_queue_type                priority_queues
% 2.01/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.01/0.99  --res_passive_queues_freq               [15;5]
% 2.01/0.99  --res_forward_subs                      full
% 2.01/0.99  --res_backward_subs                     full
% 2.01/0.99  --res_forward_subs_resolution           true
% 2.01/0.99  --res_backward_subs_resolution          true
% 2.01/0.99  --res_orphan_elimination                true
% 2.01/0.99  --res_time_limit                        2.
% 2.01/0.99  --res_out_proof                         true
% 2.01/0.99  
% 2.01/0.99  ------ Superposition Options
% 2.01/0.99  
% 2.01/0.99  --superposition_flag                    true
% 2.01/0.99  --sup_passive_queue_type                priority_queues
% 2.01/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.01/0.99  --sup_passive_queues_freq               [8;1;4]
% 2.01/0.99  --demod_completeness_check              fast
% 2.01/0.99  --demod_use_ground                      true
% 2.01/0.99  --sup_to_prop_solver                    passive
% 2.01/0.99  --sup_prop_simpl_new                    true
% 2.01/0.99  --sup_prop_simpl_given                  true
% 2.01/0.99  --sup_fun_splitting                     false
% 2.01/0.99  --sup_smt_interval                      50000
% 2.01/0.99  
% 2.01/0.99  ------ Superposition Simplification Setup
% 2.01/0.99  
% 2.01/0.99  --sup_indices_passive                   []
% 2.01/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.01/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.01/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.01/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 2.01/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.01/0.99  --sup_full_bw                           [BwDemod]
% 2.01/0.99  --sup_immed_triv                        [TrivRules]
% 2.01/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.01/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.01/0.99  --sup_immed_bw_main                     []
% 2.01/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.01/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 2.01/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.01/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.01/0.99  
% 2.01/0.99  ------ Combination Options
% 2.01/0.99  
% 2.01/0.99  --comb_res_mult                         3
% 2.01/0.99  --comb_sup_mult                         2
% 2.01/0.99  --comb_inst_mult                        10
% 2.01/0.99  
% 2.01/0.99  ------ Debug Options
% 2.01/0.99  
% 2.01/0.99  --dbg_backtrace                         false
% 2.01/0.99  --dbg_dump_prop_clauses                 false
% 2.01/0.99  --dbg_dump_prop_clauses_file            -
% 2.01/0.99  --dbg_out_stat                          false
% 2.01/0.99  ------ Parsing...
% 2.01/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.01/0.99  
% 2.01/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 4 0s  sf_e  pe_s  pe_e 
% 2.01/0.99  
% 2.01/0.99  ------ Preprocessing... gs_s  sp: 3 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.01/0.99  
% 2.01/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.01/0.99  ------ Proving...
% 2.01/0.99  ------ Problem Properties 
% 2.01/0.99  
% 2.01/0.99  
% 2.01/0.99  clauses                                 25
% 2.01/0.99  conjectures                             5
% 2.01/0.99  EPR                                     4
% 2.01/0.99  Horn                                    21
% 2.01/0.99  unary                                   6
% 2.01/0.99  binary                                  7
% 2.01/0.99  lits                                    72
% 2.01/0.99  lits eq                                 18
% 2.01/0.99  fd_pure                                 0
% 2.01/0.99  fd_pseudo                               0
% 2.01/0.99  fd_cond                                 3
% 2.01/0.99  fd_pseudo_cond                          1
% 2.01/0.99  AC symbols                              0
% 2.01/0.99  
% 2.01/0.99  ------ Schedule dynamic 5 is on 
% 2.01/0.99  
% 2.01/0.99  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.01/0.99  
% 2.01/0.99  
% 2.01/0.99  ------ 
% 2.01/0.99  Current options:
% 2.01/0.99  ------ 
% 2.01/0.99  
% 2.01/0.99  ------ Input Options
% 2.01/0.99  
% 2.01/0.99  --out_options                           all
% 2.01/0.99  --tptp_safe_out                         true
% 2.01/0.99  --problem_path                          ""
% 2.01/0.99  --include_path                          ""
% 2.01/0.99  --clausifier                            res/vclausify_rel
% 2.01/0.99  --clausifier_options                    --mode clausify
% 2.01/0.99  --stdin                                 false
% 2.01/0.99  --stats_out                             all
% 2.01/0.99  
% 2.01/0.99  ------ General Options
% 2.01/0.99  
% 2.01/0.99  --fof                                   false
% 2.01/0.99  --time_out_real                         305.
% 2.01/0.99  --time_out_virtual                      -1.
% 2.01/0.99  --symbol_type_check                     false
% 2.01/0.99  --clausify_out                          false
% 2.01/0.99  --sig_cnt_out                           false
% 2.01/0.99  --trig_cnt_out                          false
% 2.01/0.99  --trig_cnt_out_tolerance                1.
% 2.01/0.99  --trig_cnt_out_sk_spl                   false
% 2.01/0.99  --abstr_cl_out                          false
% 2.01/0.99  
% 2.01/0.99  ------ Global Options
% 2.01/0.99  
% 2.01/0.99  --schedule                              default
% 2.01/0.99  --add_important_lit                     false
% 2.01/0.99  --prop_solver_per_cl                    1000
% 2.01/0.99  --min_unsat_core                        false
% 2.01/0.99  --soft_assumptions                      false
% 2.01/0.99  --soft_lemma_size                       3
% 2.01/0.99  --prop_impl_unit_size                   0
% 2.01/0.99  --prop_impl_unit                        []
% 2.01/0.99  --share_sel_clauses                     true
% 2.01/0.99  --reset_solvers                         false
% 2.01/0.99  --bc_imp_inh                            [conj_cone]
% 2.01/0.99  --conj_cone_tolerance                   3.
% 2.01/0.99  --extra_neg_conj                        none
% 2.01/0.99  --large_theory_mode                     true
% 2.01/0.99  --prolific_symb_bound                   200
% 2.01/0.99  --lt_threshold                          2000
% 2.01/0.99  --clause_weak_htbl                      true
% 2.01/0.99  --gc_record_bc_elim                     false
% 2.01/0.99  
% 2.01/0.99  ------ Preprocessing Options
% 2.01/0.99  
% 2.01/0.99  --preprocessing_flag                    true
% 2.01/0.99  --time_out_prep_mult                    0.1
% 2.01/0.99  --splitting_mode                        input
% 2.01/0.99  --splitting_grd                         true
% 2.01/0.99  --splitting_cvd                         false
% 2.01/0.99  --splitting_cvd_svl                     false
% 2.01/0.99  --splitting_nvd                         32
% 2.01/0.99  --sub_typing                            true
% 2.01/0.99  --prep_gs_sim                           true
% 2.01/0.99  --prep_unflatten                        true
% 2.01/0.99  --prep_res_sim                          true
% 2.01/0.99  --prep_upred                            true
% 2.01/0.99  --prep_sem_filter                       exhaustive
% 2.01/0.99  --prep_sem_filter_out                   false
% 2.01/0.99  --pred_elim                             true
% 2.01/0.99  --res_sim_input                         true
% 2.01/0.99  --eq_ax_congr_red                       true
% 2.01/0.99  --pure_diseq_elim                       true
% 2.01/0.99  --brand_transform                       false
% 2.01/0.99  --non_eq_to_eq                          false
% 2.01/0.99  --prep_def_merge                        true
% 2.01/0.99  --prep_def_merge_prop_impl              false
% 2.01/0.99  --prep_def_merge_mbd                    true
% 2.01/0.99  --prep_def_merge_tr_red                 false
% 2.01/0.99  --prep_def_merge_tr_cl                  false
% 2.01/0.99  --smt_preprocessing                     true
% 2.01/0.99  --smt_ac_axioms                         fast
% 2.01/0.99  --preprocessed_out                      false
% 2.01/0.99  --preprocessed_stats                    false
% 2.01/0.99  
% 2.01/0.99  ------ Abstraction refinement Options
% 2.01/0.99  
% 2.01/0.99  --abstr_ref                             []
% 2.01/0.99  --abstr_ref_prep                        false
% 2.01/0.99  --abstr_ref_until_sat                   false
% 2.01/0.99  --abstr_ref_sig_restrict                funpre
% 2.01/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 2.01/0.99  --abstr_ref_under                       []
% 2.01/0.99  
% 2.01/0.99  ------ SAT Options
% 2.01/0.99  
% 2.01/0.99  --sat_mode                              false
% 2.01/0.99  --sat_fm_restart_options                ""
% 2.01/1.00  --sat_gr_def                            false
% 2.01/1.00  --sat_epr_types                         true
% 2.01/1.00  --sat_non_cyclic_types                  false
% 2.01/1.00  --sat_finite_models                     false
% 2.01/1.00  --sat_fm_lemmas                         false
% 2.01/1.00  --sat_fm_prep                           false
% 2.01/1.00  --sat_fm_uc_incr                        true
% 2.01/1.00  --sat_out_model                         small
% 2.01/1.00  --sat_out_clauses                       false
% 2.01/1.00  
% 2.01/1.00  ------ QBF Options
% 2.01/1.00  
% 2.01/1.00  --qbf_mode                              false
% 2.01/1.00  --qbf_elim_univ                         false
% 2.01/1.00  --qbf_dom_inst                          none
% 2.01/1.00  --qbf_dom_pre_inst                      false
% 2.01/1.00  --qbf_sk_in                             false
% 2.01/1.00  --qbf_pred_elim                         true
% 2.01/1.00  --qbf_split                             512
% 2.01/1.00  
% 2.01/1.00  ------ BMC1 Options
% 2.01/1.00  
% 2.01/1.00  --bmc1_incremental                      false
% 2.01/1.00  --bmc1_axioms                           reachable_all
% 2.01/1.00  --bmc1_min_bound                        0
% 2.01/1.00  --bmc1_max_bound                        -1
% 2.01/1.00  --bmc1_max_bound_default                -1
% 2.01/1.00  --bmc1_symbol_reachability              true
% 2.01/1.00  --bmc1_property_lemmas                  false
% 2.01/1.00  --bmc1_k_induction                      false
% 2.01/1.00  --bmc1_non_equiv_states                 false
% 2.01/1.00  --bmc1_deadlock                         false
% 2.01/1.00  --bmc1_ucm                              false
% 2.01/1.00  --bmc1_add_unsat_core                   none
% 2.01/1.00  --bmc1_unsat_core_children              false
% 2.01/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 2.01/1.00  --bmc1_out_stat                         full
% 2.01/1.00  --bmc1_ground_init                      false
% 2.01/1.00  --bmc1_pre_inst_next_state              false
% 2.01/1.00  --bmc1_pre_inst_state                   false
% 2.01/1.00  --bmc1_pre_inst_reach_state             false
% 2.01/1.00  --bmc1_out_unsat_core                   false
% 2.01/1.00  --bmc1_aig_witness_out                  false
% 2.01/1.00  --bmc1_verbose                          false
% 2.01/1.00  --bmc1_dump_clauses_tptp                false
% 2.01/1.00  --bmc1_dump_unsat_core_tptp             false
% 2.01/1.00  --bmc1_dump_file                        -
% 2.01/1.00  --bmc1_ucm_expand_uc_limit              128
% 2.01/1.00  --bmc1_ucm_n_expand_iterations          6
% 2.01/1.00  --bmc1_ucm_extend_mode                  1
% 2.01/1.00  --bmc1_ucm_init_mode                    2
% 2.01/1.00  --bmc1_ucm_cone_mode                    none
% 2.01/1.00  --bmc1_ucm_reduced_relation_type        0
% 2.01/1.00  --bmc1_ucm_relax_model                  4
% 2.01/1.00  --bmc1_ucm_full_tr_after_sat            true
% 2.01/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 2.01/1.00  --bmc1_ucm_layered_model                none
% 2.01/1.00  --bmc1_ucm_max_lemma_size               10
% 2.01/1.00  
% 2.01/1.00  ------ AIG Options
% 2.01/1.00  
% 2.01/1.00  --aig_mode                              false
% 2.01/1.00  
% 2.01/1.00  ------ Instantiation Options
% 2.01/1.00  
% 2.01/1.00  --instantiation_flag                    true
% 2.01/1.00  --inst_sos_flag                         false
% 2.01/1.00  --inst_sos_phase                        true
% 2.01/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.01/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.01/1.00  --inst_lit_sel_side                     none
% 2.01/1.00  --inst_solver_per_active                1400
% 2.01/1.00  --inst_solver_calls_frac                1.
% 2.01/1.00  --inst_passive_queue_type               priority_queues
% 2.01/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.01/1.00  --inst_passive_queues_freq              [25;2]
% 2.01/1.00  --inst_dismatching                      true
% 2.01/1.00  --inst_eager_unprocessed_to_passive     true
% 2.01/1.00  --inst_prop_sim_given                   true
% 2.01/1.00  --inst_prop_sim_new                     false
% 2.01/1.00  --inst_subs_new                         false
% 2.01/1.00  --inst_eq_res_simp                      false
% 2.01/1.00  --inst_subs_given                       false
% 2.01/1.00  --inst_orphan_elimination               true
% 2.01/1.00  --inst_learning_loop_flag               true
% 2.01/1.00  --inst_learning_start                   3000
% 2.01/1.00  --inst_learning_factor                  2
% 2.01/1.00  --inst_start_prop_sim_after_learn       3
% 2.01/1.00  --inst_sel_renew                        solver
% 2.01/1.00  --inst_lit_activity_flag                true
% 2.01/1.00  --inst_restr_to_given                   false
% 2.01/1.00  --inst_activity_threshold               500
% 2.01/1.00  --inst_out_proof                        true
% 2.01/1.00  
% 2.01/1.00  ------ Resolution Options
% 2.01/1.00  
% 2.01/1.00  --resolution_flag                       false
% 2.01/1.00  --res_lit_sel                           adaptive
% 2.01/1.00  --res_lit_sel_side                      none
% 2.01/1.00  --res_ordering                          kbo
% 2.01/1.00  --res_to_prop_solver                    active
% 2.01/1.00  --res_prop_simpl_new                    false
% 2.01/1.00  --res_prop_simpl_given                  true
% 2.01/1.00  --res_passive_queue_type                priority_queues
% 2.01/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.01/1.00  --res_passive_queues_freq               [15;5]
% 2.01/1.00  --res_forward_subs                      full
% 2.01/1.00  --res_backward_subs                     full
% 2.01/1.00  --res_forward_subs_resolution           true
% 2.01/1.00  --res_backward_subs_resolution          true
% 2.01/1.00  --res_orphan_elimination                true
% 2.01/1.00  --res_time_limit                        2.
% 2.01/1.00  --res_out_proof                         true
% 2.01/1.00  
% 2.01/1.00  ------ Superposition Options
% 2.01/1.00  
% 2.01/1.00  --superposition_flag                    true
% 2.01/1.00  --sup_passive_queue_type                priority_queues
% 2.01/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.01/1.00  --sup_passive_queues_freq               [8;1;4]
% 2.01/1.00  --demod_completeness_check              fast
% 2.01/1.00  --demod_use_ground                      true
% 2.01/1.00  --sup_to_prop_solver                    passive
% 2.01/1.00  --sup_prop_simpl_new                    true
% 2.01/1.00  --sup_prop_simpl_given                  true
% 2.01/1.00  --sup_fun_splitting                     false
% 2.01/1.00  --sup_smt_interval                      50000
% 2.01/1.00  
% 2.01/1.00  ------ Superposition Simplification Setup
% 2.01/1.00  
% 2.01/1.00  --sup_indices_passive                   []
% 2.01/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.01/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.01/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.01/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 2.01/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.01/1.00  --sup_full_bw                           [BwDemod]
% 2.01/1.00  --sup_immed_triv                        [TrivRules]
% 2.01/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.01/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.01/1.00  --sup_immed_bw_main                     []
% 2.01/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.01/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 2.01/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.01/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.01/1.00  
% 2.01/1.00  ------ Combination Options
% 2.01/1.00  
% 2.01/1.00  --comb_res_mult                         3
% 2.01/1.00  --comb_sup_mult                         2
% 2.01/1.00  --comb_inst_mult                        10
% 2.01/1.00  
% 2.01/1.00  ------ Debug Options
% 2.01/1.00  
% 2.01/1.00  --dbg_backtrace                         false
% 2.01/1.00  --dbg_dump_prop_clauses                 false
% 2.01/1.00  --dbg_dump_prop_clauses_file            -
% 2.01/1.00  --dbg_out_stat                          false
% 2.01/1.00  
% 2.01/1.00  
% 2.01/1.00  
% 2.01/1.00  
% 2.01/1.00  ------ Proving...
% 2.01/1.00  
% 2.01/1.00  
% 2.01/1.00  % SZS status Theorem for theBenchmark.p
% 2.01/1.00  
% 2.01/1.00  % SZS output start CNFRefutation for theBenchmark.p
% 2.01/1.00  
% 2.01/1.00  fof(f6,conjecture,(
% 2.01/1.00    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => (v2_funct_1(X1) => ! [X2,X3] : ((k1_funct_1(X1,X2) = k1_funct_1(X1,X3) & r2_hidden(X3,X0) & r2_hidden(X2,X0)) => X2 = X3)))),
% 2.01/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.01/1.00  
% 2.01/1.00  fof(f7,negated_conjecture,(
% 2.01/1.00    ~! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => (v2_funct_1(X1) => ! [X2,X3] : ((k1_funct_1(X1,X2) = k1_funct_1(X1,X3) & r2_hidden(X3,X0) & r2_hidden(X2,X0)) => X2 = X3)))),
% 2.01/1.00    inference(negated_conjecture,[],[f6])).
% 2.01/1.00  
% 2.01/1.00  fof(f16,plain,(
% 2.01/1.00    ? [X0,X1] : ((? [X2,X3] : (X2 != X3 & (k1_funct_1(X1,X2) = k1_funct_1(X1,X3) & r2_hidden(X3,X0) & r2_hidden(X2,X0))) & v2_funct_1(X1)) & (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)))),
% 2.01/1.00    inference(ennf_transformation,[],[f7])).
% 2.01/1.00  
% 2.01/1.00  fof(f17,plain,(
% 2.01/1.00    ? [X0,X1] : (? [X2,X3] : (X2 != X3 & k1_funct_1(X1,X2) = k1_funct_1(X1,X3) & r2_hidden(X3,X0) & r2_hidden(X2,X0)) & v2_funct_1(X1) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1))),
% 2.01/1.00    inference(flattening,[],[f16])).
% 2.01/1.00  
% 2.01/1.00  fof(f29,plain,(
% 2.01/1.00    ( ! [X0,X1] : (? [X2,X3] : (X2 != X3 & k1_funct_1(X1,X2) = k1_funct_1(X1,X3) & r2_hidden(X3,X0) & r2_hidden(X2,X0)) => (sK5 != sK6 & k1_funct_1(X1,sK5) = k1_funct_1(X1,sK6) & r2_hidden(sK6,X0) & r2_hidden(sK5,X0))) )),
% 2.01/1.00    introduced(choice_axiom,[])).
% 2.01/1.00  
% 2.01/1.00  fof(f28,plain,(
% 2.01/1.00    ? [X0,X1] : (? [X2,X3] : (X2 != X3 & k1_funct_1(X1,X2) = k1_funct_1(X1,X3) & r2_hidden(X3,X0) & r2_hidden(X2,X0)) & v2_funct_1(X1) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => (? [X3,X2] : (X2 != X3 & k1_funct_1(sK4,X2) = k1_funct_1(sK4,X3) & r2_hidden(X3,sK3) & r2_hidden(X2,sK3)) & v2_funct_1(sK4) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK3,sK3))) & v1_funct_2(sK4,sK3,sK3) & v1_funct_1(sK4))),
% 2.01/1.00    introduced(choice_axiom,[])).
% 2.01/1.00  
% 2.01/1.00  fof(f30,plain,(
% 2.01/1.00    (sK5 != sK6 & k1_funct_1(sK4,sK5) = k1_funct_1(sK4,sK6) & r2_hidden(sK6,sK3) & r2_hidden(sK5,sK3)) & v2_funct_1(sK4) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK3,sK3))) & v1_funct_2(sK4,sK3,sK3) & v1_funct_1(sK4)),
% 2.01/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5,sK6])],[f17,f29,f28])).
% 2.01/1.00  
% 2.01/1.00  fof(f52,plain,(
% 2.01/1.00    r2_hidden(sK5,sK3)),
% 2.01/1.00    inference(cnf_transformation,[],[f30])).
% 2.01/1.00  
% 2.01/1.00  fof(f2,axiom,(
% 2.01/1.00    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (k2_funct_1(X0) = X1 <=> (! [X2,X3] : (((k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))) => (k1_funct_1(X1,X2) = X3 & r2_hidden(X2,k2_relat_1(X0)))) & ((k1_funct_1(X1,X2) = X3 & r2_hidden(X2,k2_relat_1(X0))) => (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))) & k1_relat_1(X1) = k2_relat_1(X0))))))),
% 2.01/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.01/1.00  
% 2.01/1.00  fof(f10,plain,(
% 2.01/1.00    ! [X0] : ((! [X1] : ((k2_funct_1(X0) = X1 <=> (! [X2,X3] : (((k1_funct_1(X1,X2) = X3 & r2_hidden(X2,k2_relat_1(X0))) | (k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0)))) & ((k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))) | (k1_funct_1(X1,X2) != X3 | ~r2_hidden(X2,k2_relat_1(X0))))) & k1_relat_1(X1) = k2_relat_1(X0))) | (~v1_funct_1(X1) | ~v1_relat_1(X1))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 2.01/1.00    inference(ennf_transformation,[],[f2])).
% 2.01/1.00  
% 2.01/1.00  fof(f11,plain,(
% 2.01/1.00    ! [X0] : (! [X1] : ((k2_funct_1(X0) = X1 <=> (! [X2,X3] : (((k1_funct_1(X1,X2) = X3 & r2_hidden(X2,k2_relat_1(X0))) | k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0))) & ((k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))) | k1_funct_1(X1,X2) != X3 | ~r2_hidden(X2,k2_relat_1(X0)))) & k1_relat_1(X1) = k2_relat_1(X0))) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.01/1.00    inference(flattening,[],[f10])).
% 2.01/1.00  
% 2.01/1.00  fof(f18,plain,(
% 2.01/1.00    ! [X2,X3,X0,X1] : (sP0(X2,X3,X0,X1) <=> ((k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))) | k1_funct_1(X1,X2) != X3 | ~r2_hidden(X2,k2_relat_1(X0))))),
% 2.01/1.00    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 2.01/1.00  
% 2.01/1.00  fof(f19,plain,(
% 2.01/1.00    ! [X0] : (! [X1] : ((k2_funct_1(X0) = X1 <=> (! [X2,X3] : (((k1_funct_1(X1,X2) = X3 & r2_hidden(X2,k2_relat_1(X0))) | k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0))) & sP0(X2,X3,X0,X1)) & k1_relat_1(X1) = k2_relat_1(X0))) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.01/1.00    inference(definition_folding,[],[f11,f18])).
% 2.01/1.00  
% 2.01/1.00  fof(f23,plain,(
% 2.01/1.00    ! [X0] : (! [X1] : (((k2_funct_1(X0) = X1 | (? [X2,X3] : (((k1_funct_1(X1,X2) != X3 | ~r2_hidden(X2,k2_relat_1(X0))) & k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))) | ~sP0(X2,X3,X0,X1)) | k1_relat_1(X1) != k2_relat_1(X0))) & ((! [X2,X3] : (((k1_funct_1(X1,X2) = X3 & r2_hidden(X2,k2_relat_1(X0))) | k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0))) & sP0(X2,X3,X0,X1)) & k1_relat_1(X1) = k2_relat_1(X0)) | k2_funct_1(X0) != X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.01/1.00    inference(nnf_transformation,[],[f19])).
% 2.01/1.00  
% 2.01/1.00  fof(f24,plain,(
% 2.01/1.00    ! [X0] : (! [X1] : (((k2_funct_1(X0) = X1 | ? [X2,X3] : (((k1_funct_1(X1,X2) != X3 | ~r2_hidden(X2,k2_relat_1(X0))) & k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))) | ~sP0(X2,X3,X0,X1)) | k1_relat_1(X1) != k2_relat_1(X0)) & ((! [X2,X3] : (((k1_funct_1(X1,X2) = X3 & r2_hidden(X2,k2_relat_1(X0))) | k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0))) & sP0(X2,X3,X0,X1)) & k1_relat_1(X1) = k2_relat_1(X0)) | k2_funct_1(X0) != X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.01/1.00    inference(flattening,[],[f23])).
% 2.01/1.00  
% 2.01/1.00  fof(f25,plain,(
% 2.01/1.00    ! [X0] : (! [X1] : (((k2_funct_1(X0) = X1 | ? [X2,X3] : (((k1_funct_1(X1,X2) != X3 | ~r2_hidden(X2,k2_relat_1(X0))) & k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))) | ~sP0(X2,X3,X0,X1)) | k1_relat_1(X1) != k2_relat_1(X0)) & ((! [X4,X5] : (((k1_funct_1(X1,X4) = X5 & r2_hidden(X4,k2_relat_1(X0))) | k1_funct_1(X0,X5) != X4 | ~r2_hidden(X5,k1_relat_1(X0))) & sP0(X4,X5,X0,X1)) & k1_relat_1(X1) = k2_relat_1(X0)) | k2_funct_1(X0) != X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.01/1.00    inference(rectify,[],[f24])).
% 2.01/1.00  
% 2.01/1.00  fof(f26,plain,(
% 2.01/1.00    ! [X1,X0] : (? [X2,X3] : (((k1_funct_1(X1,X2) != X3 | ~r2_hidden(X2,k2_relat_1(X0))) & k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))) | ~sP0(X2,X3,X0,X1)) => (((k1_funct_1(X1,sK1(X0,X1)) != sK2(X0,X1) | ~r2_hidden(sK1(X0,X1),k2_relat_1(X0))) & k1_funct_1(X0,sK2(X0,X1)) = sK1(X0,X1) & r2_hidden(sK2(X0,X1),k1_relat_1(X0))) | ~sP0(sK1(X0,X1),sK2(X0,X1),X0,X1)))),
% 2.01/1.00    introduced(choice_axiom,[])).
% 2.01/1.00  
% 2.01/1.00  fof(f27,plain,(
% 2.01/1.00    ! [X0] : (! [X1] : (((k2_funct_1(X0) = X1 | (((k1_funct_1(X1,sK1(X0,X1)) != sK2(X0,X1) | ~r2_hidden(sK1(X0,X1),k2_relat_1(X0))) & k1_funct_1(X0,sK2(X0,X1)) = sK1(X0,X1) & r2_hidden(sK2(X0,X1),k1_relat_1(X0))) | ~sP0(sK1(X0,X1),sK2(X0,X1),X0,X1)) | k1_relat_1(X1) != k2_relat_1(X0)) & ((! [X4,X5] : (((k1_funct_1(X1,X4) = X5 & r2_hidden(X4,k2_relat_1(X0))) | k1_funct_1(X0,X5) != X4 | ~r2_hidden(X5,k1_relat_1(X0))) & sP0(X4,X5,X0,X1)) & k1_relat_1(X1) = k2_relat_1(X0)) | k2_funct_1(X0) != X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.01/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f25,f26])).
% 2.01/1.00  
% 2.01/1.00  fof(f41,plain,(
% 2.01/1.00    ( ! [X4,X0,X5,X1] : (k1_funct_1(X1,X4) = X5 | k1_funct_1(X0,X5) != X4 | ~r2_hidden(X5,k1_relat_1(X0)) | k2_funct_1(X0) != X1 | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.01/1.00    inference(cnf_transformation,[],[f27])).
% 2.01/1.00  
% 2.01/1.00  fof(f59,plain,(
% 2.01/1.00    ( ! [X0,X5,X1] : (k1_funct_1(X1,k1_funct_1(X0,X5)) = X5 | ~r2_hidden(X5,k1_relat_1(X0)) | k2_funct_1(X0) != X1 | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.01/1.00    inference(equality_resolution,[],[f41])).
% 2.01/1.00  
% 2.01/1.00  fof(f60,plain,(
% 2.01/1.00    ( ! [X0,X5] : (k1_funct_1(k2_funct_1(X0),k1_funct_1(X0,X5)) = X5 | ~r2_hidden(X5,k1_relat_1(X0)) | ~v1_funct_1(k2_funct_1(X0)) | ~v1_relat_1(k2_funct_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.01/1.00    inference(equality_resolution,[],[f59])).
% 2.01/1.00  
% 2.01/1.00  fof(f51,plain,(
% 2.01/1.00    v2_funct_1(sK4)),
% 2.01/1.00    inference(cnf_transformation,[],[f30])).
% 2.01/1.00  
% 2.01/1.00  fof(f48,plain,(
% 2.01/1.00    v1_funct_1(sK4)),
% 2.01/1.00    inference(cnf_transformation,[],[f30])).
% 2.01/1.00  
% 2.01/1.00  fof(f3,axiom,(
% 2.01/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 2.01/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.01/1.00  
% 2.01/1.00  fof(f12,plain,(
% 2.01/1.00    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.01/1.00    inference(ennf_transformation,[],[f3])).
% 2.01/1.00  
% 2.01/1.00  fof(f45,plain,(
% 2.01/1.00    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.01/1.00    inference(cnf_transformation,[],[f12])).
% 2.01/1.00  
% 2.01/1.00  fof(f50,plain,(
% 2.01/1.00    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK3,sK3)))),
% 2.01/1.00    inference(cnf_transformation,[],[f30])).
% 2.01/1.00  
% 2.01/1.00  fof(f1,axiom,(
% 2.01/1.00    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))))),
% 2.01/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.01/1.00  
% 2.01/1.00  fof(f8,plain,(
% 2.01/1.00    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 2.01/1.00    inference(ennf_transformation,[],[f1])).
% 2.01/1.00  
% 2.01/1.00  fof(f9,plain,(
% 2.01/1.00    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.01/1.00    inference(flattening,[],[f8])).
% 2.01/1.00  
% 2.01/1.00  fof(f32,plain,(
% 2.01/1.00    ( ! [X0] : (v1_funct_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.01/1.00    inference(cnf_transformation,[],[f9])).
% 2.01/1.00  
% 2.01/1.00  fof(f31,plain,(
% 2.01/1.00    ( ! [X0] : (v1_relat_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.01/1.00    inference(cnf_transformation,[],[f9])).
% 2.01/1.00  
% 2.01/1.00  fof(f4,axiom,(
% 2.01/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 2.01/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.01/1.00  
% 2.01/1.00  fof(f13,plain,(
% 2.01/1.00    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.01/1.00    inference(ennf_transformation,[],[f4])).
% 2.01/1.00  
% 2.01/1.00  fof(f46,plain,(
% 2.01/1.00    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.01/1.00    inference(cnf_transformation,[],[f13])).
% 2.01/1.00  
% 2.01/1.00  fof(f5,axiom,(
% 2.01/1.00    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => k1_relset_1(X0,X0,X1) = X0)),
% 2.01/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.01/1.00  
% 2.01/1.00  fof(f14,plain,(
% 2.01/1.00    ! [X0,X1] : (k1_relset_1(X0,X0,X1) = X0 | (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)))),
% 2.01/1.00    inference(ennf_transformation,[],[f5])).
% 2.01/1.00  
% 2.01/1.00  fof(f15,plain,(
% 2.01/1.00    ! [X0,X1] : (k1_relset_1(X0,X0,X1) = X0 | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1))),
% 2.01/1.00    inference(flattening,[],[f14])).
% 2.01/1.00  
% 2.01/1.00  fof(f47,plain,(
% 2.01/1.00    ( ! [X0,X1] : (k1_relset_1(X0,X0,X1) = X0 | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)) )),
% 2.01/1.00    inference(cnf_transformation,[],[f15])).
% 2.01/1.00  
% 2.01/1.00  fof(f49,plain,(
% 2.01/1.00    v1_funct_2(sK4,sK3,sK3)),
% 2.01/1.00    inference(cnf_transformation,[],[f30])).
% 2.01/1.00  
% 2.01/1.00  fof(f53,plain,(
% 2.01/1.00    r2_hidden(sK6,sK3)),
% 2.01/1.00    inference(cnf_transformation,[],[f30])).
% 2.01/1.00  
% 2.01/1.00  fof(f54,plain,(
% 2.01/1.00    k1_funct_1(sK4,sK5) = k1_funct_1(sK4,sK6)),
% 2.01/1.00    inference(cnf_transformation,[],[f30])).
% 2.01/1.00  
% 2.01/1.00  fof(f55,plain,(
% 2.01/1.00    sK5 != sK6),
% 2.01/1.00    inference(cnf_transformation,[],[f30])).
% 2.01/1.00  
% 2.01/1.00  cnf(c_20,negated_conjecture,
% 2.01/1.00      ( r2_hidden(sK5,sK3) ),
% 2.01/1.00      inference(cnf_transformation,[],[f52]) ).
% 2.01/1.00  
% 2.01/1.00  cnf(c_1256,negated_conjecture,
% 2.01/1.00      ( r2_hidden(sK5,sK3) ),
% 2.01/1.00      inference(subtyping,[status(esa)],[c_20]) ).
% 2.01/1.00  
% 2.01/1.00  cnf(c_1728,plain,
% 2.01/1.00      ( r2_hidden(sK5,sK3) = iProver_top ),
% 2.01/1.00      inference(predicate_to_equality,[status(thm)],[c_1256]) ).
% 2.01/1.00  
% 2.01/1.00  cnf(c_10,plain,
% 2.01/1.00      ( ~ r2_hidden(X0,k1_relat_1(X1))
% 2.01/1.00      | ~ v2_funct_1(X1)
% 2.01/1.00      | ~ v1_relat_1(X1)
% 2.01/1.00      | ~ v1_relat_1(k2_funct_1(X1))
% 2.01/1.00      | ~ v1_funct_1(X1)
% 2.01/1.00      | ~ v1_funct_1(k2_funct_1(X1))
% 2.01/1.00      | k1_funct_1(k2_funct_1(X1),k1_funct_1(X1,X0)) = X0 ),
% 2.01/1.00      inference(cnf_transformation,[],[f60]) ).
% 2.01/1.00  
% 2.01/1.00  cnf(c_21,negated_conjecture,
% 2.01/1.00      ( v2_funct_1(sK4) ),
% 2.01/1.00      inference(cnf_transformation,[],[f51]) ).
% 2.01/1.00  
% 2.01/1.00  cnf(c_446,plain,
% 2.01/1.00      ( ~ r2_hidden(X0,k1_relat_1(X1))
% 2.01/1.00      | ~ v1_relat_1(X1)
% 2.01/1.00      | ~ v1_relat_1(k2_funct_1(X1))
% 2.01/1.00      | ~ v1_funct_1(X1)
% 2.01/1.00      | ~ v1_funct_1(k2_funct_1(X1))
% 2.01/1.00      | k1_funct_1(k2_funct_1(X1),k1_funct_1(X1,X0)) = X0
% 2.01/1.00      | sK4 != X1 ),
% 2.01/1.00      inference(resolution_lifted,[status(thm)],[c_10,c_21]) ).
% 2.01/1.00  
% 2.01/1.00  cnf(c_447,plain,
% 2.01/1.00      ( ~ r2_hidden(X0,k1_relat_1(sK4))
% 2.01/1.00      | ~ v1_relat_1(k2_funct_1(sK4))
% 2.01/1.00      | ~ v1_relat_1(sK4)
% 2.01/1.00      | ~ v1_funct_1(k2_funct_1(sK4))
% 2.01/1.00      | ~ v1_funct_1(sK4)
% 2.01/1.00      | k1_funct_1(k2_funct_1(sK4),k1_funct_1(sK4,X0)) = X0 ),
% 2.01/1.00      inference(unflattening,[status(thm)],[c_446]) ).
% 2.01/1.00  
% 2.01/1.00  cnf(c_24,negated_conjecture,
% 2.01/1.00      ( v1_funct_1(sK4) ),
% 2.01/1.00      inference(cnf_transformation,[],[f48]) ).
% 2.01/1.00  
% 2.01/1.00  cnf(c_451,plain,
% 2.01/1.00      ( ~ v1_funct_1(k2_funct_1(sK4))
% 2.01/1.00      | ~ v1_relat_1(sK4)
% 2.01/1.00      | ~ v1_relat_1(k2_funct_1(sK4))
% 2.01/1.00      | ~ r2_hidden(X0,k1_relat_1(sK4))
% 2.01/1.00      | k1_funct_1(k2_funct_1(sK4),k1_funct_1(sK4,X0)) = X0 ),
% 2.01/1.00      inference(global_propositional_subsumption,
% 2.01/1.00                [status(thm)],
% 2.01/1.00                [c_447,c_24]) ).
% 2.01/1.00  
% 2.01/1.00  cnf(c_452,plain,
% 2.01/1.00      ( ~ r2_hidden(X0,k1_relat_1(sK4))
% 2.01/1.00      | ~ v1_relat_1(k2_funct_1(sK4))
% 2.01/1.00      | ~ v1_relat_1(sK4)
% 2.01/1.00      | ~ v1_funct_1(k2_funct_1(sK4))
% 2.01/1.00      | k1_funct_1(k2_funct_1(sK4),k1_funct_1(sK4,X0)) = X0 ),
% 2.01/1.00      inference(renaming,[status(thm)],[c_451]) ).
% 2.01/1.00  
% 2.01/1.00  cnf(c_1246,plain,
% 2.01/1.00      ( ~ r2_hidden(X0_48,k1_relat_1(sK4))
% 2.01/1.00      | ~ v1_relat_1(k2_funct_1(sK4))
% 2.01/1.00      | ~ v1_relat_1(sK4)
% 2.01/1.00      | ~ v1_funct_1(k2_funct_1(sK4))
% 2.01/1.00      | k1_funct_1(k2_funct_1(sK4),k1_funct_1(sK4,X0_48)) = X0_48 ),
% 2.01/1.00      inference(subtyping,[status(esa)],[c_452]) ).
% 2.01/1.00  
% 2.01/1.00  cnf(c_1269,plain,
% 2.01/1.00      ( ~ r2_hidden(X0_48,k1_relat_1(sK4))
% 2.01/1.00      | k1_funct_1(k2_funct_1(sK4),k1_funct_1(sK4,X0_48)) = X0_48
% 2.01/1.00      | ~ sP1_iProver_split ),
% 2.01/1.00      inference(splitting,
% 2.01/1.00                [splitting(split),new_symbols(definition,[sP1_iProver_split])],
% 2.01/1.00                [c_1246]) ).
% 2.01/1.00  
% 2.01/1.00  cnf(c_1738,plain,
% 2.01/1.00      ( k1_funct_1(k2_funct_1(sK4),k1_funct_1(sK4,X0_48)) = X0_48
% 2.01/1.00      | r2_hidden(X0_48,k1_relat_1(sK4)) != iProver_top
% 2.01/1.00      | sP1_iProver_split != iProver_top ),
% 2.01/1.00      inference(predicate_to_equality,[status(thm)],[c_1269]) ).
% 2.01/1.00  
% 2.01/1.00  cnf(c_14,plain,
% 2.01/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.01/1.00      | v1_relat_1(X0) ),
% 2.01/1.00      inference(cnf_transformation,[],[f45]) ).
% 2.01/1.00  
% 2.01/1.00  cnf(c_22,negated_conjecture,
% 2.01/1.00      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK3,sK3))) ),
% 2.01/1.00      inference(cnf_transformation,[],[f50]) ).
% 2.01/1.00  
% 2.01/1.00  cnf(c_286,plain,
% 2.01/1.00      ( v1_relat_1(X0)
% 2.01/1.00      | k1_zfmisc_1(k2_zfmisc_1(X1,X2)) != k1_zfmisc_1(k2_zfmisc_1(sK3,sK3))
% 2.01/1.00      | sK4 != X0 ),
% 2.01/1.00      inference(resolution_lifted,[status(thm)],[c_14,c_22]) ).
% 2.01/1.00  
% 2.01/1.00  cnf(c_287,plain,
% 2.01/1.00      ( v1_relat_1(sK4)
% 2.01/1.00      | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK3,sK3)) ),
% 2.01/1.00      inference(unflattening,[status(thm)],[c_286]) ).
% 2.01/1.00  
% 2.01/1.00  cnf(c_1252,plain,
% 2.01/1.00      ( v1_relat_1(sK4)
% 2.01/1.00      | k1_zfmisc_1(k2_zfmisc_1(X0_50,X1_50)) != k1_zfmisc_1(k2_zfmisc_1(sK3,sK3)) ),
% 2.01/1.00      inference(subtyping,[status(esa)],[c_287]) ).
% 2.01/1.00  
% 2.01/1.00  cnf(c_1340,plain,
% 2.01/1.00      ( k1_zfmisc_1(k2_zfmisc_1(X0_50,X1_50)) != k1_zfmisc_1(k2_zfmisc_1(sK3,sK3))
% 2.01/1.00      | v1_relat_1(sK4) = iProver_top ),
% 2.01/1.00      inference(predicate_to_equality,[status(thm)],[c_1252]) ).
% 2.01/1.00  
% 2.01/1.00  cnf(c_1342,plain,
% 2.01/1.00      ( k1_zfmisc_1(k2_zfmisc_1(sK3,sK3)) != k1_zfmisc_1(k2_zfmisc_1(sK3,sK3))
% 2.01/1.00      | v1_relat_1(sK4) = iProver_top ),
% 2.01/1.00      inference(instantiation,[status(thm)],[c_1340]) ).
% 2.01/1.00  
% 2.01/1.00  cnf(c_1358,plain,
% 2.01/1.00      ( k1_funct_1(k2_funct_1(sK4),k1_funct_1(sK4,X0_48)) = X0_48
% 2.01/1.00      | r2_hidden(X0_48,k1_relat_1(sK4)) != iProver_top
% 2.01/1.00      | sP1_iProver_split != iProver_top ),
% 2.01/1.00      inference(predicate_to_equality,[status(thm)],[c_1269]) ).
% 2.01/1.00  
% 2.01/1.00  cnf(c_1270,plain,
% 2.01/1.00      ( ~ v1_relat_1(k2_funct_1(sK4))
% 2.01/1.00      | ~ v1_relat_1(sK4)
% 2.01/1.00      | ~ v1_funct_1(k2_funct_1(sK4))
% 2.01/1.00      | sP1_iProver_split ),
% 2.01/1.00      inference(splitting,
% 2.01/1.00                [splitting(split),new_symbols(definition,[])],
% 2.01/1.00                [c_1246]) ).
% 2.01/1.00  
% 2.01/1.00  cnf(c_0,plain,
% 2.01/1.00      ( ~ v1_relat_1(X0)
% 2.01/1.00      | ~ v1_funct_1(X0)
% 2.01/1.00      | v1_funct_1(k2_funct_1(X0)) ),
% 2.01/1.00      inference(cnf_transformation,[],[f32]) ).
% 2.01/1.00  
% 2.01/1.00  cnf(c_1266,plain,
% 2.01/1.00      ( ~ v1_relat_1(X0_49)
% 2.01/1.00      | ~ v1_funct_1(X0_49)
% 2.01/1.00      | v1_funct_1(k2_funct_1(X0_49)) ),
% 2.01/1.00      inference(subtyping,[status(esa)],[c_0]) ).
% 2.01/1.00  
% 2.01/1.00  cnf(c_1316,plain,
% 2.01/1.00      ( ~ v1_relat_1(sK4)
% 2.01/1.00      | v1_funct_1(k2_funct_1(sK4))
% 2.01/1.00      | ~ v1_funct_1(sK4) ),
% 2.01/1.00      inference(instantiation,[status(thm)],[c_1266]) ).
% 2.01/1.00  
% 2.01/1.00  cnf(c_1,plain,
% 2.01/1.00      ( ~ v1_relat_1(X0)
% 2.01/1.00      | v1_relat_1(k2_funct_1(X0))
% 2.01/1.00      | ~ v1_funct_1(X0) ),
% 2.01/1.00      inference(cnf_transformation,[],[f31]) ).
% 2.01/1.00  
% 2.01/1.00  cnf(c_1265,plain,
% 2.01/1.00      ( ~ v1_relat_1(X0_49)
% 2.01/1.00      | v1_relat_1(k2_funct_1(X0_49))
% 2.01/1.00      | ~ v1_funct_1(X0_49) ),
% 2.01/1.00      inference(subtyping,[status(esa)],[c_1]) ).
% 2.01/1.00  
% 2.01/1.00  cnf(c_1319,plain,
% 2.01/1.00      ( v1_relat_1(k2_funct_1(sK4))
% 2.01/1.00      | ~ v1_relat_1(sK4)
% 2.01/1.00      | ~ v1_funct_1(sK4) ),
% 2.01/1.00      inference(instantiation,[status(thm)],[c_1265]) ).
% 2.01/1.00  
% 2.01/1.00  cnf(c_1416,plain,
% 2.01/1.00      ( ~ v1_relat_1(sK4) | sP1_iProver_split ),
% 2.01/1.00      inference(global_propositional_subsumption,
% 2.01/1.00                [status(thm)],
% 2.01/1.00                [c_1270,c_24,c_1316,c_1319]) ).
% 2.01/1.00  
% 2.01/1.00  cnf(c_1418,plain,
% 2.01/1.00      ( v1_relat_1(sK4) != iProver_top
% 2.01/1.00      | sP1_iProver_split = iProver_top ),
% 2.01/1.00      inference(predicate_to_equality,[status(thm)],[c_1416]) ).
% 2.01/1.00  
% 2.01/1.00  cnf(c_1277,plain,( X0_51 = X0_51 ),theory(equality) ).
% 2.01/1.00  
% 2.01/1.00  cnf(c_1937,plain,
% 2.01/1.00      ( k1_zfmisc_1(k2_zfmisc_1(sK3,sK3)) = k1_zfmisc_1(k2_zfmisc_1(sK3,sK3)) ),
% 2.01/1.00      inference(instantiation,[status(thm)],[c_1277]) ).
% 2.01/1.00  
% 2.01/1.00  cnf(c_2325,plain,
% 2.01/1.00      ( r2_hidden(X0_48,k1_relat_1(sK4)) != iProver_top
% 2.01/1.00      | k1_funct_1(k2_funct_1(sK4),k1_funct_1(sK4,X0_48)) = X0_48 ),
% 2.01/1.00      inference(global_propositional_subsumption,
% 2.01/1.00                [status(thm)],
% 2.01/1.00                [c_1738,c_1342,c_1358,c_1418,c_1937]) ).
% 2.01/1.00  
% 2.01/1.00  cnf(c_2326,plain,
% 2.01/1.00      ( k1_funct_1(k2_funct_1(sK4),k1_funct_1(sK4,X0_48)) = X0_48
% 2.01/1.00      | r2_hidden(X0_48,k1_relat_1(sK4)) != iProver_top ),
% 2.01/1.00      inference(renaming,[status(thm)],[c_2325]) ).
% 2.01/1.00  
% 2.01/1.00  cnf(c_15,plain,
% 2.01/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.01/1.00      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 2.01/1.00      inference(cnf_transformation,[],[f46]) ).
% 2.01/1.00  
% 2.01/1.00  cnf(c_277,plain,
% 2.01/1.00      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 2.01/1.00      | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK3,sK3))
% 2.01/1.00      | sK4 != X2 ),
% 2.01/1.00      inference(resolution_lifted,[status(thm)],[c_15,c_22]) ).
% 2.01/1.00  
% 2.01/1.00  cnf(c_278,plain,
% 2.01/1.00      ( k1_relset_1(X0,X1,sK4) = k1_relat_1(sK4)
% 2.01/1.00      | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK3,sK3)) ),
% 2.01/1.00      inference(unflattening,[status(thm)],[c_277]) ).
% 2.01/1.00  
% 2.01/1.00  cnf(c_1253,plain,
% 2.01/1.00      ( k1_zfmisc_1(k2_zfmisc_1(X0_50,X1_50)) != k1_zfmisc_1(k2_zfmisc_1(sK3,sK3))
% 2.01/1.00      | k1_relset_1(X0_50,X1_50,sK4) = k1_relat_1(sK4) ),
% 2.01/1.00      inference(subtyping,[status(esa)],[c_278]) ).
% 2.01/1.00  
% 2.01/1.00  cnf(c_1951,plain,
% 2.01/1.00      ( k1_relset_1(sK3,sK3,sK4) = k1_relat_1(sK4) ),
% 2.01/1.00      inference(equality_resolution,[status(thm)],[c_1253]) ).
% 2.01/1.00  
% 2.01/1.00  cnf(c_16,plain,
% 2.01/1.00      ( ~ v1_funct_2(X0,X1,X1)
% 2.01/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
% 2.01/1.00      | ~ v1_funct_1(X0)
% 2.01/1.00      | k1_relset_1(X1,X1,X0) = X1 ),
% 2.01/1.00      inference(cnf_transformation,[],[f47]) ).
% 2.01/1.00  
% 2.01/1.00  cnf(c_23,negated_conjecture,
% 2.01/1.00      ( v1_funct_2(sK4,sK3,sK3) ),
% 2.01/1.00      inference(cnf_transformation,[],[f49]) ).
% 2.01/1.00  
% 2.01/1.00  cnf(c_268,plain,
% 2.01/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
% 2.01/1.00      | ~ v1_funct_1(X0)
% 2.01/1.00      | k1_relset_1(X1,X1,X0) = X1
% 2.01/1.00      | sK3 != X1
% 2.01/1.00      | sK4 != X0 ),
% 2.01/1.00      inference(resolution_lifted,[status(thm)],[c_16,c_23]) ).
% 2.01/1.00  
% 2.01/1.00  cnf(c_269,plain,
% 2.01/1.00      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK3,sK3)))
% 2.01/1.00      | ~ v1_funct_1(sK4)
% 2.01/1.00      | k1_relset_1(sK3,sK3,sK4) = sK3 ),
% 2.01/1.00      inference(unflattening,[status(thm)],[c_268]) ).
% 2.01/1.00  
% 2.01/1.00  cnf(c_271,plain,
% 2.01/1.00      ( k1_relset_1(sK3,sK3,sK4) = sK3 ),
% 2.01/1.00      inference(global_propositional_subsumption,
% 2.01/1.00                [status(thm)],
% 2.01/1.00                [c_269,c_24,c_22]) ).
% 2.01/1.00  
% 2.01/1.00  cnf(c_1254,plain,
% 2.01/1.00      ( k1_relset_1(sK3,sK3,sK4) = sK3 ),
% 2.01/1.00      inference(subtyping,[status(esa)],[c_271]) ).
% 2.01/1.00  
% 2.01/1.00  cnf(c_1952,plain,
% 2.01/1.00      ( k1_relat_1(sK4) = sK3 ),
% 2.01/1.00      inference(light_normalisation,[status(thm)],[c_1951,c_1254]) ).
% 2.01/1.00  
% 2.01/1.00  cnf(c_2331,plain,
% 2.01/1.00      ( k1_funct_1(k2_funct_1(sK4),k1_funct_1(sK4,X0_48)) = X0_48
% 2.01/1.00      | r2_hidden(X0_48,sK3) != iProver_top ),
% 2.01/1.00      inference(light_normalisation,[status(thm)],[c_2326,c_1952]) ).
% 2.01/1.00  
% 2.01/1.00  cnf(c_2338,plain,
% 2.01/1.00      ( k1_funct_1(k2_funct_1(sK4),k1_funct_1(sK4,sK5)) = sK5 ),
% 2.01/1.00      inference(superposition,[status(thm)],[c_1728,c_2331]) ).
% 2.01/1.00  
% 2.01/1.00  cnf(c_19,negated_conjecture,
% 2.01/1.00      ( r2_hidden(sK6,sK3) ),
% 2.01/1.00      inference(cnf_transformation,[],[f53]) ).
% 2.01/1.00  
% 2.01/1.00  cnf(c_1257,negated_conjecture,
% 2.01/1.00      ( r2_hidden(sK6,sK3) ),
% 2.01/1.00      inference(subtyping,[status(esa)],[c_19]) ).
% 2.01/1.00  
% 2.01/1.00  cnf(c_1727,plain,
% 2.01/1.00      ( r2_hidden(sK6,sK3) = iProver_top ),
% 2.01/1.00      inference(predicate_to_equality,[status(thm)],[c_1257]) ).
% 2.01/1.00  
% 2.01/1.00  cnf(c_2337,plain,
% 2.01/1.00      ( k1_funct_1(k2_funct_1(sK4),k1_funct_1(sK4,sK6)) = sK6 ),
% 2.01/1.00      inference(superposition,[status(thm)],[c_1727,c_2331]) ).
% 2.01/1.00  
% 2.01/1.00  cnf(c_18,negated_conjecture,
% 2.01/1.00      ( k1_funct_1(sK4,sK5) = k1_funct_1(sK4,sK6) ),
% 2.01/1.00      inference(cnf_transformation,[],[f54]) ).
% 2.01/1.00  
% 2.01/1.00  cnf(c_1258,negated_conjecture,
% 2.01/1.00      ( k1_funct_1(sK4,sK5) = k1_funct_1(sK4,sK6) ),
% 2.01/1.00      inference(subtyping,[status(esa)],[c_18]) ).
% 2.01/1.00  
% 2.01/1.00  cnf(c_2342,plain,
% 2.01/1.00      ( k1_funct_1(k2_funct_1(sK4),k1_funct_1(sK4,sK5)) = sK6 ),
% 2.01/1.00      inference(light_normalisation,[status(thm)],[c_2337,c_1258]) ).
% 2.01/1.00  
% 2.01/1.00  cnf(c_2626,plain,
% 2.01/1.00      ( sK6 = sK5 ),
% 2.01/1.00      inference(demodulation,[status(thm)],[c_2338,c_2342]) ).
% 2.01/1.00  
% 2.01/1.00  cnf(c_1279,plain,
% 2.01/1.00      ( X0_48 != X1_48 | X2_48 != X1_48 | X2_48 = X0_48 ),
% 2.01/1.00      theory(equality) ).
% 2.01/1.00  
% 2.01/1.00  cnf(c_1946,plain,
% 2.01/1.00      ( sK6 != X0_48 | sK5 != X0_48 | sK5 = sK6 ),
% 2.01/1.00      inference(instantiation,[status(thm)],[c_1279]) ).
% 2.01/1.00  
% 2.01/1.00  cnf(c_1947,plain,
% 2.01/1.00      ( sK6 != sK5 | sK5 = sK6 | sK5 != sK5 ),
% 2.01/1.00      inference(instantiation,[status(thm)],[c_1946]) ).
% 2.01/1.00  
% 2.01/1.00  cnf(c_17,negated_conjecture,
% 2.01/1.00      ( sK5 != sK6 ),
% 2.01/1.00      inference(cnf_transformation,[],[f55]) ).
% 2.01/1.00  
% 2.01/1.00  cnf(c_1259,negated_conjecture,
% 2.01/1.00      ( sK5 != sK6 ),
% 2.01/1.00      inference(subtyping,[status(esa)],[c_17]) ).
% 2.01/1.00  
% 2.01/1.00  cnf(c_1274,plain,( X0_48 = X0_48 ),theory(equality) ).
% 2.01/1.00  
% 2.01/1.00  cnf(c_1310,plain,
% 2.01/1.00      ( sK5 = sK5 ),
% 2.01/1.00      inference(instantiation,[status(thm)],[c_1274]) ).
% 2.01/1.00  
% 2.01/1.00  cnf(contradiction,plain,
% 2.01/1.00      ( $false ),
% 2.01/1.00      inference(minisat,[status(thm)],[c_2626,c_1947,c_1259,c_1310]) ).
% 2.01/1.00  
% 2.01/1.00  
% 2.01/1.00  % SZS output end CNFRefutation for theBenchmark.p
% 2.01/1.00  
% 2.01/1.00  ------                               Statistics
% 2.01/1.00  
% 2.01/1.00  ------ General
% 2.01/1.00  
% 2.01/1.00  abstr_ref_over_cycles:                  0
% 2.01/1.00  abstr_ref_under_cycles:                 0
% 2.01/1.00  gc_basic_clause_elim:                   0
% 2.01/1.00  forced_gc_time:                         0
% 2.01/1.00  parsing_time:                           0.009
% 2.01/1.00  unif_index_cands_time:                  0.
% 2.01/1.00  unif_index_add_time:                    0.
% 2.01/1.00  orderings_time:                         0.
% 2.01/1.00  out_proof_time:                         0.01
% 2.01/1.00  total_time:                             0.116
% 2.01/1.00  num_of_symbols:                         56
% 2.01/1.00  num_of_terms:                           2281
% 2.01/1.00  
% 2.01/1.00  ------ Preprocessing
% 2.01/1.00  
% 2.01/1.00  num_of_splits:                          3
% 2.01/1.00  num_of_split_atoms:                     3
% 2.01/1.00  num_of_reused_defs:                     0
% 2.01/1.00  num_eq_ax_congr_red:                    14
% 2.01/1.00  num_of_sem_filtered_clauses:            1
% 2.01/1.00  num_of_subtypes:                        5
% 2.01/1.00  monotx_restored_types:                  1
% 2.01/1.00  sat_num_of_epr_types:                   0
% 2.01/1.00  sat_num_of_non_cyclic_types:            0
% 2.01/1.00  sat_guarded_non_collapsed_types:        1
% 2.01/1.00  num_pure_diseq_elim:                    0
% 2.01/1.00  simp_replaced_by:                       0
% 2.01/1.00  res_preprocessed:                       142
% 2.01/1.00  prep_upred:                             0
% 2.01/1.00  prep_unflattend:                        155
% 2.01/1.00  smt_new_axioms:                         0
% 2.01/1.00  pred_elim_cands:                        4
% 2.01/1.00  pred_elim:                              3
% 2.01/1.00  pred_elim_cl:                           3
% 2.01/1.00  pred_elim_cycles:                       5
% 2.01/1.00  merged_defs:                            0
% 2.01/1.00  merged_defs_ncl:                        0
% 2.01/1.00  bin_hyper_res:                          0
% 2.01/1.00  prep_cycles:                            4
% 2.01/1.00  pred_elim_time:                         0.021
% 2.01/1.00  splitting_time:                         0.
% 2.01/1.00  sem_filter_time:                        0.
% 2.01/1.00  monotx_time:                            0.001
% 2.01/1.00  subtype_inf_time:                       0.001
% 2.01/1.00  
% 2.01/1.00  ------ Problem properties
% 2.01/1.00  
% 2.01/1.00  clauses:                                25
% 2.01/1.00  conjectures:                            5
% 2.01/1.00  epr:                                    4
% 2.01/1.00  horn:                                   21
% 2.01/1.00  ground:                                 10
% 2.01/1.00  unary:                                  6
% 2.01/1.00  binary:                                 7
% 2.01/1.00  lits:                                   72
% 2.01/1.00  lits_eq:                                18
% 2.01/1.00  fd_pure:                                0
% 2.01/1.00  fd_pseudo:                              0
% 2.01/1.00  fd_cond:                                3
% 2.01/1.00  fd_pseudo_cond:                         1
% 2.01/1.00  ac_symbols:                             0
% 2.01/1.00  
% 2.01/1.00  ------ Propositional Solver
% 2.01/1.00  
% 2.01/1.00  prop_solver_calls:                      26
% 2.01/1.00  prop_fast_solver_calls:                 1075
% 2.01/1.00  smt_solver_calls:                       0
% 2.01/1.00  smt_fast_solver_calls:                  0
% 2.01/1.00  prop_num_of_clauses:                    596
% 2.01/1.00  prop_preprocess_simplified:             3755
% 2.01/1.00  prop_fo_subsumed:                       24
% 2.01/1.00  prop_solver_time:                       0.
% 2.01/1.00  smt_solver_time:                        0.
% 2.01/1.00  smt_fast_solver_time:                   0.
% 2.01/1.00  prop_fast_solver_time:                  0.
% 2.01/1.00  prop_unsat_core_time:                   0.
% 2.01/1.00  
% 2.01/1.00  ------ QBF
% 2.01/1.00  
% 2.01/1.00  qbf_q_res:                              0
% 2.01/1.00  qbf_num_tautologies:                    0
% 2.01/1.00  qbf_prep_cycles:                        0
% 2.01/1.00  
% 2.01/1.00  ------ BMC1
% 2.01/1.00  
% 2.01/1.00  bmc1_current_bound:                     -1
% 2.01/1.00  bmc1_last_solved_bound:                 -1
% 2.01/1.00  bmc1_unsat_core_size:                   -1
% 2.01/1.00  bmc1_unsat_core_parents_size:           -1
% 2.01/1.00  bmc1_merge_next_fun:                    0
% 2.01/1.00  bmc1_unsat_core_clauses_time:           0.
% 2.01/1.00  
% 2.01/1.00  ------ Instantiation
% 2.01/1.00  
% 2.01/1.00  inst_num_of_clauses:                    167
% 2.01/1.00  inst_num_in_passive:                    30
% 2.01/1.00  inst_num_in_active:                     111
% 2.01/1.00  inst_num_in_unprocessed:                26
% 2.01/1.00  inst_num_of_loops:                      140
% 2.01/1.00  inst_num_of_learning_restarts:          0
% 2.01/1.00  inst_num_moves_active_passive:          24
% 2.01/1.00  inst_lit_activity:                      0
% 2.01/1.00  inst_lit_activity_moves:                0
% 2.01/1.00  inst_num_tautologies:                   0
% 2.01/1.00  inst_num_prop_implied:                  0
% 2.01/1.00  inst_num_existing_simplified:           0
% 2.01/1.00  inst_num_eq_res_simplified:             0
% 2.01/1.00  inst_num_child_elim:                    0
% 2.01/1.00  inst_num_of_dismatching_blockings:      54
% 2.01/1.00  inst_num_of_non_proper_insts:           133
% 2.01/1.00  inst_num_of_duplicates:                 0
% 2.01/1.00  inst_inst_num_from_inst_to_res:         0
% 2.01/1.00  inst_dismatching_checking_time:         0.
% 2.01/1.00  
% 2.01/1.00  ------ Resolution
% 2.01/1.00  
% 2.01/1.00  res_num_of_clauses:                     0
% 2.01/1.00  res_num_in_passive:                     0
% 2.01/1.00  res_num_in_active:                      0
% 2.01/1.00  res_num_of_loops:                       146
% 2.01/1.00  res_forward_subset_subsumed:            5
% 2.01/1.00  res_backward_subset_subsumed:           0
% 2.01/1.00  res_forward_subsumed:                   0
% 2.01/1.00  res_backward_subsumed:                  0
% 2.01/1.00  res_forward_subsumption_resolution:     0
% 2.01/1.00  res_backward_subsumption_resolution:    0
% 2.01/1.00  res_clause_to_clause_subsumption:       90
% 2.01/1.00  res_orphan_elimination:                 0
% 2.01/1.00  res_tautology_del:                      42
% 2.01/1.00  res_num_eq_res_simplified:              0
% 2.01/1.00  res_num_sel_changes:                    0
% 2.01/1.00  res_moves_from_active_to_pass:          0
% 2.01/1.00  
% 2.01/1.00  ------ Superposition
% 2.01/1.00  
% 2.01/1.00  sup_time_total:                         0.
% 2.01/1.00  sup_time_generating:                    0.
% 2.01/1.00  sup_time_sim_full:                      0.
% 2.01/1.00  sup_time_sim_immed:                     0.
% 2.01/1.00  
% 2.01/1.00  sup_num_of_clauses:                     37
% 2.01/1.00  sup_num_in_active:                      24
% 2.01/1.00  sup_num_in_passive:                     13
% 2.01/1.00  sup_num_of_loops:                       26
% 2.01/1.00  sup_fw_superposition:                   17
% 2.01/1.00  sup_bw_superposition:                   2
% 2.01/1.00  sup_immediate_simplified:               11
% 2.01/1.00  sup_given_eliminated:                   0
% 2.01/1.00  comparisons_done:                       0
% 2.01/1.00  comparisons_avoided:                    0
% 2.01/1.00  
% 2.01/1.00  ------ Simplifications
% 2.01/1.00  
% 2.01/1.00  
% 2.01/1.00  sim_fw_subset_subsumed:                 0
% 2.01/1.00  sim_bw_subset_subsumed:                 0
% 2.01/1.00  sim_fw_subsumed:                        0
% 2.01/1.00  sim_bw_subsumed:                        0
% 2.01/1.00  sim_fw_subsumption_res:                 0
% 2.01/1.00  sim_bw_subsumption_res:                 0
% 2.01/1.00  sim_tautology_del:                      4
% 2.01/1.00  sim_eq_tautology_del:                   4
% 2.01/1.00  sim_eq_res_simp:                        0
% 2.01/1.00  sim_fw_demodulated:                     2
% 2.01/1.00  sim_bw_demodulated:                     2
% 2.01/1.00  sim_light_normalised:                   11
% 2.01/1.00  sim_joinable_taut:                      0
% 2.01/1.00  sim_joinable_simp:                      0
% 2.01/1.00  sim_ac_normalised:                      0
% 2.01/1.00  sim_smt_subsumption:                    0
% 2.01/1.00  
%------------------------------------------------------------------------------
